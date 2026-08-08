/*-------------------------------------------------------------------------
 *
 * standby.c
 *	  Misc functions used in Hot Standby mode.
 *
 *	All functions for handling RM_STANDBY_ID, which relate to
 *	AccessExclusiveLocks and starting snapshots for Hot Standby mode.
 *	Plus conflict recovery processing.
 *
 * 【模块总览(中文)】
 * 本文件承载热备(Hot Standby)模式的两大职责:
 * 1) RM_STANDBY_ID 这个 WAL 资源管理器(rmgr)的全部处理:重放
 *    (standby_redo)与生成(XLOG_STANDBY_LOCK / XLOG_RUNNING_XACTS /
 *    XLOG_INVALIDATIONS 三类记录);
 * 2) "恢复冲突"(recovery conflict)的解决:当 WAL 重放需要推进,
 *    而正在运行的查询事务妨碍了重放(快照过旧、持有锁、顶着
 *    buffer pin 等)时,决定是耐心等待还是取消/终止查询。
 *
 * 【热备的工作原理(简)】
 * 主库周期性把"当前运行事务的快照"(xl_running_xacts)与"当前持有
 * 的 AccessExclusiveLock 清单"(XLOG_STANDBY_LOCK)写进 WAL。备库
 * 重放时用这些信息模拟主库的事务环境:KnownAssignedXids 重建可见
 * 性,让只读查询继续运行;Startup 进程以自己的虚拟事务(vxid,见
 * InitRecoveryTransactionEnvironment)代理持有这些
 * AccessExclusiveLock,使正在执行的查询在同一套锁管理器上排队,
 * 从而与重放产生真实的锁等待关系。
 *
 * 【恢复冲突的两种解决手段】
 *  - 可以等:锁冲突(buffer pin、锁)发生时,重放方按
 *    max_standby_archive_delay / max_standby_streaming_delay 限定的
 *    时限耐心等待,超时才动手;
 *  - 必须动手:一旦决定取消,给目标后端发 PROCSIG_RECOVERY_CONFLICT
 *    信号,查询端在安全点检查 PGPROC->pendingRecoveryConflicts 并抛
 *    出 "canceling statement due to conflict with recovery" 错误
 *    (或死锁检查请求)。锁冲突只能"取消查询"来化解;快照冲突则可
 *    以靠等待(查询提交后重放自然继续)。
 *
 * 【结构】文件内容分四块:冲突判定与等待/取消逻辑(含三个超时
 * 处理器)、重放期间代理持有/释放 AccessExclusiveLock 的哈希表
 * 管理、RM_STANDBY_ID 的重放与 WAL 记录生成、冲突原因的文字描述。
 * 另有两个 GUC:max_standby_archive_delay / max_standby_streaming_delay
 * 决定等待时限(-1 表示无限等),log_recovery_conflict_waits 控制
 * 冲突等待的日志输出。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/standby.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"
#include "access/transam.h"
#include "access/twophase.h"
#include "access/xact.h"
#include "access/xloginsert.h"
#include "access/xlogrecovery.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "replication/slot.h"
#include "storage/bufmgr.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/sinvaladt.h"
#include "storage/standby.h"
#include "utils/hsearch.h"
#include "utils/injection_point.h"
#include "utils/ps_status.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"
#include "utils/wait_event.h"

/* User-settable GUC parameters */
/* (中文)用户可调的 GUC 参数:
 * - max_standby_archive_delay  : 重放源为归档恢复时,允许等待冲突
 *                                查询结束的最长时限(毫秒);-1 表示
 *                                无限等待;
 * - max_standby_streaming_delay: 重放源为流复制时,同一时限;
 * - log_recovery_conflict_waits: 为 true 时,把"等待恢复冲突解决"
 *                                记入日志(等待超过 deadlock_timeout
 *                                才输出,见 ResolveRecoveryConflictWithVirtualXIDs)。 */
int			max_standby_archive_delay = 30 * 1000;
int			max_standby_streaming_delay = 30 * 1000;
bool		log_recovery_conflict_waits = false;

/*
 * Keep track of all the exclusive locks owned by original transactions.
 * For each known exclusive lock, there is a RecoveryLockEntry in the
 * RecoveryLockHash hash table.  All RecoveryLockEntrys belonging to a
 * given XID are chained together so that we can find them easily.
 * For each original transaction that is known to have any such locks,
 * there is a RecoveryLockXidEntry in the RecoveryLockXidHash hash table,
 * which stores the head of the chain of its locks.
 */
/* (中文)恢复期间跟踪"原事务持有的 AccessExclusiveLock"的两张哈希表
 * (见 RecoveryLockEntry / RecoveryLockXidEntry 的注释):由
 * InitRecoveryTransactionEnvironment 创建,ShutdownRecoveryTransactionEnvironment
 * 销毁;只在 Startup 进程内使用,无并发问题。 */
typedef struct RecoveryLockEntry
{
	xl_standby_lock key;		/* hash key: xid, dbOid, relOid */
	struct RecoveryLockEntry *next; /* chain link */
} RecoveryLockEntry;
/* (中文)恢复锁哈希表条目:
 * - RecoveryLockEntry    : 一条已知的 AccessExclusiveLock。key 即
 *   xl_standby_lock(xid + dbOid + relOid),next 把它串进所属事务的
 *   锁链;
 * - RecoveryLockXidEntry : 一个"原事务(xid)"的锁链头。以 xid 为键,
 *   head 指向该事务持有的第一条 RecoveryLockEntry。
 * 两张表配合:RecoveryLockHash 用于去重(检查点会重复上报同样的锁,
 * 已有条目直接跳过加锁);RecoveryLockXidHash 用于在事务提交/中止
 * 重放时快速找到该事务的全部锁一并释放。 */
typedef struct RecoveryLockXidEntry
{
	TransactionId xid;			/* hash key -- must be first */
	struct RecoveryLockEntry *head; /* chain head */
} RecoveryLockXidEntry;

/* (中文)指向上述两张恢复锁哈希表的全局指针;RecoveryLockHash 为
 * NULL 还同时被 ShutdownRecoveryTransactionEnvironment 用作"是否已
 * 初始化"的判据。 */
static HTAB *RecoveryLockHash = NULL;
static HTAB *RecoveryLockXidHash = NULL;

/* Flags set by timeout handlers */
/* (中文)由超时处理器设置的标志,在睡眠唤醒后检查:
 * - got_standby_deadlock_timeout: STANDBY_DEADLOCK_TIMEOUT 到期
 *   (deadlock_timeout),需要请求冲突后端自查死锁;
 * - got_standby_delay_timeout   : STANDBY_TIMEOUT 到期(等待 buffer
 *   pin 冲突的耐心耗尽),应立即取消顶着 pin 的查询;
 * - got_standby_lock_timeout    : STANDBY_LOCK_TIMEOUT 到期(等待锁
 *   冲突的耐心耗尽),应取消持锁查询。
 * 类型为 volatile sig_atomic_t:超时处理器在信号上下文里置位,
 * 主逻辑在安全检查点读取。 */
static volatile sig_atomic_t got_standby_deadlock_timeout = false;
static volatile sig_atomic_t got_standby_delay_timeout = false;
static volatile sig_atomic_t got_standby_lock_timeout = false;

static void ResolveRecoveryConflictWithVirtualXIDs(VirtualTransactionId *waitlist,
												   RecoveryConflictReason reason,
												   uint32 wait_event_info,
												   bool report_waiting);
static void SendRecoveryConflictWithBufferPin(RecoveryConflictReason reason);
static XLogRecPtr LogCurrentRunningXacts(RunningTransactions CurrRunningXacts);
static void LogAccessExclusiveLocks(int nlocks, xl_standby_lock *locks);
static const char *get_recovery_conflict_desc(RecoveryConflictReason reason);

/*
 * InitRecoveryTransactionEnvironment
 *		Initialize tracking of our primary's in-progress transactions.
 *
 * We need to issue shared invalidations and hold locks. Holding locks
 * means others may want to wait on us, so we need to make a lock table
 * vxact entry like a real transaction. We could create and delete
 * lock table entries for each transaction but its simpler just to create
 * one permanent entry and leave it there all the time. Locks are then
 * acquired and released as needed. Yes, this means you can see the
 * Startup process in pg_locks once we have run this.
 */
/*
 * InitRecoveryTransactionEnvironment - (中文)初始化对主库"在途事务"的跟踪环境
 *
 * 【作用】standby 进入热备前由 Startup 进程调用一次,建立模拟主库
 * 事务环境所需的一切:创建两张恢复锁哈希表;以 sendOnly 身份注册
 * 进共享失效队列(SharedInvalBackendInit(true),重放期间它要向查询
 * 后端广播失效消息,但自己不需要读);为自己的虚拟事务 vxid 分配
 * LocalTransactionId 并在锁管理器登记(vxid 锁条目,此后重放持有
 * 的所有 AccessExclusiveLock 都记在这把虚拟事务名下);置
 * standbyState = STANDBY_INITIALIZED。
 *
 * 【设计思想】
 * - 重放期间代理持有锁的人必须是"真实存在"的事务,否则查询后端
 *   在锁管理器里等不到任何人。为每个原事务临时建/删锁表条目太
 *   麻烦,于是为 Startup 进程建一个常驻的 vxid 条目(这就是为什么
 *   运行热备后能在 pg_locks 里看到 Startup 进程);
 * - 不需要 XactLockTableInsert:行级锁(由 xid 持有)的持有者在备库
 *   上并不存在,查询后端只可能等表锁(vxid 持有),而查询都只拿
 *   AccessShareLock,永远不会等 xid;
 * - SharedInvalBackendInit 会把本地事务号计数器置为无效,必须先
 *   GetNextLocalTransactionId() 取一个有效值,锁管理器不接受无效
 *   的本地事务号。
 *
 * 【参数】无。
 * 【返回值】无;重复调用会因 RecoveryLockHash 非空而断言失败。
 */
void
InitRecoveryTransactionEnvironment(void)
{
	VirtualTransactionId vxid;
	HASHCTL		hash_ctl;

	Assert(RecoveryLockHash == NULL);	/* don't run this twice */

	/*
	 * Initialize the hash tables for tracking the locks held by each
	 * transaction.
	 */
	hash_ctl.keysize = sizeof(xl_standby_lock);
	hash_ctl.entrysize = sizeof(RecoveryLockEntry);
	RecoveryLockHash = hash_create("RecoveryLockHash",
								   64,
								   &hash_ctl,
								   HASH_ELEM | HASH_BLOBS);
	hash_ctl.keysize = sizeof(TransactionId);
	hash_ctl.entrysize = sizeof(RecoveryLockXidEntry);
	RecoveryLockXidHash = hash_create("RecoveryLockXidHash",
									  64,
									  &hash_ctl,
									  HASH_ELEM | HASH_BLOBS);

	/*
	 * Initialize shared invalidation management for Startup process, being
	 * careful to register ourselves as a sendOnly process so we don't need to
	 * read messages, nor will we get signaled when the queue starts filling
	 * up.
	 */
	SharedInvalBackendInit(true);

	/*
	 * Lock a virtual transaction id for Startup process.
	 *
	 * We need to do GetNextLocalTransactionId() because
	 * SharedInvalBackendInit() leaves localTransactionId invalid and the lock
	 * manager doesn't like that at all.
	 *
	 * Note that we don't need to run XactLockTableInsert() because nobody
	 * needs to wait on xids. That sounds a little strange, but table locks
	 * are held by vxids and row level locks are held by xids. All queries
	 * hold AccessShareLocks so never block while we write or lock new rows.
	 */
	MyProc->vxid.procNumber = MyProcNumber;
	vxid.procNumber = MyProcNumber;
	vxid.localTransactionId = GetNextLocalTransactionId();
	VirtualXactLockTableInsert(vxid);

	standbyState = STANDBY_INITIALIZED;
}

/*
 * ShutdownRecoveryTransactionEnvironment
 *		Shut down transaction tracking
 *
 * Prepare to switch from hot standby mode to normal operation. Shut down
 * recovery-time transaction tracking.
 *
 * This must be called even in shutdown of startup process if transaction
 * tracking has been initialized. Otherwise some locks the tracked
 * transactions were holding will not be released and may interfere with
 * the processes still running (but will exit soon later) at the exit of
 * startup process.
 */
/*
 * ShutdownRecoveryTransactionEnvironment - (中文)关闭恢复期事务跟踪环境
 *
 * 【作用】从热备模式切换回正常模式(或 Startup 进程退出)时调用:
 * 把所有 KnownAssignedXids 标记为结束、释放重放期间代理持有的全部
 * AccessExclusiveLock(StandbyReleaseAllLocks)、销毁两张哈希表、
 * 清理自己的 vxid 锁条目。
 *
 * 【设计思想】必须以 RecoveryLockHash 是否为 NULL 做幂等保护:进程
 * 退出路径上可能重复调用本函数(或跟踪从未初始化),直接返回即可。
 * 若漏掉释放,Startup 进程退出时这些代理锁可能一直卡住仍在运行的
 * 其他进程。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
ShutdownRecoveryTransactionEnvironment(void)
{
	/*
	 * Do nothing if RecoveryLockHash is NULL because that means that
	 * transaction tracking has not yet been initialized or has already been
	 * shut down.  This makes it safe to have possibly-redundant calls of this
	 * function during process exit.
	 */
	if (RecoveryLockHash == NULL)
		return;

	/* Mark all tracked in-progress transactions as finished. */
	ExpireAllKnownAssignedTransactionIds();

	/* Release all locks the tracked transactions were holding */
	StandbyReleaseAllLocks();

	/* Destroy the lock hash tables. */
	hash_destroy(RecoveryLockHash);
	hash_destroy(RecoveryLockXidHash);
	RecoveryLockHash = NULL;
	RecoveryLockXidHash = NULL;

	/* Cleanup our VirtualTransaction */
	VirtualXactLockTableCleanup();
}


/*
 * -----------------------------------------------------
 *		Standby wait timers and backend cancel logic
 * -----------------------------------------------------
 */

/*
 * Determine the cutoff time at which we want to start canceling conflicting
 * transactions.  Returns zero (a time safely in the past) if we are willing
 * to wait forever.
 */
/*
 * GetStandbyLimitTime - (中文)计算"开始取消冲突事务"的截止时刻
 *
 * 【作用】返回一个时间戳:在此之前冲突解决逻辑愿意等待,到达之后
 * 就该动手(取消查询/发起死锁检查)。算法是"最近一次收到 WAL 数据
 * 的时间 + 对应的延迟配置"——按重放源是流复制还是归档,分别使用
 * max_standby_streaming_delay 或 max_standby_archive_delay。
 *
 * 【设计思想】以"最后收到 WAL 数据"而非"当前时刻"为基准:备库
 * 收不到新 WAL(主库空闲)时,等待就不该计入时限;一旦主库送来新
 * 数据,时限重新开始计。配置为 -1 时返回 0——一个恒在过去的时间,
 * 语义是"愿意无限等"。
 *
 * 【参数】无。
 * 【返回值】截止时间戳(TimestampTz);0 表示无限等待。
 */
static TimestampTz
GetStandbyLimitTime(void)
{
	TimestampTz rtime;
	bool		fromStream;

	/*
	 * The cutoff time is the last WAL data receipt time plus the appropriate
	 * delay variable.  Delay of -1 means wait forever.
	 */
	GetXLogReceiptTime(&rtime, &fromStream);
	if (fromStream)
	{
		if (max_standby_streaming_delay < 0)
			return 0;			/* wait forever */
		return TimestampTzPlusMilliseconds(rtime, max_standby_streaming_delay);
	}
	else
	{
		if (max_standby_archive_delay < 0)
			return 0;			/* wait forever */
		return TimestampTzPlusMilliseconds(rtime, max_standby_archive_delay);
	}
}

#define STANDBY_INITIAL_WAIT_US  1000
/* (中文)冲突等待的退避计数状态:
 * - STANDBY_INITIAL_WAIT_US : 首次等待时长(1 毫秒);
 * - standbyWait_us          : 当前等待时长,每次等待后翻倍,上限
 *   1 秒(再久就会让重放明显变慢,且 pg_usleep 在部分平台上不可
 *   中断)。每处理完一个冲突事务会重置为初始值(见
 *   ResolveRecoveryConflictWithVirtualXIDs)。 */
static int	standbyWait_us = STANDBY_INITIAL_WAIT_US;

/*
 * Standby wait logic for ResolveRecoveryConflictWithVirtualXIDs.
 * We wait here for a while then return. If we decide we can't wait any
 * more then we return true, if we can wait some more return false.
 */
/*
 * WaitExceedsMaxStandbyDelay - (中文)判定冲突等待是否已超过耐心上限
 *
 * 【作用】ResolveRecoveryConflictWithVirtualXIDs 的等待循环里调用:
 * 先做一次中断检查(CHECK_FOR_INTERRUPTS,让 Startup 进程在等待中
 * 也能响应信号),再比较当前时刻与 GetStandbyLimitTime():已过限
 * 返回 true(该动手取消查询了);未过限则按退避策略睡
 * standbyWait_us 微秒(并上报等待事件),把下次等待时长翻倍
 * (上限 1 秒)后返回 false(继续等)。
 *
 * 【设计思想】轮询等待必须睡眠,否则会忙等烧 CPU;退避式增长避免
 * 在冲突很快就解决时做无谓长睡,又在冲突持久时把唤醒开销压下来。
 * 睡眠用 pg_usleep 而不是 latch:Startup 进程的唤醒源是 WAL 到达
 * (走不同 latch,见英文注释对 ProcWaitForSignal 的说明),简单轮询
 * 反而最直接。
 *
 * 【参数】
 *   wait_event_info —— 等待事件编号,上报 pg_stat_activity 用。
 * 【返回值】true:已超过耐心上限,应取消冲突查询;false:继续等待。
 */
static bool
WaitExceedsMaxStandbyDelay(uint32 wait_event_info)
{
	TimestampTz ltime;

	CHECK_FOR_INTERRUPTS();

	/* Are we past the limit time? */
	ltime = GetStandbyLimitTime();
	if (ltime && GetCurrentTimestamp() >= ltime)
		return true;

	/*
	 * Sleep a bit (this is essential to avoid busy-waiting).
	 */
	pgstat_report_wait_start(wait_event_info);
	pg_usleep(standbyWait_us);
	pgstat_report_wait_end();

	/*
	 * Progressively increase the sleep times, but not to more than 1s, since
	 * pg_usleep isn't interruptible on some platforms.
	 */
	standbyWait_us *= 2;
	if (standbyWait_us > 1000000)
		standbyWait_us = 1000000;

	return false;
}

/*
 * Log the recovery conflict.
 *
 * wait_start is the timestamp when the caller started to wait.
 * now is the timestamp when this function has been called.
 * wait_list is the list of virtual transaction ids assigned to
 * conflicting processes. still_waiting indicates whether
 * the startup process is still waiting for the recovery conflict
 * to be resolved or not.
 */
/*
 * LogRecoveryConflict - (中文)记录恢复冲突的等待/解决日志
 *
 * 【作用】在 log_recovery_conflict_waits 开启、且冲突等待超过
 * deadlock_timeout 时被调用:把等待时长(毫秒级)与冲突原因
 * (get_recovery_conflict_desc 的文字描述)记入日志。still_waiting
 * 为 true 表示仍在等待,并附上冲突进程的 PID 列表(通过 wait_list
 * 里每个 vxid 反查 PGPROC->pid;已不活跃的进程跳过);为 false
 * 表示冲突刚解决,记录"finished waiting"。
 *
 * 【设计思想】这是诊断"为什么 standby 重放被卡住"的核心日志:
 * 通过冲突进程 PID 列表,管理员可以立刻定位到是哪条查询挡住了
 * 重放。wait_list 只对"仍在等待"的调用有意义(断言保证)。
 *
 * 【参数】
 *   reason        —— 冲突原因(RecoveryConflictReason);
 *   wait_start    —— 开始等待的时刻;
 *   now           —— 本次调用的时刻;
 *   wait_list     —— 冲突事务的 vxid 数组(以无效 vxid 结尾),可为
 *                    NULL;
 *   still_waiting —— 是否仍在等待(决定日志文案与 detail)。
 * 【返回值】无。
 */
void
LogRecoveryConflict(RecoveryConflictReason reason, TimestampTz wait_start,
					TimestampTz now, VirtualTransactionId *wait_list,
					bool still_waiting)
{
	long		secs;
	int			usecs;
	long		msecs;
	StringInfoData buf;
	int			nprocs = 0;

	/*
	 * There must be no conflicting processes when the recovery conflict has
	 * already been resolved.
	 */
	Assert(still_waiting || wait_list == NULL);

	TimestampDifference(wait_start, now, &secs, &usecs);
	msecs = secs * 1000 + usecs / 1000;
	usecs = usecs % 1000;

	if (wait_list)
	{
		VirtualTransactionId *vxids;

		/* Construct a string of list of the conflicting processes */
		vxids = wait_list;
		while (VirtualTransactionIdIsValid(*vxids))
		{
			PGPROC	   *proc = ProcNumberGetProc(vxids->procNumber);

			/* proc can be NULL if the target backend is not active */
			if (proc)
			{
				if (nprocs == 0)
				{
					initStringInfo(&buf);
					appendStringInfo(&buf, "%d", proc->pid);
				}
				else
					appendStringInfo(&buf, ", %d", proc->pid);

				nprocs++;
			}

			vxids++;
		}
	}

	/*
	 * If wait_list is specified, report the list of PIDs of active
	 * conflicting backends in a detail message. Note that if all the backends
	 * in the list are not active, no detail message is logged.
	 */
	if (still_waiting)
	{
		ereport(LOG,
				errmsg("recovery still waiting after %ld.%03d ms: %s",
					   msecs, usecs, get_recovery_conflict_desc(reason)),
				nprocs > 0 ? errdetail_log_plural("Conflicting process: %s.",
												  "Conflicting processes: %s.",
												  nprocs, buf.data) : 0);
	}
	else
	{
		ereport(LOG,
				errmsg("recovery finished waiting after %ld.%03d ms: %s",
					   msecs, usecs, get_recovery_conflict_desc(reason)));
	}

	if (nprocs > 0)
		pfree(buf.data);
}

/*
 * This is the main executioner for any query backend that conflicts with
 * recovery processing. Judgement has already been passed on it within
 * a specific rmgr. Here we just issue the orders to the procs. The procs
 * then throw the required error as instructed.
 *
 * If report_waiting is true, "waiting" is reported in PS display and the
 * wait for recovery conflict is reported in the log, if necessary. If
 * the caller is responsible for reporting them, report_waiting should be
 * false. Otherwise, both the caller and this function report the same
 * thing unexpectedly.
 */
/*
 * ResolveRecoveryConflictWithVirtualXIDs - (中文)针对一组虚拟事务解决恢复冲突(等待/取消的核心执行者)
 *
 * 【作用】所有"针对特定后端集合"的冲突解决都会汇聚到这里。对
 * waitlist 里的每个虚拟事务(原事务在备库的代理):
 * 1) 等它消失(VirtualXactLock,即原事务提交/中止、代理锁释放);
 * 2) 每轮等待后问 WaitExceedsMaxStandbyDelay:超限则调用
 *    SignalRecoveryConflictWithVirtualXID 给该 vxid 的后端发
 *    PROCSIG_RECOVERY_CONFLICT 信号(它随后按 reason 抛出对应
 *    错误:快照/锁/表空间冲突),然后睡 5ms 避免对不响应后端
 *    的"信号轰炸";
 * 3) 可选地汇报:等待超 500ms 在 ps 显示加 "waiting" 后缀;等待
 *    超 deadlock_timeout 且开启 log_recovery_conflict_waits 时
 *    记日志(LogRecoveryConflict)。
 * 所有冲突事务都消失后,若曾记过日志,再记一条"finished waiting"。
 *
 * 【设计思想】
 * - "等"与"杀"双轨:重放不急于推进时尽量等(查询提交后重放自动
 *   继续,双方都不受伤);超时才动手,且动手后只发信号、不亲自
 *   等它死——错误处理在查询端自己的安全点完成,这是跨进程安全
 *   的唯一途径;
 * - 发信号与等待之间留 5ms 缓冲,防止系统高负载时向无响应的
 *   后端连续发信号把 CPU 打满;
 * - report_waiting 参数避免重复汇报:锁冲突路径的调用方
 *   (ResolveRecoveryConflictWithLock)自己已在 pg_locks 与 ps 里
 *   汇报过"等待中",这里就不再汇报。
 *
 * 【参数】
 *   waitlist       —— 冲突虚拟事务的数组,以无效 vxid 结尾(原地
 *                      遍历,不修改);
 *   reason         —— 冲突原因,决定信号投递后查询端的行为;
 *   wait_event_info—— 等待事件编号,上报 pg_stat_activity;
 *   report_waiting —— 是否由本函数负责 ps 后缀与日志汇报。
 * 【返回值】无。
 */
static void
ResolveRecoveryConflictWithVirtualXIDs(VirtualTransactionId *waitlist,
									   RecoveryConflictReason reason,
									   uint32 wait_event_info,
									   bool report_waiting)
{
	TimestampTz waitStart = 0;
	bool		waiting = false;
	bool		logged_recovery_conflict = false;

	/* Fast exit, to avoid a kernel call if there's no work to be done. */
	if (!VirtualTransactionIdIsValid(*waitlist))
		return;

	/* Set the wait start timestamp for reporting */
	if (report_waiting && (log_recovery_conflict_waits || update_process_title))
		waitStart = GetCurrentTimestamp();

	while (VirtualTransactionIdIsValid(*waitlist))
	{
		/* reset standbyWait_us for each xact we wait for */
		standbyWait_us = STANDBY_INITIAL_WAIT_US;

		/* wait until the virtual xid is gone */
		while (!VirtualXactLock(*waitlist, false))
		{
			/* Is it time to kill it? */
			if (WaitExceedsMaxStandbyDelay(wait_event_info))
			{
				bool		signaled;

				/*
				 * Now find out who to throw out of the balloon.
				 */
				Assert(VirtualTransactionIdIsValid(*waitlist));
				signaled = SignalRecoveryConflictWithVirtualXID(*waitlist, reason);

				/*
				 * Wait a little bit for it to die so that we avoid flooding
				 * an unresponsive backend when system is heavily loaded.
				 */
				if (signaled)
					pg_usleep(5000L);
			}

			if (waitStart != 0 && (!logged_recovery_conflict || !waiting))
			{
				TimestampTz now = 0;
				bool		maybe_log_conflict;
				bool		maybe_update_title;

				maybe_log_conflict = (log_recovery_conflict_waits && !logged_recovery_conflict);
				maybe_update_title = (update_process_title && !waiting);

				/* Get the current timestamp if not report yet */
				if (maybe_log_conflict || maybe_update_title)
					now = GetCurrentTimestamp();

				/*
				 * Report via ps if we have been waiting for more than 500
				 * msec (should that be configurable?)
				 */
				if (maybe_update_title &&
					TimestampDifferenceExceeds(waitStart, now, 500))
				{
					set_ps_display_suffix("waiting");
					waiting = true;
				}

				/*
				 * Emit the log message if the startup process is waiting
				 * longer than deadlock_timeout for recovery conflict.
				 */
				if (maybe_log_conflict &&
					TimestampDifferenceExceeds(waitStart, now, DeadlockTimeout))
				{
					LogRecoveryConflict(reason, waitStart, now, waitlist, true);
					logged_recovery_conflict = true;
				}
			}
		}

		/* The virtual transaction is gone now, wait for the next one */
		waitlist++;
	}

	/*
	 * Emit the log message if recovery conflict was resolved but the startup
	 * process waited longer than deadlock_timeout for it.
	 */
	if (logged_recovery_conflict)
		LogRecoveryConflict(reason, waitStart, GetCurrentTimestamp(),
							NULL, false);

	/* reset ps display to remove the suffix if we added one */
	if (waiting)
		set_ps_display_remove_suffix();

}

/*
 * Generate whatever recovery conflicts are needed to eliminate snapshots that
 * might see XIDs <= snapshotConflictHorizon as still running.
 *
 * snapshotConflictHorizon cutoffs are our standard approach to generating
 * granular recovery conflicts.  Note that InvalidTransactionId values are
 * interpreted as "definitely don't need any conflicts" here, which is a
 * general convention that WAL records can (and often do) depend on.
 */
/*
 * ResolveRecoveryConflictWithSnapshot - (中文)消除"能看到旧 XID"的快照冲突
 *
 * 【作用】WAL 重放删除/修改数据前调用(各 rmgr 在重放记录时调用):
 * 任何"仍然认为 snapshotConflictHorizon 之前的 XID 还在运行"的快照
 * 都会妨碍本次重放的可见性,必须让持有它们的查询退出。做法:用
 * GetConflictingVirtualXIDs(snapshotConflictHorizon, dbOid) 找出
 * 所有这类后端,交给 ResolveRecoveryConflictWithVirtualXIDs 处理
 * (等待超限后取消)。若开了逻辑解码且是目录表,还顺带作废过时的
 * 复制槽(InvalidateObsoleteReplicationSlots)。
 *
 * 【设计思想】
 * - snapshotConflictHorizon 即 WAL 记录里附带的"冲突阈值":XID <=
 *   该值的快照都有问题。InvalidTransactionId 表示"本记录无需任何
 *   冲突"(通用约定,大量 WAL 记录依赖这一点),直接返回;
 * - 这是细粒度冲突的标准手段:只有"确实会看到旧数据"的查询才被
 *   波及,其余查询不受影响;
 * - 与锁冲突不同,这类冲突大多能靠"等待查询提交"自然化解,取消
 *   只是超时后的保底手段。
 *
 * 【参数】
 *   snapshotConflictHorizon —— 快照冲突阈值 XID(无效时视为无需
 *                               冲突,直接返回);
 *   isCatalogRel            —— 是否系统目录表(决定是否顺带作废
 *                               复制槽);
 *   locator                 —— 受影响关系的定位符(提供 dbOid,
 *                               用于筛选同库后端)。
 * 【返回值】无。
 */
void
ResolveRecoveryConflictWithSnapshot(TransactionId snapshotConflictHorizon,
									bool isCatalogRel,
									RelFileLocator locator)
{
	VirtualTransactionId *backends;

	/*
	 * If we get passed InvalidTransactionId then we do nothing (no conflict).
	 *
	 * This can happen whenever the changes in the WAL record do not affect
	 * visibility on a standby. For example: a record that only freezes an
	 * xmax from a locker.
	 *
	 * It's also quite common with records generated during index deletion
	 * (original execution of the deletion can reason that a recovery conflict
	 * which is sufficient for the deletion operation must take place before
	 * replay of the deletion record itself).
	 */
	if (!TransactionIdIsValid(snapshotConflictHorizon))
		return;

	Assert(TransactionIdIsNormal(snapshotConflictHorizon));
	backends = GetConflictingVirtualXIDs(snapshotConflictHorizon,
										 locator.dbOid);
	ResolveRecoveryConflictWithVirtualXIDs(backends,
										   RECOVERY_CONFLICT_SNAPSHOT,
										   WAIT_EVENT_RECOVERY_CONFLICT_SNAPSHOT,
										   true);

	/*
	 * Note that WaitExceedsMaxStandbyDelay() is not taken into account here
	 * (as opposed to ResolveRecoveryConflictWithVirtualXIDs() above). That
	 * seems OK, given that this kind of conflict should not normally be
	 * reached, e.g. due to using a physical replication slot.
	 */
	if (IsLogicalDecodingEnabled() && isCatalogRel)
		InvalidateObsoleteReplicationSlots(RS_INVAL_HORIZON, 0, locator.dbOid,
										   snapshotConflictHorizon);
}

/*
 * Variant of ResolveRecoveryConflictWithSnapshot that works with
 * FullTransactionId values
 */
/*
 * ResolveRecoveryConflictWithSnapshotFullXid - (中文)FullTransactionId 版本的快照冲突解决
 *
 * 【作用】与 ResolveRecoveryConflictWithSnapshot 相同,只是输入是
 * 64 位 FullTransactionId(某些 WAL 记录携带的冲突阈值是完整 XID):
 * 先与当前 nextXid 做差判断,若该值"距离现在不超过半个事务号空间"
 * (说明它尚未经历 XID 回卷),截断为 32 位 TransactionId 后转交
 * ResolveRecoveryConflictWithSnapshot 处理。
 *
 * 【设计思想】32 位 XID 会回卷(环绕),如果记录里的完整 XID 已经
 * 老到"回卷发生在其之后",那么 32 位截断值会失去意义,且也不可能有
 * 快照还看得见它——直接跳过冲突处理是正确的。
 *
 * 【参数】
 *   snapshotConflictHorizon —— 64 位快照冲突阈值;
 *   isCatalogRel / locator   —— 同 ResolveRecoveryConflictWithSnapshot。
 * 【返回值】无。
 */
void
ResolveRecoveryConflictWithSnapshotFullXid(FullTransactionId snapshotConflictHorizon,
										   bool isCatalogRel,
										   RelFileLocator locator)
{
	/*
	 * ResolveRecoveryConflictWithSnapshot operates on 32-bit TransactionIds,
	 * so truncate the logged FullTransactionId.  If the logged value is very
	 * old, so that XID wrap-around already happened on it, there can't be any
	 * snapshots that still see it.
	 */
	FullTransactionId nextXid = ReadNextFullTransactionId();
	uint64		diff;

	diff = U64FromFullTransactionId(nextXid) -
		U64FromFullTransactionId(snapshotConflictHorizon);
	if (diff < MaxTransactionId / 2)
	{
		TransactionId truncated;

		truncated = XidFromFullTransactionId(snapshotConflictHorizon);
		ResolveRecoveryConflictWithSnapshot(truncated,
											isCatalogRel,
											locator);
	}
}

void
ResolveRecoveryConflictWithTablespace(Oid tsid)
{
/*
 * ResolveRecoveryConflictWithTablespace - (中文)解决表空间删除导致的恢复冲突
 *
 * 【作用】重放 DROP TABLESPACE 记录时调用:备库上可能有查询正在用
 * 该表空间放临时文件,不赶走它们就无法删除表空间目录。做法:找出
 * 全部后端(GetConflictingVirtualXIDs 传 InvalidTransactionId +
 * InvalidOid,即"无差别全部"),立即要求全部取消,不留等待期。
 *
 * 【设计思想】DROP TABLESPACE 是非事务性操作,重放它时没有"等冲突
 * 事务提交"的耐心资本——临时文件可能在任意时刻被创建,越早清场
 * 越安全;temp_tablespace 参数对已不存在的表空间会自动忽略,所以
 * 只需处理当前正在使用它的进程。英文注释自嘲地引用"核弹清场"
 * (Nuke the entire site from orbit)。
 *
 * 【参数】
 *   tsid —— 被删除的表空间 OID(当前仅用于记录)。
 * 【返回值】无。
 */
	VirtualTransactionId *temp_file_users;

	/*
	 * Standby users may be currently using this tablespace for their
	 * temporary files. We only care about current users because
	 * temp_tablespace parameter will just ignore tablespaces that no longer
	 * exist.
	 *
	 * Ask everybody to cancel their queries immediately so we can ensure no
	 * temp files remain and we can remove the tablespace. Nuke the entire
	 * site from orbit, it's the only way to be sure.
	 *
	 * XXX: We could work out the pids of active backends using this
	 * tablespace by examining the temp filenames in the directory. We would
	 * then convert the pids into VirtualXIDs before attempting to cancel
	 * them.
	 *
	 * We don't wait for commit because drop tablespace is non-transactional.
	 */
	temp_file_users = GetConflictingVirtualXIDs(InvalidTransactionId,
												InvalidOid);
	ResolveRecoveryConflictWithVirtualXIDs(temp_file_users,
										   RECOVERY_CONFLICT_TABLESPACE,
										   WAIT_EVENT_RECOVERY_CONFLICT_TABLESPACE,
										   true);
}

void
ResolveRecoveryConflictWithDatabase(Oid dbid)
{
/*
 * ResolveRecoveryConflictWithDatabase - (中文)解决数据库删除导致的恢复冲突
 *
 * 【作用】重放 DROP DATABASE 记录时调用:把仍在连接该数据库的后端
 * 全部赶走(循环:计数 -> 全体发 PROCSIG_RECOVERY_CONFLICT ->
 * 睡 10ms 再查),直到 CountDBBackends(dbid) 归零。
 *
 * 【设计思想】不使用"等待 vxid 消失"的那套机制:完全空闲的会话
 * (没有任何活动事务)不会被 vxid 等待捕获,却会一直占着连接——
 * 删库场景下没有耐心可言,直接无差别清场,简单粗暴但正确。无需
 * 额外加锁:此时 Startup 进程已持有该库的 AccessExclusiveLock,
 * 任何想新连进来的进程都会在 InitPostgres 里等锁、随后发现库已
 * 不存在而断开。每次信号后睡 10ms 是为避免向无响应后端"信号
 * 轰炸"。
 *
 * 【参数】
 *   dbid —— 被删除的数据库 OID。
 * 【返回值】无。
 */
	/*
	 * We don't do ResolveRecoveryConflictWithVirtualXIDs() here since that
	 * only waits for transactions and completely idle sessions would block
	 * us. This is rare enough that we do this as simply as possible: no wait,
	 * just force them off immediately.
	 *
	 * No locking is required here because we already acquired
	 * AccessExclusiveLock. Anybody trying to connect while we do this will
	 * block during InitPostgres() and then disconnect when they see the
	 * database has been removed.
	 */
	while (CountDBBackends(dbid) > 0)
	{
		SignalRecoveryConflictWithDatabase(dbid, RECOVERY_CONFLICT_DATABASE);

		/*
		 * Wait awhile for them to die so that we avoid flooding an
		 * unresponsive backend when system is heavily loaded.
		 */
		pg_usleep(10000);
	}
}

/*
 * ResolveRecoveryConflictWithLock is called from ProcSleep()
 * to resolve conflicts with other backends holding relation locks.
 *
 * The WaitLatch sleep normally done in ProcSleep()
 * (when not InHotStandby) is performed here, for code clarity.
 *
 * We either resolve conflicts immediately or set a timeout to wake us at
 * the limit of our patience.
 *
 * Resolve conflicts by canceling to all backends holding a conflicting
 * lock.  As we are already queued to be granted the lock, no new lock
 * requests conflicting with ours will be granted in the meantime.
 *
 * We also must check for deadlocks involving the Startup process and
 * hot-standby backend processes. If deadlock_timeout is reached in
 * this function, all the backends holding the conflicting locks are
 * requested to check themselves for deadlocks.
 *
 * logging_conflict should be true if the recovery conflict has not been
 * logged yet even though logging is enabled. After deadlock_timeout is
 * reached and the request for deadlock check is sent, we wait again to
 * be signaled by the release of the lock if logging_conflict is false.
 * Otherwise we return without waiting again so that the caller can report
 * the recovery conflict. In this case, then, this function is called again
 * with logging_conflict=false (because the recovery conflict has already
 * been logged) and we will wait again for the lock to be released.
 */
/*
 * ResolveRecoveryConflictWithLock - (中文)解决锁冲突:热备下 Startup 进程的锁等待路径
 *
 * 【作用】Startup 进程在锁管理器里排队等待一把关系锁时
 * (ProcSleep 检测到 InHotStandby 后调用本函数替代常规睡眠):
 * 1) 若已过耐心上限(ltime),立即找出所有持冲突锁的后端
 *    (GetLockConflicts),经 ResolveRecoveryConflictWithVirtualXIDs
 *    依次取消它们;
 * 2) 否则设置两个超时(STANDBY_LOCK_TIMEOUT = 耐心上限,
 *    STANDBY_DEADLOCK_TIMEOUT = deadlock_timeout 之后)后,用
 *    ProcWaitForSignal 睡在锁释放信号上;
 * 3) 被唤醒后:锁超时到期则退出(等下次调用时取消持锁者);死锁
 *    超时到期则给所有持锁后端发"自查死锁"请求
 *    (RECOVERY_CONFLICT_STARTUP_DEADLOCK),必要时再睡一轮。
 *
 * 【设计思想】
 * - 这是热备死锁的核心防线:查询等待的锁必在某把 AccessExclusiveLock
 *   之后,而后者只能等 Startup 重放"事务结束记录"才释放;若
 *   Startup 又反过来等查询,就成环了。Startup 不亲自跑死锁检测
 *   (它不能回滚自己),而是请持锁后端自查,宁可杀查询也不杀自己;
 * - "排队即必胜":既然本进程已排在冲突队列里,就不会再有新的
 *   冲突锁授予出去,所以取消只需针对当前持有者;
 * - 日志与汇报交由调用者(WaitOnLock 已汇报过等待),因此传
 *   report_waiting = false;
 * - waitStart 无锁更新(原子读写):pg_locks 的 waitstart 可能短暂
 *   为 NULL,可接受。
 *
 * 【参数】
 *   locktag         —— 本进程正在等待的锁标识;
 *   logging_conflict—— 是否尚未记录该冲突的日志(决定死锁超时后
 *                       是否立即返回让调用者记日志)。
 * 【返回值】无(锁释放或冲突解决后返回,调用者继续)。
 */
void
ResolveRecoveryConflictWithLock(LOCKTAG locktag, bool logging_conflict)
{
	TimestampTz ltime;
	TimestampTz now;

	Assert(InHotStandby);

	ltime = GetStandbyLimitTime();
	now = GetCurrentTimestamp();

	/*
	 * Update waitStart if first time through after the startup process
	 * started waiting for the lock. It should not be updated every time
	 * ResolveRecoveryConflictWithLock() is called during the wait.
	 *
	 * Use the current time obtained for comparison with ltime as waitStart
	 * (i.e., the time when this process started waiting for the lock). Since
	 * getting the current time newly can cause overhead, we reuse the
	 * already-obtained time to avoid that overhead.
	 *
	 * Note that waitStart is updated without holding the lock table's
	 * partition lock, to avoid the overhead by additional lock acquisition.
	 * This can cause "waitstart" in pg_locks to become NULL for a very short
	 * period of time after the wait started even though "granted" is false.
	 * This is OK in practice because we can assume that users are likely to
	 * look at "waitstart" when waiting for the lock for a long time.
	 */
	if (pg_atomic_read_u64(&MyProc->waitStart) == 0)
		pg_atomic_write_u64(&MyProc->waitStart, now);

	if (now >= ltime && ltime != 0)
	{
		/*
		 * We're already behind, so clear a path as quickly as possible.
		 */
		VirtualTransactionId *backends;

		backends = GetLockConflicts(&locktag, AccessExclusiveLock, NULL);

		/*
		 * Prevent ResolveRecoveryConflictWithVirtualXIDs() from reporting
		 * "waiting" in PS display by disabling its argument report_waiting
		 * because the caller, WaitOnLock(), has already reported that.
		 */
		ResolveRecoveryConflictWithVirtualXIDs(backends,
											   RECOVERY_CONFLICT_LOCK,
											   PG_WAIT_LOCK | locktag.locktag_type,
											   false);
	}
	else
	{
		/*
		 * Wait (or wait again) until ltime, and check for deadlocks as well
		 * if we will be waiting longer than deadlock_timeout
		 */
		EnableTimeoutParams timeouts[2];
		int			cnt = 0;

		if (ltime != 0)
		{
			got_standby_lock_timeout = false;
			timeouts[cnt].id = STANDBY_LOCK_TIMEOUT;
			timeouts[cnt].type = TMPARAM_AT;
			timeouts[cnt].fin_time = ltime;
			cnt++;
		}

		got_standby_deadlock_timeout = false;
		timeouts[cnt].id = STANDBY_DEADLOCK_TIMEOUT;
		timeouts[cnt].type = TMPARAM_AFTER;
		timeouts[cnt].delay_ms = DeadlockTimeout;
		cnt++;

		enable_timeouts(timeouts, cnt);
	}

	/* Wait to be signaled by the release of the Relation Lock */
	ProcWaitForSignal(PG_WAIT_LOCK | locktag.locktag_type);

	/*
	 * Exit if ltime is reached. Then all the backends holding conflicting
	 * locks will be canceled in the next ResolveRecoveryConflictWithLock()
	 * call.
	 */
	if (got_standby_lock_timeout)
		goto cleanup;

	if (got_standby_deadlock_timeout)
	{
		VirtualTransactionId *backends;

		backends = GetLockConflicts(&locktag, AccessExclusiveLock, NULL);

		/* Quick exit if there's no work to be done */
		if (!VirtualTransactionIdIsValid(*backends))
			goto cleanup;

		/*
		 * Send signals to all the backends holding the conflicting locks, to
		 * ask them to check themselves for deadlocks.
		 */
		while (VirtualTransactionIdIsValid(*backends))
		{
			(void) SignalRecoveryConflictWithVirtualXID(*backends,
														RECOVERY_CONFLICT_STARTUP_DEADLOCK);
			backends++;
		}

		/*
		 * Exit if the recovery conflict has not been logged yet even though
		 * logging is enabled, so that the caller can log that. Then
		 * RecoveryConflictWithLock() is called again and we will wait again
		 * for the lock to be released.
		 */
		if (logging_conflict)
			goto cleanup;

		/*
		 * Wait again here to be signaled by the release of the Relation Lock,
		 * to prevent the subsequent RecoveryConflictWithLock() from causing
		 * deadlock_timeout and sending a request for deadlocks check again.
		 * Otherwise the request continues to be sent every deadlock_timeout
		 * until the relation locks are released or ltime is reached.
		 */
		got_standby_deadlock_timeout = false;
		ProcWaitForSignal(PG_WAIT_LOCK | locktag.locktag_type);
	}

cleanup:

	/*
	 * Clear any timeout requests established above.  We assume here that the
	 * Startup process doesn't have any other outstanding timeouts than those
	 * used by this function. If that stops being true, we could cancel the
	 * timeouts individually, but that'd be slower.
	 */
	disable_all_timeouts(false);
	got_standby_lock_timeout = false;
	got_standby_deadlock_timeout = false;
}

/*
 * ResolveRecoveryConflictWithBufferPin is called from LockBufferForCleanup()
 * to resolve conflicts with other backends holding buffer pins.
 *
 * The ProcWaitForSignal() sleep normally done in LockBufferForCleanup()
 * (when not InHotStandby) is performed here, for code clarity.
 *
 * We either resolve conflicts immediately or set a timeout to wake us at
 * the limit of our patience.
 *
 * Resolve conflicts by sending a PROCSIG signal to all backends to check if
 * they hold one of the buffer pins that is blocking Startup process. If so,
 * those backends will take an appropriate error action, ERROR or FATAL.
 *
 * We also must check for deadlocks.  Deadlocks occur because if queries
 * wait on a lock, that must be behind an AccessExclusiveLock, which can only
 * be cleared if the Startup process replays a transaction completion record.
 * If Startup process is also waiting then that is a deadlock. The deadlock
 * can occur if the query is waiting and then the Startup sleeps, or if
 * Startup is sleeping and the query waits on a lock. We protect against
 * only the former sequence here, the latter sequence is checked prior to
 * the query sleeping, in CheckRecoveryConflictDeadlock().
 *
 * Deadlocks are extremely rare, and relatively expensive to check for,
 * so we don't do a deadlock check right away ... only if we have had to wait
 * at least deadlock_timeout.
 */
/*
 * ResolveRecoveryConflictWithBufferPin - (中文)解决 buffer pin 冲突:等待 pin 释放或取消持有者
 *
 * 【作用】LockBufferForCleanup 发现要清理的缓冲区被别的后端 pin 着、
 * 而本进程处于热备模式时调用(替代常规的 ProcWaitForSignal 睡眠):
 * 1) 已过耐心上限则立即给所有后端发"检查是否持有此 pin"
 *    (RECOVERY_CONFLICT_BUFFERPIN 信号,无辜者忽略,持有者抛错);
 * 2) 否则设 STANDBY_TIMEOUT(耐心上限)与 STANDBY_DEADLOCK_TIMEOUT
 *    (deadlock_timeout)两个超时,睡在 ProcWaitForSignal 上等待
 *    UnpinBuffer 或超时;
 * 3) 唤醒后按原因分派:delay 超时 -> 再发一次"取消 pin 持有者";
 *    死锁超时 -> 发"pin 死锁自查"请求
 *    (RECOVERY_CONFLICT_BUFFERPIN_DEADLOCK,因为常规死锁检测器
 *    不跟踪 buffer pin,必须由持有者自查)。
 *
 * 【设计思想】热备下 buffer pin 冲突的超时/死锁语义与锁冲突同源
 * (见 ResolveRecoveryConflictWithLock 的注释):查询等锁可能等成
 * 对 Startup 的死锁,这里用"请持有者自查"化解;pin 冲突本质只能
 * 等持有者自己放,所以超时后只能发信号求他们取消查询。
 *
 * 【参数】无。
 * 【返回值】无(冲突解决或信号发出后返回)。
 */
void
ResolveRecoveryConflictWithBufferPin(void)
{
	TimestampTz ltime;

	Assert(InHotStandby);

	ltime = GetStandbyLimitTime();

	if (GetCurrentTimestamp() >= ltime && ltime != 0)
	{
		/*
		 * We're already behind, so clear a path as quickly as possible.
		 */
		SendRecoveryConflictWithBufferPin(RECOVERY_CONFLICT_BUFFERPIN);
	}
	else
	{
		/*
		 * Wake up at ltime, and check for deadlocks as well if we will be
		 * waiting longer than deadlock_timeout
		 */
		EnableTimeoutParams timeouts[2];
		int			cnt = 0;

		if (ltime != 0)
		{
			timeouts[cnt].id = STANDBY_TIMEOUT;
			timeouts[cnt].type = TMPARAM_AT;
			timeouts[cnt].fin_time = ltime;
			cnt++;
		}

		got_standby_deadlock_timeout = false;
		timeouts[cnt].id = STANDBY_DEADLOCK_TIMEOUT;
		timeouts[cnt].type = TMPARAM_AFTER;
		timeouts[cnt].delay_ms = DeadlockTimeout;
		cnt++;

		enable_timeouts(timeouts, cnt);
	}

	/*
	 * Wait to be signaled by UnpinBuffer() or for the wait to be interrupted
	 * by one of the timeouts established above.
	 *
	 * We assume that only UnpinBuffer() and the timeout requests established
	 * above can wake us up here. WakeupRecovery() called by walreceiver or
	 * SIGHUP signal handler, etc cannot do that because it uses the different
	 * latch from that ProcWaitForSignal() waits on.
	 */
	ProcWaitForSignal(WAIT_EVENT_BUFFER_CLEANUP);

	if (got_standby_delay_timeout)
		SendRecoveryConflictWithBufferPin(RECOVERY_CONFLICT_BUFFERPIN);
	else if (got_standby_deadlock_timeout)
	{
		/*
		 * Send out a request for hot-standby backends to check themselves for
		 * deadlocks.
		 *
		 * XXX The subsequent ResolveRecoveryConflictWithBufferPin() will wait
		 * to be signaled by UnpinBuffer() again and send a request for
		 * deadlocks check if deadlock_timeout happens. This causes the
		 * request to continue to be sent every deadlock_timeout until the
		 * buffer is unpinned or ltime is reached. This would increase the
		 * workload in the startup process and backends. In practice it may
		 * not be so harmful because the period that the buffer is kept pinned
		 * is basically no so long. But we should fix this?
		 */
		SendRecoveryConflictWithBufferPin(RECOVERY_CONFLICT_BUFFERPIN_DEADLOCK);
	}

	/*
	 * Clear any timeout requests established above.  We assume here that the
	 * Startup process doesn't have any other timeouts than what this function
	 * uses.  If that stops being true, we could cancel the timeouts
	 * individually, but that'd be slower.
	 */
	disable_all_timeouts(false);
	got_standby_delay_timeout = false;
	got_standby_deadlock_timeout = false;
}

static void
SendRecoveryConflictWithBufferPin(RecoveryConflictReason reason)
{
/*
 * SendRecoveryConflictWithBufferPin - (中文)向全体后端广播"检查是否持有阻塞 pin"的信号
 *
 * 【作用】ResolveRecoveryConflictWithBufferPin 的辅助函数:给所有
 * 后端(按数据库维度广播,传 InvalidOid 即全体)发一次
 * PROCSIG_RECOVERY_CONFLICT 信号,原因是 BUFFERPIN 或
 * BUFFERPIN_DEADLOCK。每个后端在安全点检查自己是否持有那块正被
 * Startup 等待的 pin(通过 PGPROC->pendingRecoveryConflicts 与
 * HoldingBufferPinThatDelaysRecovery),持有者抛出对应错误。
 *
 * 【设计思想】广播比精确定位持有者便宜且健壮:绝大多数后端无辜,
 * 让每个后端自行判定命运(信号处理器里读 PGPROC 标志,零锁开销)。
 *
 * 【参数】
 *   reason —— RECOVERY_CONFLICT_BUFFERPIN(催促放 pin)或
 *             RECOVERY_CONFLICT_BUFFERPIN_DEADLOCK(请自查死锁)。
 * 【返回值】无。
 */
	Assert(reason == RECOVERY_CONFLICT_BUFFERPIN ||
		   reason == RECOVERY_CONFLICT_BUFFERPIN_DEADLOCK);

	/*
	 * We send signal to all backends to ask them if they are holding the
	 * buffer pin which is delaying the Startup process. Most of them will be
	 * innocent, but we let the SIGUSR1 handling in each backend decide their
	 * own fate.
	 */
	SignalRecoveryConflictWithDatabase(InvalidOid, reason);
}

/*
 * In Hot Standby perform early deadlock detection.  We abort the lock
 * wait if we are about to sleep while holding the buffer pin that Startup
 * process is waiting for.
 *
 * Note: this code is pessimistic, because there is no way for it to
 * determine whether an actual deadlock condition is present: the lock we
 * need to wait for might be unrelated to any held by the Startup process.
 * Sooner or later, this mechanism should get ripped out in favor of somehow
 * accounting for buffer locks in DeadLockCheck().  However, errors here
 * seem to be very low-probability in practice, so for now it's not worth
 * the trouble.
 */
/*
 * CheckRecoveryConflictDeadlock - (中文)热备下查询端的"早期死锁检测"
 *
 * 【作用】查询后端在锁管理器里即将入睡(LockAcquire 排队成功、准备
 * 睡眠)之前调用(ProcSleep 检测 InHotStandby 时):若本进程正顶着
 * 一块"Startup 正在等待"的 buffer pin,而它即将去等待另一把锁,
 * 则立刻取消当前语句——因为那可能形成"查询等锁 -> 锁等 Startup ->
 * Startup 等 pin -> pin 在本进程手里"的死锁环。
 *
 * 【设计思想】这是保守检测:本函数无法确定死锁真的存在(要等的锁
 * 可能与 Startup 毫无关系),宁可误杀也不赌;真正的死锁检测器
 * (DeadLockCheck)不跟踪 buffer pin,因此这个"旁路"在可预见的
 * 未来仍会保留。只取消当前事务(不 FATAL),若 pin 由父事务持有,
 * Startup 可能还要继续等,属于已知的局限。
 *
 * 【参数】无。
 * 【返回值】无;检测到冲突时抛出
 * "canceling statement due to conflict with recovery" 错误。
 */
void
CheckRecoveryConflictDeadlock(void)
{
	Assert(!InRecovery);		/* do not call in Startup process */

	if (!HoldingBufferPinThatDelaysRecovery())
		return;

	/*
	 * Error message should match ProcessInterrupts() but we avoid calling
	 * that because we aren't handling an interrupt at this point. Note that
	 * we only cancel the current transaction here, so if we are in a
	 * subtransaction and the pin is held by a parent, then the Startup
	 * process will continue to wait even though we have avoided deadlock.
	 */
	ereport(ERROR,
			(errcode(ERRCODE_T_R_DEADLOCK_DETECTED),
			 errmsg("canceling statement due to conflict with recovery"),
			 errdetail("User transaction caused buffer deadlock with recovery.")));
}


/* --------------------------------
 *		timeout handler routines
 * --------------------------------
 */

/*
 * StandbyDeadLockHandler() will be called if STANDBY_DEADLOCK_TIMEOUT is
 * exceeded.
 */
/*
 * StandbyDeadLockHandler - (中文)STANDBY_DEADLOCK_TIMEOUT 超时处理器
 *
 * 【作用】Startup 进程等待锁/buffer pin 超过 deadlock_timeout 时,
 * 超时机制调用本函数:把 got_standby_deadlock_timeout 置为 true。
 * 等待循环(ResolveRecoveryConflictWithLock /
 * ResolveRecoveryConflictWithBufferPin)被唤醒后看到该标志,就会给
 * 冲突后端发"自查死锁"请求。
 *
 * 【设计思想】超时处理器运行在信号上下文,只能做"记账";真正的
 * 死锁检查请求由主流程发出。这也是"热备死锁由持锁端自查"机制
 * 的触发器。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
StandbyDeadLockHandler(void)
{
	got_standby_deadlock_timeout = true;
}

/*
 * StandbyTimeoutHandler() will be called if STANDBY_TIMEOUT is exceeded.
 */
/*
 * StandbyTimeoutHandler - (中文)STANDBY_TIMEOUT 超时处理器(buffer pin 等待的耐心上限)
 *
 * 【作用】Startup 进程等待 buffer pin 释放超过耐心上限
 * (GetStandbyLimitTime)时,超时机制调用本函数:置位
 * got_standby_delay_timeout。等待循环唤醒后据此调用
 * SendRecoveryConflictWithBufferPin 取消顶着 pin 的查询。
 *
 * 【设计思想】与 StandbyLockTimeoutHandler 是同一思路的"计时器
 * 记账",区分两个标志是为了在共用同一个等待点
 * (ProcWaitForSignal)时,按不同的超时来源走不同的处理分支。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
StandbyTimeoutHandler(void)
{
	got_standby_delay_timeout = true;
}

/*
 * StandbyLockTimeoutHandler() will be called if STANDBY_LOCK_TIMEOUT is exceeded.
 */
/*
 * StandbyLockTimeoutHandler - (中文)STANDBY_LOCK_TIMEOUT 超时处理器(锁冲突的耐心上限)
 *
 * 【作用】Startup 进程等待关系锁超过耐心上限时调用:置位
 * got_standby_lock_timeout。ResolveRecoveryConflictWithLock 唤醒后
 * 看到该标志即退出等待,由下一次调用执行"取消全部持锁者"。
 *
 * 【设计思想】锁冲突路径把"取消动作"推迟到下一个调用周期执行:
 * 等待点(ProcWaitForSignal)与取消点分离,避免在信号上下文里做
 * 复杂工作。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
StandbyLockTimeoutHandler(void)
{
	got_standby_lock_timeout = true;
}

/*
 * -----------------------------------------------------
 * Locking in Recovery Mode
 * -----------------------------------------------------
 *
 * All locks are held by the Startup process using a single virtual
 * transaction. This implementation is both simpler and in some senses,
 * more correct. The locks held mean "some original transaction held
 * this lock, so query access is not allowed at this time". So the Startup
 * process is the proxy by which the original locks are implemented.
 *
 * We only keep track of AccessExclusiveLocks, which are only ever held by
 * one transaction on one relation.
 *
 * We keep a table of known locks in the RecoveryLockHash hash table.
 * The point of that table is to let us efficiently de-duplicate locks,
 * which is important because checkpoints will re-report the same locks
 * already held.  There is also a RecoveryLockXidHash table with one entry
 * per xid, which allows us to efficiently find all the locks held by a
 * given original transaction.
 *
 * We use session locks rather than normal locks so we don't need
 * ResourceOwners.
 */
/* (中文)重放期间的锁管理设计(配合上方英文注释阅读):
 * 热备下"原事务"的 AccessExclusiveLock 由 Startup 进程以其单个
 * 虚拟事务(vxid)代理持有:锁的含义是"某个原事务曾经持有此锁,
 * 查询访问此刻不被允许"。这样查询后端在同一套锁管理器上与
 * Startup 排队,产生真实的等待关系,且备库无需为每个原事务创建
 * 独立锁条目。只跟踪 AccessExclusiveLock(只有它才可能被并发事务
 * 交叉持有、也只需它来挡查询);用会话级锁(session lock)而非
 * 事务锁,免去 ResourceOwner 管理。两张哈希表(RecoveryLockHash
 * 去重 + RecoveryLockXidHash 按 xid 索引锁链)支撑了
 * StandbyAcquireAccessExclusiveLock / StandbyReleaseXidEntryLocks
 * 等增删操作。 */


void
StandbyAcquireAccessExclusiveLock(TransactionId xid, Oid dbOid, Oid relOid)
{
/*
 * StandbyAcquireAccessExclusiveLock - (中文)代理"原事务"获取一把 AccessExclusiveLock
 *
 * 【作用】重放 XLOG_STANDBY_LOCK 记录时对每条锁调用:若该原事务
 * (xid)已提交/中止则忽略(它在主库已不持有任何锁);否则在
 * RecoveryLockXidHash 建立该 xid 的锁链头(首次),在
 * RecoveryLockHash 查重——新锁则在锁管理器里真实获取
 * (LockAcquire,会话级、不等待),并链进该 xid 的锁链。
 *
 * 【设计思想】
 * - 去重是必须的:检查点会重复上报同一批锁,重复获取同一把
 *   AccessExclusiveLock 会无谓堆积会话锁;但去重依赖"锁链上已有
 *   该锁"的事实,而锁链只在新锁时增长;
 * - 跳过已提交/中止的事务:它们的锁在 WAL 里已由 COMMIT/ABORT
 *   记录释放,无需再现;
 * - dbOid 为 InvalidOid 表示共享关系(如 pg_database),锁表支持。
 *
 * 【参数】
 *   xid    —— 原事务 ID;
 *   dbOid  —— 关系所在库 OID(共享关系为 InvalidOid);
 *   relOid —— 关系 OID(必须有效)。
 * 【返回值】无。
 */
	RecoveryLockXidEntry *xidentry;
	RecoveryLockEntry *lockentry;
	xl_standby_lock key;
	LOCKTAG		locktag;
	bool		found;

	/* Already processed? */
	if (!TransactionIdIsValid(xid) ||
		TransactionIdDidCommit(xid) ||
		TransactionIdDidAbort(xid))
		return;

	elog(DEBUG4, "adding recovery lock: db %u rel %u", dbOid, relOid);

	/* dbOid is InvalidOid when we are locking a shared relation. */
	Assert(OidIsValid(relOid));

	/* Create a hash entry for this xid, if we don't have one already. */
	xidentry = hash_search(RecoveryLockXidHash, &xid, HASH_ENTER, &found);
	if (!found)
	{
		Assert(xidentry->xid == xid);	/* dynahash should have set this */
		xidentry->head = NULL;
	}

	/* Create a hash entry for this lock, unless we have one already. */
	key.xid = xid;
	key.dbOid = dbOid;
	key.relOid = relOid;
	lockentry = hash_search(RecoveryLockHash, &key, HASH_ENTER, &found);
	if (!found)
	{
		/* First, acquire the lock ... */
		SET_LOCKTAG_RELATION(locktag, dbOid, relOid);

		(void) LockAcquire(&locktag, AccessExclusiveLock, true, false);

		/* ... and then, as it is new, link it into the XID's list. */
		lockentry->next = xidentry->head;
		xidentry->head = lockentry;
	}
}

/*
 * Release all the locks associated with this RecoveryLockXidEntry.
 */
/*
 * StandbyReleaseXidEntryLocks - (中文)释放某个原事务的全部代理锁
 *
 * 【作用】遍历 RecoveryLockXidEntry 的锁链,对每条锁:在锁管理器
 * 释放会话级 AccessExclusiveLock(LockRelease),并从
 * RecoveryLockHash 删除对应条目;最后清空锁链头。
 *
 * 【设计思想】锁链把同一个 xid 的所有锁串在一起,释放是 O(锁数)
 * 的线性遍历。若锁管理器里已找不到这把锁(记录与实际状态不一致),
 * 记 LOG 并断言失败——这是内部一致性错误,属于防御性检查。
 *
 * 【参数】
 *   xidentry —— 目标事务的锁链条目(将被清空 head,条目本身由
 *                调用者负责从哈希表移除)。
 * 【返回值】无。
 */
static void
StandbyReleaseXidEntryLocks(RecoveryLockXidEntry *xidentry)
{
	RecoveryLockEntry *entry;
	RecoveryLockEntry *next;

	for (entry = xidentry->head; entry != NULL; entry = next)
	{
		LOCKTAG		locktag;

		elog(DEBUG4,
			 "releasing recovery lock: xid %u db %u rel %u",
			 entry->key.xid, entry->key.dbOid, entry->key.relOid);
		/* Release the lock ... */
		SET_LOCKTAG_RELATION(locktag, entry->key.dbOid, entry->key.relOid);
		if (!LockRelease(&locktag, AccessExclusiveLock, true))
		{
			elog(LOG,
				 "RecoveryLockHash contains entry for lock no longer recorded by lock manager: xid %u database %u relation %u",
				 entry->key.xid, entry->key.dbOid, entry->key.relOid);
			Assert(false);
		}
		/* ... and remove the per-lock hash entry */
		next = entry->next;
		hash_search(RecoveryLockHash, entry, HASH_REMOVE, NULL);
	}

	xidentry->head = NULL;		/* just for paranoia */
}

/*
 * Release locks for specific XID, or all locks if it's InvalidXid.
 */
/*
 * StandbyReleaseLocks - (中文)释放指定原事务的代理锁(InvalidXid 时释放全部)
 *
 * 【作用】分派器:xid 有效时在 RecoveryLockXidHash 找到并释放该
 * 事务的全部锁、删除其哈希条目(xid 未登记则无事可做);xid 为
 * InvalidXid 时转调 StandbyReleaseAllLocks()。
 *
 * 【设计思想】StandbyReleaseLockTree 对一棵事务树(父 + 全部子
 * 事务)逐个调用本函数;找不到条目是合法的(该事务从未被上报过
 * 锁,或早已释放),不得报错。
 *
 * 【参数】
 *   xid —— 目标事务 ID;InvalidTransactionId 表示全部释放。
 * 【返回值】无。
 */
static void
StandbyReleaseLocks(TransactionId xid)
{
	RecoveryLockXidEntry *entry;

	if (TransactionIdIsValid(xid))
	{
		if ((entry = hash_search(RecoveryLockXidHash, &xid, HASH_FIND, NULL)))
		{
			StandbyReleaseXidEntryLocks(entry);
			hash_search(RecoveryLockXidHash, entry, HASH_REMOVE, NULL);
		}
	}
	else
		StandbyReleaseAllLocks();
}

/*
 * Release locks for a transaction tree, starting at xid down, from
 * RecoveryLockXidHash.
 *
 * Called during WAL replay of COMMIT/ROLLBACK when in hot standby mode,
 * to remove any AccessExclusiveLocks requested by a transaction.
 */
/*
 * StandbyReleaseLockTree - (中文)释放一棵事务树(含所有子事务)的代理锁
 *
 * 【作用】热备下重放 COMMIT/ABORT 记录时调用:先释放根事务 xid
 * 的锁,再逐个释放其子事务的锁(事务树在主库以子事务链提交,
 * 备库重放时同样逐个清理)。
 *
 * 【设计思想】父事务的锁与子事务的锁分别登记(各自 xid 一条锁
 * 链),因此必须逐个 xid 释放;找不到条目是正常情况,静默忽略。
 *
 * 【参数】
 *   xid     —— 根事务 ID;
 *   nsubxids/ subxids —— 子事务数量与 ID 数组。
 * 【返回值】无。
 */
void
StandbyReleaseLockTree(TransactionId xid, int nsubxids, TransactionId *subxids)
{
	int			i;

	StandbyReleaseLocks(xid);

	for (i = 0; i < nsubxids; i++)
		StandbyReleaseLocks(subxids[i]);
}

/*
 * Called at end of recovery and when we see a shutdown checkpoint.
 */
/*
 * StandbyReleaseAllLocks - (中文)释放全部代理持有的 AccessExclusiveLock
 *
 * 【作用】热备结束(ShutdownRecoveryTransactionEnvironment)以及
 * 重放到 shutdown checkpoint(准备切换回正常模式)时调用:遍历
 * RecoveryLockXidHash 的每个条目,释放其全部锁并删除条目,最终
 * 哈希表清空。
 *
 * 【设计思想】恢复结束时主库的所有事务状态都已了结,不再需要
 * 任何代理锁;全部释放保证后续正常模式下的锁管理器状态干净。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
StandbyReleaseAllLocks(void)
{
	HASH_SEQ_STATUS status;
	RecoveryLockXidEntry *entry;

	elog(DEBUG2, "release all standby locks");

	hash_seq_init(&status, RecoveryLockXidHash);
	while ((entry = hash_seq_search(&status)))
	{
		StandbyReleaseXidEntryLocks(entry);
		hash_search(RecoveryLockXidHash, entry, HASH_REMOVE, NULL);
	}
}

/*
 * StandbyReleaseOldLocks
 *		Release standby locks held by top-level XIDs that aren't running,
 *		as long as they're not prepared transactions.
 *
 * This is needed to prune the locks of crashed transactions, which didn't
 * write an ABORT/COMMIT record.
 */
/*
 * StandbyReleaseOldLocks - (中文)清理崩溃事务遗留的代理锁
 *
 * 【作用】重放期间周期性调用:遍历 RecoveryLockXidHash,凡满足
 * "xid < oldxid 且不是 prepared(两阶段已准备)事务"的条目,释放
 * 其全部锁并删除条目。这用于回收崩溃事务(没有写出 ABORT/COMMIT
 * 记录,正常释放路径不会触发)的锁,防止它们无限期卡住查询。
 *
 * 【设计思想】崩溃事务在主库侧死后,其锁在主库立即释放,但备库
 * 只能靠"它永远不会再推进"来推断——所以凡是比某个"安全界"
 * (oldxid,由 KnownAssignedXids 推进给出)老的、又不在两阶段清单
 * 里的 xid,其锁必然可安全释放。prepared 事务要排除:它们可能
 * 还会被提交,锁必须保留。
 *
 * 【参数】
 *   oldxid —— 安全界:xid 早于它的条目才处理(不早于它的保留)。
 * 【返回值】无。
 */
void
StandbyReleaseOldLocks(TransactionId oldxid)
{
	HASH_SEQ_STATUS status;
	RecoveryLockXidEntry *entry;

	hash_seq_init(&status, RecoveryLockXidHash);
	while ((entry = hash_seq_search(&status)))
	{
		Assert(TransactionIdIsValid(entry->xid));

		/* Skip if prepared transaction. */
		if (StandbyTransactionIdIsPrepared(entry->xid))
			continue;

		/* Skip if >= oldxid. */
		if (!TransactionIdPrecedes(entry->xid, oldxid))
			continue;

		/* Remove all locks and hash table entry. */
		StandbyReleaseXidEntryLocks(entry);
		hash_search(RecoveryLockXidHash, entry, HASH_REMOVE, NULL);
	}
}

/*
 * --------------------------------------------------------------------
 *		Recovery handling for Rmgr RM_STANDBY_ID
 *
 * These record types will only be created if XLogStandbyInfoActive()
 * --------------------------------------------------------------------
 */
/*
 * standby_redo - (中文)重放 RM_STANDBY_ID 类别的 WAL 记录
 *
 * 【作用】WAL 重放框架按资源管理器分派,RM_STANDBY_ID 的所有记录
 * 都汇聚到这里,按记录类型(info 去掉标志位后)分三类处理:
 *  - XLOG_STANDBY_LOCK:对记录里每条锁调用
 *    StandbyAcquireAccessExclusiveLock,重建原事务的代理锁;
 *  - XLOG_RUNNING_XACTS:把主库快照恢复进 ProcArray
 *    (ProcArrayApplyRecoveryInfo,含 KnownAssignedXids 维护),并
 *    顺手上报一次统计(pgstat_report_stat);
 *  - XLOG_INVALIDATIONS:把主库提交事务(无 xid 的事务)的失效消息
 *    转发给查询后端(ProcessCommittedInvalidationMessages)。
 * 未知类型直接 PANIC(WAL 损坏或版本不匹配)。
 *
 * 【设计思想】热备重放的核心是把"主库当时的事务环境"逐步重建:
 * 锁记录重建锁,运行事务记录重建快照,失效记录让备库缓存与主库
 * 保持同步。若热备未启用(standbyState == STANDBY_DISABLED)则
 * 全部忽略。
 *
 * 【参数】
 *   record —— 待重放的 WAL 记录(XLogReaderState,含数据与元信息)。
 * 【返回值】无。
 */
void
standby_redo(XLogReaderState *record)
{
	uint8		info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;

	/* Backup blocks are not used in standby records */
	Assert(!XLogRecHasAnyBlockRefs(record));

	/* Do nothing if we're not in hot standby mode */
	if (standbyState == STANDBY_DISABLED)
		return;

	if (info == XLOG_STANDBY_LOCK)
	{
		xl_standby_locks *xlrec = (xl_standby_locks *) XLogRecGetData(record);
		int			i;

		for (i = 0; i < xlrec->nlocks; i++)
			StandbyAcquireAccessExclusiveLock(xlrec->locks[i].xid,
											  xlrec->locks[i].dbOid,
											  xlrec->locks[i].relOid);
	}
	else if (info == XLOG_RUNNING_XACTS)
	{
		xl_running_xacts *xlrec = (xl_running_xacts *) XLogRecGetData(record);
		RunningTransactionsData running;

		running.xcnt = xlrec->xcnt;
		running.subxcnt = xlrec->subxcnt;
		running.subxid_status = xlrec->subxid_overflow ? SUBXIDS_MISSING : SUBXIDS_IN_ARRAY;
		running.nextXid = xlrec->nextXid;
		running.latestCompletedXid = xlrec->latestCompletedXid;
		running.oldestRunningXid = xlrec->oldestRunningXid;
		running.xids = xlrec->xids;

		ProcArrayApplyRecoveryInfo(&running);

		/*
		 * The startup process currently has no convenient way to schedule
		 * stats to be reported. XLOG_RUNNING_XACTS records issued at a
		 * regular cadence, making this a convenient location to report stats.
		 * While these records aren't generated with wal_level=minimal, stats
		 * also cannot be accessed during WAL replay.
		 */
		pgstat_report_stat(true);
	}
	else if (info == XLOG_INVALIDATIONS)
	{
		xl_invalidations *xlrec = (xl_invalidations *) XLogRecGetData(record);

		ProcessCommittedInvalidationMessages(xlrec->msgs,
											 xlrec->nmsgs,
											 xlrec->relcacheInitFileInval,
											 xlrec->dbId,
											 xlrec->tsId);
	}
	else
		elog(PANIC, "standby_redo: unknown op code %u", info);
}

/*
 * Log details of the current snapshot to WAL. This allows the snapshot state
 * to be reconstructed on the standby and for logical decoding.
 *
 * This is used for Hot Standby as follows:
 *
 * We can move directly to STANDBY_SNAPSHOT_READY at startup if we
 * start from a shutdown checkpoint because we know nothing was running
 * at that time and our recovery snapshot is known empty. In the more
 * typical case of an online checkpoint we need to jump through a few
 * hoops to get a correct recovery snapshot and this requires a two or
 * sometimes a three stage process.
 *
 * The initial snapshot must contain all running xids and all current
 * AccessExclusiveLocks at a point in time on the standby. Assembling
 * that information while the server is running requires many and
 * various LWLocks, so we choose to derive that information piece by
 * piece and then re-assemble that info on the standby. When that
 * information is fully assembled we move to STANDBY_SNAPSHOT_READY.
 *
 * Since locking on the primary when we derive the information is not
 * strict, we note that there is a time window between the derivation and
 * writing to WAL of the derived information. That allows race conditions
 * that we must resolve, since xids and locks may enter or leave the
 * snapshot during that window. This creates the issue that an xid or
 * lock may start *after* the snapshot has been derived yet *before* the
 * snapshot is logged in the running xacts WAL record. We resolve this by
 * starting to accumulate changes at a point just prior to when we derive
 * the snapshot on the primary, then ignore duplicates when we later apply
 * the snapshot from the running xacts record. This is implemented during
 * CreateCheckPoint() where we use the logical checkpoint location as
 * our starting point and then write the running xacts record immediately
 * before writing the main checkpoint WAL record. Since we always start
 * up from a checkpoint and are immediately at our starting point, we
 * unconditionally move to STANDBY_INITIALIZED. After this point we
 * must do 4 things:
 *	* move shared nextXid forwards as we see new xids
 *	* extend the clog and subtrans with each new xid
 *	* keep track of uncommitted known assigned xids
 *	* keep track of uncommitted AccessExclusiveLocks
 *
 * When we see a commit/abort we must remove known assigned xids and locks
 * from the completing transaction. Attempted removals that cannot locate
 * an entry are expected and must not cause an error when we are in state
 * STANDBY_INITIALIZED. This is implemented in StandbyReleaseLocks() and
 * KnownAssignedXidsRemove().
 *
 * Later, when we apply the running xact data we must be careful to ignore
 * transactions already committed, since those commits raced ahead when
 * making WAL entries.
 *
 * For logical decoding only the running xacts information is needed;
 * there's no need to look at the locking information, but it's logged anyway,
 * as there's no independent knob to just enable logical decoding. For
 * details of how this is used, check snapbuild.c's introductory comment.
 *
 *
 * Returns the RecPtr of the last inserted record.
 */
/*
 * LogStandbySnapshot - (中文)把当前运行事务快照与 AccessExclusiveLock 清单写入 WAL
 *
 * 【作用】主库侧(检查点、周期调度)调用:先取当前全部
 * AccessExclusiveLock 清单(GetRunningTransactionLocks)写成
 * XLOG_STANDBY_LOCK 记录;再取当前运行事务数据
 * (GetRunningTransactionData,持 ProcArrayLock + XidGenLock)写成
 * XLOG_RUNNING_XACTS 记录,并返回该记录的 LSN。
 *
 * 【设计思想】
 * - "锁记录先写、运行事务记录后写":备库看到运行事务记录才会
 *   开放查询(STANDBY_SNAPSHOT_READY),此时锁必须已经就位;
 * - 锁的获取与快照推导之间存在竞态窗口(英文注释详述),备库侧
 *   通过"忽略重复/已提交"来消化(ProcArrayApplyRecoveryInfo 用
 *    clog 复核提交状态);
 * - ProcArrayLock 的释放时机有讲究:热备(非逻辑解码)可以早放
 *   (备库会用 clog 复核),逻辑解码必须保留到 WAL 写入之后(否则
 *   历史快照可能看见"未来的 clog 状态");
 * - 记录标记 XLOG_MARK_UNIMPORTANT:不触发无谓的检查点/归档活动。
 *
 * 【参数】无。
 * 【返回值】XLOG_RUNNING_XACTS 记录的 LSN。
 */
XLogRecPtr
LogStandbySnapshot(void)
{
	XLogRecPtr	recptr;
	RunningTransactions running;
	xl_standby_lock *locks;
	int			nlocks;
	bool		logical_decoding_enabled = IsLogicalDecodingEnabled();

	Assert(XLogStandbyInfoActive());

#ifdef USE_INJECTION_POINTS
	if (IS_INJECTION_POINT_ATTACHED("skip-log-running-xacts"))
	{
		/*
		 * This record could move slot's xmin forward during decoding, leading
		 * to unpredictable results, so skip it when requested by the test.
		 */
		return GetInsertRecPtr();
	}
#endif

	/*
	 * Get details of any AccessExclusiveLocks being held at the moment.
	 */
	locks = GetRunningTransactionLocks(&nlocks);
	if (nlocks > 0)
		LogAccessExclusiveLocks(nlocks, locks);
	pfree(locks);

	/*
	 * Log details of all in-progress transactions. This should be the last
	 * record we write, because standby will open up when it sees this.
	 */
	running = GetRunningTransactionData();

	/*
	 * GetRunningTransactionData() acquired ProcArrayLock, we must release it.
	 * For Hot Standby this can be done before inserting the WAL record
	 * because ProcArrayApplyRecoveryInfo() rechecks the commit status using
	 * the clog. For logical decoding, though, the lock can't be released
	 * early because the clog might be "in the future" from the POV of the
	 * historic snapshot. This would allow for situations where we're waiting
	 * for the end of a transaction listed in the xl_running_xacts record
	 * which, according to the WAL, has committed before the xl_running_xacts
	 * record. Fortunately this routine isn't executed frequently, and it's
	 * only a shared lock.
	 */
	if (!logical_decoding_enabled)
		LWLockRelease(ProcArrayLock);

	recptr = LogCurrentRunningXacts(running);

	/* Release lock if we kept it longer ... */
	if (logical_decoding_enabled)
		LWLockRelease(ProcArrayLock);

	/* GetRunningTransactionData() acquired XidGenLock, we must release it */
	LWLockRelease(XidGenLock);

	return recptr;
}

/*
 * Record an enhanced snapshot of running transactions into WAL.
 *
 * The definitions of RunningTransactionsData and xl_running_xacts are
 * similar. We keep them separate because xl_running_xacts is a contiguous
 * chunk of memory and never exists fully until it is assembled in WAL.
 * The inserted records are marked as not being important for durability,
 * to avoid triggering superfluous checkpoint / archiving activity.
 */
/*
 * LogCurrentRunningXacts - (中文)把运行事务快照组装成 XLOG_RUNNING_XACTS 记录并写入
 *
 * 【作用】LogStandbySnapshot 的辅助函数:把 RunningTransactionsData
 * 里的字段(xcnt / subxcnt / 溢出标志 / nextXid / oldestRunningXid /
 * latestCompletedXid / xids 数组)组装成连续的 xl_running_xacts 记录,
 * 标记为"不重要的"后写入 WAL,返回其 LSN;随后用
 * XLogSetAsyncXactLSN 提醒 WAL writer 尽快把该 LSN 刷盘
 * (备库依赖这条记录开闸,不能拖太久,但也不强制同步刷,避免
 * 阻塞主库写入)。
 *
 * 【设计思想】RunningTransactionsData 与 xl_running_xacts 结构相似
 * 但刻意分开:后者必须是一块连续内存(直接进 WAL),前者散落在
 * ProcArray 各字段。subxid 溢出时(xids 数组装不下全部子事务)置
 * 溢出标志,备库以"子事务缺失"模式重建(KnownAssignedXids 视为
 * 全部缺失),只影响一点可见性精度、不影响正确性。
 *
 * 【参数】
 *   CurrRunningXacts —— 运行事务数据(GetRunningTransactionData
 *                        的返回,调用者保证 ProcArrayLock 等锁的
 *                        持有与释放顺序)。
 * 【返回值】刚写入记录的 LSN。
 */
static XLogRecPtr
LogCurrentRunningXacts(RunningTransactions CurrRunningXacts)
{
	xl_running_xacts xlrec;
	XLogRecPtr	recptr;

	xlrec.xcnt = CurrRunningXacts->xcnt;
	xlrec.subxcnt = CurrRunningXacts->subxcnt;
	xlrec.subxid_overflow = (CurrRunningXacts->subxid_status != SUBXIDS_IN_ARRAY);
	xlrec.nextXid = CurrRunningXacts->nextXid;
	xlrec.oldestRunningXid = CurrRunningXacts->oldestRunningXid;
	xlrec.latestCompletedXid = CurrRunningXacts->latestCompletedXid;

	/* Header */
	XLogBeginInsert();
	XLogSetRecordFlags(XLOG_MARK_UNIMPORTANT);
	XLogRegisterData(&xlrec, MinSizeOfXactRunningXacts);

	/* array of TransactionIds */
	if (xlrec.xcnt > 0)
		XLogRegisterData(CurrRunningXacts->xids,
						 (xlrec.xcnt + xlrec.subxcnt) * sizeof(TransactionId));

	recptr = XLogInsert(RM_STANDBY_ID, XLOG_RUNNING_XACTS);

	if (xlrec.subxid_overflow)
		elog(DEBUG2,
			 "snapshot of %d running transactions overflowed (lsn %X/%08X oldest xid %u latest complete %u next xid %u)",
			 CurrRunningXacts->xcnt,
			 LSN_FORMAT_ARGS(recptr),
			 CurrRunningXacts->oldestRunningXid,
			 CurrRunningXacts->latestCompletedXid,
			 CurrRunningXacts->nextXid);
	else
		elog(DEBUG2,
			 "snapshot of %d+%d running transaction ids (lsn %X/%08X oldest xid %u latest complete %u next xid %u)",
			 CurrRunningXacts->xcnt, CurrRunningXacts->subxcnt,
			 LSN_FORMAT_ARGS(recptr),
			 CurrRunningXacts->oldestRunningXid,
			 CurrRunningXacts->latestCompletedXid,
			 CurrRunningXacts->nextXid);

	/*
	 * Ensure running_xacts information is synced to disk not too far in the
	 * future. We don't want to stall anything though (i.e. use XLogFlush()),
	 * so we let the wal writer do it during normal operation.
	 * XLogSetAsyncXactLSN() conveniently will mark the LSN as to-be-synced
	 * and nudge the WALWriter into action if sleeping. Check
	 * XLogBackgroundFlush() for details why a record might not be flushed
	 * without it.
	 */
	XLogSetAsyncXactLSN(recptr);

	return recptr;
}

/*
 * Wholesale logging of AccessExclusiveLocks. Other lock types need not be
 * logged, as described in backend/storage/lmgr/README.
 */
/*
 * LogAccessExclusiveLocks - (中文)批量把一组 AccessExclusiveLock 写入 WAL
 *
 * 【作用】组装 XLOG_STANDBY_LOCK 记录:固定头(xl_standby_locks,
 * 只含 nlocks) + 紧随其后的 xl_standby_lock 数组,一并注册进
 * WAL 并写入,记录标记为"不重要"。被两个入口使用:检查点/周期
 * 快照(LogStandbySnapshot)与单把锁实时记录(LogAccessExclusiveLock)。
 *
 * 【设计思想】XLOG_STANDBY_LOCK 是备库重建代理锁的唯一来源;其它
 * 锁类型(共享/更新等)不需要记录,因为它们不构成对查询的排他
 * 阻塞(详见 lmgr/README)。"不重要"标记让这类记录不拖累检查点
 * 与归档节奏。
 *
 * 【参数】
 *   nlocks —— 锁条数;
 *   locks  —— xl_standby_lock 数组(只读)。
 * 【返回值】无。
 */
static void
LogAccessExclusiveLocks(int nlocks, xl_standby_lock *locks)
{
	xl_standby_locks xlrec;

	xlrec.nlocks = nlocks;

	XLogBeginInsert();
	XLogRegisterData(&xlrec, offsetof(xl_standby_locks, locks));
	XLogRegisterData(locks, nlocks * sizeof(xl_standby_lock));
	XLogSetRecordFlags(XLOG_MARK_UNIMPORTANT);

	(void) XLogInsert(RM_STANDBY_ID, XLOG_STANDBY_LOCK);
}

/*
 * Individual logging of AccessExclusiveLocks for use during LockAcquire()
 */
/*
 * LogAccessExclusiveLock - (中文)实时记录本事务刚获取的一把 AccessExclusiveLock
 *
 * 【作用】LockAcquire 成功获取 AccessExclusiveLock 时被调用:把
 * (当前事务 xid, dbOid, relOid) 写成一条 XLOG_STANDBY_LOCK 记录
 * (经 LogAccessExclusiveLocks),并给 MyXactFlags 置
 * XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK(事务提交时据此决定是否
 * 需要额外写失效/运行信息)。
 *
 * 【设计思想】这把锁必须进入 WAL:备库重放时需要以同样的排他
 * 语义阻塞查询(否则重放期间会有查询读到"主库当时被锁保护"的
 * 数据)。日志开销只在 AccessExclusiveLock(罕见锁)上发生。
 *
 * 【参数】
 *   dbOid  —— 关系所在库 OID(共享关系为 InvalidOid);
 *   relOid —— 关系 OID。
 * 【返回值】无。
 */
void
LogAccessExclusiveLock(Oid dbOid, Oid relOid)
{
	xl_standby_lock xlrec;

	xlrec.xid = GetCurrentTransactionId();

	xlrec.dbOid = dbOid;
	xlrec.relOid = relOid;

	LogAccessExclusiveLocks(1, &xlrec);
	MyXactFlags |= XACT_FLAGS_ACQUIREDACCESSEXCLUSIVELOCK;
}

/*
 * Prepare to log an AccessExclusiveLock, for use during LockAcquire()
 */
/*
 * LogAccessExclusiveLockPrepare - (中文)为记录 AccessExclusiveLock 做前置准备
 *
 * 【作用】LockAcquire 在加锁之前调用:确保当前事务已分配
 * TransactionId(GetCurrentTransactionId,必要时强制分配)。
 *
 * 【设计思想】必须分配 xid 有两个原因:
 * 1) 没有 xid 时,RecordTransactionCommit/Abort 可能优化掉事务结束
 *    WAL 记录——而备库恰恰依赖那条记录来释放代理锁,不能省;
 * 2) 锁必须先有归属 xid 再进共享内存,否则并发执行的
 *    GetRunningTransactionLocks 可能读到"xid 无效的锁"(后面有
 *    断言保证不会出现),产生不一致的快照。
 *
 * 【参数】无。
 * 【返回值】无(副作用:为当前事务分配 xid)。
 */
void
LogAccessExclusiveLockPrepare(void)
{
	/*
	 * Ensure that a TransactionId has been assigned to this transaction, for
	 * two reasons, both related to lock release on the standby. First, we
	 * must assign an xid so that RecordTransactionCommit() and
	 * RecordTransactionAbort() do not optimise away the transaction
	 * completion record which recovery relies upon to release locks. It's a
	 * hack, but for a corner case not worth adding code for into the main
	 * commit path. Second, we must assign an xid before the lock is recorded
	 * in shared memory, otherwise a concurrently executing
	 * GetRunningTransactionLocks() might see a lock associated with an
	 * InvalidTransactionId which we later assert cannot happen.
	 */
	(void) GetCurrentTransactionId();
}

/*
 * Emit WAL for invalidations. This currently is only used for commits without
 * an xid but which contain invalidations.
 */
/*
 * LogStandbyInvalidations - (中文)把无 xid 提交事务的失效消息写进 WAL
 *
 * 【作用】主库上"无 xid 的事务"(只做纯目录操作、未写入数据)提交
 * 且带有缓存失效消息时调用:把这些失效消息连同 dbId / tsId /
 * relcacheInitFileInval 标志组装成 XLOG_INVALIDATIONS 记录写入
 * WAL。备库重放到该记录时,把失效广播给所有查询后端
 * (standby_redo 里转调 ProcessCommittedInvalidationMessages)。
 *
 * 【设计思想】有 xid 的事务,其失效消息随事务提交记录(含
 * RelcacheInitFileInval)一起进 WAL;无 xid 的事务没有提交记录,
 * 失效消息必须单独成记录,否则备库查询后端看不到主库的目录变更。
 *
 * 【参数】
 *   nmsgs              —— 失效消息条数;
 *   msgs               —— 失效消息数组(只读);
 *   relcacheInitFileInval —— 是否需要作废 relcache 初始化文件。
 * 【返回值】无。
 */
void
LogStandbyInvalidations(int nmsgs, SharedInvalidationMessage *msgs,
						bool relcacheInitFileInval)
{
	xl_invalidations xlrec;

	/* prepare record */
	memset(&xlrec, 0, sizeof(xlrec));
	xlrec.dbId = MyDatabaseId;
	xlrec.tsId = MyDatabaseTableSpace;
	xlrec.relcacheInitFileInval = relcacheInitFileInval;
	xlrec.nmsgs = nmsgs;

	/* perform insertion */
	XLogBeginInsert();
	XLogRegisterData(&xlrec, MinSizeOfInvalidations);
	XLogRegisterData(msgs,
					 nmsgs * sizeof(SharedInvalidationMessage));
	XLogInsert(RM_STANDBY_ID, XLOG_INVALIDATIONS);
}

/* Return the description of recovery conflict */
/*
 * get_recovery_conflict_desc - (中文)返回恢复冲突原因的可读文字描述
 *
 * 【作用】LogRecoveryConflict 调用:把 RecoveryConflictReason 枚举
 * 映射为本地化的人类可读字符串(buffer pin 冲突、锁冲突、表空间
 * 冲突、快照冲突、复制槽冲突、死锁等),未知原因返回
 * "unknown reason"。
 *
 * 【设计思想】纯展示层的小函数,把枚举到文案的映射集中在一处,
 * 便于日志阅读与翻译维护;文案带 _() 本地化宏。
 *
 * 【参数】
 *   reason —— 冲突原因枚举。
 * 【返回值】静态字符串指针(无需释放)。
 */
static const char *
get_recovery_conflict_desc(RecoveryConflictReason reason)
{
	const char *reasonDesc = _("unknown reason");

	switch (reason)
	{
		case RECOVERY_CONFLICT_BUFFERPIN:
			reasonDesc = _("recovery conflict on buffer pin");
			break;
		case RECOVERY_CONFLICT_LOCK:
			reasonDesc = _("recovery conflict on lock");
			break;
		case RECOVERY_CONFLICT_TABLESPACE:
			reasonDesc = _("recovery conflict on tablespace");
			break;
		case RECOVERY_CONFLICT_SNAPSHOT:
			reasonDesc = _("recovery conflict on snapshot");
			break;
		case RECOVERY_CONFLICT_LOGICALSLOT:
			reasonDesc = _("recovery conflict on replication slot");
			break;
		case RECOVERY_CONFLICT_STARTUP_DEADLOCK:
			reasonDesc = _("recovery conflict on deadlock");
			break;
		case RECOVERY_CONFLICT_BUFFERPIN_DEADLOCK:
			reasonDesc = _("recovery conflict on buffer deadlock");
			break;
		case RECOVERY_CONFLICT_DATABASE:
			reasonDesc = _("recovery conflict on database");
			break;
	}

	return reasonDesc;
}
