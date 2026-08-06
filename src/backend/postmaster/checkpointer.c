/*-------------------------------------------------------------------------
 *
 * checkpointer.c
 *
 * The checkpointer is new as of Postgres 9.2.  It handles all checkpoints.
 * Checkpoints are automatically dispatched after a certain amount of time has
 * elapsed since the last one, and it can be signaled to perform requested
 * checkpoints as well.  (The GUC parameter that mandates a checkpoint every
 * so many WAL segments is implemented by having backends signal when they
 * fill WAL segments; the checkpointer itself doesn't watch for the
 * condition.)
 *
 * The normal termination sequence is that checkpointer is instructed to
 * execute the shutdown checkpoint by SIGINT.  After that checkpointer waits
 * to be terminated via SIGUSR2, which instructs the checkpointer to exit(0).
 * All backends must be stopped before SIGINT or SIGUSR2 is issued!
 *
 * Emergency termination is by SIGQUIT; like any backend, the checkpointer
 * will simply abort and exit on SIGQUIT.
 *
 * If the checkpointer exits unexpectedly, the postmaster treats that the same
 * as a backend crash: shared memory may be corrupted, so remaining backends
 * should be killed by SIGQUIT and then a recovery cycle started.  (Even if
 * shared memory isn't corrupted, we have lost information about which
 * files need to be fsync'd for the next checkpoint, and so a system
 * restart needs to be forced.)
 *
 * 【中文总述】
 * 本文件实现检查点进程（checkpointer，Postgres 9.2 引入）：
 * 负责所有 checkpoint 的执行。checkpoint 的触发方式有两种：
 *   1. 定时触发：距上次 checkpoint 超过 checkpoint_timeout（默认 300 秒）
 *   2. 请求触发：普通后端进程在需要时通过共享内存标志 + 信号请求
 *      （其中"写满 max_wal_size 个 WAL 段就触发"这条规则也是由后端
 *      进程在填充 WAL 段时发信号实现，checkpointer 自己不监控 WAL 段数）
 * 一次 checkpoint 大致做三件事（细节见 CreateCheckPoint()）：
 *   1. 把共享缓冲池里的脏页全部刷到磁盘（BufferSync()）
 *   2. 写一条 CHECKPOINT WAL 记录（记录 Redo 点，即崩溃后重放的起点）
 *   3. 更新 pg_control 文件，标记崩溃恢复的起点
 * 它与 bgwriter 的分工：bgwriter 平时分批刷脏页、维持干净缓冲池；
 * checkpointer 只在 checkpoint 时做全量刷盘 + fsync 收尾。
 * 正常关闭流程：postmaster 先停掉所有后端，再给 checkpointer 发 SIGINT
 * 要求它写"关闭检查点"（shutdown checkpoint），写完再发 SIGUSR2 让它
 * exit(0)。SIGQUIT 紧急退出。若 checkpointer 意外退出，postmaster
 * 视同后端崩溃：先 SIGQUIT 杀其余进程再进恢复循环（即使共享内存没坏，
 * 我们也丢失了"下一个 checkpoint 需要 fsync 哪些文件"的信息，
 * 因此必须强制重启系统）。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 *
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/checkpointer.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <sys/time.h>
#include <time.h>

#include "access/xlog.h"
#include "access/xlog_internal.h"
#include "access/xlogrecovery.h"
#include "catalog/pg_authid.h"
#include "commands/defrem.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "port/atomics.h"
#include "postmaster/auxprocess.h"
#include "postmaster/bgwriter.h"
#include "postmaster/interrupt.h"
#include "replication/syncrep.h"
#include "storage/aio_subsys.h"
#include "storage/bufmgr.h"
#include "storage/condition_variable.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/lwlock.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/shmem.h"
#include "storage/smgr.h"
#include "storage/spin.h"
#include "storage/subsystems.h"
#include "utils/acl.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/resowner.h"
#include "utils/wait_event.h"


/*----------
 * Shared memory area for communication between checkpointer and backends
 *
 * The ckpt counters allow backends to watch for completion of a checkpoint
 * request they send.  Here's how it works:
 *	* At start of a checkpoint, checkpointer reads (and clears) the request
 *	  flags and increments ckpt_started, while holding ckpt_lck.
 *	* On completion of a checkpoint, checkpointer sets ckpt_done to
 *	  equal ckpt_started.
 *	* On failure of a checkpoint, checkpointer increments ckpt_failed
 *	  and sets ckpt_done to equal ckpt_started.
 *
 * The algorithm for backends is:
 *	1. Record current values of ckpt_failed and ckpt_started, and
 *	   set request flags, while holding ckpt_lck.
 *	2. Send signal to request checkpoint.
 *	3. Sleep until ckpt_started changes.  Now you know a checkpoint has
 *	   begun since you started this algorithm (although *not* that it was
 *	   specifically initiated by your signal), and that it is using your flags.
 *	4. Record new value of ckpt_started.
 *	5. Sleep until ckpt_done >= saved value of ckpt_started.  (Use modulo
 *	   arithmetic here in case counters wrap around.)  Now you know a
 *	   checkpoint has started and completed, but not whether it was
 *	   successful.
 *	6. If ckpt_failed is different from the originally saved value,
 *	   assume request failed; otherwise it was definitely successful.
 *
 * ckpt_flags holds the OR of the checkpoint request flags sent by all
 * requesting backends since the last checkpoint start.  The flags are
 * chosen so that OR'ing is the correct way to combine multiple requests.
 *
 * The requests array holds fsync requests sent by backends and not yet
 * absorbed by the checkpointer.
 *
 * Unlike the checkpoint fields, requests related fields are protected by
 * CheckpointerCommLock.
 *
 * 【中文总述】
 * 这是 checkpointer 与后端进程之间的共享内存通信区，包含两部分：
 * 1. checkpoint 状态计数器（ckpt_started / ckpt_done / ckpt_failed 和
 *    ckpt_flags），用自旋锁 ckpt_lck 保护，配合两个条件变量
 *    （start_cv / done_cv）实现"请求-完成"握手协议（后端等待算法
 *    见 RequestCheckpoint()，共 6 步）：
 *    - checkpointer 开始 checkpoint 时读取并清零请求标志、
 *      ckpt_started + 1；
 *    - 完成时 ckpt_done = ckpt_started；失败时 ckpt_failed + 1
 *      并把 ckpt_done 也同步到 ckpt_started，让等待方知道自己失败了。
 *    后端用"模运算"比较计数器，以容忍计数器回绕。
 * 2. fsync 请求环形队列（requests[]）：后端进程被迫直接写盘时
 *    把"哪个文件脏了、需要 fsync"登记到这里，checkpointer 定期
 *    AbsorbSyncRequests() 收走并转交给本地 fsync 记录（从而在下一次
 *    checkpoint 的 fsync 阶段统一执行）。这块由 CheckpointerCommLock
 *    保护。
 *
 *----------
 */
typedef struct
{
	SyncRequestType type;		/* request type */
	FileTag		ftag;			/* file identifier */
} CheckpointerRequest;

typedef struct
{
	pid_t		checkpointer_pid;	/* PID (0 if not started) */

	slock_t		ckpt_lck;		/* protects all the ckpt_* fields */

	int			ckpt_started;	/* advances when checkpoint starts */
	int			ckpt_done;		/* advances when checkpoint done */
	int			ckpt_failed;	/* advances when checkpoint fails */

	int			ckpt_flags;		/* checkpoint flags, as defined in xlog.h */

	ConditionVariable start_cv; /* signaled when ckpt_started advances */
	ConditionVariable done_cv;	/* signaled when ckpt_done advances */

	int			num_requests;	/* current # of requests */
	int			max_requests;	/* allocated array size */

	int			head;			/* Index of the first request in the ring
								 * buffer */
	int			tail;			/* Index of the last request in the ring
								 * buffer */

	/* The ring buffer of pending checkpointer requests */
	CheckpointerRequest requests[FLEXIBLE_ARRAY_MEMBER];
} CheckpointerShmemStruct;
/* 【中文】head/tail 是环形队列的读写游标：head 指向队头（checkpointer
 * 消费处），tail 指向队尾（后端写入处），用 (x+1) % max_requests 推进；
 * num_requests 为待处理的请求数；requests[] 是柔性数组，容量 =
 * min(NBuffers, MAX_CHECKPOINT_REQUESTS)，由 CheckpointerShmemRequest
 * 申请共享内存时定下（每缓冲区最多一条请求，队列再满时后端会自己
 * fsync 兜底）。 */

static CheckpointerShmemStruct *CheckpointerShmem;

static void CheckpointerShmemRequest(void *arg);
static void CheckpointerShmemInit(void *arg);
/* 【中文】CheckpointerShmemRequest / CheckpointerShmemInit 是共享内存
 * 子系统回调：前者在申请阶段登记所需内存大小，后者在共享内存创建好
 * 之后做字段初始化（见下文对应函数注释）。 */

const ShmemCallbacks CheckpointerShmemCallbacks = {
	.request_fn = CheckpointerShmemRequest,
	.init_fn = CheckpointerShmemInit,
};

/* interval for calling AbsorbSyncRequests in CheckpointWriteDelay */
#define WRITES_PER_ABSORB		1000
/* 【中文】CheckpointWriteDelay() 里每隔 WRITES_PER_ABSORB 次写盘调用
 * 一次 AbsorbSyncRequests()，及时收走后端排队进来的 fsync 请求。 */

/* Maximum number of checkpointer requests to process in one batch */
#define CKPT_REQ_BATCH_SIZE 10000
/* 【中文】AbsorbSyncRequests() 一次批量处理的请求上限，防止长时间
 * 持有 CheckpointerCommLock 阻塞其它后端登记请求。 */

/* Max number of requests the checkpointer request queue can hold */
#define MAX_CHECKPOINT_REQUESTS 10000000
/* 【中文】请求环形队列的容量上限（默认 1000 万条），实际容量取
 * min(NBuffers, MAX_CHECKPOINT_REQUESTS)。 */

/*
 * GUC parameters
 */
/* 【中文】三个 checkpoint 相关 GUC 参数的底层变量：
 *  - CheckPointTimeout（checkpoint_timeout，默认 300 秒）：距上次
 *    checkpoint 超过该时长就自动触发一次定时 checkpoint；
 *  - CheckPointWarning（checkpoint_warning，默认 30 秒）：若两次
 *    checkpoint 间隔短于该值且又是因 WAL 写满触发，就发日志警告
 *    "checkpoints are occurring too frequently"；
 *  - CheckPointCompletionTarget（checkpoint_completion_target，默认
 *    0.9）：把刷脏页的工作量尽量摊到"两次 checkpoint 间隔的 90%"
 *    内完成，避免瞬时大 IO 尖峰（见 IsCheckpointOnSchedule）。 */
int			CheckPointTimeout = 300;
int			CheckPointWarning = 30;
double		CheckPointCompletionTarget = 0.9;

/*
 * Private state
 */
static bool ckpt_active = false;
static volatile sig_atomic_t ShutdownXLOGPending = false;

/* these values are valid when ckpt_active is true: */
static pg_time_t ckpt_start_time;
static XLogRecPtr ckpt_start_recptr;
static double ckpt_cached_elapsed;

static pg_time_t last_checkpoint_time;
static pg_time_t last_xlog_switch_time;
/* 【中文】本进程私有的检查点状态：
 *  - ckpt_active：当前是否正处在一个 checkpoint 执行期间（出错恢复时
 *    据此判断要不要向等待的后端报告 ckpt_failed）；
 *  - ShutdownXLOGPending：SIGINT 处理函数置位，要求写关闭检查点；
 *  - ckpt_start_time / ckpt_start_recptr：本次 checkpoint 开始时刻与
 *    开始时的 WAL 插入位点（供 IsCheckpointOnSchedule 计算进度基准）；
 *  - ckpt_cached_elapsed：进度判断的缓存结果，避免每写一页都重算；
 *  - last_checkpoint_time：上次 checkpoint 开始时间（定时检查点据此
 *    判断是否到期，注意记录的是"开始"时间以保证间隔可预测）；
 *  - last_xlog_switch_time：上次 WAL 段切换（或请求切换）时间，
 *    供 archive_timeout 判定。 */

/* Prototypes for private functions */
/* 【中文】本文件内部函数原型一览（各函数注释见正文）：
 * ProcessCheckpointerInterrupts 统一处理信号；CheckArchiveTimeout
 * 处理 archive_timeout 的 WAL 段切换；IsCheckpointOnSchedule 判断
 * 刷盘进度是否落后；FastCheckpointRequested 查是否有人请求了快速
 * 检查点；CompactCheckpointerRequestQueue 压缩 fsync 请求队列去重；
 * UpdateSharedMemoryConfig 把 GUC 新值同步到共享内存。 */

static void ProcessCheckpointerInterrupts(void);
static void CheckArchiveTimeout(void);
static bool IsCheckpointOnSchedule(double progress);
static bool FastCheckpointRequested(void);
static bool CompactCheckpointerRequestQueue(void);
static void UpdateSharedMemoryConfig(void);

/* Signal handlers */
static void ReqShutdownXLOG(SIGNAL_ARGS);


/*
 * Main entry point for checkpointer process
 *
 * This is invoked from AuxiliaryProcessMain, which has already created the
 * basic execution environment, but not enabled signals yet.
 *
 * 【中文总述】
 * checkpointer 进程的主入口（由 AuxiliaryProcessMain 分发调用，
 * 彼时基本执行环境已就绪，但信号尚未启用）。执行阶段概览：
 *   1. 安装/忽略本进程的信号（注意故意忽略 SIGTERM！）
 *   2. 初始化：登记"关机前写统计"的退出回调、创建专属内存上下文
 *   3. 建立错误恢复现场（sigsetjmp），出错时向等待的后端报告失败
 *   4. 更新共享内存中的配置快照
 *   5. 主循环（for(;;)），每轮依次判断：
 *      a. 收走后端排队的 fsync 请求（AbsorbSyncRequests）
 *      b. 处理信号中断；被要求关闭（SIGINT 写关闭检查点 /
 *         SIGUSR2 停机）则跳出主循环
 *      c. 检测"是否有人请求 checkpoint"（共享内存 ckpt_flags 非零）
 *      d. 检测"是否到定时 checkpoint 时间"（超过 checkpoint_timeout）
 *      e. 需要时执行 CreateCheckPoint() / CreateRestartPoint()，
 *         完成后广播 done_cv 唤醒等待的后端，并记录时间/统计
 *      f. 处理逻辑解码停用、archive_timeout 切换 WAL 段、上报统计
 *      g. 无事可做时按"距下个事件的时间"计算超时，WaitLatch 睡眠
 *   6. 退出主循环后：若收到 SIGINT，执行 ShutdownXLOG() 写
 *      关闭检查点并通知 postmaster；然后等 SIGUSR2 到来，exit(0)
 *
 * 核心知识：checkpoint 刷脏页并不是一口气刷完，而是通过
 * CheckpointWriteDelay() 节流，把刷盘工作摊到
 * checkpoint_completion_target 规定的时间窗口内完成，避免写放大
 * 把系统 IO 打满。
 */
void
CheckpointerMain(const void *startup_data, size_t startup_data_len)
{
	sigjmp_buf	local_sigjmp_buf;
	MemoryContext checkpointer_context;

	/* checkpointer 进程不需要 postmaster 传任何启动数据 */
	Assert(startup_data_len == 0);

	/* 辅助进程公共初始化（挂接共享内存、登记进程类型、加载 GUC 等，
	 * 与 bgwriter 的初始化路径一致，见 bgwriter.c 的调用链注释） */
	AuxiliaryProcessMainCommon();

	/* 向共享内存登记自己的 PID：后端发 fsync 请求时先检查这个字段
	 * 判断 checkpointer 是否在运行（0 表示未启动） */
	CheckpointerShmem->checkpointer_pid = MyProcPid;

	/*
	 * Properly accept or ignore signals the postmaster might send us
	 *
	 * Note: we deliberately ignore SIGTERM, because during a standard Unix
	 * system shutdown cycle, init will SIGTERM all processes at once.  We
	 * want to wait for the backends to exit, whereupon the postmaster will
	 * tell us it's okay to shut down (via SIGUSR2).
	 * 【中文】逐个设置信号处理方式（本进程的"信号清单"）：
	 * SIGHUP → 重载配置文件；SIGINT → ReqShutdownXLOG（请求写关闭
	 * 检查点）；SIGTERM → 故意忽略：Unix 系统关机时 init 会对所有
	 * 进程同时发 SIGTERM，我们要等所有后端退出后由 postmaster 发
	 * SIGUSR2 通知我们"可以退出了"；SIGUSR2 → 停机请求（exit(0)）。
	 * SIGUSR1 → procsignal；SIGALRM/SIGPIPE → 忽略。
	 * SIGQUIT 已在 InitPostmasterChild 里设为立即退出。
	 */
	pqsignal(SIGHUP, SignalHandlerForConfigReload);
	/* SIGINT → 置 ShutdownXLOGPending 标志（不是退出，见 ReqShutdownXLOG） */
	pqsignal(SIGINT, ReqShutdownXLOG);
	pqsignal(SIGTERM, PG_SIG_IGN);	/* ignore SIGTERM */
	/* SIGQUIT handler was already set up by InitPostmasterChild */
	/* 【中文】SIGQUIT 处理函数由 InitPostmasterChild() 在 fork 时已
	 * 设置好，无需重复安装 */
	pqsignal(SIGALRM, PG_SIG_IGN);
	pqsignal(SIGPIPE, PG_SIG_IGN);
	/* SIGUSR1 → 其它进程投递的 procsignal（屏障、内存日志等请求） */
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	/* SIGUSR2 → 停机请求（置 ShutdownRequestPending，收尾后 exit(0)） */
	pqsignal(SIGUSR2, SignalHandlerForShutdownRequest);

	/*
	 * Reset some signals that are accepted by postmaster but not here
	 * 【中文】SIGCHLD 恢复默认行为：checkpointer 不 fork 子进程，
	 * 不需要像 postmaster 那样收割子进程（与 bgwriter 相同）。
	 */
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/*
	 * Initialize so that first time-driven event happens at the correct time.
	 * 【中文】把"上次检查点时间 / 上次 WAL 段切换时间"都初始化为当前
	 * 时刻：这样定时 checkpoint 的计时从启动那一刻算起，第一个时间
	 * 驱动事件恰好落在正确的时间点（不会启动即触发、也不会拖很久）。
	 */
	last_checkpoint_time = last_xlog_switch_time = (pg_time_t) time(NULL);

	/*
	 * Write out stats after shutdown. This needs to be called by exactly one
	 * process during a normal shutdown, and since checkpointer is shut down
	 * very late...
	 *
	 * While e.g. walsenders are active after the shutdown checkpoint has been
	 * written (and thus could produce more stats), checkpointer stays around
	 * after the shutdown checkpoint has been written. postmaster will only
	 * signal checkpointer to exit after all processes that could emit stats
	 * have been shut down.
	 * 【中文】登记"服务器关闭前"回调：把最终统计写盘。这个工作只能由
	 * 恰好一个进程在正常关闭期间做，而 checkpointer 是退出最晚的进程
	 * （写完关闭检查点后还赖着不走，等 postmaster 发 SIGUSR2）——
	 * 写关闭检查点后 walsender 等进程还可能继续产生统计，postmaster
	 * 会等所有可能产生统计的进程都退出后才发 SIGUSR2，因此由
	 * checkpointer 在退出前统一落盘最合适。
	 */
	before_shmem_exit(pgstat_before_server_shutdown, 0);

	/*
	 * Create a memory context that we will do all our work in.  We do this so
	 * that we can reset the context during error recovery and thereby avoid
	 * possible memory leaks.  Formerly this code just ran in
	 * TopMemoryContext, but resetting that would be a really bad idea.
	 * 【中文】创建本进程专用的内存上下文 "Checkpointer"：所有工作都在
	 * 这里面分配内存，出错恢复时整体 Reset 即可清掉泄漏，比直接跑在
	 * TopMemoryContext 上安全得多（与 bgwriter 的做法一致）。
	 */
	checkpointer_context = AllocSetContextCreate(TopMemoryContext,
												 "Checkpointer",
												 ALLOCSET_DEFAULT_SIZES);
	MemoryContextSwitchTo(checkpointer_context);

	/*
	 * If an exception is encountered, processing resumes here.
	 *
	 * You might wonder why this isn't coded as an infinite loop around a
	 * PG_TRY construct.  The reason is that this is the bottom of the
	 * exception stack, and so with PG_TRY there would be no exception handler
	 * in force at all during the CATCH part.  By leaving the outermost setjmp
	 * always active, we have at least some chance of recovering from an error
	 * during error recovery.  (If we get into an infinite loop thereby, it
	 * will soon be stopped by overflow of elog.c's internal state stack.)
	 *
	 * Note that we use sigsetjmp(..., 1), so that the prevailing signal mask
	 * (to wit, BlockSig) will be restored when longjmp'ing to here.  Thus,
	 * signals other than SIGQUIT will be blocked until we complete error
	 * recovery.  It might seem that this policy makes the HOLD_INTERRUPTS()
	 * call redundant, but it is not since InterruptPending might be set
	 * already.
	 */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/* Since not using PG_TRY, must reset error stack by hand */
		error_context_stack = NULL;

		/* Prevent interrupts while cleaning up */
		HOLD_INTERRUPTS();

		/* Report the error to the server log */
		EmitErrorReport();

		/*
		 * These operations are really just a minimal subset of
		 * AbortTransaction().  We don't have very many resources to worry
		 * about in checkpointer, but we do have LWLocks, buffers, and temp
		 * files.
		 */
		LWLockReleaseAll();
		ConditionVariableCancelSleep();
		pgstat_report_wait_end();
		pgaio_error_cleanup();
		UnlockBuffers();
		ReleaseAuxProcessResources(false);
		AtEOXact_Buffers(false);
		AtEOXact_SMgr();
		AtEOXact_Files(false);
		AtEOXact_HashTables(false);

		/* Warn any waiting backends that the checkpoint failed. */
		if (ckpt_active)
		{
			SpinLockAcquire(&CheckpointerShmem->ckpt_lck);
			CheckpointerShmem->ckpt_failed++;
			CheckpointerShmem->ckpt_done = CheckpointerShmem->ckpt_started;
			SpinLockRelease(&CheckpointerShmem->ckpt_lck);

			ConditionVariableBroadcast(&CheckpointerShmem->done_cv);

			ckpt_active = false;
		}

		/*
		 * Now return to normal top-level context and clear ErrorContext for
		 * next time.
		 */
		MemoryContextSwitchTo(checkpointer_context);
		FlushErrorState();

		/* Flush any leaked data in the top-level context */
		MemoryContextReset(checkpointer_context);

		/* Now we can allow interrupts again */
		RESUME_INTERRUPTS();

		/*
		 * Sleep at least 1 second after any error.  A write error is likely
		 * to be repeated, and we don't want to be filling the error logs as
		 * fast as we can.
		 */
		pg_usleep(1000000L);
	}

	/* We can now handle ereport(ERROR) */
	PG_exception_stack = &local_sigjmp_buf;

	/*
	 * Unblock signals (they were blocked when the postmaster forked us)
	 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * Ensure all shared memory values are set correctly for the config. Doing
	 * this here ensures no race conditions from other concurrent updaters.
	 */
	UpdateSharedMemoryConfig();

	/*
	 * Loop until we've been asked to write the shutdown checkpoint or
	 * terminate.
	 */
	for (;;)
	{
		bool		do_checkpoint = false;
		int			flags = 0;
		pg_time_t	now;
		int			elapsed_secs;
		int			cur_timeout;
		bool		chkpt_or_rstpt_requested = false;
		bool		chkpt_or_rstpt_timed = false;

		/* Clear any already-pending wakeups */
		ResetLatch(MyLatch);

		/*
		 * Process any requests or signals received recently.
		 */
		AbsorbSyncRequests();

		ProcessCheckpointerInterrupts();
		if (ShutdownXLOGPending || ShutdownRequestPending)
			break;

		/*
		 * Detect a pending checkpoint request by checking whether the flags
		 * word in shared memory is nonzero.  We shouldn't need to acquire the
		 * ckpt_lck for this.
		 */
		if (((volatile CheckpointerShmemStruct *) CheckpointerShmem)->ckpt_flags)
		{
			do_checkpoint = true;
			chkpt_or_rstpt_requested = true;
		}

		/*
		 * Force a checkpoint if too much time has elapsed since the last one.
		 * Note that we count a timed checkpoint in stats only when this
		 * occurs without an external request, but we set the CAUSE_TIME flag
		 * bit even if there is also an external request.
		 */
		now = (pg_time_t) time(NULL);
		elapsed_secs = now - last_checkpoint_time;
		if (elapsed_secs >= CheckPointTimeout)
		{
			if (!do_checkpoint)
				chkpt_or_rstpt_timed = true;
			do_checkpoint = true;
			flags |= CHECKPOINT_CAUSE_TIME;
		}

		/*
		 * Do a checkpoint if requested.
		 */
		if (do_checkpoint)
		{
			bool		ckpt_performed = false;
			bool		do_restartpoint;

			/* Check if we should perform a checkpoint or a restartpoint. */
			do_restartpoint = RecoveryInProgress();

			/*
			 * Atomically fetch the request flags to figure out what kind of a
			 * checkpoint we should perform, and increase the started-counter
			 * to acknowledge that we've started a new checkpoint.
			 */
			SpinLockAcquire(&CheckpointerShmem->ckpt_lck);
			flags |= CheckpointerShmem->ckpt_flags;
			CheckpointerShmem->ckpt_flags = 0;
			CheckpointerShmem->ckpt_started++;
			SpinLockRelease(&CheckpointerShmem->ckpt_lck);

			ConditionVariableBroadcast(&CheckpointerShmem->start_cv);

			/*
			 * The end-of-recovery checkpoint is a real checkpoint that's
			 * performed while we're still in recovery.
			 */
			if (flags & CHECKPOINT_END_OF_RECOVERY)
				do_restartpoint = false;

			if (chkpt_or_rstpt_timed)
			{
				chkpt_or_rstpt_timed = false;
				if (do_restartpoint)
					PendingCheckpointerStats.restartpoints_timed++;
				else
					PendingCheckpointerStats.num_timed++;
			}

			if (chkpt_or_rstpt_requested)
			{
				chkpt_or_rstpt_requested = false;
				if (do_restartpoint)
					PendingCheckpointerStats.restartpoints_requested++;
				else
					PendingCheckpointerStats.num_requested++;
			}

			/*
			 * We will warn if (a) too soon since last checkpoint (whatever
			 * caused it) and (b) somebody set the CHECKPOINT_CAUSE_XLOG flag
			 * since the last checkpoint start.  Note in particular that this
			 * implementation will not generate warnings caused by
			 * CheckPointTimeout < CheckPointWarning.
			 */
			if (!do_restartpoint &&
				(flags & CHECKPOINT_CAUSE_XLOG) &&
				elapsed_secs < CheckPointWarning)
				ereport(LOG,
						(errmsg_plural("checkpoints are occurring too frequently (%d second apart)",
									   "checkpoints are occurring too frequently (%d seconds apart)",
									   elapsed_secs,
									   elapsed_secs),
						 errhint("Consider increasing the configuration parameter \"%s\".", "max_wal_size")));

			/*
			 * Initialize checkpointer-private variables used during
			 * checkpoint.
			 */
			ckpt_active = true;
			if (do_restartpoint)
				ckpt_start_recptr = GetXLogReplayRecPtr(NULL);
			else
				ckpt_start_recptr = GetInsertRecPtr();
			ckpt_start_time = now;
			ckpt_cached_elapsed = 0;

			/*
			 * Do the checkpoint.
			 */
			if (!do_restartpoint)
				ckpt_performed = CreateCheckPoint(flags);
			else
				ckpt_performed = CreateRestartPoint(flags);

			/*
			 * After any checkpoint, free all smgr objects.  Otherwise we
			 * would never do so for dropped relations, as the checkpointer
			 * does not process shared invalidation messages or call
			 * AtEOXact_SMgr().
			 */
			smgrdestroyall();

			/*
			 * Indicate checkpoint completion to any waiting backends.
			 */
			SpinLockAcquire(&CheckpointerShmem->ckpt_lck);
			CheckpointerShmem->ckpt_done = CheckpointerShmem->ckpt_started;
			SpinLockRelease(&CheckpointerShmem->ckpt_lck);

			ConditionVariableBroadcast(&CheckpointerShmem->done_cv);

			if (!do_restartpoint)
			{
				/*
				 * Note we record the checkpoint start time not end time as
				 * last_checkpoint_time.  This is so that time-driven
				 * checkpoints happen at a predictable spacing.
				 */
				last_checkpoint_time = now;

				if (ckpt_performed)
					PendingCheckpointerStats.num_performed++;
			}
			else
			{
				if (ckpt_performed)
				{
					/*
					 * The same as for checkpoint. Please see the
					 * corresponding comment.
					 */
					last_checkpoint_time = now;

					PendingCheckpointerStats.restartpoints_performed++;
				}
				else
				{
					/*
					 * We were not able to perform the restartpoint
					 * (checkpoints throw an ERROR in case of error).  Most
					 * likely because we have not received any new checkpoint
					 * WAL records since the last restartpoint. Try again in
					 * 15 s.
					 */
					last_checkpoint_time = now - CheckPointTimeout + 15;
				}
			}

			ckpt_active = false;

			/*
			 * We may have received an interrupt during the checkpoint and the
			 * latch might have been reset (e.g. in CheckpointWriteDelay).
			 */
			ProcessCheckpointerInterrupts();
			if (ShutdownXLOGPending || ShutdownRequestPending)
				break;
		}

		/*
		 * Disable logical decoding if someone requested it. See comments atop
		 * logicalctl.c.
		 */
		DisableLogicalDecodingIfNecessary();

		/* Check for archive_timeout and switch xlog files if necessary. */
		CheckArchiveTimeout();

		/* Report pending statistics to the cumulative stats system */
		pgstat_report_checkpointer();
		pgstat_report_wal(true);

		/*
		 * If any checkpoint flags have been set, redo the loop to handle the
		 * checkpoint without sleeping.
		 */
		if (((volatile CheckpointerShmemStruct *) CheckpointerShmem)->ckpt_flags)
			continue;

		/*
		 * Sleep until we are signaled or it's time for another checkpoint or
		 * xlog file switch.
		 */
		now = (pg_time_t) time(NULL);
		elapsed_secs = now - last_checkpoint_time;
		if (elapsed_secs >= CheckPointTimeout)
			continue;			/* no sleep for us ... */
		cur_timeout = CheckPointTimeout - elapsed_secs;
		if (XLogArchiveTimeout > 0 && !RecoveryInProgress())
		{
			elapsed_secs = now - last_xlog_switch_time;
			if (elapsed_secs >= XLogArchiveTimeout)
				continue;		/* no sleep for us ... */
			cur_timeout = Min(cur_timeout, XLogArchiveTimeout - elapsed_secs);
		}

		(void) WaitLatch(MyLatch,
						 WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
						 cur_timeout * 1000L /* convert to ms */ ,
						 WAIT_EVENT_CHECKPOINTER_MAIN);
	}

	/*
	 * From here on, elog(ERROR) should end with exit(1), not send control
	 * back to the sigsetjmp block above.
	 */
	ExitOnAnyError = true;

	if (ShutdownXLOGPending)
	{
		/*
		 * Close down the database.
		 *
		 * Since ShutdownXLOG() creates restartpoint or checkpoint, and
		 * updates the statistics, increment the checkpoint request and flush
		 * out pending statistic.
		 */
		PendingCheckpointerStats.num_requested++;
		ShutdownXLOG(0, 0);
		pgstat_report_checkpointer();
		pgstat_report_wal(true);

		/*
		 * Tell postmaster that we're done.
		 */
		SendPostmasterSignal(PMSIGNAL_XLOG_IS_SHUTDOWN);
		ShutdownXLOGPending = false;
	}

	/*
	 * Wait until we're asked to shut down. By separating the writing of the
	 * shutdown checkpoint from checkpointer exiting, checkpointer can perform
	 * some should-be-as-late-as-possible work like writing out stats.
	 */
	for (;;)
	{
		/* Clear any already-pending wakeups */
		ResetLatch(MyLatch);

		ProcessCheckpointerInterrupts();

		if (ShutdownRequestPending)
			break;

		(void) WaitLatch(MyLatch,
						 WL_LATCH_SET | WL_EXIT_ON_PM_DEATH,
						 0,
						 WAIT_EVENT_CHECKPOINTER_SHUTDOWN);
	}

	/* Normal exit from the checkpointer is here */
	proc_exit(0);				/* done */
}

/*
 * Process any new interrupts.
 *
 * 【中文总述】
 * checkpointer 的主中断处理函数，统一处理三类事件：
 *   1. ProcSignalBarrierPending → ProcessProcSignalBarrier()（进程屏障同步）
 *   2. ConfigReloadPending → 重载 postgresql.conf 并同步 GUC 到共享内存
 *   3. LogMemoryContextPending → 输出本进程内存上下文统计
 * 【调用链】CheckpointerMain() 主循环每轮开头调用此函数；
 *   ProcessProcSignalBarrier() → 阻塞所有信号 → 执行待处理的屏障回调
 */
static void
ProcessCheckpointerInterrupts(void)
{
	if (ProcSignalBarrierPending)
		ProcessProcSignalBarrier();

	if (ConfigReloadPending)
	{
		ConfigReloadPending = false;
		ProcessConfigFile(PGC_SIGHUP);

		/*
		 * Checkpointer is the last process to shut down, so we ask it to hold
		 * the keys for a range of other tasks required most of which have
		 * nothing to do with checkpointing at all.
		 *
		 * For various reasons, some config values can change dynamically so
		 * the primary copy of them is held in shared memory to make sure all
		 * backends see the same value.  We make Checkpointer responsible for
		 * updating the shared memory copy if the parameter setting changes
		 * because of SIGHUP.
		 */
		UpdateSharedMemoryConfig();
	}

	/* Perform logging of memory contexts of this process */
	if (LogMemoryContextPending)
		ProcessLogMemoryContextInterrupt();
}

/*
 * CheckArchiveTimeout -- check for archive_timeout and switch xlog files
 *
 * This will switch to a new WAL file and force an archive file write if
 * meaningful activity is recorded in the current WAL file. This includes most
 * writes, including just a single checkpoint record, but excludes WAL records
 * that were inserted with the XLOG_MARK_UNIMPORTANT flag being set (like
 * snapshots of running transactions).  Such records, depending on
 * configuration, occur on regular intervals and don't contain important
 * information.  This avoids generating archives with a few unimportant
 * records.
 *
 * 【中文总述】
 * 检查 archive_timeout 是否到期，到期则强制切换 WAL 段并触发归档。
 * 切换条件：
 *   1. archive_timeout > 0 且不在恢复模式中
 *   2. 自上次切换以来的时间 >= XLogArchiveTimeout
 *   3. 期间写入了"重要"WAL 记录（XLOG_MARK_UNIMPORTANT 标记的跳过，
 *      如快照等不重要的记录）
 * 切换后更新 last_xlog_switch_time，避免在系统空闲时反复触发。
 * 【调用链】CheckpointerMain() 主循环 → CheckArchiveTimeout() →
 *   RequestXLogSwitch() → XLogSwitch() → 写 CHECKPOINT/FULL_PAGE_WRITE 等
 *   记录 → 触发归档进程 pgarch 归档
 */
static void
CheckArchiveTimeout(void)
{
	pg_time_t	now;
	pg_time_t	last_time;
	XLogRecPtr	last_switch_lsn;

	if (XLogArchiveTimeout <= 0 || RecoveryInProgress())
		return;

	now = (pg_time_t) time(NULL);

	/* First we do a quick check using possibly-stale local state. */
	if ((int) (now - last_xlog_switch_time) < XLogArchiveTimeout)
		return;

	/*
	 * Update local state ... note that last_xlog_switch_time is the last time
	 * a switch was performed *or requested*.
	 */
	last_time = GetLastSegSwitchData(&last_switch_lsn);

	last_xlog_switch_time = Max(last_xlog_switch_time, last_time);

	/* Now we can do the real checks */
	if ((int) (now - last_xlog_switch_time) >= XLogArchiveTimeout)
	{
		/*
		 * Switch segment only when "important" WAL has been logged since the
		 * last segment switch (last_switch_lsn points to end of segment
		 * switch occurred in).
		 */
		if (GetLastImportantRecPtr() > last_switch_lsn)
		{
			XLogRecPtr	switchpoint;

			/* mark switch as unimportant, avoids triggering checkpoints */
			switchpoint = RequestXLogSwitch(true);

			/*
			 * If the returned pointer points exactly to a segment boundary,
			 * assume nothing happened.
			 */
			if (XLogSegmentOffset(switchpoint, wal_segment_size) != 0)
				elog(DEBUG1, "write-ahead log switch forced (\"archive_timeout\"=%d)",
					 XLogArchiveTimeout);
		}

		/*
		 * Update state in any case, so we don't retry constantly when the
		 * system is idle.
		 */
		last_xlog_switch_time = now;
	}
}

/*
 * Returns true if a fast checkpoint request is pending.  (Note that this does
 * not check the *current* checkpoint's FAST flag, but whether there is one
 * pending behind it.)
 *
 * 【中文】检查是否有"快速检查点"请求挂起。
 * 注意：这里查的是 ckpt_flags 中 CHECKPOINT_FAST 标志是否被置位，
 * 即是否有后端请求了快速检查点（不按 checkpoint_completion_target 节流，
 * 立即开始刷脏页），而不是查当前正在执行的检查点本身是否是快速模式。
 * 【调用链】CheckpointerMain() 主循环 → FastCheckpointRequested()
 *   → 读取 CheckpointerShmem->ckpt_flags & CHECKPOINT_FAST
 *   → 不需要加 ckpt_lck 锁（只查单标志位，天然原子）
 */
static bool
FastCheckpointRequested(void)
{
	volatile CheckpointerShmemStruct *cps = CheckpointerShmem;

	/*
	 * We don't need to acquire the ckpt_lck in this case because we're only
	 * looking at a single flag bit.
	 */
	if (cps->ckpt_flags & CHECKPOINT_FAST)
		return true;
	return false;
}

/*
 * CheckpointWriteDelay -- control rate of checkpoint
 *
 * This function is called after each page write performed by BufferSync().
 * It is responsible for throttling BufferSync()'s write rate to hit
 * checkpoint_completion_target.
 *
 * The checkpoint request flags should be passed in; currently the only one
 * examined is CHECKPOINT_FAST, which disables delays between writes.
 *
 * 'progress' is an estimate of how much of the work has been done, as a
 * fraction between 0.0 meaning none, and 1.0 meaning all done.
 */
void
CheckpointWriteDelay(int flags, double progress)
{
	static int	absorb_counter = WRITES_PER_ABSORB;

	/* Do nothing if checkpoint is being executed by non-checkpointer process */
	if (!AmCheckpointerProcess())
		return;

	/*
	 * Perform the usual duties and take a nap, unless we're behind schedule,
	 * in which case we just try to catch up as quickly as possible.
	 */
	if (!(flags & CHECKPOINT_FAST) &&
		!ShutdownXLOGPending &&
		!ShutdownRequestPending &&
		!FastCheckpointRequested() &&
		IsCheckpointOnSchedule(progress))
	{
		if (ConfigReloadPending)
		{
			ConfigReloadPending = false;
			ProcessConfigFile(PGC_SIGHUP);
			/* update shmem copies of config variables */
			UpdateSharedMemoryConfig();
		}

		AbsorbSyncRequests();
		absorb_counter = WRITES_PER_ABSORB;

		CheckArchiveTimeout();

		/* Report interim statistics to the cumulative stats system */
		pgstat_report_checkpointer();

		/*
		 * This sleep used to be connected to bgwriter_delay, typically 200ms.
		 * That resulted in more frequent wakeups if not much work to do.
		 * Checkpointer and bgwriter are no longer related so take the Big
		 * Sleep.
		 */
		WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH | WL_TIMEOUT,
				  100,
				  WAIT_EVENT_CHECKPOINT_WRITE_DELAY);
		ResetLatch(MyLatch);
	}
	else if (--absorb_counter <= 0)
	{
		/*
		 * Absorb pending fsync requests after each WRITES_PER_ABSORB write
		 * operations even when we don't sleep, to prevent overflow of the
		 * fsync request queue.
		 */
		AbsorbSyncRequests();
		absorb_counter = WRITES_PER_ABSORB;
	}

	/* Check for barrier events. */
	if (ProcSignalBarrierPending)
		ProcessProcSignalBarrier();
}

/*
 * IsCheckpointOnSchedule -- are we on schedule to finish this checkpoint
 *		 (or restartpoint) in time?
 *
 * Compares the current progress against the time/segments elapsed since last
 * checkpoint, and returns true if the progress we've made this far is greater
 * than the elapsed time/segments.
 *
 * 【中文总述】
 * 判断当前 checkpoint 的刷脏页进度是否"跟得上"预定的时间表。
 * 原理：将 checkpoint_completion_target（默认 0.9）乘到进度上，
 * 然后同时对比"已写入的 WAL 段数比例"和"已过去的时间比例"，
 * 只有两者都达标才认为在计划内（任一个落后就返回 false，
 * 触发 CheckpointWriteDelay 节流等待）。
 * 恢复模式下用重放位点（GetXLogReplayRecPtr）代替插入位点，
 * 与正常 checkpoint 的进度口径保持一致。
 * 【调用链】CheckpointWriteDelay() → IsCheckpointOnSchedule()
 *   → GetInsertRecPtr() / GetXLogReplayRecPtr() 取当前 WAL 位点
 *   → 与 ckpt_start_recptr 算出已写入段数比例
 *   → 与 ckpt_start_time 算出已过去时间比例
 *   → 两者都 ≥ progress × CheckPointCompletionTarget 则返回 true
 */
static bool
IsCheckpointOnSchedule(double progress)
{
	XLogRecPtr	recptr;
	struct timeval now;
	double		elapsed_xlogs,
				elapsed_time;

	Assert(ckpt_active);

	/* Scale progress according to checkpoint_completion_target. */
	progress *= CheckPointCompletionTarget;

	/*
	 * Check against the cached value first. Only do the more expensive
	 * calculations once we reach the target previously calculated. Since
	 * neither time or WAL insert pointer moves backwards, a freshly
	 * calculated value can only be greater than or equal to the cached value.
	 */
	if (progress < ckpt_cached_elapsed)
		return false;

	/*
	 * Check progress against WAL segments written and CheckPointSegments.
	 *
	 * We compare the current WAL insert location against the location
	 * computed before calling CreateCheckPoint. The code in XLogInsert that
	 * actually triggers a checkpoint when CheckPointSegments is exceeded
	 * compares against RedoRecPtr, so this is not completely accurate.
	 * However, it's good enough for our purposes, we're only calculating an
	 * estimate anyway.
	 *
	 * During recovery, we compare last replayed WAL record's location with
	 * the location computed before calling CreateRestartPoint. That maintains
	 * the same pacing as we have during checkpoints in normal operation, but
	 * we might exceed max_wal_size by a fair amount. That's because there can
	 * be a large gap between a checkpoint's redo-pointer and the checkpoint
	 * record itself, and we only start the restartpoint after we've seen the
	 * checkpoint record. (The gap is typically up to CheckPointSegments *
	 * checkpoint_completion_target where checkpoint_completion_target is the
	 * value that was in effect when the WAL was generated).
	 */
	if (RecoveryInProgress())
		recptr = GetXLogReplayRecPtr(NULL);
	else
		recptr = GetInsertRecPtr();
	elapsed_xlogs = (((double) (recptr - ckpt_start_recptr)) /
					 wal_segment_size) / CheckPointSegments;

	if (progress < elapsed_xlogs)
	{
		ckpt_cached_elapsed = elapsed_xlogs;
		return false;
	}

	/*
	 * Check progress against time elapsed and checkpoint_timeout.
	 */
	gettimeofday(&now, NULL);
	elapsed_time = ((double) ((pg_time_t) now.tv_sec - ckpt_start_time) +
					now.tv_usec / 1000000.0) / CheckPointTimeout;

	if (progress < elapsed_time)
	{
		ckpt_cached_elapsed = elapsed_time;
		return false;
	}

	/* It looks like we're on schedule. */
	return true;
}


/* --------------------------------
 *		signal handler routines
 * --------------------------------
 */

/* SIGINT: set flag to trigger writing of shutdown checkpoint */
/* 【中文】SIGINT 信号处理函数：将 ShutdownXLOGPending 置位，
 * 通知 CheckpointerMain() 主循环在下一轮执行关闭检查点。
 * 正常关闭流程：postmaster 先停所有后端 → 发 SIGINT 给 checkpointer
 * → checkpointer 写关闭检查点（记录关闭时的 WAL 位点）→ 再发 SIGUSR2 退出。
 * 【调用链】CheckpointerMain() 主循环检测到 ShutdownXLOGPending 后
 *   → CreateCheckPoint(CHECKPOINT_IS_SHUTDOWN) 写关闭检查点
 *   → 通知 postmaster 关闭完成 */
static void
ReqShutdownXLOG(SIGNAL_ARGS)
{
	ShutdownXLOGPending = true;
	SetLatch(MyLatch);
}


/* --------------------------------
 *		communication with backends
 * --------------------------------
 */

/*
 * CheckpointerShmemRequest
 *		Register shared memory space needed for checkpointer
 */
static void
CheckpointerShmemRequest(void *arg)
{
	Size		size;

	/*
	 * The size of the requests[] array is arbitrarily set equal to NBuffers.
	 * But there is a cap of MAX_CHECKPOINT_REQUESTS to prevent accumulating
	 * too many checkpoint requests in the ring buffer.
	 */
	size = offsetof(CheckpointerShmemStruct, requests);
	size = add_size(size, mul_size(Min(NBuffers,
									   MAX_CHECKPOINT_REQUESTS),
								   sizeof(CheckpointerRequest)));
	ShmemRequestStruct(.name = "Checkpointer Data",
					   .size = size,
					   .ptr = (void **) &CheckpointerShmem,
		);
}

/*
 * CheckpointerShmemInit
 *		Initialize checkpointer-related shared memory
 */
static void
CheckpointerShmemInit(void *arg)
{
	SpinLockInit(&CheckpointerShmem->ckpt_lck);
	CheckpointerShmem->max_requests = Min(NBuffers, MAX_CHECKPOINT_REQUESTS);
	CheckpointerShmem->head = CheckpointerShmem->tail = 0;
	ConditionVariableInit(&CheckpointerShmem->start_cv);
	ConditionVariableInit(&CheckpointerShmem->done_cv);
}

/*
 * ExecCheckpoint
 *		Primary entry point for manual CHECKPOINT commands
 *
 * This is mainly a wrapper for RequestCheckpoint().
 *
 * 【中文总述】
 * SQL 命令 CHECKPOINT 的入口函数。解析命令选项（mode=fast/spread、
 * flush_unlogged），权限校验后调用 RequestCheckpoint()。
 * 选项含义：
 *   - mode=fast：立即执行，不按 checkpoint_completion_target 节流
 *   - mode=spread：按 checkpoint_completion_target 节流刷脏页（默认）
 *   - flush_unlogged：对未日志化（UNLOGGED）表也强制刷盘
 *   - 非恢复模式下自动加 CHECKPOINT_FORCE 标志
 * 【调用链】SQL 解析器 → ExecCheckpoint() → RequestCheckpoint()
 *   → 设置共享内存 ckpt_flags + 信号唤醒 checkpointer
 *   → checkpointer 执行 CreateCheckPoint() → 刷脏页 + 写 WAL + 更新 pg_control
 */
void
ExecCheckpoint(ParseState *pstate, CheckPointStmt *stmt)
{
	bool		fast = true;
	bool		unlogged = false;

	foreach_ptr(DefElem, opt, stmt->options)
	{
		if (strcmp(opt->defname, "mode") == 0)
		{
			char	   *mode = defGetString(opt);

			if (strcmp(mode, "spread") == 0)
				fast = false;
			else if (strcmp(mode, "fast") != 0)
				ereport(ERROR,
						(errcode(ERRCODE_SYNTAX_ERROR),
						 errmsg("unrecognized value for %s option \"%s\": \"%s\"",
								"CHECKPOINT", "mode", mode),
						 parser_errposition(pstate, opt->location)));
		}
		else if (strcmp(opt->defname, "flush_unlogged") == 0)
			unlogged = defGetBoolean(opt);
		else
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("unrecognized %s option \"%s\"",
							"CHECKPOINT", opt->defname),
					 parser_errposition(pstate, opt->location)));
	}

	if (!has_privs_of_role(GetUserId(), ROLE_PG_CHECKPOINT))
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
		/* translator: %s is name of an SQL command (e.g., CHECKPOINT) */
				 errmsg("permission denied to execute %s command",
						"CHECKPOINT"),
				 errdetail("Only roles with privileges of the \"%s\" role may execute this command.",
						   "pg_checkpoint")));

	RequestCheckpoint(CHECKPOINT_WAIT |
					  (fast ? CHECKPOINT_FAST : 0) |
					  (unlogged ? CHECKPOINT_FLUSH_UNLOGGED : 0) |
					  (RecoveryInProgress() ? 0 : CHECKPOINT_FORCE));
}

/*
 * RequestCheckpoint
 *		Called in backend processes to request a checkpoint
 *
 * flags is a bitwise OR of the following:
 *	CHECKPOINT_IS_SHUTDOWN: checkpoint is for database shutdown.
 *	CHECKPOINT_END_OF_RECOVERY: checkpoint is for end of WAL recovery.
 *	CHECKPOINT_FAST: finish the checkpoint ASAP,
 *		ignoring checkpoint_completion_target parameter.
 *	CHECKPOINT_FORCE: force a checkpoint even if no XLOG activity has occurred
 *		since the last one (implied by CHECKPOINT_IS_SHUTDOWN or
 *		CHECKPOINT_END_OF_RECOVERY, and the CHECKPOINT command).
 *	CHECKPOINT_WAIT: wait for completion before returning (otherwise,
 *		just signal checkpointer to do it, and return).
 *	CHECKPOINT_CAUSE_XLOG: checkpoint is requested due to xlog filling.
 *		(This affects logging, and in particular enables CheckPointWarning.)
 *
 * 【中文总述】
 * 后端进程请求 checkpointer 执行检查点的统一入口。
 * 核心流程分两步：
 *   1. 独立后端（standalone backend）直接同步执行 CreateCheckPoint()，
 *      不经过 checkpointer 进程（因为没有其他后端会被干扰）。
 *   2. postmaster 环境下的普通后端：
 *      a. 加 ckpt_lck 锁，原子地 OR 入请求标志 + CHECKPOINT_REQUESTED，
 *         并记录当前 ckpt_started/ckpt_failed 快照
 *      b. 通过 SetLatch 唤醒 checkpointer 进程
 *      c. 若 CHECKPOINT_WAIT 标志位，则通过 start_cv / done_cv
 *         条件变量等待 checkpointer 完成，使用模运算比较计数器
 *         以容忍计数器回绕
 * 【调用链】ExecCheckpoint() / CheckpointerMain() / 自动触发逻辑
 *   → RequestCheckpoint() → SetLatch(CheckpointerProc) 唤醒 checkpointer
 *   → checkpointer 的 CheckpointerMain() 主循环检测到 ckpt_flags 非零
 *   → CreateCheckPoint() 执行实际检查点
 */
void
RequestCheckpoint(int flags)
{
	int			ntries;
	int			old_failed,
				old_started;

	/*
	 * If in a standalone backend, just do it ourselves.
	 */
	if (!IsPostmasterEnvironment)
	{
		/*
		 * There's no point in doing slow checkpoints in a standalone backend,
		 * because there's no other backends the checkpoint could disrupt.
		 */
		CreateCheckPoint(flags | CHECKPOINT_FAST);

		/* Free all smgr objects, as CheckpointerMain() normally would. */
		smgrdestroyall();

		return;
	}

	/*
	 * Atomically set the request flags, and take a snapshot of the counters.
	 * When we see ckpt_started > old_started, we know the flags we set here
	 * have been seen by checkpointer.
	 *
	 * Note that we OR the flags with any existing flags, to avoid overriding
	 * a "stronger" request by another backend.  The flag senses must be
	 * chosen to make this work!
	 */
	SpinLockAcquire(&CheckpointerShmem->ckpt_lck);

	old_failed = CheckpointerShmem->ckpt_failed;
	old_started = CheckpointerShmem->ckpt_started;
	CheckpointerShmem->ckpt_flags |= (flags | CHECKPOINT_REQUESTED);

	SpinLockRelease(&CheckpointerShmem->ckpt_lck);

	/*
	 * Set checkpointer's latch to request checkpoint.  It's possible that the
	 * checkpointer hasn't started yet, so we will retry a few times if
	 * needed.  (Actually, more than a few times, since on slow or overloaded
	 * buildfarm machines, it's been observed that the checkpointer can take
	 * several seconds to start.)  However, if not told to wait for the
	 * checkpoint to occur, we consider failure to set the latch to be
	 * nonfatal and merely LOG it.  The checkpointer should see the request
	 * when it does start, with or without the SetLatch().
	 */
#define MAX_SIGNAL_TRIES 600	/* max wait 60.0 sec */
	for (ntries = 0;; ntries++)
	{
		ProcNumber	checkpointerProc = pg_atomic_read_u32(&ProcGlobal->checkpointerProc);

		if (checkpointerProc == INVALID_PROC_NUMBER)
		{
			if (ntries >= MAX_SIGNAL_TRIES || !(flags & CHECKPOINT_WAIT))
			{
				elog((flags & CHECKPOINT_WAIT) ? ERROR : LOG,
					 "could not notify checkpoint: checkpointer is not running");
				break;
			}
		}
		else
		{
			SetLatch(&GetPGProcByNumber(checkpointerProc)->procLatch);
			/* notified successfully */
			break;
		}

		CHECK_FOR_INTERRUPTS();
		pg_usleep(100000L);		/* wait 0.1 sec, then retry */
	}

	/*
	 * If requested, wait for completion.  We detect completion according to
	 * the algorithm given above.
	 */
	if (flags & CHECKPOINT_WAIT)
	{
		int			new_started,
					new_failed;

		/* Wait for a new checkpoint to start. */
		ConditionVariablePrepareToSleep(&CheckpointerShmem->start_cv);
		for (;;)
		{
			SpinLockAcquire(&CheckpointerShmem->ckpt_lck);
			new_started = CheckpointerShmem->ckpt_started;
			SpinLockRelease(&CheckpointerShmem->ckpt_lck);

			if (new_started != old_started)
				break;

			ConditionVariableSleep(&CheckpointerShmem->start_cv,
								   WAIT_EVENT_CHECKPOINT_START);
		}
		ConditionVariableCancelSleep();

		/*
		 * We are waiting for ckpt_done >= new_started, in a modulo sense.
		 */
		ConditionVariablePrepareToSleep(&CheckpointerShmem->done_cv);
		for (;;)
		{
			int			new_done;

			SpinLockAcquire(&CheckpointerShmem->ckpt_lck);
			new_done = CheckpointerShmem->ckpt_done;
			new_failed = CheckpointerShmem->ckpt_failed;
			SpinLockRelease(&CheckpointerShmem->ckpt_lck);

			if (new_done - new_started >= 0)
				break;

			ConditionVariableSleep(&CheckpointerShmem->done_cv,
								   WAIT_EVENT_CHECKPOINT_DONE);
		}
		ConditionVariableCancelSleep();

		if (new_failed != old_failed)
			ereport(ERROR,
					(errmsg("checkpoint request failed"),
					 errhint("Consult recent messages in the server log for details.")));
	}
}

/*
 * ForwardSyncRequest
 *		Forward a file-fsync request from a backend to the checkpointer
 *
 * Whenever a backend is compelled to write directly to a relation
 * (which should be seldom, if the background writer is getting its job done),
 * the backend calls this routine to pass over knowledge that the relation
 * is dirty and must be fsync'd before next checkpoint.  We also use this
 * opportunity to count such writes for statistical purposes.
 *
 * To avoid holding the lock for longer than necessary, we normally write
 * to the requests[] queue without checking for duplicates.  The checkpointer
 * will have to eliminate dups internally anyway.  However, if we discover
 * that the queue is full, we make a pass over the entire queue to compact
 * it.  This is somewhat expensive, but the alternative is for the backend
 * to perform its own fsync, which is far more expensive in practice.  It
 * is theoretically possible a backend fsync might still be necessary, if
 * the queue is full and contains no duplicate entries.  In that case, we
 * let the backend know by returning false.
 *
 * 【中文总述】
 * 后端被迫直接写盘时，将"此关系脏了、需 fsync"的请求转发给 checkpointer。
 * 核心逻辑：
 *   1. 非 postmaster 环境或本进程就是 checkpointer 时直接返回（不可能或非法）
 *   2. 加 CheckpointerCommLock 排他锁
 *   3. 若 checkpointer 未运行或队列满，先尝试 CompactCheckpointerRequestQueue()
 *      去重压缩（队列满时后端自行 fsync 是更昂贵的兜底方案）
 *   4. 将请求写入环形队列 tail 位置，tail 推进
 *   5. 队列超过半满时，唤醒 checkpointer 进程来消费
 * 【调用链】BufferSync() / backend 直接写盘路径
 *   → ForwardSyncRequest() → 登记到 CheckpointerShmem->requests[] 环形队列
 *   → checkpointer 的 AbsorbSyncRequests() 批量收走
 *   → 下一 checkpoint 的 fsync 阶段统一执行
 */
bool
ForwardSyncRequest(const FileTag *ftag, SyncRequestType type)
{
	CheckpointerRequest *request;
	bool		too_full;
	int			insert_pos;

	if (!IsUnderPostmaster)
		return false;			/* probably shouldn't even get here */

	if (AmCheckpointerProcess())
		elog(ERROR, "ForwardSyncRequest must not be called in checkpointer");

	LWLockAcquire(CheckpointerCommLock, LW_EXCLUSIVE);

	/*
	 * If the checkpointer isn't running or the request queue is full, the
	 * backend will have to perform its own fsync request.  But before forcing
	 * that to happen, we can try to compact the request queue.
	 */
	if (CheckpointerShmem->checkpointer_pid == 0 ||
		(CheckpointerShmem->num_requests >= CheckpointerShmem->max_requests &&
		 !CompactCheckpointerRequestQueue()))
	{
		LWLockRelease(CheckpointerCommLock);
		return false;
	}

	/* OK, insert request */
	insert_pos = CheckpointerShmem->tail;
	request = &CheckpointerShmem->requests[insert_pos];
	request->ftag = *ftag;
	request->type = type;

	CheckpointerShmem->tail = (CheckpointerShmem->tail + 1) % CheckpointerShmem->max_requests;
	CheckpointerShmem->num_requests++;

	/* If queue is more than half full, nudge the checkpointer to empty it */
	too_full = (CheckpointerShmem->num_requests >=
				CheckpointerShmem->max_requests / 2);

	LWLockRelease(CheckpointerCommLock);

	/* ... but not till after we release the lock */
	if (too_full)
	{
		ProcNumber	checkpointerProc = pg_atomic_read_u32(&ProcGlobal->checkpointerProc);

		if (checkpointerProc != INVALID_PROC_NUMBER)
			SetLatch(&GetPGProcByNumber(checkpointerProc)->procLatch);
	}

	return true;
}

/*
 * CompactCheckpointerRequestQueue
 *		Remove duplicates from the request queue to avoid backend fsyncs.
 *		Returns "true" if any entries were removed.
 *
 * Although a full fsync request queue is not common, it can lead to severe
 * performance problems when it does happen.  So far, this situation has
 * only been observed to occur when the system is under heavy write load,
 * and especially during the "sync" phase of a checkpoint.  Without this
 * logic, each backend begins doing an fsync for every block written, which
 * gets very expensive and can slow down the whole system.
 *
 * Trying to do this every time the queue is full could lose if there
 * aren't any removable entries.  But that should be vanishingly rare in
 * practice: there's one queue entry per shared buffer.
 *
 * 【中文总述】
 * 对 checkpointer 的 fsync 请求环形队列做原地去重压缩。
 * 核心算法：
 *   1. 用哈希表记录每个请求值最后一次出现的环形队列下标
 *   2. 遍历队列，若某请求值在哈希表中已存在，则标记前一个位置为"可跳过"
 *   3. 二次遍历：将未被标记的请求按顺序前移（类似删除有序数组中的重复项）
 *   4. 更新 tail 和 num_requests，返回 true 表示有重复被删除
 * 为什么不反过来从后往前删？因为 SYNC_FORGET_REQUEST / SYNC_FILTER_REQUEST
 * 这类特殊请求会改变语义，正向遍历才能正确处理。
 * 【调用链】ForwardSyncRequest() → 队列满时调用 CompactCheckpointerRequestQueue()
 *   → 哈希表去重 → 原地紧凑 → 返回是否删除了重复项
 *   → 若返回 false 且队列仍满，后端只能自行 fsync（兜底）
 */
static bool
CompactCheckpointerRequestQueue(void)
{
	struct CheckpointerSlotMapping
	{
		CheckpointerRequest request;
		int			ring_idx;
	};

	int			n;
	int			num_skipped = 0;
	int			head;
	int			max_requests;
	int			num_requests;
	int			read_idx,
				write_idx;
	HASHCTL		ctl;
	HTAB	   *htab;
	bool	   *skip_slot;

	/* must hold CheckpointerCommLock in exclusive mode */
	Assert(LWLockHeldByMe(CheckpointerCommLock));

	/* Avoid memory allocations in a critical section. */
	if (CritSectionCount > 0)
		return false;

	max_requests = CheckpointerShmem->max_requests;
	num_requests = CheckpointerShmem->num_requests;

	/* Initialize skip_slot array */
	skip_slot = palloc0_array(bool, max_requests);

	head = CheckpointerShmem->head;

	/* Initialize temporary hash table */
	ctl.keysize = sizeof(CheckpointerRequest);
	ctl.entrysize = sizeof(struct CheckpointerSlotMapping);
	ctl.hcxt = CurrentMemoryContext;

	htab = hash_create("CompactCheckpointerRequestQueue",
					   CheckpointerShmem->num_requests,
					   &ctl,
					   HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);

	/*
	 * The basic idea here is that a request can be skipped if it's followed
	 * by a later, identical request.  It might seem more sensible to work
	 * backwards from the end of the queue and check whether a request is
	 * *preceded* by an earlier, identical request, in the hopes of doing less
	 * copying.  But that might change the semantics, if there's an
	 * intervening SYNC_FORGET_REQUEST or SYNC_FILTER_REQUEST, so we do it
	 * this way.  It would be possible to be even smarter if we made the code
	 * below understand the specific semantics of such requests (it could blow
	 * away preceding entries that would end up being canceled anyhow), but
	 * it's not clear that the extra complexity would buy us anything.
	 */
	read_idx = head;
	for (n = 0; n < num_requests; n++)
	{
		CheckpointerRequest *request;
		struct CheckpointerSlotMapping *slotmap;
		bool		found;

		/*
		 * We use the request struct directly as a hashtable key.  This
		 * assumes that any padding bytes in the structs are consistently the
		 * same, which should be okay because we zeroed them in
		 * CheckpointerShmemInit.  Note also that RelFileLocator had better
		 * contain no pad bytes.
		 */
		request = &CheckpointerShmem->requests[read_idx];
		slotmap = hash_search(htab, request, HASH_ENTER, &found);
		if (found)
		{
			/* Duplicate, so mark the previous occurrence as skippable */
			skip_slot[slotmap->ring_idx] = true;
			num_skipped++;
		}
		/* Remember slot containing latest occurrence of this request value */
		slotmap->ring_idx = read_idx;

		/* Move to the next request in the ring buffer */
		read_idx = (read_idx + 1) % max_requests;
	}

	/* Done with the hash table. */
	hash_destroy(htab);

	/* If no duplicates, we're out of luck. */
	if (!num_skipped)
	{
		pfree(skip_slot);
		return false;
	}

	/* We found some duplicates; remove them. */
	read_idx = write_idx = head;
	for (n = 0; n < num_requests; n++)
	{
		/* If this slot is NOT skipped, keep it */
		if (!skip_slot[read_idx])
		{
			/* If the read and write positions are different, copy the request */
			if (write_idx != read_idx)
				CheckpointerShmem->requests[write_idx] =
					CheckpointerShmem->requests[read_idx];

			/* Advance the write position */
			write_idx = (write_idx + 1) % max_requests;
		}

		read_idx = (read_idx + 1) % max_requests;
	}

	/*
	 * Update ring buffer state: head remains the same, tail moves, count
	 * decreases
	 */
	CheckpointerShmem->tail = write_idx;
	CheckpointerShmem->num_requests -= num_skipped;

	ereport(DEBUG1,
			(errmsg_internal("compacted fsync request queue from %d entries to %d entries",
							 num_requests, CheckpointerShmem->num_requests)));

	/* Cleanup. */
	pfree(skip_slot);
	return true;
}

/*
 * AbsorbSyncRequests
 *		Retrieve queued sync requests and pass them to sync mechanism.
 *
 * This is exported because it must be called during CreateCheckPoint;
 * we have to be sure we have accepted all pending requests just before
 * we start fsync'ing.  Since CreateCheckPoint sometimes runs in
 * non-checkpointer processes, do nothing if not checkpointer.
 */
void
AbsorbSyncRequests(void)
{
	CheckpointerRequest *requests = NULL;
	CheckpointerRequest *request;
	int			n,
				i;
	bool		loop;

	if (!AmCheckpointerProcess())
		return;

	do
	{
		LWLockAcquire(CheckpointerCommLock, LW_EXCLUSIVE);

		/*---
		 * We try to avoid holding the lock for a long time by:
		 * 1. Copying the request array and processing the requests after
		 *    releasing the lock;
		 * 2. Processing not the whole queue, but only batches of
		 *    CKPT_REQ_BATCH_SIZE at once.
		 *
		 * Once we have cleared the requests from shared memory, we must
		 * PANIC if we then fail to absorb them (e.g., because our hashtable
		 * runs out of memory).  This is because the system cannot run safely
		 * if we are unable to fsync what we have been told to fsync.
		 * Fortunately, the hashtable is so small that the problem is quite
		 * unlikely to arise in practice.
		 *
		 * Note: The maximum possible size of a ring buffer is
		 * MAX_CHECKPOINT_REQUESTS entries, which fit into a maximum palloc
		 * allocation size of 1Gb.  Our maximum batch size,
		 * CKPT_REQ_BATCH_SIZE, is even smaller.
		 */
		n = Min(CheckpointerShmem->num_requests, CKPT_REQ_BATCH_SIZE);
		if (n > 0)
		{
			if (!requests)
				requests = (CheckpointerRequest *) palloc(n * sizeof(CheckpointerRequest));

			for (i = 0; i < n; i++)
			{
				requests[i] = CheckpointerShmem->requests[CheckpointerShmem->head];
				CheckpointerShmem->head = (CheckpointerShmem->head + 1) % CheckpointerShmem->max_requests;
			}

			CheckpointerShmem->num_requests -= n;

		}

		START_CRIT_SECTION();

		/* Are there any requests in the queue? If so, keep going. */
		loop = CheckpointerShmem->num_requests != 0;

		LWLockRelease(CheckpointerCommLock);

		for (request = requests; n > 0; request++, n--)
			RememberSyncRequest(&request->ftag, request->type);

		END_CRIT_SECTION();
	} while (loop);

	if (requests)
		pfree(requests);
}

/*
 * Update any shared memory configurations based on config parameters
 *
 * 【中文总述】
 * 根据 SIGHUP 重载的配置参数，同步更新共享内存中的相关状态。
 * 两个核心操作：
 *   1. SyncRepUpdateSyncStandbysDefined()：更新同步复制的 standby 定义
 *   2. UpdateFullPageWrites()：若 full_page_writes 被修改，写入 XLOG_FPW_CHANGE 记录
 * 仅在 checkpointer 进程中被调用，由 ProcessCheckpointerInterrupts() 在每次主循环迭代时触发。
 * 【调用链】ProcessCheckpointerInterrupts() → UpdateSharedMemoryConfig()
 *   → SyncRepUpdateSyncStandbysDefined() + UpdateFullPageWrites()
 */
static void
UpdateSharedMemoryConfig(void)
{
	/* update global shmem state for sync rep */
	SyncRepUpdateSyncStandbysDefined();

	/*
	 * If full_page_writes has been changed by SIGHUP, we update it in shared
	 * memory and write an XLOG_FPW_CHANGE record.
	 */
	UpdateFullPageWrites();

	elog(DEBUG2, "checkpointer updated shared memory configuration values");
}

/*
 * FirstCallSinceLastCheckpoint allows a process to take an action once
 * per checkpoint cycle by asynchronously checking for checkpoint completion.
 *
 * 【中文总述】
 * 让其他进程在每个检查点周期中仅执行一次指定动作的辅助函数。
 * 通过异步检查检查点完成状态来实现：每次调用时比较当前的 ckpt_done
 * 与上次记录的值，若不同则说明检查点已完成，返回 true。
 * 典型用法：在后端进程的某个关键路径上调用，若返回 true 则执行一次
 * 清理或刷新操作（如释放临时快照、刷新 WAL 等）。
 * 注意：ckpt_done 是共享内存中的原子计数器，由 checkpointer 在每次
 * 检查点完成后更新；本函数使用自旋锁保护本地静态变量的读取。
 * 【调用链】checkpointer 完成检查点 → 更新 ckpt_done → 后端调用
 *   FirstCallSinceLastCheckpoint() → 返回 true → 执行一次动作
 */
bool
FirstCallSinceLastCheckpoint(void)
{
	static int	ckpt_done = 0;
	int			new_done;
	bool		FirstCall = false;

	SpinLockAcquire(&CheckpointerShmem->ckpt_lck);
	new_done = CheckpointerShmem->ckpt_done;
	SpinLockRelease(&CheckpointerShmem->ckpt_lck);

	if (new_done != ckpt_done)
		FirstCall = true;

	ckpt_done = new_done;

	return FirstCall;
}

/*
 * Wake up the checkpointer process.
 *
 * 【中文总述】
 * 唤醒检查点进程，使其从等待状态中退出并重新进入主循环。
 * 通过读取共享内存中记录的 checkpointer 进程号，获取其 procLatch，
 * 然后调用 SetLatch() 触发 latch 信号。
 * 任何需要触发检查点的进程都可以调用本函数（例如：收到 checkpoint
 * 请求、检测到 WAL 归档超时、检测到快速检查点请求等）。
 * 如果当前系统中没有 checkpointer 进程（checkpointerProc == INVALID_PROC_NUMBER），
 * 则不做任何操作。
 * 【调用链】RequestCheckpoint() / CheckArchiveTimeout() / FastCheckpointRequested()
 *   → WakeupCheckpointer() → SetLatch(checkpointerProc->procLatch)
 *   → checkpointer 主循环被唤醒 → ProcessCheckpointerInterrupts()
 */
void
WakeupCheckpointer(void)
{
	ProcNumber	checkpointerProc = pg_atomic_read_u32(&ProcGlobal->checkpointerProc);

	if (checkpointerProc != INVALID_PROC_NUMBER)
		SetLatch(&GetPGProcByNumber(checkpointerProc)->procLatch);
}
