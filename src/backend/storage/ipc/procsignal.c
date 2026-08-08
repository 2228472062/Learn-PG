/*-------------------------------------------------------------------------
 *
 * procsignal.c
 *	  Routines for interprocess signaling
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 进程间"信号级"通信机制:任何进程(后端、
 * 辅助进程、postmaster)都可以通过一块共享内存向另一个特定进程
 * 投递一个"带原因的软中断";目标进程收到 SIGUSR1 后,按共享内存
 * 里记录的原因做相应的处理。
 *
 * 【与 pmsignal.c / latch 的分工】
 *  - pmsignal.c 是"postmaster ↔ 子进程"的单向通知通道,用于进程
 *    管理级别的事件(数据库宕机、配置重载、子进程退出等);
 *  - procsignal.c 更通用:任何进程之间都能互相发,投递对象按
 *    ProcNumber(或 PID)精确定位,原因用枚举 ProcSignalReason 区分
 *    (sinval 追赶、NOTIFY、并行消息、恢复冲突、屏障等);
 *  - 共享内存通道传递"原因",真正把沉睡中的进程唤醒靠 latch:
 *    SIGUSR1 处理器检查并清除相应标志后,统一 SetLatch(MyLatch),
 *    进程主循环由此被唤醒。
 *
 * 【实现要点】
 *  - 共享内存里为每个 ProcNumber(+辅助进程类型)预留一个
 *    ProcSignalSlot,槽内用 pss_signalFlags 布尔数组记录"有哪些
 *    原因被投递过",由自旋锁 pss_mutex 保护;同一原因连续投递
 *    多次可能只被观察到一次(信号合并),这对现有用途无害;
 *  - 除"通知型"原因外,还有一种"屏障(barrier)"协议
 *    (EmitProcSignalBarrier / WaitForProcSignalBarrier):用于需要
 *    确认"每个进程都已吸收某项全局状态变更"的场景(如 smgr 关闭
 *    文件、数据校验和开关)。每个槽位维护一个"已确认代数"
 *    pss_barrierGeneration,发起者递增全局代数、在每槽位置位检查
 *    位图并唤醒所有进程;等待方(如 postmaster)逐个槽位等待代数
 *    追平,即可确信全局变更已被全员吸收;
 *  - SendCancelRequest 是客户端"取消查询"请求的入口:按 PID +
 *    随机取消密钥(cancel key)双重校验后给目标进程发 SIGINT,
 *    是 procsignal.c 中唯一直接使用 SIGINT(而非 SIGUSR1)的路径。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/procsignal.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>

#include "access/parallel.h"
#include "commands/async.h"
#include "commands/repack.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "port/pg_bitutils.h"
#include "postmaster/datachecksum_state.h"
#include "replication/logicalctl.h"
#include "replication/logicalworker.h"
#include "replication/slotsync.h"
#include "replication/walsender.h"
#include "storage/condition_variable.h"
#include "storage/ipc.h"
#include "storage/latch.h"
#include "storage/proc.h"
#include "storage/shmem.h"
#include "storage/sinval.h"
#include "storage/smgr.h"
#include "storage/subsystems.h"
#include "tcop/tcopprot.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

/*
 * The SIGUSR1 signal is multiplexed to support signaling multiple event
 * types. The specific reason is communicated via flags in shared memory.
 * We keep a boolean flag for each possible "reason", so that different
 * reasons can be signaled to a process concurrently.  (However, if the same
 * reason is signaled more than once nearly simultaneously, the process may
 * observe it only once.)
 *
 * Each process that wants to receive signals registers its process ID
 * in the ProcSignalSlots array. The array is indexed by ProcNumber to make
 * slot allocation simple, and to avoid having to search the array when you
 * know the ProcNumber of the process you're signaling.  (We do support
 * signaling without ProcNumber, but it's a bit less efficient.)
 *
 * The fields in each slot are protected by a spinlock, pss_mutex. pss_pid can
 * also be read without holding the spinlock, as a quick preliminary check
 * when searching for a particular PID in the array.
 *
 * pss_signalFlags are intended to be set in cases where we don't need to
 * keep track of whether or not the target process has handled the signal,
 * but sometimes we need confirmation, as when making a global state change
 * that cannot be considered complete until all backends have taken notice
 * of it. For such use cases, we set a bit in pss_barrierCheckMask and then
 * increment the current "barrier generation"; when the new barrier generation
 * (or greater) appears in the pss_barrierGeneration flag of every process,
 * we know that the message has been received everywhere.
 */
/* (中文)共享内存中的"进程信号槽":每个 ProcNumber(或辅助进程类型)
 * 一个,数组下标即 ProcNumber,因此按编号发信号是 O(1) 的。
 *
 * 字段含义:
 * - pss_pid              : 占用该槽位的进程 PID,0 表示槽位空闲;可用
 *                          原子读做"免锁快速初检"(SendProcSignal /
 *                          SendCancelRequest 先读它,命中才拿自旋锁);
 * - pss_cancel_key_len   : 取消密钥长度,0 表示无法取消该进程(例如
 *                          辅助进程没有可取消的查询);
 * - pss_cancel_key[]     : 随机取消密钥。客户端发取消请求时凭它验证
 *                          身份:即使知道了 PID,没有密钥也无法取消,
 *                          防止第三方误杀;
 * - pss_signalFlags[]    : 每种 ProcSignalReason 一个布尔标志,置位
 *                          表示"已向该进程投递过此原因"。类型为
 *                          volatile sig_atomic_t:信号处理器里读/清
 *                          无需自旋锁也保证原子;
 * - pss_mutex            : 保护 pss_pid / pss_cancel_key / pss_signalFlags
 *                          的自旋锁(barrier 相关字段不归它管);
 * - pss_barrierGeneration: 本进程已确认吸收的屏障代数。比全局代数小
 *                          说明还有未确认的屏障;进程退出时置
 *                          PG_UINT64_MAX 表示"永不阻塞等待方";
 * - pss_barrierCheckMask : 需要本进程吸收的屏障类型位图(原子);
 * - pss_barrierCV        : 等待方(WaitForProcSignalBarrier)睡眠用的
 *                          条件变量;本进程吸收屏障后广播唤醒。
 *                          (后三个字段用原子/条件变量,不依赖
 *                          pss_mutex。) */
typedef struct
{
	pg_atomic_uint32 pss_pid;
	int			pss_cancel_key_len; /* 0 means no cancellation is possible */
	uint8		pss_cancel_key[MAX_CANCEL_KEY_LENGTH];
	volatile sig_atomic_t pss_signalFlags[NUM_PROCSIGNALS];
	slock_t		pss_mutex;		/* protects the above fields */

	/* Barrier-related fields (not protected by pss_mutex) */
	pg_atomic_uint64 pss_barrierGeneration;
	pg_atomic_uint32 pss_barrierCheckMask;
	ConditionVariable pss_barrierCV;
} ProcSignalSlot;

/*
 * Information that is global to the entire ProcSignal system can be stored
 * here.
 *
 * psh_barrierGeneration is the highest barrier generation in existence.
 */
/* (中文)ProcSignal 系统的全局信息(共享内存首部):
 * - psh_barrierGeneration: 全系统当前最高的屏障代数,每次
 *   EmitProcSignalBarrier 递增 1(各槽位的 pss_barrierGeneration 应
 *   视其"确认进度" <= 此值);
 * - psh_slot[]           : 所有进程的信号槽数组(柔性数组,长度
 *   NumProcSignalSlots)。 */
struct ProcSignalHeader
{
	pg_atomic_uint64 psh_barrierGeneration;
	ProcSignalSlot psh_slot[FLEXIBLE_ARRAY_MEMBER];
};

/*
 * We reserve a slot for each possible ProcNumber, plus one for each
 * possible auxiliary process type.  (This scheme assumes there is not
 * more than one of any auxiliary process type at a time, except for
 * IO workers.)
 */
/* (中文)信号槽总数:每个可能的 ProcNumber 一个,外加每种辅助进程
 * 类型一个(方案假设每种辅助进程至多一个,IO worker 除外)。
 * 辅助进程没有 ProcNumber,使用靠后的专用槽位,因此按 PID 查找时
 * 从数组尾部往前搜更高效(SendProcSignal 的注释有说明)。 */
#define NumProcSignalSlots	(MaxBackends + NUM_AUXILIARY_PROCS)

/* Check whether the relevant type bit is set in the flags. */
/* (中文)屏障类型位的辅助宏:
 * - BARRIER_SHOULD_CHECK(flags, type):判断 flags 中该屏障类型位
 *   是否置位(本文件已不直接使用,保留为对称实现);
 * - BARRIER_CLEAR_BIT(flags, type):清除 flags 中的该屏障类型位。 */
#define BARRIER_SHOULD_CHECK(flags, type) \
	(((flags) & (((uint32) 1) << (uint32) (type))) != 0)

/* Clear the relevant type bit from the flags. */
#define BARRIER_CLEAR_BIT(flags, type) \
	((flags) &= ~(((uint32) 1) << (uint32) (type)))

static void ProcSignalShmemRequest(void *arg);
static void ProcSignalShmemInit(void *arg);

/* (中文)本文件向共享内存子系统登记的 request/init 回调:request 阶段
 * 声明 "ProcSignal" 区域大小(首部 + NumProcSignalSlots 个槽),init
 * 阶段初始化各原子字段、自旋锁与条件变量。 */
const ShmemCallbacks ProcSignalShmemCallbacks = {
	.request_fn = ProcSignalShmemRequest,
	.init_fn = ProcSignalShmemInit,
};

/* (中文)指向共享内存中 ProcSignalHeader 的指针。postmaster 启动时
 * 经 request/init 回调建立;Unix 系下所有子进程经 fork() 继承同一
 * 地址(EXEC_BACKEND 模式下进程重新附着)。 */
NON_EXEC_STATIC ProcSignalHeader *ProcSignal = NULL;

/* (中文)本进程自己的信号槽指针:ProcSignalInit 时指向
 * psh_slot[MyProcNumber],CheckProcSignal 与 CleanupProcSignalState
 * 使用;进程退出清理时先置 NULL,防止退出后到达的 SIGUSR1 处理器
 * 误访问已被释放的槽位。 */
static ProcSignalSlot *MyProcSignalSlot = NULL;

static bool CheckProcSignal(ProcSignalReason reason);
static void CleanupProcSignalState(int status, Datum arg);
static void ResetProcSignalBarrierBits(uint32 flags);

/*
 * ProcSignalShmemRequest
 *		Register ProcSignal's shared memory needs at postmaster startup
 */
/*
 * ProcSignalShmemRequest - (中文)登记 ProcSignal 的共享内存需求(request 阶段回调)
 *
 * 【作用】postmaster 启动早期的 request 阶段被共享内存框架调用:
 * 计算所需字节数(ProcSignalHeader 固定部分 + NumProcSignalSlots
 * 个 ProcSignalSlot),登记名为 "ProcSignal" 的区域,框架把最终
 * 地址写入全局指针 ProcSignal。
 *
 * 【设计思想】槽位数组用柔性数组紧随首部,一次分配成型。此时只
 * 记账,字段初始化留到 ProcSignalShmemInit。
 *
 * 【参数】arg —— 未使用(ShmemCallbacks 统一接口保留)。
 * 【返回值】无。
 */
static void
ProcSignalShmemRequest(void *arg)
{
	Size		size;

	size = mul_size(NumProcSignalSlots, sizeof(ProcSignalSlot));
	size = add_size(size, offsetof(ProcSignalHeader, psh_slot));

	ShmemRequestStruct(.name = "ProcSignal",
					   .size = size,
					   .ptr = (void **) &ProcSignal,
		);
}

/*
 * ProcSignalShmemInit
 *		Initialize ProcSignal's shared memory at postmaster startup
 */
/*
 * ProcSignalShmemInit - (中文)初始化 ProcSignal 共享段(init 阶段回调)
 *
 * 【作用】共享内存分配完成后由框架调用:把全局屏障代数清零,然后
 * 逐个槽位初始化:pss_mutex 自旋锁、pss_pid = 0(槽位空闲)、清空
 * 取消密钥与信号标志位图、pss_barrierGeneration 置 PG_UINT64_MAX
 * (表示"没有未确认的屏障",保证启动阶段不会有等待方被它卡住)、
 * pss_barrierCheckMask = 0、初始化条件变量。
 *
 * 【设计思想】此刻没有任何进程注册,不存在并发,可放心逐槽初始化。
 * 屏障代数初始为最大值,恰好与"进程退出时置最大值"的做法一致:
 * 空闲槽位永远不会阻塞 WaitForProcSignalBarrier。
 *
 * 【参数】arg —— 未使用。
 * 【返回值】无。
 */
static void
ProcSignalShmemInit(void *arg)
{
	pg_atomic_init_u64(&ProcSignal->psh_barrierGeneration, 0);

	for (int i = 0; i < NumProcSignalSlots; ++i)
	{
		ProcSignalSlot *slot = &ProcSignal->psh_slot[i];

		SpinLockInit(&slot->pss_mutex);
		pg_atomic_init_u32(&slot->pss_pid, 0);
		slot->pss_cancel_key_len = 0;
		MemSet(slot->pss_signalFlags, 0, sizeof(slot->pss_signalFlags));
		pg_atomic_init_u64(&slot->pss_barrierGeneration, PG_UINT64_MAX);
		pg_atomic_init_u32(&slot->pss_barrierCheckMask, 0);
		ConditionVariableInit(&slot->pss_barrierCV);
	}
}

/*
 * ProcSignalInit
 *		Register the current process in the ProcSignal array
 */
/*
 * ProcSignalInit - (中文)把当前进程注册进 ProcSignal 槽位数组
 *
 * 【作用】后端启动早期(InitPostgres 之前,用于处理早期取消请求)及
 * 辅助进程启动时调用:取 MyProcNumber 对应的槽位,在自旋锁保护下
 * 清掉遗留的信号标志、写入自己的 PID 与取消密钥、把屏障状态初始
 * 化为"已吸收最新全局代数"、记录 MyProcSignalSlot,并注册退出
 * 清理例程 on_shmem_exit(CleanupProcSignalState)。
 *
 * 【设计思想】
 * - "先发布 PID、再读全局屏障代数"的顺序是刻意安排的:若反过来,
 *   EmitProcSignalBarrier 可能在本进程登记前扫过该槽位、认定它
 *   不存在而跳过它,随后本进程却读到旧代数、声称"旧屏障已吸收"。
 *   两次原子写之间用内存屏障保证顺序;
 * - 新进程没有任何需要失效的旧状态,所以直接把自己宣告为"最新
 *   代数已吸收"(pss_barrierGeneration = 全局值),并清空检查位图;
 * - 这个初始化必须在启动序列中足够早,早到本进程还没有缓存任何
 *   需要被屏障作废的状态(否则"直接宣告已吸收"就会出错);
 * - 取消密钥:只有客户端可连接的进程(后端)才有,辅助进程传
 *   空密钥、长度为 0(表示不可取消)。
 *
 * 【参数】
 *   cancel_key     —— 本进程的取消密钥(随机字节串),可 NULL;
 *   cancel_key_len —— 密钥长度,0..MAX_CANCEL_KEY_LENGTH。
 * 【返回值】无;MyProcNumber 非法或槽位越界时报 ERROR。
 */
void
ProcSignalInit(const uint8 *cancel_key, int cancel_key_len)
{
	ProcSignalSlot *slot;
	uint64		barrier_generation;
	uint32		old_pss_pid;

	Assert(cancel_key_len >= 0 && cancel_key_len <= MAX_CANCEL_KEY_LENGTH);
	if (MyProcNumber < 0)
		elog(ERROR, "MyProcNumber not set");
	if (MyProcNumber >= NumProcSignalSlots)
		elog(ERROR, "unexpected MyProcNumber %d in ProcSignalInit (max %d)", MyProcNumber, NumProcSignalSlots);
	slot = &ProcSignal->psh_slot[MyProcNumber];

	SpinLockAcquire(&slot->pss_mutex);

	/* Value used for sanity check below */
	old_pss_pid = pg_atomic_read_u32(&slot->pss_pid);

	/* Clear out any leftover signal reasons */
	MemSet(slot->pss_signalFlags, 0, NUM_PROCSIGNALS * sizeof(sig_atomic_t));

	/*
	 * Publish the PID before reading the global barrier generation to ensure
	 * that EmitProcSignalBarrier() doesn't skip us while we are grabbing an
	 * older generation. We need a memory barrier here to make sure that the
	 * update of pss_pid is ordered before the subsequent load of
	 * psh_barrierGeneration.
	 */
	pg_atomic_write_membarrier_u32(&slot->pss_pid, MyProcPid);

	/*
	 * Initialize barrier state. Since we're a brand-new process, there
	 * shouldn't be any leftover backend-private state that needs to be
	 * updated. Therefore, we can broadcast the latest barrier generation and
	 * disregard any previously-set check bits.
	 *
	 * NB: This only works if this initialization happens early enough in the
	 * startup sequence that we haven't yet cached any state that might need
	 * to be invalidated. That's also why we have a memory barrier here, to be
	 * sure that any later reads of memory happen strictly after this.
	 */
	pg_atomic_write_u32(&slot->pss_barrierCheckMask, 0);
	barrier_generation =
		pg_atomic_read_u64(&ProcSignal->psh_barrierGeneration);
	pg_atomic_write_u64(&slot->pss_barrierGeneration, barrier_generation);

	if (cancel_key_len > 0)
		memcpy(slot->pss_cancel_key, cancel_key, cancel_key_len);
	slot->pss_cancel_key_len = cancel_key_len;

	SpinLockRelease(&slot->pss_mutex);

	/* Spinlock is released, do the check */
	if (old_pss_pid != 0)
		elog(LOG, "process %d taking over ProcSignal slot %d, but it's not empty",
			 MyProcPid, MyProcNumber);

	/* Remember slot location for CheckProcSignal */
	MyProcSignalSlot = slot;

	/* Set up to release the slot on process exit */
	on_shmem_exit(CleanupProcSignalState, (Datum) 0);
}

/*
 * CleanupProcSignalState
 *		Remove current process from ProcSignal mechanism
 *
 * This function is called via on_shmem_exit() during backend shutdown.
 */
/*
 * CleanupProcSignalState - (中文)进程退出时从 ProcSignal 机制中注销自己
 *
 * 【作用】经 on_shmem_exit() 在后端/辅助进程关闭时调用:先把
 * MyProcSignalSlot 置 NULL(此后到达的 SIGUSR1 处理器不会访问它),
 * 再在自旋锁保护下核对槽位里的 PID 确属自己,然后把 pss_pid 置 0
 * 释放槽位、清空取消密钥、把 pss_barrierGeneration 置为
 * PG_UINT64_MAX(向屏障等待方宣告"我不再阻塞你"),最后广播条件
 * 变量唤醒正在等待本槽位的 WaitForProcSignalBarrier。
 *
 * 【设计思想】
 * - 若发现槽位里已不是自己的 PID(异常情况,如槽位被别的进程
 *   顶替),只记 LOG 直接返回,绝不报错——进程反正要退出,报错
 *   可能陷入"退出失败→再触发退出"的循环;
 * - 屏障代数置最大值是"退出即豁免"的语义:等待方只需代数 >=
 *   目标代数,退出进程永远不会再吸收任何屏障,让等待方认为它
 *   已"吸收"即可,否则一个死掉的进程会让全局变更永久悬空。
 *
 * 【参数】
 *   status —— 退出状态码(on_shmem_exit 统一接口,未使用);
 *   arg    —— 未使用(ProcSignalInit 注册时传 0)。
 * 【返回值】无。
 */
static void
CleanupProcSignalState(int status, Datum arg)
{
	pid_t		old_pid;
	ProcSignalSlot *slot = MyProcSignalSlot;

	/*
	 * Clear MyProcSignalSlot, so that a SIGUSR1 received after this point
	 * won't try to access it after it's no longer ours (and perhaps even
	 * after we've unmapped the shared memory segment).
	 */
	Assert(MyProcSignalSlot != NULL);
	MyProcSignalSlot = NULL;

	/* sanity check */
	SpinLockAcquire(&slot->pss_mutex);
	old_pid = pg_atomic_read_u32(&slot->pss_pid);
	if (old_pid != MyProcPid)
	{
		/*
		 * don't ERROR here. We're exiting anyway, and don't want to get into
		 * infinite loop trying to exit
		 */
		SpinLockRelease(&slot->pss_mutex);
		elog(LOG, "process %d releasing ProcSignal slot %d, but it contains %d",
			 MyProcPid, (int) (slot - ProcSignal->psh_slot), (int) old_pid);
		return;					/* XXX better to zero the slot anyway? */
	}

	/* Mark the slot as unused */
	pg_atomic_write_u32(&slot->pss_pid, 0);
	slot->pss_cancel_key_len = 0;

	/*
	 * Make this slot look like it's absorbed all possible barriers, so that
	 * no barrier waits block on it.
	 */
	pg_atomic_write_u64(&slot->pss_barrierGeneration, PG_UINT64_MAX);

	SpinLockRelease(&slot->pss_mutex);

	ConditionVariableBroadcast(&slot->pss_barrierCV);
}

/*
 * SendProcSignal
 *		Send a signal to a Postgres process
 *
 * Providing procNumber is optional, but it will speed up the operation.
 *
 * On success (a signal was sent), zero is returned.
 * On error, -1 is returned, and errno is set (typically to ESRCH or EPERM).
 *
 * Not to be confused with ProcSendSignal
 */
/*
 * SendProcSignal - (中文)向指定的 PostgreSQL 进程投递一个带原因的软中断(SIGUSR1)
 *
 * 【作用】通用"单播通知"入口:在目标进程的槽位里置位
 * pss_signalFlags[reason],然后 kill(pid, SIGUSR1)。目标进程的
 * procsignal_sigusr1_handler() 收到信号后按原因分派处理。本函数
 * 是 sinvaladt.c(SIGET 追赶)、standby.c(恢复冲突)、异步通知等
 * 众多子系统的信号投递通道。
 *
 * 【设计思想】
 * - 传 procNumber 时是 O(1) 直达槽位;不传(INVALID_PROC_NUMBER)
 *   时按 PID 从数组尾部往前线性搜索——辅助进程的槽位在数组尾部,
 *   反向搜更可能先命中;
 * - 两次校验:先无锁原子读 pss_pid 快速初筛(免锁),命中后再拿
 *   自旋锁复读确认。PID 可能已被别的进程顶替(槽位被回收复用),
 *   复读保证不会把信号投给错误的进程;
 * - "先置标志、后发信号"的顺序很重要:若反过来,目标可能先收到
 *   信号、处理器检查标志发现没置位,漏掉这次通知;
 * - 同一原因连续投递多次可能被合并成一次(标志是布尔值),这是
 *   刻意接受的语义,所有调用方都按"至少通知一次"来使用;
 * - 与 ProcSendSignal(latch.c 的等待唤醒接口)不同:后者用 latch
 *   唤醒睡眠中的进程,本函数用信号标志 + SIGUSR1。
 *
 * 【参数】
 *   pid         —— 目标进程的 PID;
 *   reason      —— 通知原因(ProcSignalReason 枚举);
 *   procNumber  —— 目标进程的 ProcNumber;不知道可传
 *                  INVALID_PROC_NUMBER(将退化为按 PID 查找)。
 * 【返回值】0:信号已发送; -1:失败,errno 被设置(通常 ESRCH
 * 目标不存在,或 EPERM 无权限)。
 */
int
SendProcSignal(pid_t pid, ProcSignalReason reason, ProcNumber procNumber)
{
	ProcSignalSlot *slot;

	if (procNumber != INVALID_PROC_NUMBER)
	{
		Assert(procNumber < NumProcSignalSlots);
		slot = &ProcSignal->psh_slot[procNumber];

		SpinLockAcquire(&slot->pss_mutex);
		if (pg_atomic_read_u32(&slot->pss_pid) == pid)
		{
			/* Atomically set the proper flag */
			slot->pss_signalFlags[reason] = true;
			SpinLockRelease(&slot->pss_mutex);
			/* Send signal */
			return kill(pid, SIGUSR1);
		}
		SpinLockRelease(&slot->pss_mutex);
	}
	else
	{
		/*
		 * procNumber not provided, so search the array using pid.  We search
		 * the array back to front so as to reduce search overhead.  Passing
		 * INVALID_PROC_NUMBER means that the target is most likely an
		 * auxiliary process, which will have a slot near the end of the
		 * array.
		 */
		int			i;

		for (i = NumProcSignalSlots - 1; i >= 0; i--)
		{
			slot = &ProcSignal->psh_slot[i];

			if (pg_atomic_read_u32(&slot->pss_pid) == pid)
			{
				SpinLockAcquire(&slot->pss_mutex);
				if (pg_atomic_read_u32(&slot->pss_pid) == pid)
				{
					/* Atomically set the proper flag */
					slot->pss_signalFlags[reason] = true;
					SpinLockRelease(&slot->pss_mutex);
					/* Send signal */
					return kill(pid, SIGUSR1);
				}
				SpinLockRelease(&slot->pss_mutex);
			}
		}
	}

	errno = ESRCH;
	return -1;
}

/*
 * EmitProcSignalBarrier
 *		Send a signal to every Postgres process
 *
 * The return value of this function is the barrier "generation" created
 * by this operation. This value can be passed to WaitForProcSignalBarrier
 * to wait until it is known that every participant in the ProcSignal
 * mechanism has absorbed the signal (or started afterwards).
 *
 * Note that it would be a bad idea to use this for anything that happens
 * frequently, as interrupting every backend could cause a noticeable
 * performance hit.
 *
 * Callers are entitled to assume that this function will not throw ERROR
 * or FATAL.
 */
/*
 * EmitProcSignalBarrier - (中文)发起一轮"全局屏障":让所有进程确认吸收某状态变更
 *
 * 【作用】需要"所有参与进程都已吸收某项全局状态变更"时调用(例如
 * smgr 关闭所有已打开的文件、切换数据校验和设置)。执行三步:
 * 1) 在每个槽位的 pss_barrierCheckMask 里置入本屏障类型的位;
 * 2) 递增全局屏障代数 psh_barrierGeneration,得到本次的代数
 *    generation;
 * 3) 给所有活跃进程发 PROCSIG_BARRIER(置标志 + SIGUSR1),让它们
 *    尽快跑 ProcessProcSignalBarrier() 吸收屏障、更新自己槽位的
 *    pss_barrierGeneration。
 * 返回值 generation 交给调用者:WaitForProcSignalBarrier(generation)
 * 会一直等到每个槽位的代数 >= generation。
 *
 * 【设计思想】
 * - 先置检查位、再递增代数、最后发信号:任何顺序颠倒都会出现
 *   "进程已检查过旧位图、却在代数递增后才收到信号"的漏判窗口;
 *   两处原子操作本身都有全屏障语义,保证调用者之前对共享状态的
 *   修改对全体进程可见;
 * - 后加入的新进程必定已初始化到"最新代数已吸收"(见
 *   ProcSignalInit 的顺序约定),因此不会被本次屏障阻塞——但依然
 *   会被唤醒,只是不需要做任何事;
 * - 代价昂贵(打断所有后端),只能用于低频的全局变更,切勿用于
 *   热路径;
 * - 本函数绝不在调用者预期外抛错:全程只用原子操作与 kill。
 *
 * 【参数】
 *   type —— 屏障类型(ProcSignalBarrierType 枚举),决定了进程吸收
 *            时执行的处理函数。
 * 【返回值】本次屏障的代数(generation),传给 WaitForProcSignalBarrier。
 */
uint64
EmitProcSignalBarrier(ProcSignalBarrierType type)
{
	uint32		flagbit = 1 << (uint32) type;
	uint64		generation;

	/*
	 * Set all the flags.
	 *
	 * Note that pg_atomic_fetch_or_u32 has full barrier semantics, so this is
	 * totally ordered with respect to anything the caller did before, and
	 * anything that we do afterwards. (This is also true of the later call to
	 * pg_atomic_add_fetch_u64.)
	 */
	for (int i = 0; i < NumProcSignalSlots; i++)
	{
		ProcSignalSlot *slot = &ProcSignal->psh_slot[i];

		pg_atomic_fetch_or_u32(&slot->pss_barrierCheckMask, flagbit);
	}

	/*
	 * Increment the generation counter.
	 */
	generation =
		pg_atomic_add_fetch_u64(&ProcSignal->psh_barrierGeneration, 1);

	/*
	 * Signal all the processes, so that they update their advertised barrier
	 * generation.
	 *
	 * Concurrency is not a problem here. Backends that have exited don't
	 * matter, and new backends that have joined since we entered this
	 * function must already have current state, since the caller is
	 * responsible for making sure that the relevant state is entirely visible
	 * before calling this function in the first place. We still have to wake
	 * them up - because we can't distinguish between such backends and older
	 * backends that need to update state - but they won't actually need to
	 * change any state.
	 */
	for (int i = NumProcSignalSlots - 1; i >= 0; i--)
	{
		ProcSignalSlot *slot = &ProcSignal->psh_slot[i];
		pid_t		pid = pg_atomic_read_u32(&slot->pss_pid);

		if (pid != 0)
		{
			SpinLockAcquire(&slot->pss_mutex);
			pid = pg_atomic_read_u32(&slot->pss_pid);
			if (pid != 0)
			{
				/* see SendProcSignal for details */
				slot->pss_signalFlags[PROCSIG_BARRIER] = true;
				SpinLockRelease(&slot->pss_mutex);
				kill(pid, SIGUSR1);
			}
			else
				SpinLockRelease(&slot->pss_mutex);
		}
	}

	return generation;
}

/*
 * WaitForProcSignalBarrier - wait until it is guaranteed that all changes
 * requested by a specific call to EmitProcSignalBarrier() have taken effect.
 */
/*
 * WaitForProcSignalBarrier - (中文)等待某轮全局屏障被所有进程确认吸收
 *
 * 【作用】配合 EmitProcSignalBarrier 使用:逐个槽位读取
 * pss_barrierGeneration,若小于目标代数 generation,就睡在该槽位的
 * 条件变量 pss_barrierCV 上等待(每 5 秒醒来重查一次并打 LOG);
 * 所有槽位都追平后返回。
 *
 * 【设计思想】
 * - 只检查 pss_barrierGeneration、不检查 pss_barrierCheckMask:
 *   检查位在屏障"处理前"就被清零,而代数在"处理完成后"才更新,
 *   因此代数才是"已吸收"的可靠证据;
 * - 等待的是目标进程本身而不是它的行为:进程退出时把自己宣告为
 *   PG_UINT64_MAX(见 CleanupProcSignalState),等待方自然放过它,
 *   不会因个别进程死亡而永久阻塞;
 * - 返回前加一个全内存屏障:代数是用无锁原子读看到的,返回后调用
 *   者要读的"屏障所产生的共享状态变化"必须严格排在这次读取之后,
 *   屏障保证二者不重排;
 * - 调用者必须持有或独占相关的全局状态,确保"吸收"确实发生于
 *   EmitProcSignalBarrier 之前完成的所有可见变更之后。
 *
 * 【参数】
 *   generation —— EmitProcSignalBarrier 返回的代数(必须 <= 当前
 *                 全局代数,否则断言失败)。
 * 【返回值】无(永不超时返回;等待期间仅打日志)。
 */
void
WaitForProcSignalBarrier(uint64 generation)
{
	Assert(generation <= pg_atomic_read_u64(&ProcSignal->psh_barrierGeneration));

	elog(DEBUG1,
		 "waiting for all backends to process ProcSignalBarrier generation "
		 UINT64_FORMAT,
		 generation);

	for (int i = NumProcSignalSlots - 1; i >= 0; i--)
	{
		ProcSignalSlot *slot = &ProcSignal->psh_slot[i];
		uint64		oldval;

		/*
		 * It's important that we check only pss_barrierGeneration here and
		 * not pss_barrierCheckMask. Bits in pss_barrierCheckMask get cleared
		 * before the barrier is actually absorbed, but pss_barrierGeneration
		 * is updated only afterward.
		 */
		oldval = pg_atomic_read_u64(&slot->pss_barrierGeneration);
		while (oldval < generation)
		{
			if (ConditionVariableTimedSleep(&slot->pss_barrierCV,
											5000,
											WAIT_EVENT_PROC_SIGNAL_BARRIER))
				ereport(LOG,
						(errmsg("still waiting for backend with PID %d to accept ProcSignalBarrier",
								(int) pg_atomic_read_u32(&slot->pss_pid))));
			oldval = pg_atomic_read_u64(&slot->pss_barrierGeneration);
		}
		ConditionVariableCancelSleep();
	}

	elog(DEBUG1,
		 "finished waiting for all backends to process ProcSignalBarrier generation "
		 UINT64_FORMAT,
		 generation);

	/*
	 * The caller is probably calling this function because it wants to read
	 * the shared state or perform further writes to shared state once all
	 * backends are known to have absorbed the barrier. However, the read of
	 * pss_barrierGeneration was performed unlocked; insert a memory barrier
	 * to separate it from whatever follows.
	 */
	pg_memory_barrier();
}

/*
 * Handle receipt of an interrupt indicating a global barrier event.
 *
 * All the actual work is deferred to ProcessProcSignalBarrier(), because we
 * cannot safely access the barrier generation inside the signal handler as
 * 64bit atomics might use spinlock based emulation, even for reads. As this
 * routine only gets called when PROCSIG_BARRIER is sent that won't cause a
 * lot of unnecessary work.
 */
/*
 * HandleProcSignalBarrierInterrupt - (中文)屏障中断的信号处理器回调:仅记录待处理
 *
 * 【作用】收到 PROCSIG_BARRIER 信号时,由 procsignal_sigusr1_handler()
 * 调用:置位全局标志 ProcSignalBarrierPending 与 InterruptPending 后
 * 立即返回。真正的屏障吸收(ProcessProcSignalBarrier)推迟到下次
 * CHECK_FOR_INTERRUPTS() 执行。
 *
 * 【设计思想】信号处理器内不能安全地读 64 位原子(在部分平台上
 * 64 位原子用自旋锁模拟,信号上下文拿锁可能死锁),所以这里只做
 * 两个布尔赋值;唤醒进程仍由 sigusr1 处理器统一的 SetLatch 完成。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
HandleProcSignalBarrierInterrupt(void)
{
	InterruptPending = true;
	ProcSignalBarrierPending = true;
	/* latch will be set by procsignal_sigusr1_handler */
}

/*
 * Perform global barrier related interrupt checking.
 *
 * Any backend that participates in ProcSignal signaling must arrange to
 * call this function periodically. It is called from CHECK_FOR_INTERRUPTS(),
 * which is enough for normal backends, but not necessarily for all types of
 * background processes.
 */
/*
 * ProcessProcSignalBarrier - (中文)吸收(处理)本进程待确认的全局屏障
 *
 * 【作用】所有参与 ProcSignal 机制的进程都必须周期性调用(普通后端
 * 经 CHECK_FOR_INTERRUPTS 即可;辅助进程需自行安排在合适时机)。
 * 流程:
 * 1. ProcSignalBarrierPending 为假则直接返回(快速路径);
 * 2. 读自己槽位的代数与全局代数,若已追平说明信号先到、处理还没
 *    必要,返回(多轮屏障合并处理);
 * 3. 用原子交换把 pss_barrierCheckMask 取出并清零;对位图里的每个
 *    屏障类型调用对应的处理函数(ProcessBarrierSmgrRelease /
 *    ProcessBarrierUpdateXLogLogicalInfo / AbsorbDataChecksumsBarrier);
 *    处理函数返回 false(暂时无法吸收)或抛出 ERROR 时,把该类型位
 *    重新写回共享位图并置待处理标志,等下次再试;
 * 4. 全部类型处理成功后,把自己的代数更新为已观察到的全局代数,
 *    并广播条件变量唤醒等待方。
 *
 * 【设计思想】
 * - "先清零位图、再处理"是防止丢事件的正确顺序:如果先处理后清,
 *   处理期间新来的同类屏障会把位重新置上,而我们随后一清就把它
 *   清没了——必须"全部位先取走,处理失败的再放回去";
 * - 处理函数可能失败(例如暂时无法关文件)或出错,所以用
 *   PG_TRY 包裹并配合位图"找回"机制,保证任何情况下都不会丢失
 *   "需要处理"的记录;
 * - 代数只在自己槽位更新(每个进程管自己),等待方自行汇聚读取;
 * - 处理函数只对位图中实际置位的类型调用,省去无谓开销;类型位
 *   逐个用右移最低位提取,处理一个清一个,防止死循环。
 *
 * 【参数】无(操作对象是本进程自己的槽位)。
 * 【返回值】无。
 */
void
ProcessProcSignalBarrier(void)
{
	uint64		local_gen;
	uint64		shared_gen;
	volatile uint32 flags;

	Assert(MyProcSignalSlot);

	/* Exit quickly if there's no work to do. */
	if (!ProcSignalBarrierPending)
		return;
	ProcSignalBarrierPending = false;

	/*
	 * It's not unlikely to process multiple barriers at once, before the
	 * signals for all the barriers have arrived. To avoid unnecessary work in
	 * response to subsequent signals, exit early if we already have processed
	 * all of them.
	 */
	local_gen = pg_atomic_read_u64(&MyProcSignalSlot->pss_barrierGeneration);
	shared_gen = pg_atomic_read_u64(&ProcSignal->psh_barrierGeneration);

	Assert(local_gen <= shared_gen);

	if (local_gen == shared_gen)
		return;

	/*
	 * Get and clear the flags that are set for this backend. Note that
	 * pg_atomic_exchange_u32 is a full barrier, so we're guaranteed that the
	 * read of the barrier generation above happens before we atomically
	 * extract the flags, and that any subsequent state changes happen
	 * afterward.
	 *
	 * NB: In order to avoid race conditions, we must zero
	 * pss_barrierCheckMask first and only afterwards try to do barrier
	 * processing. If we did it in the other order, someone could send us
	 * another barrier of some type right after we called the
	 * barrier-processing function but before we cleared the bit. We would
	 * have no way of knowing that the bit needs to stay set in that case, so
	 * the need to call the barrier-processing function again would just get
	 * forgotten. So instead, we tentatively clear all the bits and then put
	 * back any for which we don't manage to successfully absorb the barrier.
	 */
	flags = pg_atomic_exchange_u32(&MyProcSignalSlot->pss_barrierCheckMask, 0);

	/*
	 * If there are no flags set, then we can skip doing any real work.
	 * Otherwise, establish a PG_TRY block, so that we don't lose track of
	 * which types of barrier processing are needed if an ERROR occurs.
	 */
	if (flags != 0)
	{
		bool		success = true;

		PG_TRY();
		{
			/*
			 * Process each type of barrier. The barrier-processing functions
			 * should normally return true, but may return false if the
			 * barrier can't be absorbed at the current time. This should be
			 * rare, because it's pretty expensive.  Every single
			 * CHECK_FOR_INTERRUPTS() will return here until we manage to
			 * absorb the barrier, and that cost will add up in a hurry.
			 *
			 * NB: It ought to be OK to call the barrier-processing functions
			 * unconditionally, but it's more efficient to call only the ones
			 * that might need us to do something based on the flags.
			 */
			while (flags != 0)
			{
				ProcSignalBarrierType type;
				bool		processed = true;

				type = (ProcSignalBarrierType) pg_rightmost_one_pos32(flags);
				switch (type)
				{
					case PROCSIGNAL_BARRIER_SMGRRELEASE:
						processed = ProcessBarrierSmgrRelease();
						break;
					case PROCSIGNAL_BARRIER_UPDATE_XLOG_LOGICAL_INFO:
						processed = ProcessBarrierUpdateXLogLogicalInfo();
						break;

					case PROCSIGNAL_BARRIER_CHECKSUM_INPROGRESS_ON:
					case PROCSIGNAL_BARRIER_CHECKSUM_ON:
					case PROCSIGNAL_BARRIER_CHECKSUM_INPROGRESS_OFF:
					case PROCSIGNAL_BARRIER_CHECKSUM_OFF:
						processed = AbsorbDataChecksumsBarrier(type);
						break;
				}

				/*
				 * To avoid an infinite loop, we must always unset the bit in
				 * flags.
				 */
				BARRIER_CLEAR_BIT(flags, type);

				/*
				 * If we failed to process the barrier, reset the shared bit
				 * so we try again later, and set a flag so that we don't bump
				 * our generation.
				 */
				if (!processed)
				{
					ResetProcSignalBarrierBits(((uint32) 1) << type);
					success = false;
				}
			}
		}
		PG_CATCH();
		{
			/*
			 * If an ERROR occurred, we'll need to try again later to handle
			 * that barrier type and any others that haven't been handled yet
			 * or weren't successfully absorbed.
			 */
			ResetProcSignalBarrierBits(flags);
			PG_RE_THROW();
		}
		PG_END_TRY();

		/*
		 * If some barrier types were not successfully absorbed, we will have
		 * to try again later.
		 */
		if (!success)
			return;
	}

	/*
	 * State changes related to all types of barriers that might have been
	 * emitted have now been handled, so we can update our notion of the
	 * generation to the one we observed before beginning the updates. If
	 * things have changed further, it'll get fixed up when this function is
	 * next called.
	 */
	pg_atomic_write_u64(&MyProcSignalSlot->pss_barrierGeneration, shared_gen);
	ConditionVariableBroadcast(&MyProcSignalSlot->pss_barrierCV);
}

/*
 * If it turns out that we couldn't absorb one or more barrier types, either
 * because the barrier-processing functions returned false or due to an error,
 * arrange for processing to be retried later.
 */
/*
 * ResetProcSignalBarrierBits - (中文)把未能吸收的屏障类型位放回共享位图,安排重试
 *
 * 【作用】ProcessProcSignalBarrier 中某类型处理失败(函数返回 false)
 * 或整个处理过程抛错(PG_CATCH 路径)时调用:用原子或把 flags 里
 * 的类型位重新并入 pss_barrierCheckMask,并置
 * ProcSignalBarrierPending / InterruptPending,确保下次
 * CHECK_FOR_INTERRUPTS 会再次尝试吸收。
 *
 * 【设计思想】"取走位 → 处理 → 失败的放回"三段式,配合
 * pss_barrierGeneration 只在全部成功后才更新,构成了屏障协议的
 * 不丢事件保证:等待方看到代数推进时,必然意味着该进程的所有
 * 屏障处理都已成功完成。
 *
 * 【参数】
 *   flags —— 需要重新置位的屏障类型位图(一个或多个位)。
 * 【返回值】无。
 */
static void
ResetProcSignalBarrierBits(uint32 flags)
{
	pg_atomic_fetch_or_u32(&MyProcSignalSlot->pss_barrierCheckMask, flags);
	ProcSignalBarrierPending = true;
	InterruptPending = true;
}

/*
 * CheckProcSignal - check to see if a particular reason has been
 * signaled, and clear the signal flag.  Should be called after receiving
 * SIGUSR1.
 */
/*
 * CheckProcSignal - (中文)检查指定原因是否被投递过,并清除该标志
 *
 * 【作用】procsignal_sigusr1_handler() 收到 SIGUSR1 后,对每个
 * ProcSignalReason 调用本函数轮询:若本进程槽位里该原因的标志为
 * true,清除之并返回 true(信号处理器随即分派对应的处理函数);
 * 否则返回 false。
 *
 * 【设计思想】pss_signalFlags 用 volatile sig_atomic_t 声明,允许
 * 信号处理器内"读+清"而不拿自旋锁(发送方拿锁写,接收方无锁读,
 * 这种不对称是刻意设计:信号上下文不能拿锁)。"先确认已置位再清"
 * 的顺序保证不会把一个还没观察到的通知提前抹掉。
 *
 * 【参数】
 *   reason —— 要检查的 ProcSignalReason。
 * 【返回值】true:该原因已被投递且本次消费掉;false:未投递。
 */
static bool
CheckProcSignal(ProcSignalReason reason)
{
	ProcSignalSlot *slot = MyProcSignalSlot;

	if (slot != NULL)
	{
		/*
		 * Careful here --- don't clear flag if we haven't seen it set.
		 * pss_signalFlags is of type "volatile sig_atomic_t" to allow us to
		 * read it here safely, without holding the spinlock.
		 */
		if (slot->pss_signalFlags[reason])
		{
			slot->pss_signalFlags[reason] = false;
			return true;
		}
	}

	return false;
}

/*
 * procsignal_sigusr1_handler - handle SIGUSR1 signal.
 */
/*
 * procsignal_sigusr1_handler - (中文)全局 SIGUSR1 信号处理器:按原因分派中断处理
 *
 * 【作用】本进程收到任何进程投递的 SIGUSR1 时进入(经 pqsignal 注册
 * 为 SIGUSR1 的处理器)。对每种 ProcSignalReason 依次调用
 * CheckProcSignal() 轮询;命中者调用对应的处理器(追赶 sinval、
 * NOTIFY、并行消息、恢复冲突、屏障、内存上下文转储等),最后统一
 * SetLatch(MyLatch) 唤醒主循环。
 *
 * 【设计思想】
 * - 各原因的标志位互相独立,多原因可并发投递,一次信号处理完所有
 *   已置位的原因(轮询是 O(原因数) 的常数开销);
 * - 所有"处理"都是轻量级记账(置标志),重活全部推迟到主循环的
 *   CHECK_FOR_INTERRUPTS(这是信号上下文的硬性约束);
 * - 即使进程不在睡眠(latch 已置),SetLatch 也是廉价操作,统一调用
 *   保证不遗漏唤醒;
 * - 注意与 HandleXxxInterrupt 的配合:它们可能互相同步(例如追赶
 *   处理在补读完后会请求清理队列)。
 *
 * 【参数】SIGNAL_ARGS(标准的信号处理器签名,含信号编号等)。
 * 【返回值】无。
 */
void
procsignal_sigusr1_handler(SIGNAL_ARGS)
{
	if (CheckProcSignal(PROCSIG_CATCHUP_INTERRUPT))
		HandleCatchupInterrupt();

	if (CheckProcSignal(PROCSIG_NOTIFY_INTERRUPT))
		HandleNotifyInterrupt();

	if (CheckProcSignal(PROCSIG_PARALLEL_MESSAGE))
		HandleParallelMessageInterrupt();

	if (CheckProcSignal(PROCSIG_WALSND_INIT_STOPPING))
		HandleWalSndInitStopping();

	if (CheckProcSignal(PROCSIG_BARRIER))
		HandleProcSignalBarrierInterrupt();

	if (CheckProcSignal(PROCSIG_LOG_MEMORY_CONTEXT))
		HandleLogMemoryContextInterrupt();

	if (CheckProcSignal(PROCSIG_PARALLEL_APPLY_MESSAGE))
		HandleParallelApplyMessageInterrupt();

	if (CheckProcSignal(PROCSIG_REPACK_MESSAGE))
		HandleRepackMessageInterrupt();

	if (CheckProcSignal(PROCSIG_SLOTSYNC_MESSAGE))
		HandleSlotSyncMessageInterrupt();

	if (CheckProcSignal(PROCSIG_RECOVERY_CONFLICT))
		HandleRecoveryConflictInterrupt();

	SetLatch(MyLatch);
}

/*
 * Send a query cancellation signal to backend.
 *
 * Note: This is called from a backend process before authentication.  We
 * cannot take LWLocks yet, but that's OK; we rely on atomic reads of the
 * fields in the ProcSignal slots.
 */
/*
 * SendCancelRequest - (中文)按 PID + 取消密钥向目标后端发送取消查询请求(SIGINT)
 *
 * 【作用】处理客户端"取消查询"(Cancel Request)协议消息的入口
 * (后端认证完成前就会调用,见 postmaster/backend 启动路径):遍历
 * 全部槽位,找到 PID 匹配且取消密钥一致的后端,给它(及其进程组)
 * 发 SIGINT 以中断当前查询;密钥不符或找不到则记日志。
 *
 * 【设计思想】
 * - 认证前的进程不能拿 LWLock,因此全部依赖原子读与自旋锁之外的
 *   临时窗口:读 pss_pid 与取消密钥是竞态的(目标可能刚好退出),
 *   但"密钥恰好撞上错误进程"的概率极小,可以接受;PID 复用本身
 *   也固有竞态,但 OS 通常不会很快复用 PID;
 * - 先无锁读 pss_pid 初筛,命中再拿自旋锁复读并比较密钥,减少锁
 *   开销;密钥比较用 timingsafe_bcmp(恒定时间比较,防止攻击者用
 *   时序推断密钥字节);
 * - 取消密钥是随机生成的(见 postmaster 的 cancel_key 生成),攻击
 *   者即使知道 PID 也无法取消他人的查询;
 * - 有 setsid 的平台向整个进程组发 SIGINT(HAVE_SETSID),保证
 *   --fork-process 派生出的子进程也能被取消。
 *
 * 【参数】
 *   backendPID     —— 目标后端 PID(0 视为非法,记日志后返回);
 *   cancel_key     —— 客户端提供的取消密钥;
 *   cancel_key_len —— 密钥长度。
 * 【返回值】无(成功/失败都只记录日志)。
 */
void
SendCancelRequest(int backendPID, const uint8 *cancel_key, int cancel_key_len)
{
	if (backendPID == 0)
	{
		ereport(LOG, (errmsg("invalid cancel request with PID 0")));
		return;
	}

	/*
	 * See if we have a matching backend. Reading the pss_pid and
	 * pss_cancel_key fields is racy, a backend might die and remove itself
	 * from the array at any time.  The probability of the cancellation key
	 * matching wrong process is miniscule, however, so we can live with that.
	 * PIDs are reused too, so sending the signal based on PID is inherently
	 * racy anyway, although OS's avoid reusing PIDs too soon.
	 */
	for (int i = 0; i < NumProcSignalSlots; i++)
	{
		ProcSignalSlot *slot = &ProcSignal->psh_slot[i];
		bool		match;

		if (pg_atomic_read_u32(&slot->pss_pid) != backendPID)
			continue;

		/* Acquire the spinlock and re-check */
		SpinLockAcquire(&slot->pss_mutex);
		if (pg_atomic_read_u32(&slot->pss_pid) != backendPID)
		{
			SpinLockRelease(&slot->pss_mutex);
			continue;
		}
		else
		{
			match = slot->pss_cancel_key_len == cancel_key_len &&
				timingsafe_bcmp(slot->pss_cancel_key, cancel_key, cancel_key_len) == 0;

			SpinLockRelease(&slot->pss_mutex);

			if (match)
			{
				/* Found a match; signal that backend to cancel current op */
				ereport(DEBUG2,
						(errmsg_internal("processing cancel request: sending SIGINT to process %d",
										 backendPID)));

				/*
				 * If we have setsid(), signal the backend's whole process
				 * group
				 */
#ifdef HAVE_SETSID
				kill(-backendPID, SIGINT);
#else
				kill(backendPID, SIGINT);
#endif
			}
			else
			{
				/* Right PID, wrong key: no way, Jose */
				ereport(LOG,
						(errmsg("wrong key in cancel request for process %d",
								backendPID)));
			}
			return;
		}
	}

	/* No matching backend */
	ereport(LOG,
			(errmsg("PID %d in cancel request did not match any process",
					backendPID)));
}
