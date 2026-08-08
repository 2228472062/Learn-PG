/*-------------------------------------------------------------------------
 *
 * sinvaladt.c
 *	  POSTGRES shared cache invalidation data manager.
 *
 * 【模块总览(中文)】
 * 本文件是"共享缓存失效(shared cache invalidation,简称 SI)"消息的
 * 数据管理层:在共享内存中维护一条存放失效消息的环形缓冲区,并提供
 * 入队(SIInsertDataEntries)、出队(SIGetDataEntries)、清理
 * (SICleanupQueue)三大操作。上层的 sinval.c 负责发送/接收的封装,
 * syscache.c / relcache.c 负责消费消息后真正失效本地缓存。
 *
 * 【概念模型】
 * 消息队列在概念上是一条"无限长的数组":每个消息拥有一个全局序号
 * MsgNum。maxMsgNum 是下一个将被写入的序号(写游标),minMsgNum 是
 * 尚未被所有后端读完的最老消息的序号(全局下界),两者相等表示队列
 * 为空。每个后端进程有一个自己的读游标 nextMsgNum,满足
 * maxMsgNum >= nextMsgNum >= minMsgNum。物理上消息只存放在一个
 * 4096 项的环形缓冲区 buffer[] 中,用 MsgNum % MAXNUMMESSAGES 换算
 * 槽位(取模很快,因为 MAXNUMMESSAGES 是 2 的幂)。只要
 * maxMsgNum - minMsgNum <= MAXNUMMESSAGES,队列就不溢出。
 *
 * 【溢出与追赶策略】
 * 一旦缓冲区将满,不能让所有后端陪着慢速后端一起堵死:落后太多的
 * 后端会被标记 resetState(下次读取时它必须整体重置本地缓存,代价
 * 大但可接受);同时给落后得比较多的后端发 PROCSIG_CATCHUP_INTERRUPT
 * 追赶信号,让它们尽快补读。追赶信号一次只发给"落后最远的一个",
 * 该后端处理完补读后,在 SICleanupQueue 里把信号接力传给下一个
 * ("菊花链"),避免同时唤醒大量后端造成负载尖峰;队列越来越满时
 * 清理阈值会被收紧,从而给"还没被通知"的落后后端补发信号。
 *
 * 【并发控制】
 * 加锁模型(详见下方英文注释)要点:
 *  - 写者拿 SInvalWriteLock(独占)串行入队;读者拿 SInvalReadLock
 *    (共享),且只允许修改自己的 ProcState,不允许看/改别人的;
 *  - 写者与读者可以并行:唯一交集是 maxMsgNum 字段,读者读它、
 *    写者改它,用自旋锁 msgnumLock 串行化——这同时充当内存屏障,
 *    保证"消息内容先写入 buffer、maxMsgNum 再发布"的次序对读者
 *    可见(弱内存序的多处理器上若无屏障会读到旧数据);
 *  - 需要全局性调整时(如 SICleanupQueue 重算 minMsgNum),读者锁
 *    要升级为独占,把一切读者挡在门外。
 *
 * 【附带职责】本文件还保管每个 ProcNumber 槽位的
 * nextLocalTransactionId(见 GetNextLocalTransactionId):虚拟事务号
 * VirtualTransactionId 的高半部分是 ProcNumber、低半部分是本地
 * 计数器分配的 LocalTransactionId,把"该槽位下次该用的本地序号"
 * 存进共享内存,可避免同一 PGPROC 槽位的前后继承者在短时间内
 * 重用同一个虚拟事务号。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/sinvaladt.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>

#include "miscadmin.h"
#include "storage/ipc.h"
#include "storage/proc.h"
#include "storage/procnumber.h"
#include "storage/procsignal.h"
#include "storage/shmem.h"
#include "storage/sinvaladt.h"
#include "storage/spin.h"
#include "storage/subsystems.h"

/*
 * Conceptually, the shared cache invalidation messages are stored in an
 * infinite array, where maxMsgNum is the next array subscript to store a
 * submitted message in, minMsgNum is the smallest array subscript containing
 * a message not yet read by all backends, and we always have maxMsgNum >=
 * minMsgNum.  (They are equal when there are no messages pending.)  For each
 * active backend, there is a nextMsgNum pointer indicating the next message it
 * needs to read; we have maxMsgNum >= nextMsgNum >= minMsgNum for every
 * backend.
 *
 * (In the current implementation, minMsgNum is a lower bound for the
 * per-process nextMsgNum values, but it isn't rigorously kept equal to the
 * smallest nextMsgNum --- it may lag behind.  We only update it when
 * SICleanupQueue is called, and we try not to do that often.)
 *
 * In reality, the messages are stored in a circular buffer of MAXNUMMESSAGES
 * entries.  We translate MsgNum values into circular-buffer indexes by
 * computing MsgNum % MAXNUMMESSAGES (this should be fast as long as
 * MAXNUMMESSAGES is a constant and a power of 2).  As long as maxMsgNum
 * doesn't exceed minMsgNum by more than MAXNUMMESSAGES, we have enough space
 * in the buffer.  If the buffer does overflow, we recover by setting the
 * "reset" flag for each backend that has fallen too far behind.  A backend
 * that is in "reset" state is ignored while determining minMsgNum.  When
 * it does finally attempt to receive inval messages, it must discard all
 * its invalidatable state, since it won't know what it missed.
 *
 * To reduce the probability of needing resets, we send a "catchup" interrupt
 * to any backend that seems to be falling unreasonably far behind.  The
 * normal behavior is that at most one such interrupt is in flight at a time;
 * when a backend completes processing a catchup interrupt, it executes
 * SICleanupQueue, which will signal the next-furthest-behind backend if
 * needed.  This avoids undue contention from multiple backends all trying
 * to catch up at once.  However, the furthest-back backend might be stuck
 * in a state where it can't catch up.  Eventually it will get reset, so it
 * won't cause any more problems for anyone but itself.  But we don't want
 * to find that a bunch of other backends are now too close to the reset
 * threshold to be saved.  So SICleanupQueue is designed to occasionally
 * send extra catchup interrupts as the queue gets fuller, to backends that
 * are far behind and haven't gotten one yet.  As long as there aren't a lot
 * of "stuck" backends, we won't need a lot of extra interrupts, since ones
 * that aren't stuck will propagate their interrupts to the next guy.
 *
 * We would have problems if the MsgNum values overflow an integer, so
 * whenever minMsgNum exceeds MSGNUMWRAPAROUND, we subtract MSGNUMWRAPAROUND
 * from all the MsgNum variables simultaneously.  MSGNUMWRAPAROUND can be
 * large so that we don't need to do this often.  It must be a multiple of
 * MAXNUMMESSAGES so that the existing circular-buffer entries don't need
 * to be moved when we do it.
 *
 * Access to the shared sinval array is protected by two locks, SInvalReadLock
 * and SInvalWriteLock.  Readers take SInvalReadLock in shared mode; this
 * authorizes them to modify their own ProcState but not to modify or even
 * look at anyone else's.  When we need to perform array-wide updates,
 * such as in SICleanupQueue, we take SInvalReadLock in exclusive mode to
 * lock out all readers.  Writers take SInvalWriteLock (always in exclusive
 * mode) to serialize adding messages to the queue.  Note that a writer
 * can operate in parallel with one or more readers, because the writer
 * has no need to touch anyone's ProcState, except in the infrequent cases
 * when SICleanupQueue is needed.  The only point of overlap is that
 * the writer wants to change maxMsgNum while readers need to read it.
 * We deal with that by having a spinlock that readers must take for just
 * long enough to read maxMsgNum, while writers take it for just long enough
 * to write maxMsgNum.  (The exact rule is that you need the spinlock to
 * read maxMsgNum if you are not holding SInvalWriteLock, and you need the
 * spinlock to write maxMsgNum unless you are holding both locks.)
 *
 * Note: since maxMsgNum is an int and hence presumably atomically readable/
 * writable, the spinlock might seem unnecessary.  The reason it is needed
 * is to provide a memory barrier: we need to be sure that messages written
 * to the array are actually there before maxMsgNum is increased, and that
 * readers will see that data after fetching maxMsgNum.  Multiprocessors
 * that have weak memory-ordering guarantees can fail without the memory
 * barrier instructions that are included in the spinlock sequences.
 */


/*
 * Configurable parameters.
 *
 * MAXNUMMESSAGES: max number of shared-inval messages we can buffer.
 * Must be a power of 2 for speed.
 *
 * MSGNUMWRAPAROUND: how often to reduce MsgNum variables to avoid overflow.
 * Must be a multiple of MAXNUMMESSAGES.  Should be large.
 *
 * CLEANUP_MIN: the minimum number of messages that must be in the buffer
 * before we bother to call SICleanupQueue.
 *
 * CLEANUP_QUANTUM: how often (in messages) to call SICleanupQueue once
 * we exceed CLEANUP_MIN.  Should be a power of 2 for speed.
 *
 * SIG_THRESHOLD: the minimum number of messages a backend must have fallen
 * behind before we'll send it PROCSIG_CATCHUP_INTERRUPT.
 *
 * WRITE_QUANTUM: the max number of messages to push into the buffer per
 * iteration of SIInsertDataEntries.  Noncritical but should be less than
 * CLEANUP_QUANTUM, because we only consider calling SICleanupQueue once
 * per iteration.
 */
/* (中文)可配置参数(具体语义见上方英文注释):
 * - MAXNUMMESSAGES = 4096:环形缓冲区容量,必须是 2 的幂(用位运算
 *   取模换算槽位,最快);
 * - MSGNUMWRAPAROUND:消息序号整体回退的基数——当 minMsgNum 超过该
 *   值时,把所有序号同时减去它,防止 32 位整数溢出;必须是
 *   MAXNUMMESSAGES 的整数倍,回退时环形槽位的映射(MsgNum mod
 *   MAXNUMMESSAGES)保持不变,缓冲区内容无需搬移;
 * - CLEANUP_MIN:积压消息数达到该值才值得调用 SICleanupQueue 做清理
 *   (清理本身要拿独占锁,太频繁得不偿失);
 * - CLEANUP_QUANTUM:超过 CLEANUP_MIN 后,每积压这么多条消息就再做
 *   一次清理;是 2 的幂,便于位运算;
 * - SIG_THRESHOLD:后端落后超过这么多条消息,才给它发
 *   PROCSIG_CATCHUP_INTERRUPT 追赶信号;
 * - WRITE_QUANTUM:SIInsertDataEntries 每批最多写入的消息条数,保证
 *   单次持 SInvalWriteLock 的时间可控,而且每个批次都有机会考虑
 *   是否需要调用 SICleanupQueue。 */
#define MAXNUMMESSAGES 4096
#define MSGNUMWRAPAROUND (MAXNUMMESSAGES * 262144)
#define CLEANUP_MIN (MAXNUMMESSAGES / 2)
#define CLEANUP_QUANTUM (MAXNUMMESSAGES / 16)
#define SIG_THRESHOLD (MAXNUMMESSAGES / 2)
#define WRITE_QUANTUM 64

/* Per-backend state in shared invalidation structure */
/* (中文)每个后端进程在共享失效结构中的私有状态,按 ProcNumber 索引,
 * 数组元素个数为 NumProcStateSlots。一个后端注册(SharedInvalBackendInit)
 * 后,它的读游标、追赶/重置标志等都存放在这里。
 *
 * 字段含义:
 * - procPid    : 占用该槽位的进程 PID;procPid == 0 表示槽位空闲
 *                (inactive),此时其余字段无意义;
 * - nextMsgNum : 本后端下一个要读取的消息序号(读游标);procPid == 0
 *                或 resetState 为 true 时该值无意义;
 * - resetState : 本后端已落后到必须"整体重置本地缓存"的地步(队列
 *                溢出时被强制置位),下一次读取应返回"重置"指令;
 *                置位期间其 nextMsgNum 不参与全局最小值 minMsgNum
 *                的计算;
 * - signaled   : 已向本后端发过 PROCSIG_CATCHUP_INTERRUPT 追赶信号,
 *                在它追上进度(SIGetDataEntries 读到队列底部)之前
 *                不再重复打扰它;
 * - hasMessages: 队列里存在本后端尚未读取的消息(快速预判标志;
 *                SIGetDataEntries 先无锁读它,为 false 时直接返回 0,
 *                避免不必要的锁开销);
 * - sendOnly   : 只发送、从不接收失效消息的后端。仅 standby 的
 *                Startup 进程使用:重放期间它没有本地 relcache,
 *                却要向查询后端广播 schema 变更,因此既不需要读
 *                消息、也不该被追赶信号打扰;
 * - nextLXID   : 该槽位下一个要分配的 LocalTransactionId。后端退出
 *                时(CleanupInvalidationState)把本地计数器的当前值
 *                写回,槽位被新进程继承时(SharedInvalBackendInit)
 *                取出继续递增,保证虚拟事务号在前后进程间连续。 */
typedef struct ProcState
{
	/* procPid is zero in an inactive ProcState array entry. */
	pid_t		procPid;		/* PID of backend, for signaling */
	/* nextMsgNum is meaningless if procPid == 0 or resetState is true. */
	int			nextMsgNum;		/* next message number to read */
	bool		resetState;		/* backend needs to reset its state */
	bool		signaled;		/* backend has been sent catchup signal */
	bool		hasMessages;	/* backend has unread messages */

	/*
	 * Backend only sends invalidations, never receives them. This only makes
	 * sense for Startup process during recovery because it doesn't maintain a
	 * relcache, yet it fires inval messages to allow query backends to see
	 * schema changes.
	 */
	bool		sendOnly;		/* backend only sends, never receives */

	/*
	 * Next LocalTransactionId to use for each idle backend slot.  We keep
	 * this here because it is indexed by ProcNumber and it is convenient to
	 * copy the value to and from local memory when MyProcNumber is set. It's
	 * meaningless in an active ProcState entry.
	 */
	LocalTransactionId nextLXID;
} ProcState;

/* Shared cache invalidation memory segment */
/* (中文)共享缓存失效内存段(位于共享内存,全局唯一,由指针
 * shmInvalBuffer 指向)。字段含义:
 * - minMsgNum   : 所有活跃后端中"最老仍未读完"的消息序号(全局下界,
 *                 实质是各 nextMsgNum 的最小值的近似值,只在
 *                 SICleanupQueue 里更新,可能滞后);
 * - maxMsgNum   : 下一个待分配的消息序号(写游标),恒有
 *                 maxMsgNum >= minMsgNum;
 * - nextThreshold: 下次触发 SICleanupQueue 的积压消息数阈值
 *                 (介于 CLEANUP_MIN 与 MAXNUMMESSAGES 之间);
 * - msgnumLock  : 保护 maxMsgNum 读写的自旋锁(兼作内存屏障,见
 *                 文件头英文注释);
 * - buffer[]    : 环形消息缓冲区,共 MAXNUMMESSAGES 项;槽位用
 *                 MsgNum % MAXNUMMESSAGES 定位;
 * - numProcs    : 当前活跃(已注册)的后端个数;
 * - pgprocnos   : 活跃后端 ProcNumber 的稠密数组(连续排列、无空洞),
 *                 用于快速遍历全部活跃槽位;与 ProcArray 的 pgprocnos
 *                 冗余,但省掉对 ProcArrayLock 的争用,且只跟踪参与
 *                 SI 的进程;
 * - procState[] : 每后端状态数组(见 ProcState),按 ProcNumber 索引,
 *                 柔性数组紧随固定头之后。 */
typedef struct SISeg
{
	/*
	 * General state information
	 */
	int			minMsgNum;		/* oldest message still needed */
	int			maxMsgNum;		/* next message number to be assigned */
	int			nextThreshold;	/* # of messages to call SICleanupQueue */

	slock_t		msgnumLock;		/* spinlock protecting maxMsgNum */

	/*
	 * Circular buffer holding shared-inval messages
	 */
	SharedInvalidationMessage buffer[MAXNUMMESSAGES];

	/*
	 * Per-backend invalidation state info.
	 *
	 * 'procState' has NumProcStateSlots entries, and is indexed by pgprocno.
	 * 'numProcs' is the number of slots currently in use, and 'pgprocnos' is
	 * a dense array of their indexes, to speed up scanning all in-use slots.
	 *
	 * 'pgprocnos' is largely redundant with ProcArrayStruct->pgprocnos, but
	 * having our separate copy avoids contention on ProcArrayLock, and allows
	 * us to track only the processes that participate in shared cache
	 * invalidations.
	 */
	int			numProcs;
	int		   *pgprocnos;
	ProcState	procState[FLEXIBLE_ARRAY_MEMBER];
} SISeg;

/*
 * We reserve a slot for each possible ProcNumber, plus one for each
 * possible auxiliary process type.  (This scheme assumes there is not
 * more than one of any auxiliary process type at a time, except for
 * IO workers.)
 */
/* (中文)ProcState 槽位总数:为每个可能的 ProcNumber 留一个,再为
 * 每种可能的辅助进程(auxiliary process,如 checkpointer、bgwriter
 * 等,编号靠后)各留一个。该方案假设每种辅助进程至多一个(IO
 * worker 除外)。 */
#define NumProcStateSlots	(MaxBackends + NUM_AUXILIARY_PROCS)

/* (中文)指向共享失效内存段的指针,在共享内存 request/init 回调中
 * 建立;Unix 系下所有子进程经 fork() 继承同一地址。 */
static SISeg *shmInvalBuffer;	/* pointer to the shared inval buffer */

static void SharedInvalShmemRequest(void *arg);
static void SharedInvalShmemInit(void *arg);

/* (中文)本文件向共享内存子系统登记的 request/init 回调:request 阶段
 * 声明 "shmInvalBuffer" 区域的大小,init 阶段完成字段初始化。 */
const ShmemCallbacks SharedInvalShmemCallbacks = {
	.request_fn = SharedInvalShmemRequest,
	.init_fn = SharedInvalShmemInit,
};


/* (中文)本进程当前的本地事务号计数器(LocalTransactionId 分配用):
 * 初值取自共享槽位的 nextLXID(SharedInvalBackendInit),进程退出时
 * 写回(CleanupInvalidationState)。详见 GetNextLocalTransactionId 的
 * 中文注释。 */
static LocalTransactionId nextLocalTransactionId;

static void CleanupInvalidationState(int status, Datum arg);


/*
 * SharedInvalShmemRequest
 *		Register shared memory needs for the SI message buffer
 */
/*
 * SharedInvalShmemRequest - (中文)登记 SI 消息缓冲区的共享内存需求(request 阶段回调)
 *
 * 【作用】postmaster 启动早期的 request 阶段被共享内存框架调用:计算
 * 共享失效段所需总字节数——固定头部分(offsetof(SISeg, procState)) +
 * NumProcStateSlots 个 ProcState(procState[] 数组) + NumProcStateSlots
 * 个 int(pgprocnos 数组),然后调用 ShmemRequestStruct 登记名为
 * "shmInvalBuffer" 的区域,框架会把最终地址写入全局变量
 * shmInvalBuffer。
 *
 * 【设计思想】procState 用柔性数组紧随固定头,pgprocnos 再往后追加
 * 一块,一次分配成型、无碎片。注意 request 阶段只"记账"不分配,
 * 内存要等 init 回调执行时才真正可用。
 *
 * 【参数】arg —— 未使用(ShmemCallbacks 回调的统一接口保留)。
 * 【返回值】无。
 */
static void
SharedInvalShmemRequest(void *arg)
{
	Size		size;

	size = offsetof(SISeg, procState);
	size = add_size(size, mul_size(sizeof(ProcState), NumProcStateSlots));	/* procState */
	size = add_size(size, mul_size(sizeof(int), NumProcStateSlots));	/* pgprocnos */

	ShmemRequestStruct(.name = "shmInvalBuffer",
					   .size = size,
					   .ptr = (void **) &shmInvalBuffer,
		);
}

/*
 * SharedInvalShmemInit - (中文)初始化 SI 消息缓冲区共享段(init 阶段回调)
 *
 * 【作用】共享内存分配完成后由框架调用:把消息计数器清零
 * (minMsgNum / maxMsgNum)、初始化自旋锁 msgnumLock、把全部
 * ProcState 槽位标记为空闲(procPid = 0)并初始化 nextLXID,
 * 最后把 pgprocnos 指向 procState 数组末尾之后的那块内存
 * (此刻 numProcs = 0,还没有任何活跃后端;buffer[] 无需填充,
 * 未用槽位读到什么无所谓)。
 *
 * 【设计思想】此刻系统还没有任何后端进程,不存在并发问题,可以
 * 放心逐字段初始化。nextLXID 初始化为 InvalidLocalTransactionId,
 * 第一个占用槽位的后端会从该值之后开始分配。
 *
 * 【参数】arg —— 未使用。
 * 【返回值】无。
 */
static void
SharedInvalShmemInit(void *arg)
{
	int			i;

	/* Clear message counters, init spinlock */
	shmInvalBuffer->minMsgNum = 0;
	shmInvalBuffer->maxMsgNum = 0;
	shmInvalBuffer->nextThreshold = CLEANUP_MIN;
	SpinLockInit(&shmInvalBuffer->msgnumLock);

	/* The buffer[] array is initially all unused, so we need not fill it */

	/* Mark all backends inactive, and initialize nextLXID */
	for (i = 0; i < NumProcStateSlots; i++)
	{
		shmInvalBuffer->procState[i].procPid = 0;	/* inactive */
		shmInvalBuffer->procState[i].nextMsgNum = 0;	/* meaningless */
		shmInvalBuffer->procState[i].resetState = false;
		shmInvalBuffer->procState[i].signaled = false;
		shmInvalBuffer->procState[i].hasMessages = false;
		shmInvalBuffer->procState[i].nextLXID = InvalidLocalTransactionId;
	}
	shmInvalBuffer->numProcs = 0;
	shmInvalBuffer->pgprocnos = (int *) &shmInvalBuffer->procState[i];
}

/*
 * SharedInvalBackendInit
 *		Initialize a new backend to operate on the sinval buffer
 */
/*
 * SharedInvalBackendInit - (中文)让本后端正式注册到 SI 消息队列上(成为参与者)
 *
 * 【作用】后端启动早期(InitPostgres)调用,把本进程登记进共享失效
 * 段:把自己的 ProcNumber 追加进 pgprocnos 稠密数组、把读游标
 * nextMsgNum 直接定位到当前 maxMsgNum(即"现存消息全部视为已读",
 * 新后端没有任何欠账)、恢复 nextLocalTransactionId 初值、清除各
 * 标志,最后注册退出清理例程 on_shmem_exit(CleanupInvalidationState)。
 *
 * 【设计思想】
 * - 必须持有 SInvalWriteLock(独占)执行:本函数虽只写自己的
 *   ProcState,但 SIInsertDataEntries 依赖 pgprocnos 数组给所有
 *   活跃后端置 hasMessages,不能与之并发;读操作则允许并行
 *   (procState 各字段按槽位隔离);
 * - 槽位以 MyProcNumber 固定对应,注册即占用:若该槽位 procPid
 *   非 0(上一进程未清理干净),直接报 ERROR 拒绝;
 * - sendOnly 模式(Startup 进程)不接收消息,因此永远不会收到追赶
 *   信号、也不参与 minMsgNum 计算——它在 recovery 期间要持续广播
 *   失效消息,却没有任何本地缓存需要维护;
 * - nextLXID 从共享槽位恢复,保证同一槽位的后继进程在虚拟事务号
 *   上接着递增。
 *
 * 【参数】
 *   sendOnly —— true 表示本后端只发送失效消息、从不接收(当前仅
 *               standby 的 Startup 进程使用)。
 * 【返回值】无;槽位已被占用时直接报 ERROR(不是静默失败)。
 */
void
SharedInvalBackendInit(bool sendOnly)
{
	ProcState  *stateP;
	pid_t		oldPid;
	SISeg	   *segP = shmInvalBuffer;

	if (MyProcNumber < 0)
		elog(ERROR, "MyProcNumber not set");
	if (MyProcNumber >= NumProcStateSlots)
		elog(PANIC, "unexpected MyProcNumber %d in SharedInvalBackendInit (max %d)",
			 MyProcNumber, NumProcStateSlots);
	stateP = &segP->procState[MyProcNumber];

	/*
	 * This can run in parallel with read operations, but not with write
	 * operations, since SIInsertDataEntries relies on the pgprocnos array to
	 * set hasMessages appropriately.
	 */
	LWLockAcquire(SInvalWriteLock, LW_EXCLUSIVE);

	oldPid = stateP->procPid;
	if (oldPid != 0)
	{
		LWLockRelease(SInvalWriteLock);
		elog(ERROR, "sinval slot for backend %d is already in use by process %d",
			 MyProcNumber, (int) oldPid);
	}

	shmInvalBuffer->pgprocnos[shmInvalBuffer->numProcs++] = MyProcNumber;

	/* Fetch next local transaction ID into local memory */
	nextLocalTransactionId = stateP->nextLXID;

	/* mark myself active, with all extant messages already read */
	stateP->procPid = MyProcPid;
	stateP->nextMsgNum = segP->maxMsgNum;
	stateP->resetState = false;
	stateP->signaled = false;
	stateP->hasMessages = false;
	stateP->sendOnly = sendOnly;

	LWLockRelease(SInvalWriteLock);

	/* register exit routine to mark my entry inactive at exit */
	on_shmem_exit(CleanupInvalidationState, PointerGetDatum(segP));
}

/*
 * CleanupInvalidationState
 *		Mark the current backend as no longer active.
 *
 * This function is called via on_shmem_exit() during backend shutdown.
 *
 * arg is really of type "SISeg*".
 */
/*
 * CleanupInvalidationState - (中文)后端退出时把 SI 槽位标记为空闲(共享内存退出清理例程)
 *
 * 【作用】经 on_shmem_exit() 在后端关闭时调用(与
 * SharedInvalBackendInit 成对):先把本地 nextLocalTransactionId 的
 * 当前值写回共享槽位(供下一个占用该 ProcNumber 的进程继承),再把
 * procPid 置 0 使槽位空闲,最后把本进程的 ProcNumber 从 pgprocnos
 * 稠密数组中移除(用数组最后一个元素覆盖要删除的位置,再缩短
 * numProcs,保持数组无空洞)。
 *
 * 【设计思想】全程持有 SInvalWriteLock(独占),与注册、入队互斥;
 * 从数组尾部向前查找自己的条目,若找不到说明共享数组已损坏,直接
 * PANIC。退出时本进程残留的 reset/signaled 标志一并清除,槽位交还
 * 给下一个使用者时是全新状态。
 *
 * 【参数】
 *   status —— 退出状态码(on_shmem_exit 统一接口,未使用);
 *   arg    —— Datum 包装的 SISeg * 指针。
 * 【返回值】无。
 */
static void
CleanupInvalidationState(int status, Datum arg)
{
	SISeg	   *segP = (SISeg *) DatumGetPointer(arg);
	ProcState  *stateP;
	int			i;

	Assert(segP);

	LWLockAcquire(SInvalWriteLock, LW_EXCLUSIVE);

	stateP = &segP->procState[MyProcNumber];

	/* Update next local transaction ID for next holder of this proc number */
	stateP->nextLXID = nextLocalTransactionId;

	/* Mark myself inactive */
	stateP->procPid = 0;
	stateP->nextMsgNum = 0;
	stateP->resetState = false;
	stateP->signaled = false;

	for (i = segP->numProcs - 1; i >= 0; i--)
	{
		if (segP->pgprocnos[i] == MyProcNumber)
		{
			if (i != segP->numProcs - 1)
				segP->pgprocnos[i] = segP->pgprocnos[segP->numProcs - 1];
			break;
		}
	}
	if (i < 0)
		elog(PANIC, "could not find entry in sinval array");
	segP->numProcs--;

	LWLockRelease(SInvalWriteLock);
}

/*
 * SIInsertDataEntries
 *		Add new invalidation message(s) to the buffer.
 */
/*
 * SIInsertDataEntries - (中文)把一条或多条失效消息写入共享环形缓冲队列(写入口)
 *
 * 【作用】由 sinval.c 的 SendSharedInvalidMessages() 调用,是所有
 * 失效消息进入共享队列的唯一路径。n 条消息按 WRITE_QUANTUM(64)分
 * 批写入,每个批次执行:拿 SInvalWriteLock(独占)→ 检查队列空间,
 * 空间不足或积压超阈值就调用 SICleanupQueue(循环重查,直到放得下
 * 本批)→ 把消息拷入 buffer[](槽位 = MsgNum % MAXNUMMESSAGES)→
 * 用自旋锁 msgnumLock 发布新的 maxMsgNum → 给所有活跃后端置
 * hasMessages = true(提示它们队列有新货)→ 释放锁。
 *
 * 【设计思想】
 * - 分批写是为了不长时间独占 SInvalWriteLock:尤其在某个后端刚刚
 *   追上来、正等着调用 SICleanupQueue 接力追赶信号时,不希望它等
 *   太久(英文注释:与其说是照顾其他写者,不如说是照顾读端);
 * - 队列满时"必须"腾空间:调用 SICleanupQueue 会把阻挡空间释放的
 *   落后后端强制标记为 reset(它只能整体重置本地缓存)。宁可个别
 *   后端重置,也不能阻塞全体写者;
 * - 发布 maxMsgNum 用自旋锁:既串行化与读者的竞争,又提供内存
 *   屏障,确保 buffer[] 里的消息内容先于 maxMsgNum 的新值对读者
 *   可见(否则弱内存序的机器上读者可能读到"序号已前进、槽位还是
 *   旧内容"的错乱状态);
 * - 释放 SInvalWriteLock 是一个完整的内存屏障,保证对 procState
 *   的写入(hasMessages)在函数返回前已全局可见;
 * - 无论是否真的写入了消息,都要给所有后端置 hasMessages:这比
 *   逐个精确判定"哪些后端需要"便宜,读端本身有快速预判。
 *
 * 【参数】
 *   data —— 待写入消息数组的首指针(只读);
 *   n    —— 消息条数,可为任意大小。
 * 【返回值】无。
 */
void
SIInsertDataEntries(const SharedInvalidationMessage *data, int n)
{
	SISeg	   *segP = shmInvalBuffer;

	/*
	 * N can be arbitrarily large.  We divide the work into groups of no more
	 * than WRITE_QUANTUM messages, to be sure that we don't hold the lock for
	 * an unreasonably long time.  (This is not so much because we care about
	 * letting in other writers, as that some just-caught-up backend might be
	 * trying to do SICleanupQueue to pass on its signal, and we don't want it
	 * to have to wait a long time.)  Also, we need to consider calling
	 * SICleanupQueue every so often.
	 */
	while (n > 0)
	{
		int			nthistime = Min(n, WRITE_QUANTUM);
		int			numMsgs;
		int			max;
		int			i;

		n -= nthistime;

		LWLockAcquire(SInvalWriteLock, LW_EXCLUSIVE);

		/*
		 * If the buffer is full, we *must* acquire some space.  Clean the
		 * queue and reset anyone who is preventing space from being freed.
		 * Otherwise, clean the queue only when it's exceeded the next
		 * fullness threshold.  We have to loop and recheck the buffer state
		 * after any call of SICleanupQueue.
		 */
		for (;;)
		{
			numMsgs = segP->maxMsgNum - segP->minMsgNum;
			if (numMsgs + nthistime > MAXNUMMESSAGES ||
				numMsgs >= segP->nextThreshold)
				SICleanupQueue(true, nthistime);
			else
				break;
		}

		/*
		 * Insert new message(s) into proper slot of circular buffer
		 */
		max = segP->maxMsgNum;
		while (nthistime-- > 0)
		{
			segP->buffer[max % MAXNUMMESSAGES] = *data++;
			max++;
		}

		/* Update current value of maxMsgNum using spinlock */
		SpinLockAcquire(&segP->msgnumLock);
		segP->maxMsgNum = max;
		SpinLockRelease(&segP->msgnumLock);

		/*
		 * Now that the maxMsgNum change is globally visible, we give everyone
		 * a swift kick to make sure they read the newly added messages.
		 * Releasing SInvalWriteLock will enforce a full memory barrier, so
		 * these (unlocked) changes will be committed to memory before we exit
		 * the function.
		 */
		for (i = 0; i < segP->numProcs; i++)
		{
			ProcState  *stateP = &segP->procState[segP->pgprocnos[i]];

			stateP->hasMessages = true;
		}

		LWLockRelease(SInvalWriteLock);
	}
}

/*
 * SIGetDataEntries
 *		get next SI message(s) for current backend, if there are any
 *
 * Possible return values:
 *	0:	 no SI message available
 *	n>0: next n SI messages have been extracted into data[]
 * -1:	 SI reset message extracted
 *
 * If the return value is less than the array size "datasize", the caller
 * can assume that there are no more SI messages after the one(s) returned.
 * Otherwise, another call is needed to collect more messages.
 *
 * NB: this can run in parallel with other instances of SIGetDataEntries
 * executing on behalf of other backends, since each instance will modify only
 * fields of its own backend's ProcState, and no instance will look at fields
 * of other backends' ProcStates.  We express this by grabbing SInvalReadLock
 * in shared mode.  Note that this is not exactly the normal (read-only)
 * interpretation of a shared lock! Look closely at the interactions before
 * allowing SInvalReadLock to be grabbed in shared mode for any other reason!
 *
 * NB: this can also run in parallel with SIInsertDataEntries.  It is not
 * guaranteed that we will return any messages added after the routine is
 * entered.
 *
 * Note: we assume that "datasize" is not so large that it might be important
 * to break our hold on SInvalReadLock into segments.
 */
/*
 * SIGetDataEntries - (中文)取回本后端尚未读取的失效消息(读入口)
 *
 * 【作用】由 sinval.c 的 ReceiveSharedInvalidMessages() 调用。执行
 * 流程:先无锁快速检查本后端的 hasMessages,为 false 直接返回 0
 * (省掉锁开销);否则拿 SInvalReadLock(共享模式)后,把 hasMessages
 * 复位、经自旋锁读当前 maxMsgNum、检查 resetState(置位则返回 -1),
 * 否则把从 nextMsgNum 到 maxMsgNum 之间的消息逐条复制进调用者的
 * 数组,推进自己的读游标,最后按是否追上队列尾部决定 signaled /
 * hasMessages 的复位。
 *
 * 【设计思想】
 * - 并发规则:多个后端的 SIGetDataEntries 可以并行运行
 *   (SInvalReadLock 共享),因为各实例只读写自己槽位的 ProcState;
 *   它也可以与 SIInsertDataEntries 并行——所以 maxMsgNum 的读取
 *   必须过自旋锁,既是串行化也是内存屏障(保证读到的序号所对应的
 *   槽位内容已经真实可见)。注意:SInvalReadLock 的共享模式在此
 *   并不完全是"只读"语义(英文注释特别提醒:不要据此把它用于
 *   其他场合);
 * - 先复位 hasMessages 再决定读多少:此后新入队的消息会重新置位
 *   该标志,本调用即使提前退出也不会漏掉(下次还能补上);
 * - resetState 置位时返回 -1,并把读游标直接拨到 maxMsgNum:表示
 *   "之前欠下的消息全部作废、从当前位置重新开始",接收方随即
 *   整体重置本地缓存;
 * - 已取出的消息不在此删除:其他后端可能还没读,删除统一由
 *   SICleanupQueue 负责;
 * - 收尾的转折点:完全追上(maxMsgNum)则清除 signaled(允许下次
 *   再被发追赶信号),没追上则重新置 hasMessages(本调用未读尽,
 *   下次继续)。
 *
 * 【参数】
 *   data     —— 输出参数,调用者提供的消息数组,接收复制出的消息;
 *   datasize —— 该数组的容量(消息条数上限)。
 * 【返回值】0:当前无可读消息;n(>0):复制了 n 条,若 n < datasize
 * 说明队列已读空、无需再调用;若 n == datasize 可能还有剩余,调用者
 * 应再调一次;-1:收到"重置"指令,调用者必须整体丢弃本地缓存状态。
 */
int
SIGetDataEntries(SharedInvalidationMessage *data, int datasize)
{
	SISeg	   *segP;
	ProcState  *stateP;
	int			max;
	int			n;

	segP = shmInvalBuffer;
	stateP = &segP->procState[MyProcNumber];

	/*
	 * Before starting to take locks, do a quick, unlocked test to see whether
	 * there can possibly be anything to read.  On a multiprocessor system,
	 * it's possible that this load could migrate backwards and occur before
	 * we actually enter this function, so we might miss a sinval message that
	 * was just added by some other processor.  But they can't migrate
	 * backwards over a preceding lock acquisition, so it should be OK.  If we
	 * haven't acquired a lock preventing against further relevant
	 * invalidations, any such occurrence is not much different than if the
	 * invalidation had arrived slightly later in the first place.
	 */
	if (!stateP->hasMessages)
		return 0;

	LWLockAcquire(SInvalReadLock, LW_SHARED);

	/*
	 * We must reset hasMessages before determining how many messages we're
	 * going to read.  That way, if new messages arrive after we have
	 * determined how many we're reading, the flag will get reset and we'll
	 * notice those messages part-way through.
	 *
	 * Note that, if we don't end up reading all of the messages, we had
	 * better be certain to reset this flag before exiting!
	 */
	stateP->hasMessages = false;

	/* Fetch current value of maxMsgNum using spinlock */
	SpinLockAcquire(&segP->msgnumLock);
	max = segP->maxMsgNum;
	SpinLockRelease(&segP->msgnumLock);

	if (stateP->resetState)
	{
		/*
		 * Force reset.  We can say we have dealt with any messages added
		 * since the reset, as well; and that means we should clear the
		 * signaled flag, too.
		 */
		stateP->nextMsgNum = max;
		stateP->resetState = false;
		stateP->signaled = false;
		LWLockRelease(SInvalReadLock);
		return -1;
	}

	/*
	 * Retrieve messages and advance backend's counter, until data array is
	 * full or there are no more messages.
	 *
	 * There may be other backends that haven't read the message(s), so we
	 * cannot delete them here.  SICleanupQueue() will eventually remove them
	 * from the queue.
	 */
	n = 0;
	while (n < datasize && stateP->nextMsgNum < max)
	{
		data[n++] = segP->buffer[stateP->nextMsgNum % MAXNUMMESSAGES];
		stateP->nextMsgNum++;
	}

	/*
	 * If we have caught up completely, reset our "signaled" flag so that
	 * we'll get another signal if we fall behind again.
	 *
	 * If we haven't caught up completely, reset the hasMessages flag so that
	 * we see the remaining messages next time.
	 */
	if (stateP->nextMsgNum >= max)
		stateP->signaled = false;
	else
		stateP->hasMessages = true;

	LWLockRelease(SInvalReadLock);
	return n;
}

/*
 * SICleanupQueue
 *		Remove messages that have been consumed by all active backends
 *
 * callerHasWriteLock is true if caller is holding SInvalWriteLock.
 * minFree is the minimum number of message slots to make free.
 *
 * Possible side effects of this routine include marking one or more
 * backends as "reset" in the array, and sending PROCSIG_CATCHUP_INTERRUPT
 * to some backend that seems to be getting too far behind.  We signal at
 * most one backend at a time, for reasons explained at the top of the file.
 *
 * Caution: because we transiently release write lock when we have to signal
 * some other backend, it is NOT guaranteed that there are still minFree
 * free message slots at exit.  Caller must recheck and perhaps retry.
 */
/*
 * SICleanupQueue - (中文)清理已被所有后端读完的消息,并调度追赶/重置(全局维护)
 *
 * 【作用】在三种场景被调用:写者发现队列将满或积压超过阈值
 * (SIInsertDataEntries 内带写锁调用)、追赶完成的后端接力清理
 * (sinval.c 的 ReceiveSharedInvalidMessages 内无写锁调用)。做四件事:
 * 1) 重算 minMsgNum = 所有非 reset、非 sendOnly 后端 nextMsgNum 的
 *    最小值,并把落后到"低于 lowbound(再不清腾就会溢出)"的后端
 *    强制置 resetState;
 * 2) 全体消息序号过大时统一回退(减去 MSGNUMWRAPAROUND),防止
 *    32 位计数器溢出;
 * 3) 根据当前积压量设定下次清理的阈值 nextThreshold(队列越满阈值
 *    越紧,清理就越频繁);
 * 4) 给"落后最远且尚未被通知"的一个后端发
 *    PROCSIG_CATCHUP_INTERRUPT 追赶信号(每次最多一个)。
 *
 * 【设计思想】
 * - 本函数会改动任意后端的 ProcState 与全局 minMsgNum,因此必须拿
 *   SInvalReadLock 的独占模式把所有读者挡在门外;若调用者未拿写锁,
 *   还要先拿 SInvalWriteLock(独占)把写者挡在门外;
 * - 发信号是系统调用(kill),可能慢,所以先释放两把锁再发
 *   (signaled 标志则在持锁时置位,防止并发时重复发送);因此
 *   "退出时还保证有 minFree 个空闲槽"并不成立,调用者必须循环
 *   重查并可能重试(SIInsertDataEntries 的 for(;;) 就是这样);
 * - 追赶信号每次只发一个,形成"处理完一个接力下一个"的菊花链,
 *   避免群体性补读造成负载尖峰;队列越来越满时 nextThreshold 收紧,
 *   清理被调得更勤,从而有机会给"还没被通知"的落后后端补发信号;
 * - sendOnly 后端被完全忽略:即使它是唯一活跃者,也能持续发送消息
 *   而不被误伤(它没有读游标);
 * - 序号回退必须在持有两把锁时一次性完成,并保证所有游标同步减去
 *   同一基数(减数是 MAXNUMMESSAGES 的整数倍,槽位映射不变)。
 *
 * 【参数】
 *   callerHasWriteLock —— 调用者是否已持有 SInvalWriteLock:true 时
 *                         本函数不重复获取,且只在需要发信号时短暂
 *                         释放后重新获取;false 时自行获取/释放;
 *   minFree            —— 至少需要腾出的空闲消息槽数量(队列溢出
 *                         场景传 nthistime,必须强清),普通清理传 0。
 * 【返回值】无。
 */
void
SICleanupQueue(bool callerHasWriteLock, int minFree)
{
	SISeg	   *segP = shmInvalBuffer;
	int			min,
				minsig,
				lowbound,
				numMsgs,
				i;
	ProcState  *needSig = NULL;

	/* Lock out all writers and readers */
	if (!callerHasWriteLock)
		LWLockAcquire(SInvalWriteLock, LW_EXCLUSIVE);
	LWLockAcquire(SInvalReadLock, LW_EXCLUSIVE);

	/*
	 * Recompute minMsgNum = minimum of all backends' nextMsgNum, identify the
	 * furthest-back backend that needs signaling (if any), and reset any
	 * backends that are too far back.  Note that because we ignore sendOnly
	 * backends here it is possible for them to keep sending messages without
	 * a problem even when they are the only active backend.
	 */
	min = segP->maxMsgNum;
	minsig = min - SIG_THRESHOLD;
	lowbound = min - MAXNUMMESSAGES + minFree;

	for (i = 0; i < segP->numProcs; i++)
	{
		ProcState  *stateP = &segP->procState[segP->pgprocnos[i]];
		int			n = stateP->nextMsgNum;

		/* Ignore if already in reset state */
		Assert(stateP->procPid != 0);
		if (stateP->resetState || stateP->sendOnly)
			continue;

		/*
		 * If we must free some space and this backend is preventing it, force
		 * him into reset state and then ignore until he catches up.
		 */
		if (n < lowbound)
		{
			stateP->resetState = true;
			/* no point in signaling him ... */
			continue;
		}

		/* Track the global minimum nextMsgNum */
		if (n < min)
			min = n;

		/* Also see who's furthest back of the unsignaled backends */
		if (n < minsig && !stateP->signaled)
		{
			minsig = n;
			needSig = stateP;
		}
	}
	segP->minMsgNum = min;

	/*
	 * When minMsgNum gets really large, decrement all message counters so as
	 * to forestall overflow of the counters.  This happens seldom enough that
	 * folding it into the previous loop would be a loser.
	 */
	if (min >= MSGNUMWRAPAROUND)
	{
		segP->minMsgNum -= MSGNUMWRAPAROUND;
		segP->maxMsgNum -= MSGNUMWRAPAROUND;
		for (i = 0; i < segP->numProcs; i++)
			segP->procState[segP->pgprocnos[i]].nextMsgNum -= MSGNUMWRAPAROUND;
	}

	/*
	 * Determine how many messages are still in the queue, and set the
	 * threshold at which we should repeat SICleanupQueue().
	 */
	numMsgs = segP->maxMsgNum - segP->minMsgNum;
	if (numMsgs < CLEANUP_MIN)
		segP->nextThreshold = CLEANUP_MIN;
	else
		segP->nextThreshold = (numMsgs / CLEANUP_QUANTUM + 1) * CLEANUP_QUANTUM;

	/*
	 * Lastly, signal anyone who needs a catchup interrupt.  Since
	 * SendProcSignal() might not be fast, we don't want to hold locks while
	 * executing it.
	 */
	if (needSig)
	{
		pid_t		his_pid = needSig->procPid;
		ProcNumber	his_procNumber = (needSig - &segP->procState[0]);

		needSig->signaled = true;
		LWLockRelease(SInvalReadLock);
		LWLockRelease(SInvalWriteLock);
		elog(DEBUG4, "sending sinval catchup signal to PID %d", (int) his_pid);
		SendProcSignal(his_pid, PROCSIG_CATCHUP_INTERRUPT, his_procNumber);
		if (callerHasWriteLock)
			LWLockAcquire(SInvalWriteLock, LW_EXCLUSIVE);
	}
	else
	{
		LWLockRelease(SInvalReadLock);
		if (!callerHasWriteLock)
			LWLockRelease(SInvalWriteLock);
	}
}


/*
 * GetNextLocalTransactionId --- allocate a new LocalTransactionId
 *
 * We split VirtualTransactionIds into two parts so that it is possible
 * to allocate a new one without any contention for shared memory, except
 * for a bit of additional overhead during backend startup/shutdown.
 * The high-order part of a VirtualTransactionId is a ProcNumber, and the
 * low-order part is a LocalTransactionId, which we assign from a local
 * counter.  To avoid the risk of a VirtualTransactionId being reused
 * within a short interval, successive procs occupying the same PGPROC slot
 * should use a consecutive sequence of local IDs, which is implemented
 * by copying nextLocalTransactionId as seen above.
 */
/*
 * GetNextLocalTransactionId - (中文)分配一个新的 LocalTransactionId(虚拟事务号低半部分)
 *
 * 【作用】在需要创建 VirtualTransactionId 的地方(锁管理器、两阶段
 * 提交等)被调用,返回本地计数器 nextLocalTransactionId 的下一个值,
 * 并把计数器 +1 供下次使用。
 *
 * 【设计思想】VirtualTransactionId 被拆成两半:高半部分是
 * ProcNumber(共享,后端启动时确定),低半部分是 LocalTransactionId
 * (本地计数器递增)。这样分配新虚拟事务号时完全不需要碰共享内存、
 * 不需要任何锁——唯一的一点额外开销发生在后端启动/退出时(读/写
 * 槽位里的 nextLXID)。为了避免"同一 PGPROC 槽位的前后两个进程在
 * 短时间内重用同一个虚拟事务号",槽位的 nextLXID 在进程间接力
 * (注册时读、退出时写),使序列连续递增。分配循环跳过
 * InvalidLocalTransactionId(0),防止 32 位环绕时把"无效值"发出去。
 *
 * 【参数】无。
 * 【返回值】新的 LocalTransactionId,保证有效(非 0)。
 */
LocalTransactionId
GetNextLocalTransactionId(void)
{
	LocalTransactionId result;

	/* loop to avoid returning InvalidLocalTransactionId at wraparound */
	do
	{
		result = nextLocalTransactionId++;
	} while (!LocalTransactionIdIsValid(result));

	return result;
}
