/*-------------------------------------------------------------------------
 *
 * method_worker.c
 *    AIO - perform AIO using worker processes
 *
 * IO workers consume IOs from a shared memory submission queue, run
 * traditional synchronous system calls, and perform the shared completion
 * handling immediately.  Client code submits most requests by pushing IOs
 * into the submission queue, and waits (if necessary) using condition
 * variables.  Some IOs cannot be performed in another process due to lack of
 * infrastructure for reopening the file, and must processed synchronously by
 * the client code when submitted.
 *
 * The pool of workers tries to stabilize at a size that can handle recently
 * seen variation in demand, within the configured limits.
 *
 * This method of AIO is available in all builds on all operating systems, and
 * is the default.
 *
 * 【模块总览(中文)】
 * 本文件实现 io_method=worker 的 AIO 方法(所有平台可用、也是默认
 * 方法):把"异步"委托给一组 IO worker 进程——它们从共享内存的提交
 * 队列里取 IO,用传统阻塞式系统调用执行,并立刻完成共享完成回调
 * (complete_shared)。发起者的视角就是异步的:提交后即可干别的,
 * 需要时再等(条件变量)。
 *
 * 【组件构成】
 * 1) 共享内存中的提交队列(PgAioWorkerSubmissionQueue):环形缓冲区,
 *    存放的是句柄编号(int)。由 AioWorkerSubmissionQueueLock 保护;
 * 2) 控制结构(PgAioWorkerControl):记录 worker 池的状态——当前活跃
 *    worker 集合(workerset,bitmap)、空闲集合(idle_workerset)、
 *    各 worker 的 ProcNumber、以及给 postmaster 的"扩容请求"标志
 *    (grow / grow_signal_sent)。worker 集合的操作全部经
 *    pgaio_workerset_* 系列位图辅助函数;
 * 3) 与 postmaster 的协作:pgaio_worker_request_grow() 置位并通过
 *    PMSIGNAL_IO_WORKER_GROW 信号请求扩容;postmaster 侧用
 *    pgaio_worker_pm_* 系列读取/清除标志并启动新 worker。
 *
 * 【worker 池的规模自适应】池子会稳定在"能消化近期需求波动"的规模:
 * - 扩容:某 worker 取到 IO 后发现队列还有货、且找不到更高编号的空闲
 *   worker 可唤醒,就以"队列深度 > 当前 worker 数"为判据请求扩容;
 * - 缩容:只有"最高编号"的 worker 有资格超时退出(串行化超时保证
 *   worker ID 无空洞,且不会低于 io_min_workers);退出时唤醒其余
 *   worker,让新的最高编号 worker 接替"可超时"职责;
 * - 唤醒传播:取 IO 的 worker 按"hist_wakeups ≤ hist_ios"启发式(两
 *   个计数器饱和后同时折半,得到指数衰减的"唤醒:干活"比例)决定
 *   是否唤醒更高编号的伙伴,避免 IO 极快时整条链都在空转(详见
 *   宏与主循环注释)。
 *
 * 【哪些 IO 不能交给 worker】引用进程本地内存的
 * (PGAIO_HF_REFERENCES_LOCAL)、或目标无法在其他进程重开文件的 IO,
 * 由 pgaio_worker_needs_synchronous_execution() 判定为"必须同步",
 * 在提交时直接在发起者进程里执行;提交队列满、或拿不到队列锁时,
 * 剩余 IO 也同步执行(见 pgaio_worker_submit)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/aio/method_worker.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <limits.h>

#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "port/pg_bitutils.h"
#include "postmaster/auxprocess.h"
#include "postmaster/interrupt.h"
#include "storage/aio.h"
#include "storage/aio_internal.h"
#include "storage/aio_subsys.h"
#include "storage/io_worker.h"
#include "storage/ipc.h"
#include "storage/latch.h"
#include "storage/lwlock.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/shmem.h"
#include "tcop/tcopprot.h"
#include "utils/injection_point.h"
#include "utils/memdebug.h"
#include "utils/ps_status.h"
#include "utils/wait_event.h"

/*
 * Saturation for counters used to estimate wakeup:IO ratio.
 *
 * We maintain hist_wakeups for wakeups received and hist_ios for IOs
 * processed by each worker.  When either counter reaches this saturation
 * value, we divide both by two.  The result is an exponentially decaying
 * ratio of wakeups to IOs, with a very short memory.
 *
 * If a worker is itself experiencing useless wakeups, it assumes that
 * higher-numbered workers would experience even more, so it should end the
 * chain.
 */
/* (中文)唤醒计数饱和阈值:每个 worker 维护 hist_wakeups(被唤醒次数)
 * 与 hist_ios(实际处理的 IO 数),任一计数到达该值时两者同时除以 2。
 * 效果是"唤醒:干活"比例呈指数衰减、只带很短记忆。判定规则:只有当
 * 自己"没怎么被白唤醒"(hist_wakeups ≤ hist_ios)时,才认为唤醒更高
 * 编号的伙伴有意义,从而把唤醒传播链终止在"浪费起点"之前。 */
#define PGAIO_WORKER_WAKEUP_RATIO_SATURATE 4

/* Debugging support: show current IO and wakeups:ios statistics in ps. */
/* (中文)调试开关(默认关闭):打开后,worker 会在 ps 显示当前处理的
 * IO 描述、或空闲时的"wakeups:ios"统计,便于观察池的行为。 */
/* #define PGAIO_WORKER_SHOW_PS_INFO */

/* (中文)提交队列(共享内存,由 AioWorkerSubmissionQueueLock 保护):
 * 大小取 2 的幂(可用位掩码做环形取模);head 指向下一个写入位置,
 * tail 指向下一个读出位置;sqes[] 存的是"句柄编号"
 * (pgaio_io_get_id 的返回值,整数,而非指针——共享内存里不能放
 * 进程本地指针)。队列满 = (head+1) & mask == tail,留一格哨兵。 */
typedef struct PgAioWorkerSubmissionQueue
{
	uint32		size;
	uint32		head;
	uint32		tail;
	int			sqes[FLEXIBLE_ARRAY_MEMBER];
} PgAioWorkerSubmissionQueue;

/* (中文)worker 槽位:记录该 worker ID 对应的进程号(ProcNumber);
 * 进程退出时置回 INVALID_PROC_NUMBER(见 pgaio_worker_die)。 */
typedef struct PgAioWorkerSlot
{
	ProcNumber	proc_number;
} PgAioWorkerSlot;

/*
 * Sets of worker IDs are held in a simple bitmap, accessed through functions
 * that provide a more readable abstraction.  If we wanted to support more
 * workers than that, the contention on the single queue would surely get too
 * high, so we might want to consider multiple pools instead of widening this.
 */
/* (中文)worker 集合:一个 64 位位图,第 N 位代表"worker ID = N 的
 * worker 在集合中"。用位图配合 pgaio_workerset_* 函数,让集合运算
 * (求最低/最高成员、差集、插入、删除)可读且极快。注释提醒:若未来
 * 需要更多 worker,单一提交队列的锁竞争会先成为瓶颈,应考虑多池
 * 而非加宽位图。 */
typedef uint64 PgAioWorkerSet;

/* (中文)位图位数(64),与 MAX_IO_WORKERS 的关系由下方 static_assert
 * 保证位图能容纳全部可能的 worker ID。 */
#define PGAIO_WORKERSET_BITS (sizeof(PgAioWorkerSet) * CHAR_BIT)

static_assert(PGAIO_WORKERSET_BITS >= MAX_IO_WORKERS, "too small");

/* (中文)worker 池控制结构(共享内存)。字段的锁保护划分:
 * - grow / grow_signal_sent : postmaster 可见。grow 表示"需要扩容",
 *   grow_signal_sent 表示"扩容信号已发"(避免重复发信号,由
 *   postmaster 在响应后清除);
 * - idle_workerset : 空闲 worker 集合,受 AioWorkerSubmissionQueueLock
 *   保护(空闲标记与取 IO 必须在同一把锁下原子完成,否则可能唤醒
 *   已忙的 worker);
 * - workerset / nworkers : 全部活跃 worker 集合与个数,受
 *   AioWorkerControlLock 保护(池的进出都要改这两者);
 * - workers[] : 每 ID 一个槽,记录其 ProcNumber,同样受
 *   AioWorkerControlLock 保护。 */
typedef struct PgAioWorkerControl
{
	/* Seen by postmaster */
	bool		grow;
	bool		grow_signal_sent;

	/* Protected by AioWorkerSubmissionQueueLock. */
	PgAioWorkerSet idle_workerset;

	/* Protected by AioWorkerControlLock. */
	PgAioWorkerSet workerset;
	int			nworkers;

	/* Protected by AioWorkerControlLock. */
	PgAioWorkerSlot workers[FLEXIBLE_ARRAY_MEMBER];
} PgAioWorkerControl;


static void pgaio_worker_shmem_request(void *arg);
static void pgaio_worker_shmem_init(void *arg);

static bool pgaio_worker_needs_synchronous_execution(PgAioHandle *ioh);
static int	pgaio_worker_submit(uint16 num_staged_ios, PgAioHandle **staged_ios);


/* (中文)worker 方法的 IoMethodOps 定义:
 * - 共享内存回调:request/init 申报并初始化提交队列与控制结构;
 *   其余回调(init_backend / wait_one / check_one)缺省——worker 模式
 *   的"等待"由上层直接用条件变量完成,不需要方法干预(因为完成
 *   处理由 worker 在别的进程做,发起者无需亲手推进);
 * - needs_synchronous_execution / submit:见各函数注释。 */
const IoMethodOps pgaio_worker_ops = {
	.shmem_callbacks.request_fn = pgaio_worker_shmem_request,
	.shmem_callbacks.init_fn = pgaio_worker_shmem_init,

	.needs_synchronous_execution = pgaio_worker_needs_synchronous_execution,
	.submit = pgaio_worker_submit,
};


/* GUCs */
/* (中文)worker 池规模的 GUC:
 * - io_min_workers      : 池的目标下限(低于它的 worker 永不超时退出);
 * - io_max_workers      : 池的上限(postmaster 不会启动超过这个数的
 *   worker,扩容请求在到达该数后会被 pgaio_worker_request_grow 抑制);
 * - io_worker_idle_timeout : 最高编号 worker 空闲多久后退出(毫秒;
 *   -1 = 永不超时);
 * - io_worker_launch_interval : postmaster 两次扩容动作之间至少间隔
 *   多久(毫秒),避免波动时频繁启停 worker。 */
int			io_min_workers = 2;
int			io_max_workers = 8;
int			io_worker_idle_timeout = 60000;
int			io_worker_launch_interval = 100;


/* (中文)worker 方法内部状态:
 * - io_worker_queue_size       : 提交队列的"逻辑大小"配置(实际按 2 的
 *   幂向上取整),当前硬编码 64;
 * - MyIoWorkerId               : 本进程若为 IO worker,它的 worker ID;
 *   普通后端保持 -1;
 * - io_worker_submission_queue : 共享内存提交队列指针;
 * - io_worker_control          : 共享内存 worker 池控制结构指针。 */
static int	io_worker_queue_size = 64;
static int	MyIoWorkerId = -1;
static PgAioWorkerSubmissionQueue *io_worker_submission_queue;
static PgAioWorkerControl *io_worker_control;


/*
 * pgaio_workerset_initialize - (中文)把集合清空
 *
 * 【作用】集合初始化为空集(全 0)。
 * 【参数】set —— 目标集合。
 * 【返回值】无。
 */
static void
pgaio_workerset_initialize(PgAioWorkerSet *set)
{
	*set = 0;
}

/*
 * pgaio_workerset_is_empty - (中文)集合是否为空
 *
 * 【作用】集合为空即全 0。
 * 【参数】set —— 待检查集合。
 * 【返回值】true = 空集。
 */
static bool
pgaio_workerset_is_empty(PgAioWorkerSet *set)
{
	return *set == 0;
}

/*
 * pgaio_workerset_singleton - (中文)生成"只含单个 worker"的集合
 *
 * 【作用】返回只含 worker 号对应位的位图(1 << worker)。worker 号
 * 必须在 [0, MAX_IO_WORKERS) 内(Assert)。
 * 【参数】worker —— worker ID。
 * 【返回值】单元素集合。
 */
static PgAioWorkerSet
pgaio_workerset_singleton(int worker)
{
	Assert(worker >= 0 && worker < MAX_IO_WORKERS);
	return UINT64_C(1) << worker;
}

/*
 * pgaio_workerset_all - (中文)把集合填满(所有合法 worker ID 全置位)
 *
 * 【作用】*set = 低 MAX_IO_WORKERS 位全 1。用于"找出未被占用的
 * worker ID"(先填满、再减去已占用者)。
 * 【参数】set —— 目标集合。
 * 【返回值】无。
 */
static void
pgaio_workerset_all(PgAioWorkerSet *set)
{
	*set = UINT64_MAX >> (PGAIO_WORKERSET_BITS - MAX_IO_WORKERS);
}

/*
 * pgaio_workerset_subtract - (中文)集合差集:set1 -= set2
 *
 * 【作用】把 set2 中的成员从 set1 中剔除(位与非)。
 * 【参数】set1 —— 被减集合(原地更新);set2 —— 减数集合。
 * 【返回值】无。
 */
static void
pgaio_workerset_subtract(PgAioWorkerSet *set1, const PgAioWorkerSet *set2)
{
	*set1 &= ~*set2;
}

/*
 * pgaio_workerset_insert - (中文)把某 worker 加入集合
 *
 * 【作用】置位对应位(幂等,重复插入无害)。
 * 【参数】set —— 目标集合;worker —— worker ID(范围有 Assert)。
 * 【返回值】无。
 */
static void
pgaio_workerset_insert(PgAioWorkerSet *set, int worker)
{
	Assert(worker >= 0 && worker < MAX_IO_WORKERS);
	*set |= pgaio_workerset_singleton(worker);
}

/*
 * pgaio_workerset_remove - (中文)把某 worker 从集合中剔除
 *
 * 【作用】清零对应位(幂等)。
 * 【参数】set —— 目标集合;worker —— worker ID(范围有 Assert)。
 * 【返回值】无。
 */
static void
pgaio_workerset_remove(PgAioWorkerSet *set, int worker)
{
	Assert(worker >= 0 && worker < MAX_IO_WORKERS);
	*set &= ~pgaio_workerset_singleton(worker);
}

/*
 * pgaio_workerset_remove_lte - (中文)剔除所有"编号 ≤ 给定值"的成员
 *
 * 【作用】保留编号 > worker 的成员(把低位清零)。用于"只考虑比我
 * 编号更高的 worker"的场景(pgaio_worker_choose_idle)。
 * 【参数】set —— 目标集合;worker —— 下限值(其本身也被剔除)。
 * 【返回值】无。
 */
static void
pgaio_workerset_remove_lte(PgAioWorkerSet *set, int worker)
{
	Assert(worker >= 0 && worker < MAX_IO_WORKERS);
	*set &= (~(PgAioWorkerSet) 0) << (worker + 1);
}

/*
 * pgaio_workerset_get_highest - (中文)返回集合中编号最高的 worker
 *
 * 【作用】用 pg_leftmost_one_pos64 找最高置位(编号最大的 worker)。
 * 用于"判断我是不是当前池里最高编号的 worker"(唯一有超时资格者)。
 * 【参数】set —— 非空集合(Assert)。
 * 【返回值】最高 worker ID。
 */
static int
pgaio_workerset_get_highest(PgAioWorkerSet *set)
{
	Assert(!pgaio_workerset_is_empty(set));
	return pg_leftmost_one_pos64(*set);
}

/*
 * pgaio_workerset_get_lowest - (中文)返回集合中编号最低的 worker
 *
 * 【作用】pg_rightmost_one_pos64 找最低置位。用于"挑最小编号的空闲
 * worker"等场景(见 pgaio_worker_choose_idle)。
 * 【参数】set —— 非空集合(Assert)。
 * 【返回值】最低 worker ID。
 */
static int
pgaio_workerset_get_lowest(PgAioWorkerSet *set)
{
	Assert(!pgaio_workerset_is_empty(set));
	return pg_rightmost_one_pos64(*set);
}

/*
 * pgaio_workerset_pop_lowest - (中文)取出并移除编号最低的成员
 *
 * 【作用】get_lowest + remove 的组合:返回最低成员并从集合中删除。
 * 用于遍历集合时逐个弹出(如 pgaio_workerset_wake)。
 * 【参数】set —— 非空集合(原地更新)。
 * 【返回值】被弹出的 worker ID。
 */
static int
pgaio_workerset_pop_lowest(PgAioWorkerSet *set)
{
	int			worker = pgaio_workerset_get_lowest(set);

	pgaio_workerset_remove(set, worker);
	return worker;
}

#ifdef USE_ASSERT_CHECKING
/*
 * pgaio_workerset_contains - (中文)(仅断言构建)集合是否含某 worker
 *
 * 【作用】检查某位的状态,供各处 Assert 使用。
 * 【参数】set —— 待检查集合;worker —— worker ID。
 * 【返回值】true = 在集合中。
 */
static bool
pgaio_workerset_contains(PgAioWorkerSet *set, int worker)
{
	Assert(worker >= 0 && worker < MAX_IO_WORKERS);
	return (*set & pgaio_workerset_singleton(worker)) != 0;
}

/*
 * pgaio_workerset_count - (中文)(仅断言构建)集合的元素个数
 *
 * 【作用】统计置位个数,用于校验 workerset 与 nworkers 的一致性
 * (多处 Assert 使用)。
 * 【参数】set —— 待统计集合。
 * 【返回值】成员数。
 */
static int
pgaio_workerset_count(PgAioWorkerSet *set)
{
	return pg_popcount64(*set);
}
#endif

/*
 * pgaio_worker_shmem_request - (中文)request 阶段:申报提交队列与控制结构
 *
 * 【作用】postmaster 启动早期调用,向共享内存子系统申报两块内存:
 * 1. 提交队列:环形缓冲,容量 = 按 2 的幂向上取整的 io_worker_queue_size
 *    (取 2 的幂是为了用位掩码快速取模);元素是 int(句柄编号);
 * 2. 控制结构:PgAioWorkerControl,固定 MAX_IO_WORKERS 个槽位。
 * 指针写入静态全局,init 阶段直接使用。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
pgaio_worker_shmem_request(void *arg)
{
	size_t		size;
	int			queue_size;

	/* Round size up to next power of two so we can make a mask. */
	queue_size = pg_nextpower2_32(io_worker_queue_size);

	size = offsetof(PgAioWorkerSubmissionQueue, sqes) + sizeof(int) * queue_size;
	ShmemRequestStruct(.name = "AioWorkerSubmissionQueue",
					   .size = size,
					   .ptr = (void **) &io_worker_submission_queue,
		);

	size = offsetof(PgAioWorkerControl, workers) + sizeof(PgAioWorkerSlot) * MAX_IO_WORKERS;
	ShmemRequestStruct(.name = "AioWorkerControl",
					   .size = size,
					   .ptr = (void **) &io_worker_control,
		);
}

/*
 * pgaio_worker_shmem_init - (中文)init 阶段:初始化提交队列与控制结构
 *
 * 【作用】共享内存分配完成后(postmaster)调用:队列置空(头尾都指向
 * 0、记录实际容量);控制结构清零:无扩容请求、worker 集合与空闲集合
 * 为空、所有槽位的进程号置 INVALID_PROC_NUMBER。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
pgaio_worker_shmem_init(void *arg)
{
	int			queue_size;

	/* Round size up like in pgaio_worker_shmem_request() */
	queue_size = pg_nextpower2_32(io_worker_queue_size);

	io_worker_submission_queue->size = queue_size;
	io_worker_submission_queue->head = 0;
	io_worker_submission_queue->tail = 0;
	io_worker_control->grow = false;
	pgaio_workerset_initialize(&io_worker_control->workerset);
	pgaio_workerset_initialize(&io_worker_control->idle_workerset);

	for (int i = 0; i < MAX_IO_WORKERS; ++i)
		io_worker_control->workers[i].proc_number = INVALID_PROC_NUMBER;
}

/*
 * Tell postmaster that we think a new worker is needed.
 */
/*
 * pgaio_worker_request_grow - (中文)向 postmaster 请求启动一个新 worker
 *
 * 【作用】worker(或提交路径)发现队列积压、需要更多人手时调用。三步
 * 去重:
 * 1. 已达 io_max_workers 上限 → 直接放弃(无锁读 nworkers,对这种
 *    启发式用途足够);
 * 2. 已有人在请求(grow 已置位)→ 放弃;
 * 3. 置位 grow,内存屏障,再查 grow_signal_sent:信号已发过(还没被
 *    postmaster 消费)→ 不重复发;否则置位并发 PMSIGNAL_IO_WORKER_GROW。
 *
 * 【设计思想】grow 与 grow_signal_sent 分离的原因:postmaster 对扩容
 * 请求应用 io_worker_launch_interval 的最小间隔(连被取消的请求也
 * 计数),反复置位/清除时重复发信号毫无意义。内存屏障保证置位对
 * postmaster 可见,且信号发送在置位之后。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
pgaio_worker_request_grow(void)
{
	/*
	 * Suppress useless signaling if we already know that we're at the
	 * maximum.  This uses an unlocked read of nworkers, but that's OK for
	 * this heuristic purpose.
	 */
	if (io_worker_control->nworkers >= io_max_workers)
		return;

	/* Already requested? */
	if (io_worker_control->grow)
		return;

	io_worker_control->grow = true;
	pg_memory_barrier();

	/*
	 * If the postmaster has already been signaled, don't do it again until
	 * the postmaster clears this flag.  There is no point in repeated signals
	 * if grow is being set and cleared repeatedly while the postmaster is
	 * waiting for io_worker_launch_interval, which it applies even to
	 * canceled requests.
	 */
	if (io_worker_control->grow_signal_sent)
		return;

	io_worker_control->grow_signal_sent = true;
	pg_memory_barrier();
	SendPostmasterSignal(PMSIGNAL_IO_WORKER_GROW);
}

/*
 * Cancel any request for a new worker, after observing an empty queue.
 */
/*
 * pgaio_worker_cancel_grow - (中文)取消扩容请求(观察到队列已空时)
 *
 * 【作用】空闲 worker 看到队列为空时调用:若此前有 worker 请求过
 * 扩容,清除 grow 标志。postmaster 在检查 grow 后就不会启动新
 * worker(已经发出的信号则靠 pgaio_worker_pm_test_grow 的复查来
 * 拦截)。
 *
 * 【设计思想】无锁写 + 内存屏障:只有"事实上的最后一个读者"在清,
 * 其他 worker 的并发写/读对此启发式可容忍;屏障保证清除对
 * postmaster 立即可见。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
pgaio_worker_cancel_grow(void)
{
	if (!io_worker_control->grow)
		return;

	io_worker_control->grow = false;
	pg_memory_barrier();
}

/*
 * pgaio_worker_pm_test_grow_signal_sent - (中文)(postmaster 侧)是否发出过扩容信号
 *
 * 【作用】postmaster 的 IO worker 启动循环调用:检查是否有扩容请求
 * 曾发出信号(可能已被取消)。屏障保证看到最新值;io_worker_control
 * 为 NULL(方法未启用)时返回 false。
 *
 * 【参数】无。
 * 【返回值】true = 有未消费的扩容信号。
 */
bool
pgaio_worker_pm_test_grow_signal_sent(void)
{
	pg_memory_barrier();
	return io_worker_control && io_worker_control->grow_signal_sent;
}

/*
 * pgaio_worker_pm_test_grow - (中文)(postmaster 侧)扩容请求是否仍有效
 *
 * 【作用】postmaster 在真正启动 worker 前复查:请求是否仍有效(发出
 * 信号后未被取消)。若已取消,则不再启动,实现"请求-取消"的最终
 * 仲裁。屏障保证可见性。
 *
 * 【参数】无。
 * 【返回值】true = 应启动新 worker。
 */
bool
pgaio_worker_pm_test_grow(void)
{
	pg_memory_barrier();
	return io_worker_control && io_worker_control->grow;
}

/*
 * pgaio_worker_pm_clear_grow_signal_sent - (中文)(postmaster 侧)消费扩容请求
 *
 * 【作用】postmaster 响应完扩容请求后调用:同时清除 grow 与
 * grow_signal_sent,允许未来再次发出请求(否则 grow 一旦置位会被
 * request_grow 的"已请求?"检查永久挡住)。屏障保证消费对 worker
 * 可见。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
pgaio_worker_pm_clear_grow_signal_sent(void)
{
	if (!io_worker_control)
		return;

	io_worker_control->grow = false;
	io_worker_control->grow_signal_sent = false;
	pg_memory_barrier();
}

/*
 * pgaio_worker_choose_idle - (中文)挑一个空闲 worker 并标记为忙
 *
 * 【作用】在持 AioWorkerSubmissionQueueLock 的前提下,从 idle_workerset
 * 中挑选空闲 worker;可选参数只考虑"编号 > only_workers_above"的
 * (唤醒传播只向高编号传播)。挑中后立即从空闲集合移除(标记为忙),
 * 返回其 ID;无可挑者返回 -1。
 *
 * 【设计思想】挑"最小编号"的空闲 worker,让高编号 worker 更可能
 * 保持空闲(它们才是可超时退出的候选),池子趋向"低编号干活、高
 * 编号随时可缩容"。必须持队列锁:空闲集合的读写与取 IO 在同一个
 * 临界区,避免并发误判。
 *
 * 【参数】only_workers_above —— 只考虑编号严格大于该值的空闲 worker;
 *        -1 表示不限。
 * 【返回值】被选中的 worker ID;无空闲(或满足条件的)时 -1。
 */
static int
pgaio_worker_choose_idle(int only_workers_above)
{
	PgAioWorkerSet workerset;
	int			worker;

	Assert(LWLockHeldByMeInMode(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE));

	workerset = io_worker_control->idle_workerset;
	if (only_workers_above >= 0)
		pgaio_workerset_remove_lte(&workerset, only_workers_above);
	if (pgaio_workerset_is_empty(&workerset))
		return -1;

	/* Find the lowest numbered idle worker and mark it not idle. */
	worker = pgaio_workerset_get_lowest(&workerset);
	pgaio_workerset_remove(&io_worker_control->idle_workerset, worker);

	return worker;
}

/*
 * Try to wake a worker by setting its latch, to tell it there are IOs to
 * process in the submission queue.
 */
/*
 * pgaio_worker_wake - (中文)通过设置 latch 唤醒一个 worker
 *
 * 【作用】给指定 worker ID 对应的进程 SetLatch,通知它提交队列里有活
 * 可干。若该 worker 正在并发退出(槽位进程号已是 INVALID),唤醒会
 * 静默失败——这不丢任务:退出中的 worker 会唤醒所有剩余 worker
 * (见 pgaio_worker_die),总有人看到排队的 IO;若一个 worker 都没
 * 有,postmaster 的扩容机制会兜底启动新 worker。
 *
 * 【参数】worker —— 要唤醒的 worker ID。
 * 【返回值】无。
 */
static void
pgaio_worker_wake(int worker)
{
	ProcNumber	proc_number;

	/*
	 * If the selected worker is concurrently exiting, then pgaio_worker_die()
	 * had not yet removed it as of when we saw it in idle_workerset.  That's
	 * OK, because it will wake all remaining workers to close wakeup-vs-exit
	 * races: *someone* will see the queued IO.  If there are no workers
	 * running, the postmaster will start a new one.
	 */
	proc_number = io_worker_control->workers[worker].proc_number;
	if (proc_number != INVALID_PROC_NUMBER)
		SetLatch(&GetPGProcByNumber(proc_number)->procLatch);
}

/*
 * Try to wake a set of workers.  Used on pool change, to close races
 * described in the callers.
 */
/*
 * pgaio_workerset_wake - (中文)唤醒集合中的全部 worker
 *
 * 【作用】逐个弹出集合成员并 SetLatch。用于"池规模变化"时向受影响
 * 的 worker 广播:它们需要重新评估自己的职责(例如最高的 worker
 * 换了人,新最高者要知道自己现在可超时;或有人退出后要确认队列
 * 里没有漏看的 IO)。这些场景中的竞态说明见调用方注释。
 *
 * 【参数】workerset —— 要唤醒的 worker 集合(按值传递,可原地弹出)。
 * 【返回值】无。
 */
static void
pgaio_workerset_wake(PgAioWorkerSet workerset)
{
	while (!pgaio_workerset_is_empty(&workerset))
		pgaio_worker_wake(pgaio_workerset_pop_lowest(&workerset));
}

/*
 * pgaio_worker_submission_queue_insert - (中文)向提交队列写入一个 IO
 *
 * 【作用】把句柄编号(非指针)写入环形队列的 head 位置。调用者必须
 * 已持有 AioWorkerSubmissionQueueLock(Assert)。队列满(写入后 head
 * 会追上 tail)时返回 false 且不写入——留一个空槽作"满/空"判据。
 *
 * 【参数】ioh —— 要入队的句柄。
 * 【返回值】true = 入队成功;false = 队列满。
 */
static bool
pgaio_worker_submission_queue_insert(PgAioHandle *ioh)
{
	PgAioWorkerSubmissionQueue *queue;
	uint32		new_head;

	Assert(LWLockHeldByMeInMode(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE));

	queue = io_worker_submission_queue;
	new_head = (queue->head + 1) & (queue->size - 1);
	if (new_head == queue->tail)
	{
		pgaio_debug(DEBUG3, "io queue is full, at %u elements",
					io_worker_submission_queue->size);
		return false;			/* full */
	}

	queue->sqes[queue->head] = pgaio_io_get_id(ioh);
	queue->head = new_head;

	return true;
}

/*
 * pgaio_worker_submission_queue_consume - (中文)从提交队列取一个 IO
 *
 * 【作用】worker 取任务:读 tail 处的句柄编号并推进 tail。调用者必须
 * 已持有 AioWorkerSubmissionQueueLock(Assert)。队列空(head == tail)
 * 返回 -1。
 *
 * 【参数】无。
 * 【返回值】句柄编号(≥ 0);队列空时 -1。
 */
static int
pgaio_worker_submission_queue_consume(void)
{
	PgAioWorkerSubmissionQueue *queue;
	int			result;

	Assert(LWLockHeldByMeInMode(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE));

	queue = io_worker_submission_queue;
	if (queue->tail == queue->head)
		return -1;				/* empty */

	result = queue->sqes[queue->tail];
	queue->tail = (queue->tail + 1) & (queue->size - 1);

	return result;
}

/*
 * pgaio_worker_submission_queue_depth - (中文)当前队列深度(元素个数)
 *
 * 【作用】计算 head - tail(必要时给 head 加一个队列长度再减,处理
 * 回绕)。调用者必须已持有 AioWorkerSubmissionQueueLock(Assert)。
 * 供扩容判据(队列深度 vs worker 数)与唤醒传播决策使用。
 *
 * 【参数】无。
 * 【返回值】队列中等待处理的 IO 个数。
 */
static uint32
pgaio_worker_submission_queue_depth(void)
{
	uint32		head;
	uint32		tail;

	Assert(LWLockHeldByMeInMode(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE));

	head = io_worker_submission_queue->head;
	tail = io_worker_submission_queue->tail;

	if (tail > head)
		head += io_worker_submission_queue->size;

	Assert(head >= tail);

	return head - tail;
}

/*
 * pgaio_worker_needs_synchronous_execution - (中文)判定 IO 是否必须在发起者进程同步执行
 *
 * 【作用】worker 方法对"无法交给 worker"的 IO 的判据,三种情况任一
 * 为真即同步:
 * 1. !IsUnderPostmaster:postmaster/单进程模式下没有 worker 可派;
 * 2. PGAIO_HF_REFERENCES_LOCAL:IO 引用进程本地内存(如本地/临时
 *    缓冲区的页),别的进程无法访问;
 * 3. !pgaio_io_can_reopen:目标不支持在其他进程重开文件(worker 没有
 *    发起者的 fd)。
 * 命中者由 pgaio_io_stage 走同步执行路径;pgaio_worker_submit 里也
 * 有 Assert 复核(入队的 IO 必然不满足本判定)。
 *
 * 【参数】ioh —— STAGED 状态的句柄。
 * 【返回值】true = 必须同步执行。
 */
static bool
pgaio_worker_needs_synchronous_execution(PgAioHandle *ioh)
{
	return
		!IsUnderPostmaster
		|| ioh->flags & PGAIO_HF_REFERENCES_LOCAL
		|| !pgaio_io_can_reopen(ioh);
}

/*
 * pgaio_worker_submit - (中文)批量提交:尽可能入队,余下同步执行
 *
 * 【作用】IoMethodOps->submit 实现。流程:
 * 1. 先把所有句柄 prepare_submit(状态 → SUBMITTED,挂 in-flight);
 * 2. 尝试"条件获取"队列锁(LWLockConditionalAcquire,拿不到就放弃
 *    排队——绝不为排队而阻塞调用者):
 *    - 拿到:逐个入队(Assert 复核不需要同步执行);一旦队列满,放弃
 *      剩余 IO 改同步(持锁时没人能消费,等下去无意义);入队完成后
 *      挑一个空闲 worker 唤醒(它会按需传播唤醒);
 *    - 拿不到锁:全部改同步执行(无需唤醒);
 * 3. 同步执行剩余部分(pgaio_io_perform_synchronously,在临界区内
 *    执行并完成)。
 *
 * 【设计思想】"条件拿锁 + 队列满就同步"保证了本函数绝不阻塞:它在
 * 临界区内被调用(pgaio_submit_staged),任何阻塞/等待都可能死锁。
 * 同步执行的部分仍走标准完成路径,上层无感知。
 *
 * 【参数】num_staged_ios —— 本批 IO 个数;staged_ios —— 句柄数组。
 * 【返回值】接收的 IO 个数(恒等于 num_staged_ios;未入队的已同步
 * 完成,也算"已处理")。
 */
static int
pgaio_worker_submit(uint16 num_staged_ios, PgAioHandle **staged_ios)
{
	PgAioHandle **synchronous_ios = NULL;
	int			nsync = 0;
	int			worker = -1;

	Assert(num_staged_ios <= PGAIO_SUBMIT_BATCH_SIZE);

	for (int i = 0; i < num_staged_ios; i++)
		pgaio_io_prepare_submit(staged_ios[i]);

	if (LWLockConditionalAcquire(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE))
	{
		for (int i = 0; i < num_staged_ios; ++i)
		{
			Assert(!pgaio_worker_needs_synchronous_execution(staged_ios[i]));
			if (!pgaio_worker_submission_queue_insert(staged_ios[i]))
			{
				/*
				 * Do the rest synchronously. If the queue is full, give up
				 * and do the rest synchronously. We're holding an exclusive
				 * lock on the queue so nothing can consume entries.
				 */
				synchronous_ios = &staged_ios[i];
				nsync = (num_staged_ios - i);

				break;
			}
		}
		/* Choose one worker to wake for this batch. */
		worker = pgaio_worker_choose_idle(-1);
		LWLockRelease(AioWorkerSubmissionQueueLock);

		/* Wake up chosen worker.  It will wake peers if necessary. */
		if (worker != -1)
			pgaio_worker_wake(worker);
	}
	else
	{
		/* do everything synchronously, no wakeup needed */
		synchronous_ios = staged_ios;
		nsync = num_staged_ios;
	}

	/* Run whatever is left synchronously. */
	if (nsync > 0)
	{
		for (int i = 0; i < nsync; ++i)
		{
			pgaio_io_perform_synchronously(synchronous_ios[i]);
		}
	}

	return num_staged_ios;
}

/*
 * on_shmem_exit() callback that releases the worker's slot in
 * io_worker_control.
 */
/*
 * pgaio_worker_die - (中文)worker 退出回调:注销自己的池内登记
 *
 * 【作用】worker 进程退出(on_shmem_exit 回调)时执行:
 * 1. 队列锁下从空闲集合移除自己;
 * 2. 控制锁下:清空自己的槽位进程号、从活跃集合移除、nworkers--,
 *    并用断言校验集合计数一致性;取出"剩余 worker 集合";
 * 3. 唤醒所有剩余 worker——池子变了:新的最高编号 worker 要接管
 *    "可超时"职责;同时这也关闭了 pgaio_worker_wake 注释里描述的
 *    "唤醒丢失"竞态(即将退出的 worker 曾出现在空闲集合里,唤醒
 *    可能落空,而它的退出广播能保证"总有人看到排队的 IO")。
 *
 * 【参数】code —— 退出码;arg —— 未使用。
 * 【返回值】无。
 */
static void
pgaio_worker_die(int code, Datum arg)
{
	PgAioWorkerSet notify_set;

	LWLockAcquire(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE);
	pgaio_workerset_remove(&io_worker_control->idle_workerset, MyIoWorkerId);
	LWLockRelease(AioWorkerSubmissionQueueLock);

	LWLockAcquire(AioWorkerControlLock, LW_EXCLUSIVE);
	Assert(io_worker_control->workers[MyIoWorkerId].proc_number == MyProcNumber);
	io_worker_control->workers[MyIoWorkerId].proc_number = INVALID_PROC_NUMBER;
	Assert(pgaio_workerset_contains(&io_worker_control->workerset, MyIoWorkerId));
	pgaio_workerset_remove(&io_worker_control->workerset, MyIoWorkerId);
	notify_set = io_worker_control->workerset;
	Assert(io_worker_control->nworkers > 0);
	io_worker_control->nworkers--;
	Assert(pgaio_workerset_count(&io_worker_control->workerset) ==
		   io_worker_control->nworkers);
	LWLockRelease(AioWorkerControlLock);

	/*
	 * Notify other workers on pool change.  This allows the new highest
	 * worker to know that it is now the one that can time out, and closes a
	 * wakeup-loss race described in pgaio_worker_wake().
	 */
	pgaio_workerset_wake(notify_set);
}

/*
 * Register the worker in shared memory, assign MyIoWorkerId and register a
 * shutdown callback to release registration.
 */
/*
 * pgaio_worker_register - (中文)worker 启动时登记进池子
 *
 * 【作用】worker 进程主循环开始前调用:在控制锁下——
 * 1. 用"全集 - 已占用集合"求出空闲 ID 位图,取最小编号作为自己的
 *    MyIoWorkerId(无空闲 ID 则报错);
 * 2. 把 MyProcNumber 写入自己的槽位,插入活跃集合,nworkers++(附
 *    一致性断言);
 * 3. 唤醒"老的活跃集合"成员:池子变了,尤其是若自己是新的最高编号
 *    worker,老最高者需要知道它已失去超时资格;
 * 4. 登记 on_shmem_exit(pgaio_worker_die) 保证退出时注销。
 *
 * 【参数】无。
 * 【返回值】无(MyIoWorkerId 成为有效 ID)。
 */
static void
pgaio_worker_register(void)
{
	PgAioWorkerSet free_workerset;
	PgAioWorkerSet old_workerset;

	MyIoWorkerId = -1;

	LWLockAcquire(AioWorkerControlLock, LW_EXCLUSIVE);
	/* Find lowest unused worker ID. */
	pgaio_workerset_all(&free_workerset);
	pgaio_workerset_subtract(&free_workerset, &io_worker_control->workerset);
	if (!pgaio_workerset_is_empty(&free_workerset))
		MyIoWorkerId = pgaio_workerset_get_lowest(&free_workerset);
	if (MyIoWorkerId == -1)
		elog(ERROR, "couldn't find a free worker ID");

	Assert(io_worker_control->workers[MyIoWorkerId].proc_number ==
		   INVALID_PROC_NUMBER);
	io_worker_control->workers[MyIoWorkerId].proc_number = MyProcNumber;

	old_workerset = io_worker_control->workerset;
	Assert(!pgaio_workerset_contains(&old_workerset, MyIoWorkerId));
	pgaio_workerset_insert(&io_worker_control->workerset, MyIoWorkerId);
	io_worker_control->nworkers++;
	Assert(io_worker_control->nworkers <= MAX_IO_WORKERS);
	Assert(pgaio_workerset_count(&io_worker_control->workerset) ==
		   io_worker_control->nworkers);
	LWLockRelease(AioWorkerControlLock);

	/*
	 * Notify other workers on pool change.  If we were the highest worker,
	 * this allows the new highest worker to know that it can time out.
	 */
	pgaio_workerset_wake(old_workerset);

	on_shmem_exit(pgaio_worker_die, 0);
}

/*
 * pgaio_worker_error_callback - (中文)worker 执行 IO 出错时的错误上下文回调
 *
 * 【作用】注册为错误上下文回调:worker 处理 IO 的过程中若抛错(如
 * reopen 失败等),给错误消息附加"I/O worker 正代表进程 X 执行 I/O"
 * 的说明(即被服务的是哪个发起者),便于定位。
 *
 * 【设计思想】只在确实"替别人干活"时才有意义(Assert:句柄所有者
 * 不是本 worker,且本进程确实是 B_IO_WORKER)。arg 由主循环逐个 IO
 * 更新。
 *
 * 【参数】arg —— 当前处理的句柄(可能为 NULL)。
 * 【返回值】无。
 */
static void
pgaio_worker_error_callback(void *arg)
{
	ProcNumber	owner;
	PGPROC	   *owner_proc;
	int32		owner_pid;
	PgAioHandle *ioh = arg;

	if (!ioh)
		return;

	Assert(ioh->owner_procno != MyProcNumber);
	Assert(MyBackendType == B_IO_WORKER);

	owner = ioh->owner_procno;
	owner_proc = GetPGProcByNumber(owner);
	owner_pid = owner_proc->pid;

	errcontext("I/O worker executing I/O on behalf of process %d", owner_pid);
}

/*
 * Check if this backend is allowed to time out, and thus should use a
 * non-infinite sleep time.  Only the highest-numbered worker is allowed to
 * time out, and only if the pool is above io_min_workers.  Serializing
 * timeouts keeps IDs in a range 0..N without gaps, and avoids undershooting
 * io_min_workers.
 *
 * The result is only instantaneously true and may be temporarily inconsistent
 * in different workers around transitions, but all workers are woken up on
 * pool size or GUC changes making the result eventually consistent.
 */
/*
 * pgaio_worker_can_timeout - (中文)本 worker 当前是否有资格超时退出
 *
 * 【作用】两个条件同时满足才算"可超时":
 * 1. MyIoWorkerId ≥ io_min_workers(低于下限的 worker 是池的底子,
 *    永不退出);
 * 2. 自己是当前活跃集合中编号最高的 worker(控制锁下读集合判断)。
 *
 * 【设计思想】把超时权串行化到"唯一的最高编号 worker":否则多个
 * worker 同时超时会留下 ID 空洞(集合 {0,2} 之类),也容易把池子
 * 缩到 io_min_workers 以下。结果只瞬时成立,池子变化后各 worker
 * 可能短暂不一致——但所有池子/GUC 变更都会唤醒全员(见 register/die
 * 与主循环的 ConfigReload 处理),最终趋于一致。
 *
 * 【参数】无。
 * 【返回值】true = 可超时(应使用非无限睡眠)。
 */
static bool
pgaio_worker_can_timeout(void)
{
	PgAioWorkerSet workerset;

	if (MyIoWorkerId < io_min_workers)
		return false;

	/* Serialize against pool size changes. */
	LWLockAcquire(AioWorkerControlLock, LW_SHARED);
	workerset = io_worker_control->workerset;
	LWLockRelease(AioWorkerControlLock);

	if (MyIoWorkerId != pgaio_workerset_get_highest(&workerset))
		return false;

	return true;
}

/*
 * Emit a WARNING if io_min_workers > io_max_workers, since the worker
 * pool will never exceed io_max_workers regardless of the minimum setting.
 */
/*
 * check_io_worker_gucs - (中文)校验 io_min_workers / io_max_workers 关系
 *
 * 【作用】若 io_min_workers > io_max_workers,发 WARNING 提示:池子
 * 永远不会超过 io_max_workers,下限形同虚设。只在 worker 0 里检查
 * (防止每个 worker 各报一遍,刷屏)。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
check_io_worker_gucs(void)
{
	/* Only do the check in one worker, to limit noise */
	if (MyIoWorkerId != 0)
		return;

	if (io_min_workers > io_max_workers)
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("\"%s\" (%d) should be less than or equal to \"%s\" (%d)",
						"io_min_workers", io_min_workers,
						"io_max_workers", io_max_workers),
				 errdetail("The I/O worker pool will not exceed \"%s\" (%d) workers.",
						   "io_max_workers", io_max_workers)));
}

/*
 * IoWorkerMain - (中文)IO worker 进程的主函数(辅助进程入口)
 *
 * 【作用】每个 IO worker 从 postmaster fork 后直接进入本函数,职责
 * 是"从共享提交队列取 IO → 执行 → 完成",循环往复直到被要求退出。
 *
 * 【启动阶段】
 * - AuxiliaryProcessMainCommon() 做辅助进程通用初始化;注册信号处理
 *   (SIGHUP 重载配置、SIGINT 手动触发重启、SIGTERM 忽略(与
 *   checkpointer 一样,关闭走 SIGUSR2)、SIGUSR1 通用 proc 信号、
 *   SIGUSR2 关闭请求);ps 显示 worker 编号;
 * - pgaio_worker_register() 登记进池子;挂错误上下文回调
 *   (pgaio_worker_error_callback);setjmp 建立错误恢复点。
 *
 * 【错误恢复】(setjmp 分支)IO 极少抛错;万一抛了:释放全部 LWLock、
 * 若 error_ioh 非空则把该 IO 标记为失败(pgaio_io_process_completion
 * 传 -errno,让发起者看到失败结果而不是永远等),然后 proc_exit(1)
 * ——postmaster 会启动新 worker 顶上。因此 error_ioh/error_errno
 * 在主循环里"要执行 IO 时"先登记、执行完成后立刻清除。
 *
 * 【主循环】每个周期:
 * 1. 队列锁下取一个 IO:
 *    - 取到:清空闲标记;按"hist_wakeups ≤ hist_ios"启发式决定是否
 *      唤醒更高编号的伙伴(队列还有货且挑得到就唤醒,挑不到则
 *      maybe_grow);
 *    - 没取到:把自己标记为空闲(可被唤醒/挑选),取消 pending 的
 *      扩容请求(队列已空),计算自己的睡眠时限:
 *      * io_worker_idle_timeout = -1 → 无限;
 *      * GUC 变化则重置计时;
 *      * 只有 pgaio_worker_can_timeout() 时才有非无限时限;
 *      然后 WaitLatch(超时/被唤醒/PM 死亡)。超时且已过 idle_timeout
 *      即退出循环;被唤醒则 hist_wakeups++(与 hist_ios 一起按
 *      PGAIO_WORKER_WAKEUP_RATIO_SATURATE 衰减)。
 * 2. (取到 IO 时)执行:HOLD_INTERRUPTS(防止重开 fd 与执行之间 fd
 *    被中断关闭)→ 登记 error_ioh/error_errno(默认为 ENOENT,即
 *    "reopen 失败"的兜底 errno)→ pgaio_io_reopen(在其他进程重开
 *    文件;成功则 error_errno 清零)→ valgrind 下显式解除缓冲区的
 *    NOACCESS 标记 → pgaio_io_perform_synchronously(临界区内阻塞
 *    执行并完成:共享回调在 worker 里跑,发起者由条件变量唤醒)。
 * 3. 锁外处理唤醒传播/扩容(见上);CHECK_FOR_INTERRUPTS;
 *    若 SIGHUP:重载配置,校验 GUC 关系;io_max_workers 调小时,编号
 *    ≥ 新上限的 worker 先退出(break)。
 *
 * 【退出】主循环结束后恢复错误上下文、proc_exit(0);
 * on_shmem_exit 的 pgaio_worker_die 完成注销。
 *
 * 【参数】startup_data / startup_data_len —— 未使用(辅助进程启动
 * 协议保留)。
 * 【返回值】无(进程不再返回)。
 */
void
IoWorkerMain(const void *startup_data, size_t startup_data_len)
{
	sigjmp_buf	local_sigjmp_buf;
	TimestampTz idle_timeout_abs = 0;
	int			timeout_guc_used = 0;
	PgAioHandle *volatile error_ioh = NULL;
	ErrorContextCallback errcallback = {0};
	volatile int error_errno = 0;
	char		cmd[128];
	int			hist_ios = 0;
	int			hist_wakeups = 0;

	AuxiliaryProcessMainCommon();

	pqsignal(SIGHUP, SignalHandlerForConfigReload);
	pqsignal(SIGINT, die);		/* to allow manually triggering worker restart */

	/*
	 * Ignore SIGTERM, will get explicit shutdown via SIGUSR2 later in the
	 * shutdown sequence, similar to checkpointer.
	 */
	pqsignal(SIGTERM, PG_SIG_IGN);
	/* SIGQUIT handler was already set up by InitPostmasterChild */
	pqsignal(SIGALRM, PG_SIG_IGN);
	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, SignalHandlerForShutdownRequest);

	/* also registers a shutdown callback to unregister */
	pgaio_worker_register();

	check_io_worker_gucs();

	sprintf(cmd, "%d", MyIoWorkerId);
	set_ps_display(cmd);

	errcallback.callback = pgaio_worker_error_callback;
	errcallback.previous = error_context_stack;
	error_context_stack = &errcallback;

	/* see PostgresMain() */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		error_context_stack = NULL;
		HOLD_INTERRUPTS();

		EmitErrorReport();

		/*
		 * In the - very unlikely - case that the IO failed in a way that
		 * raises an error we need to mark the IO as failed.
		 *
		 * Need to do just enough error recovery so that we can mark the IO as
		 * failed and then exit (postmaster will start a new worker).
		 */
		LWLockReleaseAll();

		if (error_ioh != NULL)
		{
			/* should never fail without setting error_errno */
			Assert(error_errno != 0);

			errno = error_errno;

			START_CRIT_SECTION();
			pgaio_io_process_completion(error_ioh, -error_errno);
			END_CRIT_SECTION();
		}

		proc_exit(1);
	}

	/* We can now handle ereport(ERROR) */
	PG_exception_stack = &local_sigjmp_buf;

	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	while (!ShutdownRequestPending)
	{
		uint32		io_index;
		int			worker = -1;
		int			queue_depth = 0;
		bool		maybe_grow = false;

		/*
		 * Try to get a job to do.
		 *
		 * The lwlock acquisition also provides the necessary memory barrier
		 * to ensure that we don't see an outdated data in the handle.
		 */
		LWLockAcquire(AioWorkerSubmissionQueueLock, LW_EXCLUSIVE);
		if ((io_index = pgaio_worker_submission_queue_consume()) == -1)
		{
			/* Nothing to do.  Mark self idle. */
			pgaio_workerset_insert(&io_worker_control->idle_workerset,
								   MyIoWorkerId);
		}
		else
		{
			/* Got one.  Clear idle flag. */
			pgaio_workerset_remove(&io_worker_control->idle_workerset,
								   MyIoWorkerId);

			/*
			 * See if we should wake up a higher numbered peer.  Only do that
			 * if this worker is not receiving spurious wakeups itself.  The
			 * intention is create a frontier beyond which idle workers stay
			 * asleep.
			 *
			 * This heuristic tries to discover the useful wakeup propagation
			 * chain length when IOs are very fast and workers wake up to find
			 * that all IOs have already been taken.
			 *
			 * If we chose not to wake a worker when we ideally should have,
			 * then the ratio will soon change to correct that.
			 */
			if (hist_wakeups <= hist_ios)
			{
				queue_depth = pgaio_worker_submission_queue_depth();
				if (queue_depth > 0)
				{
					/* Choose a worker higher than me to wake. */
					worker = pgaio_worker_choose_idle(MyIoWorkerId);
					if (worker == -1)
						maybe_grow = true;
				}
			}
		}
		LWLockRelease(AioWorkerSubmissionQueueLock);

		/* Propagate wakeups. */
		if (worker != -1)
		{
			pgaio_worker_wake(worker);
		}
		else if (maybe_grow)
		{
			/*
			 * We know there was at least one more item in the queue, and we
			 * failed to find a higher-numbered idle worker to wake.  Now we
			 * decide if we should try to start one more worker.
			 *
			 * We do this with a simple heuristic: is the queue depth greater
			 * than the current number of workers?
			 *
			 * Consider the following situations:
			 *
			 * 1. The queue depth is constantly increasing, because IOs are
			 * arriving faster than they can possibly be serviced.  It doesn't
			 * matter much which threshold we choose, as we will surely hit
			 * it.  Crossing the current worker count is a useful signal
			 * because it's clearly too deep to avoid queuing latency already,
			 * but still leaves a small window of opportunity to improve the
			 * situation before the queue overflows.
			 *
			 * 2. The worker pool is keeping up, no latency is being
			 * introduced and an extra worker would be a waste of resources.
			 * Queue depth distributions tend to be heavily skewed, with long
			 * tails of low probability spikes (due to submission clustering,
			 * scheduling, jitter, stalls, noisy neighbors, etc).  We want a
			 * number that is very unlikely to be triggered by an outlier, and
			 * we bet that an exponential or similar distribution whose
			 * outliers never reach this threshold must be almost entirely
			 * concentrated at the low end.  If we do see a spike as big as
			 * the worker count, we take it as a signal that the distribution
			 * is surely too wide.
			 *
			 * On its own, this is an extremely crude signal.  When combined
			 * with the wakeup propagation test that precedes it (but on its
			 * own tends to overshoot) and io_worker_launch_interval, the
			 * result is that we gradually test each pool size until we find
			 * one that doesn't trigger further expansion, and then hold it
			 * for at least io_worker_idle_timeout.
			 *
			 * XXX Perhaps ideas from queueing theory or control theory could
			 * do a better job of this.
			 */

			/* Read nworkers without lock for this heuristic purpose. */
			if (queue_depth > io_worker_control->nworkers)
				pgaio_worker_request_grow();
		}

		if (io_index != -1)
		{
			PgAioHandle *ioh = NULL;

			/* Cancel timeout and update wakeup:work ratio. */
			idle_timeout_abs = 0;
			if (++hist_ios == PGAIO_WORKER_WAKEUP_RATIO_SATURATE)
			{
				hist_wakeups /= 2;
				hist_ios /= 2;
			}

			ioh = &pgaio_ctl->io_handles[io_index];
			error_ioh = ioh;
			errcallback.arg = ioh;

			pgaio_debug_io(DEBUG4, ioh,
						   "worker %d processing IO",
						   MyIoWorkerId);

			/*
			 * Prevent interrupts between pgaio_io_reopen() and
			 * pgaio_io_perform_synchronously() that otherwise could lead to
			 * the FD getting closed in that window.
			 */
			HOLD_INTERRUPTS();

			/*
			 * It's very unlikely, but possible, that reopen fails. E.g. due
			 * to memory allocations failing or file permissions changing or
			 * such.  In that case we need to fail the IO.
			 *
			 * There's not really a good errno we can report here.
			 */
			error_errno = ENOENT;
			pgaio_io_reopen(ioh);

			/*
			 * To be able to exercise the reopen-fails path, allow injection
			 * points to trigger a failure at this point.
			 */
			INJECTION_POINT("aio-worker-after-reopen", ioh);

			error_errno = 0;
			error_ioh = NULL;

			/*
			 * As part of IO completion the buffer will be marked as NOACCESS,
			 * until the buffer is pinned again - which never happens in io
			 * workers. Therefore the next time there is IO for the same
			 * buffer, the memory will be considered inaccessible. To avoid
			 * that, explicitly allow access to the memory before reading data
			 * into it.
			 */
#ifdef USE_VALGRIND
			{
				struct iovec *iov;
				uint16		iov_length = pgaio_io_get_iovec_length(ioh, &iov);

				for (int i = 0; i < iov_length; i++)
					VALGRIND_MAKE_MEM_UNDEFINED(iov[i].iov_base, iov[i].iov_len);
			}
#endif

#ifdef PGAIO_WORKER_SHOW_PS_INFO
			{
				char	   *description = pgaio_io_get_target_description(ioh);

				sprintf(cmd, "%d: [%s] %s",
						MyIoWorkerId,
						pgaio_io_get_op_name(ioh),
						description);
				pfree(description);
				set_ps_display(cmd);
			}
#endif

			/*
			 * We don't expect this to ever fail with ERROR or FATAL, no need
			 * to keep error_ioh set to the IO.
			 * pgaio_io_perform_synchronously() contains a critical section to
			 * ensure we don't accidentally fail.
			 */
			pgaio_io_perform_synchronously(ioh);

			RESUME_INTERRUPTS();
			errcallback.arg = NULL;
		}
		else
		{
			int			timeout_ms;

			/* Cancel new worker request if pending. */
			pgaio_worker_cancel_grow();

			/* Compute the remaining allowed idle time. */
			if (io_worker_idle_timeout == -1)
			{
				/* Never time out. */
				timeout_ms = -1;
			}
			else
			{
				TimestampTz now = GetCurrentTimestamp();

				/* If the GUC changes, reset timer. */
				if (idle_timeout_abs != 0 &&
					io_worker_idle_timeout != timeout_guc_used)
					idle_timeout_abs = 0;

				/* Only the highest-numbered worker can time out. */
				if (pgaio_worker_can_timeout())
				{
					if (idle_timeout_abs == 0)
					{
						/*
						 * I have just been promoted to the timeout worker, or
						 * the GUC changed.  Compute new absolute time from
						 * now.
						 */
						idle_timeout_abs =
							TimestampTzPlusMilliseconds(now,
														io_worker_idle_timeout);
						timeout_guc_used = io_worker_idle_timeout;
					}
					timeout_ms =
						TimestampDifferenceMilliseconds(now, idle_timeout_abs);
				}
				else
				{
					/* No timeout for me. */
					idle_timeout_abs = 0;
					timeout_ms = -1;
				}
			}

#ifdef PGAIO_WORKER_SHOW_PS_INFO
			sprintf(cmd, "%d: idle, wakeups:ios = %d:%d",
					MyIoWorkerId, hist_wakeups, hist_ios);
			set_ps_display(cmd);
#endif

			if (WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH | WL_TIMEOUT,
						  timeout_ms,
						  WAIT_EVENT_IO_WORKER_MAIN) == WL_TIMEOUT)
			{
				/* WL_TIMEOUT */
				if (pgaio_worker_can_timeout())
					if (GetCurrentTimestamp() >= idle_timeout_abs)
						break;
			}
			else
			{
				/* WL_LATCH_SET */
				if (++hist_wakeups == PGAIO_WORKER_WAKEUP_RATIO_SATURATE)
				{
					hist_wakeups /= 2;
					hist_ios /= 2;
				}
			}
			ResetLatch(MyLatch);
		}

		CHECK_FOR_INTERRUPTS();

		if (ConfigReloadPending)
		{
			int			io_max_workers_prev = io_max_workers;
			int			io_min_workers_prev = io_min_workers;

			ConfigReloadPending = false;
			ProcessConfigFile(PGC_SIGHUP);

			/*
			 * Emit a WARNING if io_min_workers > io_max_workers.  If no bound
			 * has changed, skip this to avoid too many log messages.
			 */
			if (io_min_workers_prev != io_min_workers ||
				io_max_workers_prev != io_max_workers)
				check_io_worker_gucs();

			/* If io_max_workers has been decreased, exit highest first. */
			if (MyIoWorkerId >= io_max_workers)
				break;
		}
	}

	error_context_stack = errcallback.previous;
	proc_exit(0);
}

/*
 * pgaio_workers_enabled - (中文)worker 方法是否启用
 *
 * 【作用】供其他模块查询当前 io_method 是否为 worker(例如决定是否
 * 启动 IO worker、或某些只在 worker 模式下才有的行为)。
 *
 * 【参数】无。
 * 【返回值】true = 当前方法是 IOMETHOD_WORKER。
 */
bool
pgaio_workers_enabled(void)
{
	return io_method == IOMETHOD_WORKER;
}
