/*-------------------------------------------------------------------------
 *
 * pmsignal.c
 *	  routines for signaling between the postmaster and its child processes
 *
 * 【模块总览(中文)】
 * 本文件实现 postmaster 与其子进程之间的"带内信号通道"。注意:它不
 * 是用管道/套接字传输数据,而是"一个信号(SIGUSR1)+ 共享内存里的
 * 标志位"的组合:
 *
 * 【子进程 → postmaster 方向】
 * 子进程用 SendPostmasterSignal(reason) 把共享内存里对应原因的标志
 * 位置 1,再向 postmaster 发一个 SIGUSR1;postmaster 收到信号后在
 * CheckPostmasterSignal() 里检查并清零标志。关键性质:
 * - 多种原因可同时置位(每个原因一个布尔位),但"同一原因被多个进程
 *   同时发信号"时 postmaster 只会观察到一次(合并/丢失是允许的语义);
 * - 标志用 volatile sig_atomic_t 声明,靠平台保证的原子性免去显式锁。
 *
 * 【postmaster → 子进程方向】
 * 只有一种下行信号:广播 SIGQUIT(整个服务关停)。共享内存里保存
 * sigquit_reason(关停原因),子进程收到 SIGQUIT 后用
 * GetQuitSignalReason() 读取。崩溃重启时,该字段随共享内存重建自动
 * 清零,postmaster 无需显式处理。
 *
 * 【每子进程状态机(检测"未清理就退出"的异常)】
 * 共享内存里有 PMChildFlags[] 数组,每个子进程占一个槽位,状态:
 * UNUSED(可用)→ ASSIGNED(已分配,尚未接触共享内存,或已正常清理)
 * → ACTIVE(正在使用共享内存)→ WALSENDER(与 ACTIVE 相同,但额外
 * 标记"这是 WAL sender")。槽位由 postmaster 分配/回收;子进程启动
 * 后调用 RegisterPostmasterChildActive() 进入 ACTIVE,退出时经
 * shmem exit 钩子 MarkPostmasterChildInactive() 回到 ASSIGNED。若
 * postmaster 发现槽位不是 ASSIGNED 状态就死了,说明子进程没有走
 * 正常清理(异常退出),这正是"dead man switch"的一部分。
 *
 * 【父进程死亡检测】
 * PostmasterIsAliveInternal() 用"死亡监测管道"探测 postmaster 是否
 * 存活;支持的平台上还用父死亡信号(SIGINFO/SIGPWR,prctl)加速,由
 * postmaster_possibly_dead 标志缓存判断结果。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/pmsignal.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>

#ifdef HAVE_SYS_PRCTL_H
#include <sys/prctl.h>
#endif

#include "miscadmin.h"
#include "postmaster/postmaster.h"
#include "replication/walsender.h"
#include "storage/ipc.h"
#include "storage/pmsignal.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/memutils.h"


/*
 * The postmaster is signaled by its children by sending SIGUSR1.  The
 * specific reason is communicated via flags in shared memory.  We keep
 * a boolean flag for each possible "reason", so that different reasons
 * can be signaled by different backends at the same time.  (However,
 * if the same reason is signaled more than once simultaneously, the
 * postmaster will observe it only once.)
 *
 * The flags are actually declared as "volatile sig_atomic_t" for maximum
 * portability.  This should ensure that loads and stores of the flag
 * values are atomic, allowing us to dispense with any explicit locking.
 *
 * In addition to the per-reason flags, we store a set of per-child-process
 * flags that are currently used only for detecting whether a backend has
 * exited without performing proper shutdown.  The per-child-process flags
 * have three possible states: UNUSED, ASSIGNED, ACTIVE.  An UNUSED slot is
 * available for assignment.  An ASSIGNED slot is associated with a postmaster
 * child process, but either the process has not touched shared memory yet, or
 * it has successfully cleaned up after itself.  An ACTIVE slot means the
 * process is actively using shared memory.  The slots are assigned to child
 * processes by postmaster, and pmchild.c is responsible for tracking which
 * one goes with which PID.
 *
 * Actually there is a fourth state, WALSENDER.  This is just like ACTIVE,
 * but carries the extra information that the child is a WAL sender.
 * WAL senders too start in ACTIVE state, but switch to WALSENDER once they
 * start streaming the WAL (and they never go back to ACTIVE after that).
 *
 * We also have a shared-memory field that is used for communication in
 * the opposite direction, from postmaster to children: it tells why the
 * postmaster has broadcasted SIGQUIT signals, if indeed it has done so.
 */

#define PM_CHILD_UNUSED		0	/* these values must fit in sig_atomic_t */
#define PM_CHILD_ASSIGNED	1
#define PM_CHILD_ACTIVE		2
#define PM_CHILD_WALSENDER	3
/* (中文)每子进程槽位的四种状态(值必须能装进 sig_atomic_t,保证原子
 * 读写):
 * - PM_CHILD_UNUSED(0)  :槽位空闲,可分配;
 * - PM_CHILD_ASSIGNED(1):已分配给某个子进程,但该进程尚未接触共享内存,
 *   或者它已经正常清理完毕(等同于"干净");
 * - PM_CHILD_ACTIVE(2)  :该进程正在使用共享内存(异常退出的探测依据);
 * - PM_CHILD_WALSENDER(3):同 ACTIVE,但额外标记"是 WAL sender"(开始
 *   流式发送 WAL 后从 ACTIVE 切换,此后不再回到 ACTIVE)。 */

/* "typedef struct PMSignalData PMSignalData" appears in pmsignal.h */
/* (中文)共享内存中的信号状态结构(typedef 见 pmsignal.h):
 * - PMSignalFlags[]:每个"原因"一个布尔位(子进程 → postmaster 方向),
 *   用 volatile sig_atomic_t 保证原子读/写,无需加锁;
 * - sigquit_reason :postmaster → 子进程方向的下行信息:广播 SIGQUIT
 *   的原因(QuitSignalReason 枚举);
 * - num_child_flags:PMChildFlags[] 的元素个数;
 * - PMChildFlags[] :每子进程状态机槽位(见 PM_CHILD_* 宏)。 */
struct PMSignalData
{
	/* per-reason flags for signaling the postmaster */
	sig_atomic_t PMSignalFlags[NUM_PMSIGNALS];
	/* global flags for signals from postmaster to children */
	QuitSignalReason sigquit_reason;	/* why SIGQUIT was sent */
	/* per-child-process flags */
	int			num_child_flags;	/* # of entries in PMChildFlags[] */
	sig_atomic_t PMChildFlags[FLEXIBLE_ARRAY_MEMBER];
};

/* PMSignalState pointer is valid in both postmaster and child processes */
/* (中文)指向共享内存中 PMSignalData 的指针,postmaster 与子进程都有效
 * (经 ShmemRequestStruct 在 request/init 阶段建立)。所有信号标志的
 * 读写都经由它。 */
NON_EXEC_STATIC volatile PMSignalData *PMSignalState = NULL;

static void PMSignalShmemRequest(void *);
static void PMSignalShmemInit(void *);

/* (中文)本文件向共享内存子系统登记的 request/init 回调:request 阶段
 * 按 MaxLivePostmasterChildren() 计算槽位总数并声明需要的字节数;init
 * 阶段把槽位总数写入共享内存。 */
const ShmemCallbacks PMSignalShmemCallbacks = {
	.request_fn = PMSignalShmemRequest,
	.init_fn = PMSignalShmemInit,
};

/*
 * Local copy of PMSignalState->num_child_flags, only valid in the
 * postmaster.  Postmaster keeps a local copy so that it doesn't need to
 * trust the value in shared memory.
 */
/* (中文)postmaster 进程私有的槽位总数副本(request 阶段按当时的
 * MaxLivePostmasterChildren() 算出)。保持本地副本,postmaster 就不必
 * 每次信任/重读共享内存里的值。 */
static int	num_child_flags;

/*
 * Signal handler to be notified if postmaster dies.
 */
/* (中文)父进程死亡信号的处理入口:仅置位 postmaster_possibly_dead
 * 标志,真正判定放在 PostmasterIsAliveInternal() 的慢路径里。 */
#ifdef USE_POSTMASTER_DEATH_SIGNAL
/* (中文)缓存"postmaster 可能已死"的标志:父死亡信号处理函数与死亡
 * 监测管道检查到异常时置位,PostmasterIsAlive() 快速路径先查它,为真
 * 才走慢路径验证。 */
volatile sig_atomic_t postmaster_possibly_dead = false;

static void
postmaster_death_handler(SIGNAL_ARGS)
{
	postmaster_possibly_dead = true;
}

/*
 * The available signals depend on the OS.  SIGUSR1 and SIGUSR2 are already
 * used for other things, so choose another one.
 *
 * Currently, we assume that we can always find a signal to use.  That
 * seems like a reasonable assumption for all platforms that are modern
 * enough to have a parent-death signaling mechanism.
 */
/* (中文)挑选"父进程死亡信号":SIGUSR1/SIGUSR2 已有其他用途,因此按平台
 * 可用性选 SIGINFO 或 SIGPWR。 */
#if defined(SIGINFO)
#define POSTMASTER_DEATH_SIGNAL SIGINFO
#elif defined(SIGPWR)
#define POSTMASTER_DEATH_SIGNAL SIGPWR
#else
#error "cannot find a signal to use for postmaster death"
#endif

#endif							/* USE_POSTMASTER_DEATH_SIGNAL */

static void MarkPostmasterChildInactive(int code, Datum arg);

/*
 * PMSignalShmemRequest - Register pmsignal.c's shared memory needs
 */
/*
 * PMSignalShmemRequest - (中文)登记 pmsignal 的共享内存需求(request 阶段)
 *
 * 【作用】在 request 阶段被调用:按当前配置的"最大存活子进程数"
 * (MaxLivePostmasterChildren()) 决定每子进程槽位数组的大小,据此计算
 * PMSignalData 总字节数并 ShmemRequestStruct() 登记,同时把指针槽
 * 指向 PMSigalState 全局变量。
 *
 * 【设计思想】槽位数必须在 request 阶段定格:创建段时就要按最终大小
 * 预留 PMChildFlags 数组,运行期不可扩容。Postmaster 的本地副本
 * num_child_flags 也随之确定。
 *
 * 【参数】arg —— 回调的 opaque 参数(未使用)。
 * 【返回值】无。
 */
static void
PMSignalShmemRequest(void *arg)
{
	size_t		size;

	num_child_flags = MaxLivePostmasterChildren();

	size = add_size(offsetof(PMSignalData, PMChildFlags),
					mul_size(num_child_flags, sizeof(sig_atomic_t)));
	ShmemRequestStruct(.name = "PMSignalState",
					   .size = size,
					   .ptr = (void **) &PMSignalState,
		);
}

/*
 * PMSignalShmemInit - (中文)初始化 pmsignal 的共享内存(init 阶段)
 *
 * 【作用】把 request 阶段算好的槽位总数写入共享内存结构
 * (num_child_flags)。PMSignalFlags 与 PMChildFlags 数组依赖共享内存
 * 初始为零的特性(所有槽位天然为 UNUSED / 未置位),无需显式清零。
 *
 * 【参数】arg —— 回调的 opaque 参数(未使用)。
 * 【返回值】无。
 */
static void
PMSignalShmemInit(void *arg)
{
	Assert(PMSignalState);
	Assert(num_child_flags > 0);
	PMSignalState->num_child_flags = num_child_flags;
}

/*
 * SendPostmasterSignal - signal the postmaster from a child process
 */
/*
 * SendPostmasterSignal - (中文)子进程向 postmaster 发送信号(带原因)
 *
 * 【作用】把共享内存里对应 reason 的标志位置 1(原子写),然后向
 * postmaster 进程发送 SIGUSR1。postmaster 会在 CheckPostmasterSignal()
 * 中检查标志并清零。
 *
 * 【设计思想】信号本身不带信息(所有原因共用 SIGUSR1),原因靠共享内存
 * 的标志位传递;标志位用 sig_atomic_t 保证原子性,省去锁。语义上的
 * 允差:同一原因被多个进程同时发信号时,标志位只体现"是/否",postmaster
 * 最多观察到一次——这符合所有调用场景(那些"通知"只需唤醒一次)。
 * 单机后端(IsUnderPostmaster 为假)直接返回,无 postmaster 可发。
 *
 * 【参数】reason —— 信号原因(PMSignalReason 枚举,见 pmsignal.h)。
 * 【返回值】无。
 */
void
SendPostmasterSignal(PMSignalReason reason)
{
	/* If called in a standalone backend, do nothing */
	if (!IsUnderPostmaster)
		return;
	/* Atomically set the proper flag */
	PMSignalState->PMSignalFlags[reason] = true;
	/* Send signal to postmaster */
	kill(PostmasterPid, SIGUSR1);
}

/*
 * CheckPostmasterSignal - check to see if a particular reason has been
 * signaled, and clear the signal flag.  Should be called by postmaster
 * after receiving SIGUSR1.
 */
/*
 * CheckPostmasterSignal - (中文)postmaster 检查并清零某个"原因"标志位
 *
 * 【作用】postmaster 收到 SIGUSR1 后,对每个关心的原因调用本函数:若
 * 标志位为真则清零并返回 true(表示该原因确实被通知过),否则返回
 * false。
 *
 * 【设计思想】"检查 + 清零"必须由同一函数完成,且只在标志为真时才写:
 * 直接覆盖写(而不先读)会破坏别的子进程刚好发来的新信号。清零后再发
 * 的同类信号会在标志位上重新置 1,因此不会丢失"清零之后"的事件——
 * 丢失的只会是"清零之前已合并"的事件,这是设计允许的。
 *
 * 【参数】reason —— 要检查的原因(PMSignalReason)。
 * 【返回值】true 表示该原因曾被通知(且本次调用已清零)。
 */
bool
CheckPostmasterSignal(PMSignalReason reason)
{
	/* Careful here --- don't clear flag if we haven't seen it set */
	if (PMSignalState->PMSignalFlags[reason])
	{
		PMSignalState->PMSignalFlags[reason] = false;
		return true;
	}
	return false;
}

/*
 * SetQuitSignalReason - broadcast the reason for a system shutdown.
 * Should be called by postmaster before sending SIGQUIT to children.
 *
 * Note: in a crash-and-restart scenario, the "reason" field gets cleared
 * as a part of rebuilding shared memory; the postmaster need not do it
 * explicitly.
 */
/*
 * SetQuitSignalReason - (中文)记录广播 SIGQUIT 的原因(postmaster 侧)
 *
 * 【作用】postmaster 决定向全部子进程广播 SIGQUIT(整个服务关停)之前,
 * 先把原因写进共享内存的 sigquit_reason 字段;子进程随后可用
 * GetQuitSignalReason() 读取。
 *
 * 【设计思想】崩溃重启场景下,该字段会随共享内存重建自动清零
 * (GetQuitSignalReason 返回 PMQUIT_NOT_SENT),postmaster 无需显式
 * 清理,这保证了"新生命周期"不会读到旧原因。
 *
 * 【参数】reason —— 关停原因(QuitSignalReason 枚举)。
 * 【返回值】无。
 */
void
SetQuitSignalReason(QuitSignalReason reason)
{
	PMSignalState->sigquit_reason = reason;
}

/*
 * GetQuitSignalReason - obtain the reason for a system shutdown.
 * Called by child processes when they receive SIGQUIT.
 * If the postmaster hasn't actually sent SIGQUIT, will return PMQUIT_NOT_SENT.
 */
/*
 * GetQuitSignalReason - (中文)读取广播 SIGQUIT 的原因(子进程侧)
 *
 * 【作用】子进程收到 SIGQUIT 时调用,读取共享内存里的 sigquit_reason。
 * 若 postmaster 实际上还没发过 SIGQUIT,或本进程不是 postmaster 的
 * 子进程、或共享内存尚未建立,返回 PMQUIT_NOT_SENT。
 *
 * 【设计思想】本函数可能在信号处理上下文中被调用,因此格外保守:
 * 无条件检查 IsUnderPostmaster 与 PMSignalState 是否有效,避免访问
 * 未初始化的共享内存;读取单个 sig_atomic_t 大小的字段是原子操作,
 * 信号上下文里也安全。
 *
 * 【参数】无。
 * 【返回值】关停原因(QuitSignalReason);未发送 SIGQUIT 时为
 * PMQUIT_NOT_SENT。
 */
QuitSignalReason
GetQuitSignalReason(void)
{
	/* This is called in signal handlers, so be extra paranoid. */
	if (!IsUnderPostmaster || PMSignalState == NULL)
		return PMQUIT_NOT_SENT;
	return PMSignalState->sigquit_reason;
}


/*
 * MarkPostmasterChildSlotAssigned - mark the given slot as ASSIGNED for a
 * new postmaster child process.
 *
 * Only the postmaster is allowed to execute this routine, so we need no
 * special locking.
 */
/*
 * MarkPostmasterChildSlotAssigned - (中文)把某个子进程槽位标记为 ASSIGNED
 *
 * 【作用】postmaster 为新 fork 的子进程分配槽位:检查槽位空闲
 * (UNUSED,否则 FATAL——说明槽位管理出现重复分配),然后置为
 * ASSIGNED(该进程尚未接触共享内存或已清理干净)。
 *
 * 【设计思想】槽位与 PMChildFlags 数组的约定:外部传 1 基的槽位号,
 * 内部减 1 转 0 基下标。只有 postmaster 调用本函数,故无需锁。
 *
 * 【参数】slot —— 1 基的槽位号(1..num_child_flags)。
 * 【返回值】无(槽位已被占用则 FATAL)。
 */
void
MarkPostmasterChildSlotAssigned(int slot)
{
	Assert(slot > 0 && slot <= num_child_flags);
	slot--;

	if (PMSignalState->PMChildFlags[slot] != PM_CHILD_UNUSED)
		elog(FATAL, "postmaster child slot is already in use");

	PMSignalState->PMChildFlags[slot] = PM_CHILD_ASSIGNED;
}

/*
 * MarkPostmasterChildSlotUnassigned - release a slot after death of a
 * postmaster child process.  This must be called in the postmaster process.
 *
 * Returns true if the slot had been in ASSIGNED state (the expected case),
 * false otherwise (implying that the child failed to clean itself up).
 */
/*
 * MarkPostmasterChildSlotUnassigned - (中文)回收子进程槽位(postmaster 侧)
 *
 * 【作用】子进程死亡后,postmaster 把它占用的槽位放回 UNUSED 供复用。
 * 返回值报告"该槽位此前是否处于 ASSIGNED 状态"。
 *
 * 【设计思想】返回值的语义正是"dead man switch"的探测点:若子进程走
 * 了正常清理,它会在退出钩子里把状态改回 ASSIGNED(见
 * MarkPostmasterChildInactive);若 postmaster 发现槽位不是 ASSIGNED
 * (即仍为 ACTIVE/WALSENDER),说明子进程异常退出、没来得及清理。
 * 注意:崩溃场景下本函数可能被调用两次(槽位可能已 UNUSED),所以不
 * 对状态做断言,一律置回 UNUSED。
 *
 * 【参数】slot —— 1 基的槽位号。
 * 【返回值】true 表示槽位此前处于 ASSIGNED(正常路径);false 表示
 * 此前状态异常(ACTIVE/WALSENDER/UNUSED)。
 */
bool
MarkPostmasterChildSlotUnassigned(int slot)
{
	bool		result;

	Assert(slot > 0 && slot <= num_child_flags);
	slot--;

	/*
	 * Note: the slot state might already be unused, because the logic in
	 * postmaster.c is such that this might get called twice when a child
	 * crashes.  So we don't try to Assert anything about the state.
	 */
	result = (PMSignalState->PMChildFlags[slot] == PM_CHILD_ASSIGNED);
	PMSignalState->PMChildFlags[slot] = PM_CHILD_UNUSED;
	return result;
}

/*
 * IsPostmasterChildWalSender - check if given slot is in use by a
 * walsender process.  This is called only by the postmaster.
 */
/*
 * IsPostmasterChildWalSender - (中文)查询槽位是否被 WAL sender 进程占用
 *
 * 【作用】postmaster 判断某个子进程槽位当前是否处于 WALSENDER 状态
 * (即该子进程是正在流式发送 WAL 的 walsender)。
 *
 * 【设计思想】纯查询,不改状态。WALSENDER 状态从 ACTIVE 单向切换而来
 * (见 MarkPostmasterChildWalSender),查询它让 postmaster 能区分
 * "普通 ACTIVE 后端"与"walsender"。
 *
 * 【参数】slot —— 1 基的槽位号。
 * 【返回值】true 表示该槽位是 WALSENDER 状态。
 */
bool
IsPostmasterChildWalSender(int slot)
{
	Assert(slot > 0 && slot <= num_child_flags);
	slot--;

	if (PMSignalState->PMChildFlags[slot] == PM_CHILD_WALSENDER)
		return true;
	else
		return false;
}

/*
 * RegisterPostmasterChildActive - mark a postmaster child as about to begin
 * actively using shared memory.  This is called in the child process.
 *
 * This register an shmem exit hook to mark us as inactive again when the
 * process exits normally.
 */
/*
 * RegisterPostmasterChildActive - (中文)子进程标记自己"开始使用共享内存"
 *
 * 【作用】子进程启动早期(接触共享内存之前)调用:把自己槽位从
 * ASSIGNED 改成 ACTIVE,并注册一个 on_shmem_exit 钩子,让正常退出时
 * 自动改回 ASSIGNED。
 *
 * 【设计思想】"ACTIVE 表示正在使用共享内存"是异常退出探测的基础:
 * 若 postmaster 在子进程还处于 ACTIVE 时发现它死了,就判定为"未正确
 * 清理的崩溃"。钩子保证正常路径必定复位,不用子进程显式操心。
 *
 * 【参数】无(槽位取自全局 MyPMChildSlot)。
 * 【返回值】无。
 */
void
RegisterPostmasterChildActive(void)
{
	int			slot = MyPMChildSlot;

	Assert(slot > 0 && slot <= PMSignalState->num_child_flags);
	slot--;
	Assert(PMSignalState->PMChildFlags[slot] == PM_CHILD_ASSIGNED);
	PMSignalState->PMChildFlags[slot] = PM_CHILD_ACTIVE;

	/* Arrange to clean up at exit. */
	on_shmem_exit(MarkPostmasterChildInactive, 0);
}

/*
 * MarkPostmasterChildWalSender - mark a postmaster child as a WAL sender
 * process.  This is called in the child process, sometime after marking the
 * child as active.
 */
/*
 * MarkPostmasterChildWalSender - (中文)子进程把自己标记为 WAL sender
 *
 * 【作用】walsender 进程开始流式发送 WAL 时调用(须在
 * RegisterPostmasterChildActive 之后):把槽位从 ACTIVE 改为
 * WALSENDER。此后不再回到 ACTIVE。
 *
 * 【设计思想】WALSENDER 是 ACTIVE 的"带标签变体":对异常退出探测而言
 * 两者等价(都是"使用中"),但 postmaster 需要知道该子进程是 walsender
 * 以便做与复制相关的管理决策。
 *
 * 【参数】无(槽位取自 MyPMChildSlot;须 am_walsender)。
 * 【返回值】无。
 */
void
MarkPostmasterChildWalSender(void)
{
	int			slot = MyPMChildSlot;

	Assert(am_walsender);

	Assert(slot > 0 && slot <= PMSignalState->num_child_flags);
	slot--;
	Assert(PMSignalState->PMChildFlags[slot] == PM_CHILD_ACTIVE);
	PMSignalState->PMChildFlags[slot] = PM_CHILD_WALSENDER;
}

/*
 * MarkPostmasterChildInactive - mark a postmaster child as done using
 * shared memory.  This is called in the child process.
 */
/*
 * MarkPostmasterChildInactive - (中文)子进程退出钩子:把自己标记回 ASSIGNED
 *
 * 【作用】经 RegisterPostmasterChildActive 注册的 on_shmem_exit 回调:
 * 子进程正常退出(清理流程)时,把槽位从 ACTIVE/WALSENDER 改回
 * ASSIGNED,表示"已清理干净"。
 *
 * 【设计思想】这就是正常退出与异常退出的分界:正常路径必然回到
 * ASSIGNED;直接崩溃则停留在 ACTIVE/WALSENDER,postmaster 据此判定
 * 异常。状态断言(ACTIVE 或 WALSENDER)用于尽早暴露状态机被破坏的
 * 程序错误。
 *
 * 【参数】
 *   code —— 退出码(on_shmem_exit 约定,未使用);
 *   arg  —— 注册时的 Datum 参数(未使用)。
 * 【返回值】无。
 */
static void
MarkPostmasterChildInactive(int code, Datum arg)
{
	int			slot = MyPMChildSlot;

	Assert(slot > 0 && slot <= PMSignalState->num_child_flags);
	slot--;
	Assert(PMSignalState->PMChildFlags[slot] == PM_CHILD_ACTIVE ||
		   PMSignalState->PMChildFlags[slot] == PM_CHILD_WALSENDER);
	PMSignalState->PMChildFlags[slot] = PM_CHILD_ASSIGNED;
}


/*
 * PostmasterIsAliveInternal - check whether postmaster process is still alive
 *
 * This is the slow path of PostmasterIsAlive(), where the caller has already
 * checked 'postmaster_possibly_dead'.  (On platforms that don't support
 * a signal for parent death, PostmasterIsAlive() is just an alias for this.)
 */
/*
 * PostmasterIsAliveInternal - (中文)慢路径探测 postmaster 是否还活着
 *
 * 【作用】PostmasterIsAlive() 的慢路径(调用方已先查过
 * postmaster_possibly_dead 缓存):非 Windows 下对"死亡监测管道"的读端
 * 做一次非阻塞 read——postmaster 持有写端,若它死了管道关闭,read 立即
 * 返回 0(EOF);若还活着且没有数据,read 返回 EAGAIN/EWOULDBLOCK。
 * Windows 下等价于用 WaitForSingleObject 检查进程句柄。
 *
 * 【设计思想】"先复位标志再检查、确认死亡再置位"的顺序保证不错过
 * 恰好发生在检查瞬间的死亡信号。真正的错误(读返回异常、管道里出现
 * 意料之外的数据)说明系统状态被破坏,直接 FATAL。
 *
 * 【参数】无。
 * 【返回值】true 表示 postmaster 存活;false 表示已死。
 */
bool
PostmasterIsAliveInternal(void)
{
#ifdef USE_POSTMASTER_DEATH_SIGNAL
	/*
	 * Reset the flag before checking, so that we don't miss a signal if
	 * postmaster dies right after the check.  If postmaster was indeed dead,
	 * we'll re-arm it before returning to caller.
	 */
	postmaster_possibly_dead = false;
#endif

#ifndef WIN32
	{
		char		c;
		ssize_t		rc;

		rc = read(postmaster_alive_fds[POSTMASTER_FD_WATCH], &c, 1);

		/*
		 * In the usual case, the postmaster is still alive, and there is no
		 * data in the pipe.
		 */
		if (rc < 0 && (errno == EAGAIN || errno == EWOULDBLOCK))
			return true;
		else
		{
			/*
			 * Postmaster is dead, or something went wrong with the read()
			 * call.
			 */

#ifdef USE_POSTMASTER_DEATH_SIGNAL
			postmaster_possibly_dead = true;
#endif

			if (rc < 0)
				elog(FATAL, "read on postmaster death monitoring pipe failed: %m");
			else if (rc > 0)
				elog(FATAL, "unexpected data in postmaster death monitoring pipe");

			return false;
		}
	}

#else							/* WIN32 */
	if (WaitForSingleObject(PostmasterHandle, 0) == WAIT_TIMEOUT)
		return true;
	else
	{
#ifdef USE_POSTMASTER_DEATH_SIGNAL
		postmaster_possibly_dead = true;
#endif
		return false;
	}
#endif							/* WIN32 */
}

/*
 * PostmasterDeathSignalInit - request signal on postmaster death if possible
 */
/*
 * PostmasterDeathSignalInit - (中文)注册"父进程死亡信号"(如平台支持)
 *
 * 【作用】子进程启动时调用:注册父死亡信号的处理函数,并通过
 * PR_SET_PDEATHSIG(Linux prctl)或 PROC_PDEATHSIG_CTL(FreeBSD procctl)
 * 请求内核在父进程(postmaster)退出时给本进程发该信号;最后把
 * postmaster_possibly_dead 预置为 true。
 *
 * 【设计思想】把标志预置为 true 是一种保守策略:万一 postmaster 在
 * 注册完成之前就已经死了,内核不会补发信号,首轮检查时先走慢路径
 * (PostmasterIsAliveInternal)验证一遍,不会漏判。
 *
 * 【参数】无。
 * 【返回值】无(内核接口失败时 ERROR)。
 */
void
PostmasterDeathSignalInit(void)
{
#ifdef USE_POSTMASTER_DEATH_SIGNAL
	int			signum = POSTMASTER_DEATH_SIGNAL;

	/* Register our signal handler. */
	pqsignal(signum, postmaster_death_handler);

	/* Request a signal on parent exit. */
#if defined(PR_SET_PDEATHSIG)
	if (prctl(PR_SET_PDEATHSIG, signum) < 0)
		elog(ERROR, "could not request parent death signal: %m");
#elif defined(PROC_PDEATHSIG_CTL)
	if (procctl(P_PID, 0, PROC_PDEATHSIG_CTL, &signum) < 0)
		elog(ERROR, "could not request parent death signal: %m");
#else
#error "USE_POSTMASTER_DEATH_SIGNAL set, but there is no mechanism to request the signal"
#endif

	/*
	 * Just in case the parent was gone already and we missed it, we'd better
	 * check the slow way on the first call.
	 */
	postmaster_possibly_dead = true;
#endif							/* USE_POSTMASTER_DEATH_SIGNAL */
}
