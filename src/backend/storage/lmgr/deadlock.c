/*-------------------------------------------------------------------------
 *
 * deadlock.c
 *	  POSTGRES deadlock detection code
 *
 * See src/backend/storage/lmgr/README for a description of the deadlock
 * detection and resolution algorithms.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的死锁检测与消解算法。
 *
 * 【背景】当进程 A 等待 B 持有的锁、B 又在等待 C 持有的锁……形成环时,
 * 死锁就发生了。PostgreSQL 的策略是:等锁的进程在 deadlock_timeout
 * 之后会被唤醒执行死锁检测(见 proc.c 的 CheckDeadLock → DeadLockCheck),
 * 若确认死锁,选择牺牲一个进程回滚其事务,而不是无限等待下去。
 *
 * 【核心概念】
 * - 等待图(waits-for graph):节点是"锁组领导进程",边是"等待关系"。
 *   - 硬边(hard edge):等待者真的在等某个持锁者持有的锁;
 *   - 软边(soft edge):等待者排在锁的等待队列中、排在某进程之后,
 *     后者尚未持有锁、只是先到先等。软边之所以"软",是因为调整等待
 *     队列顺序就可以消除——这正是本文件消解死锁的手段。
 * - 检测方法:从给定进程出发做深度优先搜索(FindLockCycleRecurse),
 *   用"深度优先数 + 已访问标记"发现环;回到起点(i == 0)说明存在
 *   包含起点的死锁环。
 * - 消解方法(DeadLockCheckRecurse + TestConfiguration + TopoSort):
 *   对检测到的每个软环,尝试反转其中一条软边(即把"阻塞者"排到
 *   "等待者"前面),得到一个"约束";若所有约束能同时满足且不再有环,
 *   就按 TopoSort 给出的新顺序重排相关锁的等待队列,死锁即被消除
 *   (返回 DS_SOFT_DEADLOCK);若怎么试都有环,则必须牺牲一个进程
 *   (DS_HARD_DEADLOCK)。
 *
 * 【设计细节】
 * - 检测在"已持有锁表全部分区锁"的条件下进行(调用者保证),因此
 *   可以安全地遍历共享锁表;但这也要求本文件的算法工作区(visitedProcs
 *   等数组)在后端启动时就分配好(InitDeadLockChecking),且检测期间
 *   不能做任何可能出错/等待的操作。
 * - 锁组(lock group)支持:并行查询中组内进程的锁互为"同一人",
 *   检测时一律用组长(leader)代表整组,组内成员的等待也算组长的边。
 * - deadlockDetails[] 保存环上每一条边的(锁标签、锁模式、PID)信息,
 *   供 DeadLockReport 在释放分区锁之后打印详细报告。
 * - 本文件还与 FastPathStrongRelationLocks 配合:fast-path 锁对死锁
 *   检测不可见,因此强锁(fast-path 冲突锁)获取前必须先调用
 *   FastPathTransferRelationLocks 把相关 fast-path 锁迁移进主锁表
 *   (见 lock.c)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/deadlock.c
 *
 *	Interface:
 *
 *	DeadLockCheck()
 *	DeadLockReport()
 *	RememberSimpleDeadLock()
 *	InitDeadLockChecking()
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "storage/lmgr.h"
#include "storage/proc.h"
#include "storage/procnumber.h"
#include "utils/memutils.h"


/*
 * One edge in the waits-for graph.
 *
 * waiter and blocker may or may not be members of a lock group, but if either
 * is, it will be the leader rather than any other member of the lock group.
 * The group leaders act as representatives of the whole group even though
 * those particular processes need not be waiting at all.  There will be at
 * least one member of the waiter's lock group on the wait queue for the given
 * lock, maybe more.
 */
typedef struct
{
	PGPROC	   *waiter;			/* the leader of the waiting lock group */
	PGPROC	   *blocker;		/* the leader of the group it is waiting for */
	LOCK	   *lock;			/* the lock being waited for */
	int			pred;			/* workspace for TopoSort */
	int			link;			/* workspace for TopoSort */
} EDGE;

/* (中文)等待图(watts-for graph)的一条边:
 * - waiter  : 等待方的锁组组长(若进程不属于任何锁组,组长就是它自己);
 * - blocker : 被等待方的锁组组长;
 * - lock    : 双方围绕的那把锁;
 * - pred/link : 是 TopoSort 的临时工作字段:pred 记录"本约束对应的
 *   等待者在下标数组中的位置",link 把同一把锁的所有"after 约束"
 *   串成链表(TopoSort 内用完即弃)。
 * 一条边代表"waiter 因为 lock 排在 blocker(或其组员)之后/被其持有
 * 而必须等"。若 waiter 的锁组里至少有一个组员在 lock 的等待队列上,
 * 这条边就成立(哪怕 waiter 自己根本没在等)。 */

/* One potential reordering of a lock's wait queue */
typedef struct
{
	LOCK	   *lock;			/* the lock whose wait queue is described */
	PGPROC	  **procs;			/* array of PGPROC *'s in new wait order */
	int			nProcs;
} WAIT_ORDER;

/* (中文)一把锁的等待队列的"一种候选重排方案":
 * - lock   : 被重排的那把锁;
 * - procs  : 按新顺序排列的等待者数组(PGPROC 指针),数组空间取自
 *   工作区 waitOrderProcs;
 * - nProcs : 队列长度。
 * ExpandConstraints + TopoSort 为每条受约束的锁生成一个 WAIT_ORDER,
 * 死锁消解成功后,DeadLockCheck 按这些方案重建各锁的等待队列。 */

/*
 * Information saved about each edge in a detected deadlock cycle.  This
 * is used to print a diagnostic message upon failure.
 *
 * Note: because we want to examine this info after releasing the lock
 * manager's partition locks, we can't just store LOCK and PGPROC pointers;
 * we must extract out all the info we want to be able to print.
 */
typedef struct
{
	LOCKTAG		locktag;		/* ID of awaited lock object */
	LOCKMODE	lockmode;		/* type of lock we're waiting for */
	int			pid;			/* PID of blocked backend */
} DEADLOCK_INFO;

/* (中文)死锁环中"一条边"的打印用快照:
 * 检测算法在持全部分区锁时运行,而报告(DeadLockReport)要在放锁之后
 * 打印,那时 LOCK/PGPROC 指针可能已失效,所以检测阶段就把环上每一条
 * 等待边的信息提取成纯值:被等的锁标签 locktag、等待的锁模式 lockmode、
 * 等待方进程的 PID。数组按环的顺序存放(deadlockDetails[i] 被
 * deadlockDetails[i+1] 阻塞,最后一个被第一个阻塞),长度
 * nDeadlockDetails 即环的长度。 */


static bool DeadLockCheckRecurse(PGPROC *proc);
static int	TestConfiguration(PGPROC *startProc);
static bool FindLockCycle(PGPROC *checkProc,
						  EDGE *softEdges, int *nSoftEdges);
static bool FindLockCycleRecurse(PGPROC *checkProc, int depth,
								 EDGE *softEdges, int *nSoftEdges);
static bool FindLockCycleRecurseMember(PGPROC *checkProc,
									   PGPROC *checkProcLeader,
									   int depth, EDGE *softEdges, int *nSoftEdges);
static bool ExpandConstraints(EDGE *constraints, int nConstraints);
static bool TopoSort(LOCK *lock, EDGE *constraints, int nConstraints,
					 PGPROC **ordering);

#ifdef DEBUG_DEADLOCK
static void PrintLockQueue(LOCK *lock, const char *info);
#endif


/*
 * Working space for the deadlock detector
 */

/* Workspace for FindLockCycle */
static PGPROC **visitedProcs;	/* Array of visited procs */
static int	nVisitedProcs;
/* (中文)FindLockCycle 的工作区:
 * visitedProcs 是"深度优先搜索已访问进程"的数组(按访问顺序,下标 0
 * 即搜索起点),nVisitedProcs 是当前已访问个数。DFS 中若再次遇到
 * visitedProcs[0] 就构成死锁环;数组容量 MaxBackends,在
 * InitDeadLockChecking 时一次性分配(检测期间持全部分区锁,不能临时
 * 分配内存)。 */

/* Workspace for TopoSort */
static PGPROC **topoProcs;		/* Array of not-yet-output procs */
static int *beforeConstraints;	/* Counts of remaining before-constraints */
static int *afterConstraints;	/* List head for after-constraints */
/* (中文)TopoSort 的工作区(复用 visitedProcs 的空间,二者不同时运行):
 * - topoProcs[]      : 等待队列的当前顺序副本,排序过程中逐个置 NULL
 *                       表示"已输出";
 * - beforeConstraints[i] : 下标 i 的进程还差多少个"必须先于别人"的
 *                       约束未满足(0 表示可以输出;-1 表示与组长合并
 *                       输出,不单独参与排序);
 * - afterConstraints[i] : 以 i 为"后置者"的约束链表的表头(链指针存
 *                       在 EDGE.link 里,表头存的是 i+1,0 表示空)。 */

/* Output area for ExpandConstraints */
static WAIT_ORDER *waitOrders;	/* Array of proposed queue rearrangements */
static int	nWaitOrders;
static PGPROC **waitOrderProcs; /* Space for waitOrders queue contents */
/* (中文)ExpandConstraints 的输出区:waitOrders[] 记录对若干把锁的
 * 重排方案(最多 MaxBackends/2 个——形成一条软边至少要两个等待者),
 * waitOrderProcs[] 是这些方案共用的等待者指针空间(总长 MaxBackends),
 * nWaitOrders 是当前方案个数。 */

/* Current list of constraints being considered */
static EDGE *curConstraints;
static int	nCurConstraints;
static int	maxCurConstraints;
/* (中文)当前正在尝试的约束集合:curConstraints[] 是递归搜索(死锁消解)
 * 当前层的约束列表,nCurConstraints 为个数,maxCurConstraints 为容量
 * (MaxBackends,同时限制 DeadLockCheckRecurse 的最大递归深度,防止
 * 栈溢出)。每个约束都是"一条需要反转的软边"。 */

/* Storage space for results from FindLockCycle */
static EDGE *possibleConstraints;
static int	nPossibleConstraints;
static int	maxPossibleConstraints;
static DEADLOCK_INFO *deadlockDetails;
static int	nDeadlockDetails;
/* (中文)FindLockCycle 的结果区:
 * - possibleConstraints[] : 暂存各次检测找到的软边(容量 4*MaxBackends;
 *   后 MaxBackends 个条目作为 FindLockCycle 的输出工作区);
 * - deadlockDetails[]     : 环上各边的打印用快照(见 DEADLOCK_INFO);
 * - nDeadlockDetails      : 环的长度(边数)。 */

/* PGPROC pointer of any blocking autovacuum worker found */
static PGPROC *blocking_autovacuum_proc = NULL;
/* (中文)若发现"直接硬阻塞本进程"的是某个 autovacuum 工作进程,记下其
 * PGPROC(用于向 autovacuum 发取消信号,见 GetBlockingAutoVacuumPgproc;
 * 间接阻塞者不在此列,由直接阻塞者去处理)。 */


/*
 * InitDeadLockChecking -- initialize deadlock checker during backend startup
 *
 * This does per-backend initialization of the deadlock checker; primarily,
 * allocation of working memory for DeadLockCheck.  We do this per-backend
 * since there's no percentage in making the kernel do copy-on-write
 * inheritance of workspace from the postmaster.  We allocate the space at
 * startup because the deadlock checker is run with all the partitions of the
 * lock table locked, and we want to keep that section as short as possible.
 */
/*
 * InitDeadLockChecking
 *      (中文)后端启动时初始化死锁检测器的工作区
 *
 * 【作用】一次性为死锁检测分配全部工作内存(见上方各静态全局变量的
 * 中文注释),并把指针初始化好。
 *
 * 【设计思想】为什么要在启动时分配:
 * - 死锁检测是在"锁表全部分区锁全部被持有"的条件下运行的,那段临界区
 *   要尽可能短,绝不能在检测过程中做 palloc(可能触发内存上下文锁等
 *   与锁表无关但会出错的路径);
 * - 工作区只依赖 MaxBackends 等启动期常量,大小固定,完全可以预分配;
 * - 每个后端各自分配(而非继承 postmaster 的写时复制拷贝),避免所有
 *   后端共享同一份工作区的错觉(各后端是独立进程,本来也互不干扰,
 *   这里只是习惯性避免 COW 内存被改写)。
 *
 * 【容量论证】
 * - FindLockCycle 最多访问 MaxBackends 个进程;
 * - TopoSort 与 FindLockCycle 不同时运行,可复用同一块 visitedProcs;
 * - 最多需要重排 MaxBackends/2 个等待队列(一条软边至少两个等待者),
 *   展开后等待者总数不超过 MaxBackends;
 * - 约束最多 MaxBackends 条(这也决定了 DeadLockCheckRecurse 的递归
 *   深度上限);possibleConstraints 预留 4*MaxBackends 条,其中末尾
 *   MaxBackends 条固定留给 FindLockCycle 作输出。
 *
 * 【参数】无。【返回值】无(只设置各静态全局变量)。
 */
void
InitDeadLockChecking(void)
{
	MemoryContext oldcxt;

	/* Make sure allocations are permanent */
	oldcxt = MemoryContextSwitchTo(TopMemoryContext);

	/*
	 * FindLockCycle needs at most MaxBackends entries in visitedProcs[] and
	 * deadlockDetails[].
	 */
	visitedProcs = (PGPROC **) palloc(MaxBackends * sizeof(PGPROC *));
	deadlockDetails = (DEADLOCK_INFO *) palloc(MaxBackends * sizeof(DEADLOCK_INFO));

	/*
	 * TopoSort needs to consider at most MaxBackends wait-queue entries, and
	 * it needn't run concurrently with FindLockCycle.
	 */
	topoProcs = visitedProcs;	/* re-use this space */
	beforeConstraints = (int *) palloc(MaxBackends * sizeof(int));
	afterConstraints = (int *) palloc(MaxBackends * sizeof(int));

	/*
	 * We need to consider rearranging at most MaxBackends/2 wait queues
	 * (since it takes at least two waiters in a queue to create a soft edge),
	 * and the expanded form of the wait queues can't involve more than
	 * MaxBackends total waiters.
	 */
	waitOrders = (WAIT_ORDER *)
		palloc((MaxBackends / 2) * sizeof(WAIT_ORDER));
	waitOrderProcs = (PGPROC **) palloc(MaxBackends * sizeof(PGPROC *));

	/*
	 * Allow at most MaxBackends distinct constraints in a configuration. (Is
	 * this enough?  In practice it seems it should be, but I don't quite see
	 * how to prove it.  If we run out, we might fail to find a workable wait
	 * queue rearrangement even though one exists.)  NOTE that this number
	 * limits the maximum recursion depth of DeadLockCheckRecurse. Making it
	 * really big might potentially allow a stack-overflow problem.
	 */
	maxCurConstraints = MaxBackends;
	curConstraints = (EDGE *) palloc(maxCurConstraints * sizeof(EDGE));

	/*
	 * Allow up to 3*MaxBackends constraints to be saved without having to
	 * re-run TestConfiguration.  (This is probably more than enough, but we
	 * can survive if we run low on space by doing excess runs of
	 * TestConfiguration to re-compute constraint lists each time needed.) The
	 * last MaxBackends entries in possibleConstraints[] are reserved as
	 * output workspace for FindLockCycle.
	 */
	{
		StaticAssertDecl(MAX_BACKENDS_BITS <= (32 - 3),
						 "MAX_BACKENDS_BITS too big for * 4");
		maxPossibleConstraints = MaxBackends * 4;
		possibleConstraints =
			(EDGE *) palloc(maxPossibleConstraints * sizeof(EDGE));
	}

	MemoryContextSwitchTo(oldcxt);
}

/*
 * DeadLockCheck -- Checks for deadlocks for a given process
 *
 * This code looks for deadlocks involving the given process.  If any
 * are found, it tries to rearrange lock wait queues to resolve the
 * deadlock.  If resolution is impossible, return DS_HARD_DEADLOCK ---
 * the caller is then expected to abort the given proc's transaction.
 *
 * Caller must already have locked all partitions of the lock tables.
 *
 * On failure, deadlock details are recorded in deadlockDetails[] for
 * subsequent printing by DeadLockReport().  That activity is separate
 * because we don't want to do it while holding all those LWLocks.
 */
/*
 * DeadLockCheck
 *      (中文)为给定进程做死锁检测;若能消解,重排等待队列;否则判定硬死锁
 *
 * 【作用】这是死锁检测的对外入口(由 proc.c 在等锁超时后调用):
 * 1. 重置约束集合等状态;
 * 2. DeadLockCheckRecurse(proc) 递归搜索:为找到的每个软环尝试添加
 *    "反转软边"约束,直到某组约束完全消除死锁;
 * 3. 若找到可行方案,把 waitOrders[] 里的重排逐个应用到对应锁的等待
 *    队列上,并调用 ProcLockWakeup 让可能因此变可授予的等待者醒来;
 * 4. 若无论如何都有环(硬死锁),最后再跑一次 FindLockCycle,把环的
 *    细节填进 deadlockDetails[],供 DeadLockReport 使用,返回
 *    DS_HARD_DEADLOCK 让调用者牺牲本进程的事务。
 *
 * 【调用前置条件】调用者必须已持有锁表的全部分区锁(锁管理器的所有
 * LWLock),因此本函数内部不能再获取任何锁,也不能报错(唯一例外是
 * elog(FATAL),用于检测结果自相矛盾这种不可能情况)。
 *
 * 【返回值】DeadLockState 枚举:
 * - DS_HARD_DEADLOCK : 死锁无法消解,调用者应中止本事务(注意此时
 *                      已为 DeadLockReport 准备好细节);
 * - DS_SOFT_DEADLOCK : 通过重排等待队列消解了死锁(nWaitOrders > 0);
 * - DS_BLOCKED_BY_AUTOVACUUM : 未死锁,但本进程正被 autovacuum 硬阻塞
 *                      (调用者可考虑取消该 autovacuum);
 * - DS_NO_DEADLOCK    : 一切正常,没有死锁。
 */
DeadLockState
DeadLockCheck(PGPROC *proc)
{
	/* Initialize to "no constraints" */
	nCurConstraints = 0;
	nPossibleConstraints = 0;
	nWaitOrders = 0;

	/* Initialize to not blocked by an autovacuum worker */
	blocking_autovacuum_proc = NULL;

	/* Search for deadlocks and possible fixes */
	if (DeadLockCheckRecurse(proc))
	{
		/*
		 * Call FindLockCycle one more time, to record the correct
		 * deadlockDetails[] for the basic state with no rearrangements.
		 */
		int			nSoftEdges;

		TRACE_POSTGRESQL_DEADLOCK_FOUND();

		nWaitOrders = 0;
		if (!FindLockCycle(proc, possibleConstraints, &nSoftEdges))
			elog(FATAL, "deadlock seems to have disappeared");

		return DS_HARD_DEADLOCK;	/* cannot find a non-deadlocked state */
	}

	/* Apply any needed rearrangements of wait queues */
	for (int i = 0; i < nWaitOrders; i++)
	{
		LOCK	   *lock = waitOrders[i].lock;
		PGPROC	  **procs = waitOrders[i].procs;
		int			nProcs = waitOrders[i].nProcs;
		dclist_head *waitQueue = &lock->waitProcs;

		Assert(nProcs == dclist_count(waitQueue));

#ifdef DEBUG_DEADLOCK
		PrintLockQueue(lock, "DeadLockCheck:");
#endif

		/* Reset the queue and re-add procs in the desired order */
		dclist_init(waitQueue);
		for (int j = 0; j < nProcs; j++)
			dclist_push_tail(waitQueue, &procs[j]->waitLink);

#ifdef DEBUG_DEADLOCK
		PrintLockQueue(lock, "rearranged to:");
#endif

		/* See if any waiters for the lock can be woken up now */
		ProcLockWakeup(GetLocksMethodTable(lock), lock);
	}

	/* Return code tells caller if we had to escape a deadlock or not */
	if (nWaitOrders > 0)
		return DS_SOFT_DEADLOCK;
	else if (blocking_autovacuum_proc != NULL)
		return DS_BLOCKED_BY_AUTOVACUUM;
	else
		return DS_NO_DEADLOCK;
}

/*
 * Return the PGPROC of the autovacuum that's blocking a process.
 *
 * We reset the saved pointer as soon as we pass it back.
 */
/*
 * GetBlockingAutoVacuumPgproc
 *      (中文)取回"阻塞本进程的 autovacuum"的 PGPROC(一次性)
 *
 * 【作用】当 DeadLockCheck 返回 DS_BLOCKED_BY_AUTOVACUUM 时,调用者
 * 用本函数取回记录的那个 autovacuum 进程,以便决定是否给它发送取消
 * 信号。取出后内部指针立即清空(一次性读取语义,避免重复取消)。
 *
 * 【设计思想】为什么不直接把指针放进返回值:DeadLockCheck 的返回值
 * 是 DeadLockState 枚举,不便再带出指针;且"是否真的取消 autovacuum"
 * 由上层(ProcSleep 的调用链,最终是 lock.c 的等待逻辑)权衡决定——
 * 必须保证 autovacuum 有至少 deadlock_timeout 的宽限期,因此这里只
 * 负责安全地传递指针。
 *
 * 【参数】无。
 * 【返回值】记录的 autovacuum 的 PGPROC 指针;没有则返回 NULL。
 */
PGPROC *
GetBlockingAutoVacuumPgproc(void)
{
	PGPROC	   *ptr;

	ptr = blocking_autovacuum_proc;
	blocking_autovacuum_proc = NULL;

	return ptr;
}

/*
 * DeadLockCheckRecurse -- recursively search for valid orderings
 *
 * curConstraints[] holds the current set of constraints being considered
 * by an outer level of recursion.  Add to this each possible solution
 * constraint for any cycle detected at this level.
 *
 * Returns true if no solution exists.  Returns false if a deadlock-free
 * state is attainable, in which case waitOrders[] shows the required
 * rearrangements of lock wait queues (if any).
 */
/*
 * DeadLockCheckRecurse
 *      (中文)递归搜索"能消解死锁的约束组合"的尝试过程
 *
 * 【作用】在"当前约束集合"基础上继续搜索:
 * 1. TestConfiguration(proc) 检验当前配置:
 *    - 返回值 < 0:硬死锁或约束自相矛盾 → 无解,返回 true;
 *    - 返回值 0:配置合法、无死锁 → 找到解,返回 false;
 *    - 返回值 > 0:存在软环,返回其中一环的软边列表(写入
 *      possibleConstraints 尾部)。
 * 2. 若还有递归空间,依次把每条软边当作"新约束"加入 curConstraints
 *    后递归;只要任一分支成功就回溯返回成功。
 * 3. 全部失败则恢复 nPossibleConstraints 并返回 true(无解)。
 *
 * 【设计思想】这是典型的"回溯搜索":软环的每条软边都可能通过重排
 * 消除,而消除一条软边可能又引出新的软环(别的锁上),因此逐层尝试
 * 直到所有环都被打破。possibleConstraints 满了(savedList = false)时,
 * 不保存软边列表,而在下一层递归前重新调用 TestConfiguration 现场
 * 重算(结果必须一致,否则 FATAL——检测期间状态不允许变化)。
 * 注意递归深度受 maxCurConstraints(= MaxBackends)限制。
 *
 * 【参数】proc —— 死锁检测的起点进程(锁组组长)。
 * 【返回值】true = 无解(硬死锁);false = 找到无死锁配置(此时
 * waitOrders[] 给出所需的重排方案)。
 */
static bool
DeadLockCheckRecurse(PGPROC *proc)
{
	int			nEdges;
	int			oldPossibleConstraints;
	bool		savedList;
	int			i;

	nEdges = TestConfiguration(proc);
	if (nEdges < 0)
		return true;			/* hard deadlock --- no solution */
	if (nEdges == 0)
		return false;			/* good configuration found */
	if (nCurConstraints >= maxCurConstraints)
		return true;			/* out of room for active constraints? */
	oldPossibleConstraints = nPossibleConstraints;
	if (nPossibleConstraints + nEdges + MaxBackends <= maxPossibleConstraints)
	{
		/* We can save the edge list in possibleConstraints[] */
		nPossibleConstraints += nEdges;
		savedList = true;
	}
	else
	{
		/* Not room; will need to regenerate the edges on-the-fly */
		savedList = false;
	}

	/*
	 * Try each available soft edge as an addition to the configuration.
	 */
	for (i = 0; i < nEdges; i++)
	{
		if (!savedList && i > 0)
		{
			/* Regenerate the list of possible added constraints */
			if (nEdges != TestConfiguration(proc))
				elog(FATAL, "inconsistent results during deadlock check");
		}
		curConstraints[nCurConstraints] =
			possibleConstraints[oldPossibleConstraints + i];
		nCurConstraints++;
		if (!DeadLockCheckRecurse(proc))
			return false;		/* found a valid solution! */
		/* give up on that added constraint, try again */
		nCurConstraints--;
	}
	nPossibleConstraints = oldPossibleConstraints;
	return true;				/* no solution found */
}


/*--------------------
 * Test a configuration (current set of constraints) for validity.
 *
 * Returns:
 *		0: the configuration is good (no deadlocks)
 *	   -1: the configuration has a hard deadlock or is not self-consistent
 *		>0: the configuration has one or more soft deadlocks
 *
 * In the soft-deadlock case, one of the soft cycles is chosen arbitrarily
 * and a list of its soft edges is returned beginning at
 * possibleConstraints+nPossibleConstraints.  The return value is the
 * number of soft edges.
 *--------------------
 */
/*
 * TestConfiguration
 *      (中文)检验一组约束配置是否可行,并报告其中的软环
 *
 * 【作用】对"当前约束集合(curConstraints)"做两项检验:
 * 1. ExpandConstraints:把约束展开成各锁等待队列的具体重排;若约束
 *    互相矛盾(例如要求 A 同时排在 B 前又排在 B 后),返回 -1;
 * 2. FindLockCycle:分别在每个约束的 waiter/blocker、以及起点进程上
 *    检查是否还有环(先查约束涉及的进程,最后查起点——因为若起点
 *    还有软环,应当优先处理它的)。找到软环就把环的软边列表写进
 *    possibleConstraints 的末尾(由调用者保管),返回软边条数。
 *
 * 【返回值】0 = 配置合法无死锁;>0 = 存在软死锁,返回值是所选软环的
 * 软边条数(列表在 possibleConstraints+nPossibleConstraints 处);
 * -1 = 硬死锁或配置自相矛盾。
 */
static int
TestConfiguration(PGPROC *startProc)
{
	int			softFound = 0;
	EDGE	   *softEdges = possibleConstraints + nPossibleConstraints;
	int			nSoftEdges;
	int			i;

	/*
	 * Make sure we have room for FindLockCycle's output.
	 */
	if (nPossibleConstraints + MaxBackends > maxPossibleConstraints)
		return -1;

	/*
	 * Expand current constraint set into wait orderings.  Fail if the
	 * constraint set is not self-consistent.
	 */
	if (!ExpandConstraints(curConstraints, nCurConstraints))
		return -1;

	/*
	 * Check for cycles involving startProc or any of the procs mentioned in
	 * constraints.  We check startProc last because if it has a soft cycle
	 * still to be dealt with, we want to deal with that first.
	 */
	for (i = 0; i < nCurConstraints; i++)
	{
		if (FindLockCycle(curConstraints[i].waiter, softEdges, &nSoftEdges))
		{
			if (nSoftEdges == 0)
				return -1;		/* hard deadlock detected */
			softFound = nSoftEdges;
		}
		if (FindLockCycle(curConstraints[i].blocker, softEdges, &nSoftEdges))
		{
			if (nSoftEdges == 0)
				return -1;		/* hard deadlock detected */
			softFound = nSoftEdges;
		}
	}
	if (FindLockCycle(startProc, softEdges, &nSoftEdges))
	{
		if (nSoftEdges == 0)
			return -1;			/* hard deadlock detected */
		softFound = nSoftEdges;
	}
	return softFound;
}


/*
 * FindLockCycle -- basic check for deadlock cycles
 *
 * Scan outward from the given proc to see if there is a cycle in the
 * waits-for graph that includes this proc.  Return true if a cycle
 * is found, else false.  If a cycle is found, we return a list of
 * the "soft edges", if any, included in the cycle.  These edges could
 * potentially be eliminated by rearranging wait queues.  We also fill
 * deadlockDetails[] with information about the detected cycle; this info
 * is not used by the deadlock algorithm itself, only to print a useful
 * message after failing.
 *
 * Since we need to be able to check hypothetical configurations that would
 * exist after wait queue rearrangement, the routine pays attention to the
 * table of hypothetical queue orders in waitOrders[].  These orders will
 * be believed in preference to the actual ordering seen in the locktable.
 */
/*
 * FindLockCycle
 *      (中文)从给定进程出发,检查等待图中是否存在包含它的死锁环
 *
 * 【作用】这是"基本环检测"的包装:重置 visitedProcs / deadlockDetails
 * 计数后,以 checkProc 为起点做深度优先搜索。找到环返回 true,并把环
 * 里的软边(若有)填入 softEdges 输出数组、把环的细节填进
 * deadlockDetails[];无环返回 false。
 *
 * 【设计思想】搜索会"相信"waitOrders[] 中假想的重排顺序,而优先于
 * 锁表里的真实顺序——这样可以在"假设约束被满足"的假设配置下做检测,
 * 支持死锁消解的试错过程。softEdges 输出区由调用者从
 * possibleConstraints 中划出,本函数只负责填写。
 *
 * 【参数】
 *   checkProc  —— 检查起点(检测是否有环包含它);
 *   softEdges  —— 输出参数:环中含的软边数组;
 *   nSoftEdges —— 输出参数:软边条数。
 * 【返回值】true = 找到包含起点的环(硬死锁,或含软边的软死锁);
 * false = 无环。
 */
static bool
FindLockCycle(PGPROC *checkProc,
			  EDGE *softEdges,	/* output argument */
			  int *nSoftEdges)	/* output argument */
{
	nVisitedProcs = 0;
	nDeadlockDetails = 0;
	*nSoftEdges = 0;
	return FindLockCycleRecurse(checkProc, 0, softEdges, nSoftEdges);
}

/*
 * FindLockCycleRecurse
 *      (中文)环检测的深度优先搜索主循环(逐进程推进)
 *
 * 【作用】以 checkProc 为当前节点继续 DFS:
 * - 若它是锁组成员,先提升为组长(整组用同一代表,见文件头注释);
 * - 查 visitedProcs:若已访问过:
 *   - 是起点(下标 0):构成包含起点的环!记录环长(nDeadlockDetails =
 *     depth,之后由外层各层回溯时填充每条边的细节),返回 true;
 *   - 不是起点:是"回到了环里的其他点",说明这个环不经过起点,对
 *     本次检测而言不算死锁,返回 false 继续;
 * - 否则标记已访问,然后找它的出边:
 *   1) 若 checkProc 自己正在等待锁,遍历它被阻塞的所有对象
 *      (FindLockCycleRecurseMember);
 *   2) 即使 checkProc 没在等,若它所属的锁组里有别的组员在等,那些
 *      等待也算本组的出边——例如组 {A1,A2}、{B1,B2} 中 A1 等 B1、
 *      B2 等 A2,即便 B1 和 A2 都没在等任何东西,整体仍是死锁。
 *
 * 【参数】
 *   checkProc  —— 当前考察的进程(进入后可能被提升为组长);
 *   depth      —— 当前在环中的深度(用于写 deadlockDetails 的下标,
 *                  也用于断言环长不超过 MaxBackends);
 *   softEdges / nSoftEdges —— 软边输出(透传给递归子调用)。
 * 【返回值】true = 下游发现包含起点的环;false = 无。
 */
static bool
FindLockCycleRecurse(PGPROC *checkProc,
					 int depth,
					 EDGE *softEdges,	/* output argument */
					 int *nSoftEdges)	/* output argument */
{
	int			i;
	dlist_iter	iter;

	/*
	 * If this process is a lock group member, check the leader instead. (Note
	 * that we might be the leader, in which case this is a no-op.)
	 */	if (checkProc->lockGroupLeader != NULL)
		checkProc = checkProc->lockGroupLeader;

	/*
	 * Have we already seen this proc?
	 */
	for (i = 0; i < nVisitedProcs; i++)
	{
		if (visitedProcs[i] == checkProc)
		{
			/* If we return to starting point, we have a deadlock cycle */
			if (i == 0)
			{
				/*
				 * record total length of cycle --- outer levels will now fill
				 * deadlockDetails[]
				 */
				Assert(depth <= MaxBackends);
				nDeadlockDetails = depth;

				return true;
			}

			/*
			 * Otherwise, we have a cycle but it does not include the start
			 * point, so say "no deadlock".
			 */
			return false;
		}
	}
	/* Mark proc as seen */
	Assert(nVisitedProcs < MaxBackends);
	visitedProcs[nVisitedProcs++] = checkProc;

	/*
	 * If the process is waiting, there is an outgoing waits-for edge to each
	 * process that blocks it.
	 */
	if (!dlist_node_is_detached(&checkProc->waitLink) &&
		FindLockCycleRecurseMember(checkProc, checkProc, depth, softEdges,
								   nSoftEdges))
		return true;

	/*
	 * If the process is not waiting, there could still be outgoing waits-for
	 * edges if it is part of a lock group, because other members of the lock
	 * group might be waiting even though this process is not.  (Given lock
	 * groups {A1, A2} and {B1, B2}, if A1 waits for B1 and B2 waits for A2,
	 * that is a deadlock even neither of B1 and A2 are waiting for anything.)
	 */
	dlist_foreach(iter, &checkProc->lockGroupMembers)
	{
		PGPROC	   *memberProc;

		memberProc = dlist_container(PGPROC, lockGroupLink, iter.cur);

		if (!dlist_node_is_detached(&memberProc->waitLink) && memberProc->waitLock != NULL &&
			memberProc != checkProc &&
			FindLockCycleRecurseMember(memberProc, checkProc, depth, softEdges,
									   nSoftEdges))
			return true;
	}

	return false;
}

/*
 * FindLockCycleRecurseMember
 *      (中文)展开"一个等待中的进程"的全部出边:硬边与软边
 *
 * 【作用】checkProc 正在等待 lock(checkProc->waitLock),本函数找出
 * 所有阻塞它的进程并逐个递归:
 * 1. 硬边:遍历该锁的 procLocks 列表,凡是"持有与等待模式冲突的锁"
 *    且与 checkProcLeader 不同锁组的进程,构成一条硬边(递归下去);
 * 2. 软边:检查排在 checkProc 之前、请求模式与等待模式冲突的等待者
 *    (若 waitOrders[] 里有这把锁的假想重排,按假想顺序,否则按真实
 *    等待队列顺序),构成软边(递归下去,并把这条件记入 softEdges)。
 * 递归返回 true 时,把"checkProc 等这把锁"这条边的快照填入
 * deadlockDetails[depth],再向上层返回 true。
 *
 * 【设计细节】
 * - 特殊对象:关系扩展锁(LOCKTAG_RELATION_EXTEND)永远不会参与真正的
 *   死锁环(持它期间不允许再等别的重锁,见 lock.c 的断言),直接返回
 *   false,节省一次无谓的搜索;
 * - 硬边优先于软边:若某进程既硬阻塞又软阻塞本进程,按硬边处理
 *   (软边可消解,硬边不可);
 * - 若阻塞者恰好是 autovacuum 且被阻塞者是本进程(MyProc),记录到
 *   blocking_autovacuum_proc,供上层决定是否取消它(只记直接阻塞者,
 *   保证 autovacuum 至少得到 deadlock_timeout 的宽限期);
 * - 锁组处理:检查者恒用组长比较"是否同组";软边按"同组相邻"原则
 *   提前终止扫描(TopoSort 保证同组成员在假想队列中相邻)。
 *
 * 【参数】
 *   checkProc        —— 正在等待的进程(不是组长);
 *   checkProcLeader  —— 它所属锁组的组长;
 *   depth            —— 环深度;
 *   softEdges / nSoftEdges —— 软边输出。
 * 【返回值】true = 下游发现包含起点的环;false = 无。
 */
static bool
FindLockCycleRecurseMember(PGPROC *checkProc,
						   PGPROC *checkProcLeader,
						   int depth,
						   EDGE *softEdges, /* output argument */
						   int *nSoftEdges) /* output argument */
{
	PGPROC	   *proc;
	LOCK	   *lock = checkProc->waitLock;
	dlist_iter	proclock_iter;
	LockMethod	lockMethodTable;
	int			conflictMask;
	int			i;
	int			numLockModes,
				lm;

	/*
	 * The relation extension lock can never participate in actual deadlock
	 * cycle.  See Assert in LockAcquireExtended.  So, there is no advantage
	 * in checking wait edges from it.
	 */
	if (LOCK_LOCKTAG(*lock) == LOCKTAG_RELATION_EXTEND)
		return false;

	lockMethodTable = GetLocksMethodTable(lock);
	numLockModes = lockMethodTable->numLockModes;
	conflictMask = lockMethodTable->conflictTab[checkProc->waitLockMode];

	/*
	 * Scan for procs that already hold conflicting locks.  These are "hard"
	 * edges in the waits-for graph.
	 */
	dlist_foreach(proclock_iter, &lock->procLocks)
	{
		PROCLOCK   *proclock = dlist_container(PROCLOCK, lockLink, proclock_iter.cur);
		PGPROC	   *leader;

		proc = proclock->tag.myProc;
		leader = proc->lockGroupLeader == NULL ? proc : proc->lockGroupLeader;

		/* A proc never blocks itself or any other lock group member */
		if (leader != checkProcLeader)
		{
			for (lm = 1; lm <= numLockModes; lm++)
			{
				if ((proclock->holdMask & LOCKBIT_ON(lm)) &&
					(conflictMask & LOCKBIT_ON(lm)))
				{
					/* This proc hard-blocks checkProc */
					if (FindLockCycleRecurse(proc, depth + 1,
											 softEdges, nSoftEdges))
					{
						/* fill deadlockDetails[] */
						DEADLOCK_INFO *info = &deadlockDetails[depth];

						info->locktag = lock->tag;
						info->lockmode = checkProc->waitLockMode;
						info->pid = checkProc->pid;

						return true;
					}

					/*
					 * No deadlock here, but see if this proc is an autovacuum
					 * that is directly hard-blocking our own proc.  If so,
					 * report it so that the caller can send a cancel signal
					 * to it, if appropriate.  If there's more than one such
					 * proc, it's indeterminate which one will be reported.
					 *
					 * We don't touch autovacuums that are indirectly blocking
					 * us; it's up to the direct blockee to take action.  This
					 * rule simplifies understanding the behavior and ensures
					 * that an autovacuum won't be canceled with less than
					 * deadlock_timeout grace period.
					 *
					 * Note we read statusFlags without any locking.  This is
					 * OK only for checking the PROC_IS_AUTOVACUUM flag,
					 * because that flag is set at process start and never
					 * reset.  There is logic elsewhere to avoid canceling an
					 * autovacuum that is working to prevent XID wraparound
					 * problems (which needs to read a different statusFlags
					 * bit), but we don't do that here to avoid grabbing
					 * ProcArrayLock.
					 */
					if (checkProc == MyProc &&
						proc->statusFlags & PROC_IS_AUTOVACUUM)
						blocking_autovacuum_proc = proc;

					/* We're done looking at this proclock */
					break;
				}
			}
		}
	}

	/*
	 * Scan for procs that are ahead of this one in the lock's wait queue.
	 * Those that have conflicting requests soft-block this one.  This must be
	 * done after the hard-block search, since if another proc both hard- and
	 * soft-blocks this one, we want to call it a hard edge.
	 *
	 * If there is a proposed re-ordering of the lock's wait order, use that
	 * rather than the current wait order.
	 */
	for (i = 0; i < nWaitOrders; i++)
	{
		if (waitOrders[i].lock == lock)
			break;
	}

	if (i < nWaitOrders)
	{
		/* Use the given hypothetical wait queue order */
		PGPROC	  **procs = waitOrders[i].procs;
		int			queue_size = waitOrders[i].nProcs;

		for (i = 0; i < queue_size; i++)
		{
			PGPROC	   *leader;

			proc = procs[i];
			leader = proc->lockGroupLeader == NULL ? proc :
				proc->lockGroupLeader;

			/*
			 * TopoSort will always return an ordering with group members
			 * adjacent to each other in the wait queue (see comments
			 * therein). So, as soon as we reach a process in the same lock
			 * group as checkProc, we know we've found all the conflicts that
			 * precede any member of the lock group lead by checkProcLeader.
			 */
			if (leader == checkProcLeader)
				break;

			/* Is there a conflict with this guy's request? */
			if ((LOCKBIT_ON(proc->waitLockMode) & conflictMask) != 0)
			{
				/* This proc soft-blocks checkProc */
				if (FindLockCycleRecurse(proc, depth + 1,
										 softEdges, nSoftEdges))
				{
					/* fill deadlockDetails[] */
					DEADLOCK_INFO *info = &deadlockDetails[depth];

					info->locktag = lock->tag;
					info->lockmode = checkProc->waitLockMode;
					info->pid = checkProc->pid;

					/*
					 * Add this edge to the list of soft edges in the cycle
					 */
					Assert(*nSoftEdges < MaxBackends);
					softEdges[*nSoftEdges].waiter = checkProcLeader;
					softEdges[*nSoftEdges].blocker = leader;
					softEdges[*nSoftEdges].lock = lock;
					(*nSoftEdges)++;
					return true;
				}
			}
		}
	}
	else
	{
		PGPROC	   *lastGroupMember = NULL;
		dlist_iter	proc_iter;
		dclist_head *waitQueue;

		/* Use the true lock wait queue order */
		waitQueue = &lock->waitProcs;

		/*
		 * Find the last member of the lock group that is present in the wait
		 * queue.  Anything after this is not a soft lock conflict. If group
		 * locking is not in use, then we know immediately which process we're
		 * looking for, but otherwise we've got to search the wait queue to
		 * find the last process actually present.
		 */
		if (checkProc->lockGroupLeader == NULL)
			lastGroupMember = checkProc;
		else
		{
			dclist_foreach(proc_iter, waitQueue)
			{
				proc = dlist_container(PGPROC, waitLink, proc_iter.cur);

				if (proc->lockGroupLeader == checkProcLeader)
					lastGroupMember = proc;
			}
			Assert(lastGroupMember != NULL);
		}

		/*
		 * OK, now rescan (or scan) the queue to identify the soft conflicts.
		 */
		dclist_foreach(proc_iter, waitQueue)
		{
			PGPROC	   *leader;

			proc = dlist_container(PGPROC, waitLink, proc_iter.cur);

			leader = proc->lockGroupLeader == NULL ? proc :
				proc->lockGroupLeader;

			/* Done when we reach the target proc */
			if (proc == lastGroupMember)
				break;

			/* Is there a conflict with this guy's request? */
			if ((LOCKBIT_ON(proc->waitLockMode) & conflictMask) != 0 &&
				leader != checkProcLeader)
			{
				/* This proc soft-blocks checkProc */
				if (FindLockCycleRecurse(proc, depth + 1,
										 softEdges, nSoftEdges))
				{
					/* fill deadlockDetails[] */
					DEADLOCK_INFO *info = &deadlockDetails[depth];

					info->locktag = lock->tag;
					info->lockmode = checkProc->waitLockMode;
					info->pid = checkProc->pid;

					/*
					 * Add this edge to the list of soft edges in the cycle
					 */
					Assert(*nSoftEdges < MaxBackends);
					softEdges[*nSoftEdges].waiter = checkProcLeader;
					softEdges[*nSoftEdges].blocker = leader;
					softEdges[*nSoftEdges].lock = lock;
					(*nSoftEdges)++;
					return true;
				}
			}
		}
	}

	/*
	 * No conflict detected here.
	 */
	return false;
}


/*
 * ExpandConstraints -- expand a list of constraints into a set of
 *		specific new orderings for affected wait queues
 *
 * Input is a list of soft edges to be reversed.  The output is a list
 * of nWaitOrders WAIT_ORDER structs in waitOrders[], with PGPROC array
 * workspace in waitOrderProcs[].
 *
 * Returns true if able to build an ordering that satisfies all the
 * constraints, false if not (there are contradictory constraints).
 */
/*
 * ExpandConstraints
 *      (中文)把约束列表展开成各受影响等待队列的具体重排方案
 *
 * 【作用】输入是"需要反转的软边"列表,输出是 waitOrders[] 中的若干
 * WAIT_ORDER(每个被约束的锁一个,队列内容的工作区在 waitOrderProcs[])。
 * 任何一把锁的约束无法同时满足时返回 false(约束矛盾)。
 *
 * 【设计思想】
 * - 倒序遍历约束列表:最后加入的约束最可能失败(前面的组合已经成立),
 *   先检验它,可尽早发现矛盾;
 * - 同一把锁的多条约束合并到同一个 WAIT_ORDER,只做一次 TopoSort;
 *   TopoSort 只需看到本锁及更早的约束(更晚的约束必然属于别的锁),
 *   因此传 i+1 个约束即可。
 *
 * 【参数】
 *   constraints  —— 约束(软边)数组;
 *   nConstraints —— 约束条数。
 * 【返回值】true = 所有约束可同时满足(结果在 waitOrders[]);
 * false = 存在矛盾约束。
 */
static bool
ExpandConstraints(EDGE *constraints,
				  int nConstraints)
{
	int			nWaitOrderProcs = 0;
	int			i,
				j;

	nWaitOrders = 0;

	/*
	 * Scan constraint list backwards.  This is because the last-added
	 * constraint is the only one that could fail, and so we want to test it
	 * for inconsistency first.
	 */
	for (i = nConstraints; --i >= 0;)
	{
		LOCK	   *lock = constraints[i].lock;

		/* Did we already make a list for this lock? */
		for (j = nWaitOrders; --j >= 0;)
		{
			if (waitOrders[j].lock == lock)
				break;
		}
		if (j >= 0)
			continue;
		/* No, so allocate a new list */
		waitOrders[nWaitOrders].lock = lock;
		waitOrders[nWaitOrders].procs = waitOrderProcs + nWaitOrderProcs;
		waitOrders[nWaitOrders].nProcs = dclist_count(&lock->waitProcs);
		nWaitOrderProcs += dclist_count(&lock->waitProcs);
		Assert(nWaitOrderProcs <= MaxBackends);

		/*
		 * Do the topo sort.  TopoSort need not examine constraints after this
		 * one, since they must be for different locks.
		 */
		if (!TopoSort(lock, constraints, i + 1,
					  waitOrders[nWaitOrders].procs))
			return false;
		nWaitOrders++;
	}
	return true;
}


/*
 * TopoSort -- topological sort of a wait queue
 *
 * Generate a re-ordering of a lock's wait queue that satisfies given
 * constraints about certain procs preceding others.  (Each such constraint
 * is a fact of a partial ordering.)  Minimize rearrangement of the queue
 * not needed to achieve the partial ordering.
 *
 * This is a lot simpler and slower than, for example, the topological sort
 * algorithm shown in Knuth's Volume 1.  However, Knuth's method doesn't
 * try to minimize the damage to the existing order.  In practice we are
 * not likely to be working with more than a few constraints, so the apparent
 * slowness of the algorithm won't really matter.
 *
 * The initial queue ordering is taken directly from the lock's wait queue.
 * The output is an array of PGPROC pointers, of length equal to the lock's
 * wait queue length (the caller is responsible for providing this space).
 * The partial order is specified by an array of EDGE structs.  Each EDGE
 * is one that we need to reverse, therefore the "waiter" must appear before
 * the "blocker" in the output array.  The EDGE array may well contain
 * edges associated with other locks; these should be ignored.
 *
 * Returns true if able to build an ordering that satisfies all the
 * constraints, false if not (there are contradictory constraints).
 */
/*
 * TopoSort
 *      (中文)对一把锁的等待队列做拓扑排序,满足"先来后到"约束并尽量少动
 *
 * 【作用】把 lock 的等待队列重排成满足给定约束的顺序。约束的语义:
 * 每条 EDGE 的"waiter 必须排在 blocker 前面"(即反转原来的等待顺序)。
 * 与约束无关的锁的边会被忽略。输出 ordering[] 数组(长度等于队列长度,
 * 空间由调用者提供),返回是否可行。
 *
 * 【算法与设计思想】
 * 1. 先把真实队列按原顺序装入 topoProcs[];
 * 2. 对每条约束,在 topoProcs 里找"等待方组"和"阻塞方组"的代表下标:
 *    - 每个锁组在队列里取"最后一个成员"作代表,其余成员标记为 -1
 *      (不单独排序,随组长一起整体输出);
 *    - 找不到等待方或阻塞方(该约束与这把锁无关)就跳过;
 *    - 用 beforeConstraints[](还需满足几个"必须先出"约束)和
 *      afterConstraints[](本进程被谁约束的链表)登记偏序;
 * 3. 从后往前输出:每轮挑一个 beforeConstraints == 0 的进程,连同其
 *    锁组的所有成员一起输出(同组成员必须相邻——否则要么同时冲突
 *    二者、必然无解,要么只冲突其一、与"相邻"等价),然后把它们对
 *    别人的"先出"贡献从 beforeConstraints 里减去;
 * 4. 某轮找不到可输出的进程说明约束成环(矛盾),返回 false。
 * 该算法比 Knuth 的教科书拓扑排序慢,但能最小化对原有顺序的扰动,
 * 而实际约束数量很少,慢一点无所谓。
 *
 * 【参数】
 *   lock         —— 要重排的锁;
 *   constraints  —— 约束数组(可能包含别的锁的边,自动忽略);
 *   nConstraints —— 传入的约束条数(只考察前 nConstraints 条);
 *   ordering     —— 输出参数:重排后的等待者指针数组。
 * 【返回值】true = 重排成功;false = 约束矛盾。
 */
static bool
TopoSort(LOCK *lock,
		 EDGE *constraints,
		 int nConstraints,
		 PGPROC **ordering)		/* output argument */
{
	dclist_head *waitQueue = &lock->waitProcs;
	int			queue_size = dclist_count(waitQueue);
	PGPROC	   *proc;
	int			i,
				j,
				jj,
				k,
				kk,
				last;
	dlist_iter	proc_iter;

	/* First, fill topoProcs[] array with the procs in their current order */
	i = 0;
	dclist_foreach(proc_iter, waitQueue)
	{
		proc = dlist_container(PGPROC, waitLink, proc_iter.cur);
		topoProcs[i++] = proc;
	}
	Assert(i == queue_size);

	/*
	 * Scan the constraints, and for each proc in the array, generate a count
	 * of the number of constraints that say it must be before something else,
	 * plus a list of the constraints that say it must be after something
	 * else. The count for the j'th proc is stored in beforeConstraints[j],
	 * and the head of its list in afterConstraints[j].  Each constraint
	 * stores its list link in constraints[i].link (note any constraint will
	 * be in just one list). The array index for the before-proc of the i'th
	 * constraint is remembered in constraints[i].pred.
	 *
	 * Note that it's not necessarily the case that every constraint affects
	 * this particular wait queue.  Prior to group locking, a process could be
	 * waiting for at most one lock.  But a lock group can be waiting for
	 * zero, one, or multiple locks.  Since topoProcs[] is an array of the
	 * processes actually waiting, while constraints[] is an array of group
	 * leaders, we've got to scan through topoProcs[] for each constraint,
	 * checking whether both a waiter and a blocker for that group are
	 * present.  If so, the constraint is relevant to this wait queue; if not,
	 * it isn't.
	 */
	MemSet(beforeConstraints, 0, queue_size * sizeof(int));
	MemSet(afterConstraints, 0, queue_size * sizeof(int));
	for (i = 0; i < nConstraints; i++)
	{
		/*
		 * Find a representative process that is on the lock queue and part of
		 * the waiting lock group.  This may or may not be the leader, which
		 * may or may not be waiting at all.  If there are any other processes
		 * in the same lock group on the queue, set their number of
		 * beforeConstraints to -1 to indicate that they should be emitted
		 * with their groupmates rather than considered separately.
		 *
		 * In this loop and the similar one just below, it's critical that we
		 * consistently select the same representative member of any one lock
		 * group, so that all the constraints are associated with the same
		 * proc, and the -1's are only associated with not-representative
		 * members.  We select the last one in the topoProcs array.
		 */
		proc = constraints[i].waiter;
		Assert(proc != NULL);
		jj = -1;
		for (j = queue_size; --j >= 0;)
		{
			PGPROC	   *waiter = topoProcs[j];

			if (waiter == proc || waiter->lockGroupLeader == proc)
			{
				Assert(waiter->waitLock == lock);
				if (jj == -1)
					jj = j;
				else
				{
					Assert(beforeConstraints[j] <= 0);
					beforeConstraints[j] = -1;
				}
			}
		}

		/* If no matching waiter, constraint is not relevant to this lock. */
		if (jj < 0)
			continue;

		/*
		 * Similarly, find a representative process that is on the lock queue
		 * and waiting for the blocking lock group.  Again, this could be the
		 * leader but does not need to be.
		 */
		proc = constraints[i].blocker;
		Assert(proc != NULL);
		kk = -1;
		for (k = queue_size; --k >= 0;)
		{
			PGPROC	   *blocker = topoProcs[k];

			if (blocker == proc || blocker->lockGroupLeader == proc)
			{
				Assert(blocker->waitLock == lock);
				if (kk == -1)
					kk = k;
				else
				{
					Assert(beforeConstraints[k] <= 0);
					beforeConstraints[k] = -1;
				}
			}
		}

		/* If no matching blocker, constraint is not relevant to this lock. */
		if (kk < 0)
			continue;

		Assert(beforeConstraints[jj] >= 0);
		beforeConstraints[jj]++;	/* waiter must come before */
		/* add this constraint to list of after-constraints for blocker */
		constraints[i].pred = jj;
		constraints[i].link = afterConstraints[kk];
		afterConstraints[kk] = i + 1;
	}

	/*--------------------
	 * Now scan the topoProcs array backwards.  At each step, output the
	 * last proc that has no remaining before-constraints plus any other
	 * members of the same lock group; then decrease the beforeConstraints
	 * count of each of the procs it was constrained against.
	 * i = index of ordering[] entry we want to output this time
	 * j = search index for topoProcs[]
	 * k = temp for scanning constraint list for proc j
	 * last = last non-null index in topoProcs (avoid redundant searches)
	 *--------------------
	 */
	last = queue_size - 1;
	for (i = queue_size - 1; i >= 0;)
	{
		int			c;
		int			nmatches = 0;

		/* Find next candidate to output */
		while (topoProcs[last] == NULL)
			last--;
		for (j = last; j >= 0; j--)
		{
			if (topoProcs[j] != NULL && beforeConstraints[j] == 0)
				break;
		}

		/* If no available candidate, topological sort fails */
		if (j < 0)
			return false;

		/*
		 * Output everything in the lock group.  There's no point in
		 * outputting an ordering where members of the same lock group are not
		 * consecutive on the wait queue: if some other waiter is between two
		 * requests that belong to the same group, then either it conflicts
		 * with both of them and is certainly not a solution; or it conflicts
		 * with at most one of them and is thus isomorphic to an ordering
		 * where the group members are consecutive.
		 */
		proc = topoProcs[j];
		if (proc->lockGroupLeader != NULL)
			proc = proc->lockGroupLeader;
		Assert(proc != NULL);
		for (c = 0; c <= last; ++c)
		{
			if (topoProcs[c] == proc || (topoProcs[c] != NULL &&
										 topoProcs[c]->lockGroupLeader == proc))
			{
				ordering[i - nmatches] = topoProcs[c];
				topoProcs[c] = NULL;
				++nmatches;
			}
		}
		Assert(nmatches > 0);
		i -= nmatches;

		/* Update beforeConstraints counts of its predecessors */
		for (k = afterConstraints[j]; k > 0; k = constraints[k - 1].link)
			beforeConstraints[constraints[k - 1].pred]--;
	}

	/* Done */
	return true;
}

/* (中文)调试辅助函数(仅在 DEBUG_DEADLOCK 编译时启用):把锁的等待队列
 * 中所有进程的 PID 打成一串,前面加上调用者给的标记(如 "DeadLockCheck:"
 * 与 "rearranged to:"),用于肉眼对比重排前后的队列差异。 */
#ifdef DEBUG_DEADLOCK
static void
PrintLockQueue(LOCK *lock, const char *info)
{
	dclist_head *waitQueue = &lock->waitProcs;
	dlist_iter	proc_iter;

	printf("%s lock %p queue ", info, lock);

	dclist_foreach(proc_iter, waitQueue)
	{
		PGPROC	   *proc = dlist_container(PGPROC, waitLink, proc_iter.cur);

		printf(" %d", proc->pid);
	}
	printf("\n");
	fflush(stdout);
}
#endif

/*
 * Report a detected deadlock, with available details.
 */
/*
 * DeadLockReport
 *      (中文)报告已检测到的死锁(生成详细错误信息并抛 ERROR)
 *
 * 【作用】在死锁已确认、且已释放锁表分区锁之后调用(不能一边持着
 * 全部分区锁一边 elog)。利用 deadlockDetails[] 生成两套信息:
 * - 给客户端(clientbuf):逐行列出"进程 X 在 <对象> 上等待 <锁模式>,
 *   被进程 Y 阻塞",其中环是首尾相接的(最后一个等待第一个);
 * - 给服务器日志(logbuf):在上述内容之后,再为每个进程附加其当前
 *   查询语句(pgstat_get_backend_current_activity),帮助 DBA 定位。
 * 最后调用 pgstat_report_deadlock 计入统计,然后 ereport(ERROR)
 * 以 ERRCODE_T_R_DEADLOCK_DETECTED 抛出"deadlock detected"。
 *
 * 【设计思想】为什么报告用纯值快照而不直接引用 LOCK/PGPROC:检测时
 * 持有的全部分区锁在检测后立即释放,再打印时共享对象可能已被回收,
 * 指针失效;故检测阶段就提取出全部所需信息(见 DEADLOCK_INFO)。
 * 锁对象名称用 DescribeLockTag 打印数值(表 OID 等),不查系统目录——
 * 报告死锁的场合再去拿系统目录锁可能引发新的问题。
 *
 * 【参数】无。【返回值】无(以 ereport(ERROR) 告终,不返回)。
 */
void
DeadLockReport(void)
{
	StringInfoData clientbuf;	/* errdetail for client */
	StringInfoData logbuf;		/* errdetail for server log */
	StringInfoData locktagbuf;
	int			i;

	initStringInfo(&clientbuf);
	initStringInfo(&logbuf);
	initStringInfo(&locktagbuf);

	/* Generate the "waits for" lines sent to the client */
	for (i = 0; i < nDeadlockDetails; i++)
	{
		DEADLOCK_INFO *info = &deadlockDetails[i];
		int			nextpid;

		/* The last proc waits for the first one... */
		if (i < nDeadlockDetails - 1)
			nextpid = info[1].pid;
		else
			nextpid = deadlockDetails[0].pid;

		/* reset locktagbuf to hold next object description */
		resetStringInfo(&locktagbuf);

		DescribeLockTag(&locktagbuf, &info->locktag);

		if (i > 0)
			appendStringInfoChar(&clientbuf, '\n');

		appendStringInfo(&clientbuf,
						 _("Process %d waits for %s on %s; blocked by process %d."),
						 info->pid,
						 GetLockmodeName(info->locktag.locktag_lockmethodid,
										 info->lockmode),
						 locktagbuf.data,
						 nextpid);
	}

	/* Duplicate all the above for the server ... */
	appendBinaryStringInfo(&logbuf, clientbuf.data, clientbuf.len);

	/* ... and add info about query strings */
	for (i = 0; i < nDeadlockDetails; i++)
	{
		DEADLOCK_INFO *info = &deadlockDetails[i];

		appendStringInfoChar(&logbuf, '\n');

		appendStringInfo(&logbuf,
						 _("Process %d: %s"),
						 info->pid,
						 pgstat_get_backend_current_activity(info->pid, false));
	}

	pgstat_report_deadlock();

	ereport(ERROR,
			(errcode(ERRCODE_T_R_DEADLOCK_DETECTED),
			 errmsg("deadlock detected"),
			 errdetail_internal("%s", clientbuf.data),
			 errdetail_log("%s", logbuf.data),
			 errhint("See server log for query details.")));
}

/*
 * RememberSimpleDeadLock: set up info for DeadLockReport when ProcSleep
 * detects a trivial (two-way) deadlock.  proc1 wants to block for lockmode
 * on lock, but proc2 is already waiting and would be blocked by proc1.
 */
/*
 * RememberSimpleDeadLock
 *      (中文)记录 ProcSleep 发现的"两进程直接死锁"细节
 *
 * 【作用】有些死锁无需跑完整检测:proc1 想等 lock 上的 lockmode,但
 * proc2 已经在等这把锁,而 proc2 的等待会被 proc1 阻塞(proc1 已持有
 * 或即将持有与之冲突的锁)——这是最朴素的两方死锁。此时 ProcSleep
 * 直接调用本函数,把两条边的快照写进 deadlockDetails[0..1]
 * (proc1 等 proc2 的锁 / proc2 等 proc1 的锁),nDeadlockDetails = 2,
 * 之后统一由 DeadLockReport 打印。
 *
 * 【参数】
 *   proc1    —— 想要锁的进程;
 *   lockmode —— proc1 想要的锁模式;
 *   lock     —— proc1 想要的锁;
 *   proc2    —— 已经在该锁上等待、且会被 proc1 阻塞的进程。
 * 【返回值】无(写全局 deadlockDetails)。
 */
void
RememberSimpleDeadLock(PGPROC *proc1,
					   LOCKMODE lockmode,
					   LOCK *lock,
					   PGPROC *proc2)
{
	DEADLOCK_INFO *info = &deadlockDetails[0];

	info->locktag = lock->tag;
	info->lockmode = lockmode;
	info->pid = proc1->pid;
	info++;
	info->locktag = proc2->waitLock->tag;
	info->lockmode = proc2->waitLockMode;
	info->pid = proc2->pid;
	nDeadlockDetails = 2;
}
