/*-------------------------------------------------------------------------
 *
 * ipc.c
 *	  POSTGRES inter-process communication definitions.
 *
 * This file is misnamed, as it no longer has much of anything directly
 * to do with IPC.  The functionality here is concerned with managing
 * exit-time cleanup for either a postmaster or a backend.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 进程的"退出清理"基础设施:无论进程以何种方式
 * 结束(正常退出、ERROR 升级为 FATAL、被信号杀死、甚至有人直接调用
 * exit()),都必须保证共享资源(锁、共享内存引用、临时文件、DSM 段等)
 * 被有序释放,不污染共享内存状态。
 *
 * 【核心机制】
 * 1. 三类退出回调(数组实现,容量 MAX_ON_EXITS):
 *    - before_shmem_exit :最优先执行,用于"还需要完整系统"的用户级
 *      清理(如事务回滚、清理临时表,可能要访问系统目录);
 *    - on_shmem_exit     :次之,释放底层共享资源(如释放 PGPROC 槽);
 *    - on_proc_exit      :最后,做进程级收尾(如刷写统计、关闭文件)。
 *    每个回调都带一个 Datum 参数 arg,注册时一并给定。三张列表的
 *    调用顺序是"后注册的先调用"(LIFO,数组倒着数),与 C 语言 atexit()
 *    的语义一致。
 * 2. proc_exit(code):唯一合法的正常退出通道。先置
 *    proc_exit_inprogress 标志——此后任何 ereport() 都不得把控制流
 *    送回主循环,而必须继续执行退出逻辑(防止清理代码出错后"复活");
 *    接着 shmem_exit()(含 dsm_backend_shutdown())、再依次执行
 *    on_proc_exit 回调,最后调用系统 exit(code)。
 * 3. 兜底:通过 atexit() 注册 atexit_callback,即使有人绕过 proc_exit
 *    直接调 exit(),清理也照样执行(只是拿不到真实退出码,用 -1 代替)。
 *    _exit() 无法拦截,但有"dead man switch"让 postmaster 把这种异常
 *    退出当作崩溃处理(见 pmsignal.c)。
 *
 * 【共享内存重建】postmaster 在子进程崩溃后要用 shmem_exit()(不真正
 * exit)清理自己对该子进程的残留引用,以便重新初始化共享内存和信号量。
 * 回调在调用前先移出列表,因此即使回调里抛错也不会无限循环。
 *
 * 配套的还有 on_exit_reset():子进程 fork 出来后必须清空从 postmaster
 * 继承的这三张表,避免子进程替 postmaster"打扫卫生"。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/ipc.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>
#include <sys/stat.h>

#include "miscadmin.h"
#ifdef PROFILE_PID_DIR
#include "postmaster/autovacuum.h"
#endif
#include "storage/dsm.h"
#include "storage/ipc.h"
#include "storage/lwlock.h"
#include "tcop/tcopprot.h"


/*
 * This flag is set during proc_exit() to change ereport()'s behavior,
 * so that an ereport() from an on_proc_exit routine cannot get us out
 * of the exit procedure.  We do NOT want to go back to the idle loop...
 */
/* (中文)proc_exit() 进入后即置位:此后任何 ereport()/elog() 都不允许把
 * 控制流送回主循环,而是直接重新进入退出流程(见 proc_exit_prepare)。
 * 这是"退出过程不可中断"的硬开关,杜绝清理回调抛错导致进程"复活"。 */
bool		proc_exit_inprogress = false;

/*
 * Set when shmem_exit() is in progress.
 */
/* (中文)shmem_exit() 执行期间置位(整个 shmem 清理的"进行中"标志)。
 * 供其他模块判断"共享内存清理是否正在进行",例如避免在清理期间再去
 * 申请共享资源。 */
bool		shmem_exit_inprogress = false;

/*
 * This flag tracks whether we've called atexit() in the current process
 * (or in the parent postmaster).
 */
/* (中文)是否已在本进程调用过 atexit(atexit_callback):由于 on_proc_exit /
 * on_shmem_exit / before_shmem_exit 三个注册函数都要注册同一个 atexit
 * 回调,用此标志保证只注册一次,避免重复回调。 */
static bool atexit_callback_setup = false;

/* local functions */
static void proc_exit_prepare(int code);


/* ----------------------------------------------------------------
 *						exit() handling stuff
 *
 * These functions are in generally the same spirit as atexit(),
 * but provide some additional features we need --- in particular,
 * we want to register callbacks to invoke when we are disconnecting
 * from a broken shared-memory context but not exiting the postmaster.
 *
 * Callback functions can take zero, one, or two args: the first passed
 * arg is the integer exitcode, the second is the Datum supplied when
 * the callback was registered.
 * ----------------------------------------------------------------
 */

#define MAX_ON_EXITS 20
/* (中文)三类退出回调列表各自的容量上限(20 个)。超过即报 FATAL
 * ("out of on_proc_exit slots" 等)。 */

/* (中文)一条退出回调记录:function 是要调用的回调(参数为退出码与 arg),
 * arg 是注册时随附的 Datum 参数。 */
struct ONEXIT
{
	pg_on_exit_callback function;
	Datum		arg;
};

/* (中文)三张退出回调表(静态数组):
 * - on_proc_exit_list    :进程级清理,最后执行;
 * - on_shmem_exit_list   :共享内存级清理,其次执行;
 * - before_shmem_exit_list:用户级清理,最先执行。
 * 配套的三个 index 记录"已注册条数",既是栈顶指针也是下一空位:
 * 执行时从高到低递减(后注册先调用),注册时在低处递增。 */
static struct ONEXIT on_proc_exit_list[MAX_ON_EXITS];
static struct ONEXIT on_shmem_exit_list[MAX_ON_EXITS];
static struct ONEXIT before_shmem_exit_list[MAX_ON_EXITS];

static int	on_proc_exit_index,
			on_shmem_exit_index,
			before_shmem_exit_index;


/* ----------------------------------------------------------------
 *		proc_exit
 *
 *		this function calls all the callbacks registered
 *		for it (to free resources) and then calls exit.
 *
 *		This should be the only function to call exit().
 *		-cim 2/6/90
 *
 *		Unfortunately, we can't really guarantee that add-on code
 *		obeys the rule of not calling exit() directly.  So, while
 *		this is the preferred way out of the system, we also register
 *		an atexit callback that will make sure cleanup happens.
 * ----------------------------------------------------------------
 */
/*
 * proc_exit - (中文)进程正常退出的唯一合法通道:执行全部清理回调后 exit()
 *
 * 【作用】依次完成:1) 校验本函数只在"进程自己的上下文"里被调用(若
 * 是被 fork 出来的子进程调用立即 PANIC,防止误在子进程里替父进程退出);
 * 2) 调用 proc_exit_prepare(code) 执行全部清理;3) (PROFILE_PID_DIR
 * 编译时)为 gprof 输出建独立子目录并 chdir 进去;4) 输出 DEBUG3 日志
 * 后调用系统 exit(code)。
 *
 * 【设计思想】这是"唯一调用 exit() 的函数"(意图上),但无法强制约束
 * 第三方代码,因此另有 atexit_callback 兜底。PROFILE_PID_DIR 部分放在
 * proc_exit 末尾而非清理回调里,是为了让 gprof 的 mcleanup() 最后执行、
 * 且输出到每个进程自己的目录(autovacuum 工作进程共用目录以免磁盘
 * 膨胀)。注意 proc_exit_prepare 是共享路径:正常走这里会执行两遍
 * (proc_exit 一次、exit 触发 atexit_callback 又一次),但第二遍因
 * 索引已清零而无事可做。
 *
 * 【参数】code —— 进程退出码(传给系统 exit() 及所有清理回调)。
 * 【返回值】无(不返回)。
 */
void
proc_exit(int code)
{
	/* not safe if forked by system(), etc. */
	if (MyProcPid != (int) getpid())
		elog(PANIC, "proc_exit() called in child process");

	/* Clean up everything that must be cleaned up */
	proc_exit_prepare(code);

#ifdef PROFILE_PID_DIR
	{
		/*
		 * If we are profiling ourself then gprof's mcleanup() is about to
		 * write out a profile to ./gmon.out.  Since mcleanup() always uses a
		 * fixed file name, each backend will overwrite earlier profiles. To
		 * fix that, we create a separate subdirectory for each backend
		 * (./gprof/pid) and 'cd' to that subdirectory before we exit() - that
		 * forces mcleanup() to write each profile into its own directory.  We
		 * end up with something like: $PGDATA/gprof/8829/gmon.out
		 * $PGDATA/gprof/8845/gmon.out ...
		 *
		 * To avoid undesirable disk space bloat, autovacuum workers are
		 * discriminated against: all their gmon.out files go into the same
		 * subdirectory.  Without this, an installation that is "just sitting
		 * there" nonetheless eats megabytes of disk space every few seconds.
		 *
		 * Note that we do this here instead of in an on_proc_exit() callback
		 * because we want to ensure that this code executes last - we don't
		 * want to interfere with any other on_proc_exit() callback.  For the
		 * same reason, we do not include it in proc_exit_prepare ... so if
		 * you are exiting in the "wrong way" you won't drop your profile in a
		 * nice place.
		 */
		char		gprofDirName[32];

		if (AmAutoVacuumWorkerProcess())
			snprintf(gprofDirName, 32, "gprof/avworker");
		else
			snprintf(gprofDirName, 32, "gprof/%d", (int) getpid());

		/*
		 * Use mkdir() instead of MakePGDirectory() since we aren't making a
		 * PG directory here.
		 */
		mkdir("gprof", S_IRWXU | S_IRWXG | S_IRWXO);
		mkdir(gprofDirName, S_IRWXU | S_IRWXG | S_IRWXO);
		chdir(gprofDirName);
	}
#endif

	elog(DEBUG3, "exit(%d)", code);

	exit(code);
}

/*
 * Code shared between proc_exit and the atexit handler.  Note that in
 * normal exit through proc_exit, this will actually be called twice ...
 * but the second call will have nothing to do.
 */
/*
 * proc_exit_prepare - (中文)执行全部退出清理逻辑(proc_exit 与 atexit 兜底的公共部分)
 *
 * 【作用】1) 置 proc_exit_inprogress(此后任何 ereport 都不会打断退出);
 * 2) 清掉挂起的取消/终止请求(InterruptPending/ProcDiePending/
 * QueryCancelPending),并把 InterruptHoldoffCount 设为 1、CritSectionCount
 * 清零——HoldoffCount 置 1 是为了在剩下的退出过程里彻底屏蔽中断响应,
 * 防止信号处理程序在清理途中又置起新的中断请求;3) 清空错误上下文栈与
 * debug_query_string(防止清理回调的 elog 携带过时上下文,也防止访问
 * 已随事务 abort 失效的内存);4) 先 shmem_exit() 释放共享资源,再按
 * LIFO 依次调用全部 on_proc_exit 回调。
 *
 * 【设计思想】回调列表执行采用"边执行边把索引递减"的方式:若某回调
 * 抛 ERROR/FATAL,控制流重新回到这里时,已执行的不会重复、出错的那个
 * 也不会再执行——从结构上排除无限循环。on_proc_exit_index 最后归零,
 * 使"第二遍调用"(atexit 兜底路径)无活可干。
 *
 * 【参数】code —— 退出码,原样传给每个清理回调。
 * 【返回值】无。
 */
static void
proc_exit_prepare(int code)
{
	/*
	 * Once we set this flag, we are committed to exit.  Any ereport() will
	 * NOT send control back to the main loop, but right back here.
	 */
	proc_exit_inprogress = true;

	/*
	 * Forget any pending cancel or die requests; we're doing our best to
	 * close up shop already.  Note that the signal handlers will not set
	 * these flags again, now that proc_exit_inprogress is set.
	 */
	InterruptPending = false;
	ProcDiePending = false;
	QueryCancelPending = false;
	InterruptHoldoffCount = 1;
	CritSectionCount = 0;

	/*
	 * Also clear the error context stack, to prevent error callbacks from
	 * being invoked by any elog/ereport calls made during proc_exit. Whatever
	 * context they might want to offer is probably not relevant, and in any
	 * case they are likely to fail outright after we've done things like
	 * aborting any open transaction.  (In normal exit scenarios the context
	 * stack should be empty anyway, but it might not be in the case of
	 * elog(FATAL) for example.)
	 */
	error_context_stack = NULL;
	/* For the same reason, reset debug_query_string before it's clobbered */
	debug_query_string = NULL;

	/* do our shared memory exits first */
	shmem_exit(code);

	elog(DEBUG3, "proc_exit(%d): %d callbacks to make",
		 code, on_proc_exit_index);

	/*
	 * call all the registered callbacks.
	 *
	 * Note that since we decrement on_proc_exit_index each time, if a
	 * callback calls ereport(ERROR) or ereport(FATAL) then it won't be
	 * invoked again when control comes back here (nor will the
	 * previously-completed callbacks).  So, an infinite loop should not be
	 * possible.
	 */
	while (--on_proc_exit_index >= 0)
		on_proc_exit_list[on_proc_exit_index].function(code,
													   on_proc_exit_list[on_proc_exit_index].arg);

	on_proc_exit_index = 0;
}

/* ------------------
 * Run all of the on_shmem_exit routines --- but don't actually exit.
 * This is used by the postmaster to re-initialize shared memory and
 * semaphores after a backend dies horribly.  As with proc_exit(), we
 * remove each callback from the list before calling it, to avoid
 * infinite loop in case of error.
 * ------------------
 */
/*
 * shmem_exit - (中文)执行全部共享内存级清理回调(不退出进程)
 *
 * 【作用】按三个层次依次清理:1) LWLockReleaseAll()——先释放本进程持有
 * 的全部 LWLock。这一步很关键:它避免回调访问已被 detach 的 DSM 段里的
 * 锁对象(悬垂指针),也让回调能够重新获取新锁;2) 调用 before_shmem_exit
 * 回调(需要完整系统仍可用,如清理临时表需要访问目录);3) 调用
 * dsm_backend_shutdown()(动态共享内存的收尾,逻辑与主 shmem 段相同的
 * "先摘除再调用"渐进式设计);4) 调用 on_shmem_exit 回调(释放底层共享
 * 资源,如 PGPROC 槽)。
 *
 * 【设计思想】本函数可被 postmaster 单独调用——子进程崩溃后,postmaster
 * 需要清理自己与旧共享内存的关联以便重建,但不想真的退出。回调执行用
 * "递减索引"的渐进式方法,出错也不会死循环。注意 dsm_backend_shutdown()
 * 被硬编码在此处而不是注册为 on_shmem_exit 回调,正是为了"某个 DSM
 * 回调出错后,其余回调仍会执行",与主 shmem 段回调平权。
 *
 * 【参数】code —— 退出码(传给所有清理回调)。
 * 【返回值】无。
 */
void
shmem_exit(int code)
{
	shmem_exit_inprogress = true;

	/*
	 * Release any LWLocks we might be holding before callbacks run. This
	 * prevents accessing locks in detached DSM segments and allows callbacks
	 * to acquire new locks.
	 */
	LWLockReleaseAll();

	/*
	 * Call before_shmem_exit callbacks.
	 *
	 * These should be things that need most of the system to still be up and
	 * working, such as cleanup of temp relations, which requires catalog
	 * access.
	 */
	elog(DEBUG3, "shmem_exit(%d): %d before_shmem_exit callbacks to make",
		 code, before_shmem_exit_index);
	while (--before_shmem_exit_index >= 0)
		before_shmem_exit_list[before_shmem_exit_index].function(code,
																 before_shmem_exit_list[before_shmem_exit_index].arg);
	before_shmem_exit_index = 0;

	/*
	 * Call dynamic shared memory callbacks.
	 *
	 * These serve the same purpose as late callbacks, but for dynamic shared
	 * memory segments rather than the main shared memory segment.
	 * dsm_backend_shutdown() has the same kind of progressive logic we use
	 * for the main shared memory segment; namely, it unregisters each
	 * callback before invoking it, so that we don't get stuck in an infinite
	 * loop if one of those callbacks itself throws an ERROR or FATAL.
	 *
	 * Note that explicitly calling this function here is quite different from
	 * registering it as an on_shmem_exit callback for precisely this reason:
	 * if one dynamic shared memory callback errors out, the remaining
	 * callbacks will still be invoked.  Thus, hard-coding this call puts it
	 * equal footing with callbacks for the main shared memory segment.
	 */
	dsm_backend_shutdown();

	/*
	 * Call on_shmem_exit callbacks.
	 *
	 * These are generally releasing low-level shared memory resources.  In
	 * some cases, this is a backstop against the possibility that the early
	 * callbacks might themselves fail, leading to re-entry to this routine;
	 * in other cases, it's cleanup that only happens at process exit.
	 */
	elog(DEBUG3, "shmem_exit(%d): %d on_shmem_exit callbacks to make",
		 code, on_shmem_exit_index);
	while (--on_shmem_exit_index >= 0)
		on_shmem_exit_list[on_shmem_exit_index].function(code,
														 on_shmem_exit_list[on_shmem_exit_index].arg);
	on_shmem_exit_index = 0;

	shmem_exit_inprogress = false;
}

/* ----------------------------------------------------------------
 *		atexit_callback
 *
 *		Backstop to ensure that direct calls of exit() don't mess us up.
 *
 * Somebody who was being really uncooperative could call _exit(),
 * but for that case we have a "dead man switch" that will make the
 *		postmaster treat it as a crash --- see pmsignal.c.
 * ----------------------------------------------------------------
 */
/*
 * atexit_callback - (中文)atexit() 兜底回调:直接 exit() 也能完成清理
 *
 * 【作用】通过 atexit() 注册的系统退出回调:当有人绕过 proc_exit() 直接
 * 调用 exit() 时,由它执行 proc_exit_prepare(-1) 完成全部清理。因为此时
 * 拿不到真实退出码,统一用 -1 代替。
 *
 * 【设计思想】这是"dead man switch"之外的第二道防线:exit() 还能拦截,
 * _exit() 拦不住——那种情况由 postmaster 借助 pmsignal.c 的机制把进程
 * 当作崩溃处理。proc_exit() 正常路径下本回调也会被系统调用一遍,但因
 * 索引已清零,第二遍实际无事可做。
 *
 * 【参数】无(atexit 约定)。
 * 【返回值】无。
 */
static void
atexit_callback(void)
{
	/* Clean up everything that must be cleaned up */
	/* ... too bad we don't know the real exit code ... */
	proc_exit_prepare(-1);
}

/* ----------------------------------------------------------------
 *		on_proc_exit
 *
 *		this function adds a callback function to the list of
 *		functions invoked by proc_exit().   -cim 2/6/90
 * ----------------------------------------------------------------
 */
/*
 * on_proc_exit - (中文)注册一个进程级退出回调(proc_exit 时最后一批执行)
 *
 * 【作用】把 (function, arg) 追加进 on_proc_exit_list;槽位用尽时报
 * FATAL。首次注册时顺带注册 atexit 兜底回调(atexit_callback_setup
 * 保证只注册一次)。
 *
 * 【设计思想】退出回调按 LIFO 执行(后注册先调用),与 atexit() 语义一致,
 * 便于"成对注册、反向清理"。本表是三类回调中最后执行的,适合做"不依赖
 * 共享内存"的进程级收尾;需要共享资源的清理应注册到 before_shmem_exit
 * 或 on_shmem_exit。
 *
 * 【参数】
 *   function —— 回调函数(参数:退出码 + arg);
 *   arg      —— 回调随附参数(Datum)。
 * 【返回值】无。
 */
void
on_proc_exit(pg_on_exit_callback function, Datum arg)
{
	if (on_proc_exit_index >= MAX_ON_EXITS)
		ereport(FATAL,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg_internal("out of on_proc_exit slots")));

	on_proc_exit_list[on_proc_exit_index].function = function;
	on_proc_exit_list[on_proc_exit_index].arg = arg;

	++on_proc_exit_index;

	if (!atexit_callback_setup)
	{
		atexit(atexit_callback);
		atexit_callback_setup = true;
	}
}

/* ----------------------------------------------------------------
 *		before_shmem_exit
 *
 *		Register early callback to perform user-level cleanup,
 *		e.g. transaction abort, before we begin shutting down
 *		low-level subsystems.
 * ----------------------------------------------------------------
 */
/*
 * before_shmem_exit - (中文)注册"提前"退出回调(共享内存清理开始前执行)
 *
 * 【作用】把 (function, arg) 追加进 before_shmem_exit_list(槽位用尽报
 * FATAL),并保证 atexit 兜底已注册。这类回调在 shmem_exit() 里最先执行。
 *
 * 【设计思想】与 on_shmem_exit 的区别在于执行时机:before 回调运行时
 * 大部分系统(目录、事务基础设施、WAL 等)仍可用,适合做"用户级"清理,
 * 例如事务 abort 的回滚、临时关系的删除;而 on_shmem_exit 回调运行时
 * 低层子系统已开始关闭,只能做资源释放。同样 LIFO 执行。
 *
 * 【参数】
 *   function —— 回调函数;
 *   arg      —— 随附 Datum 参数。
 * 【返回值】无。
 */
void
before_shmem_exit(pg_on_exit_callback function, Datum arg)
{
	if (before_shmem_exit_index >= MAX_ON_EXITS)
		ereport(FATAL,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg_internal("out of before_shmem_exit slots")));

	before_shmem_exit_list[before_shmem_exit_index].function = function;
	before_shmem_exit_list[before_shmem_exit_index].arg = arg;

	++before_shmem_exit_index;

	if (!atexit_callback_setup)
	{
		atexit(atexit_callback);
		atexit_callback_setup = true;
	}
}

/* ----------------------------------------------------------------
 *		on_shmem_exit
 *
 *		Register ordinary callback to perform low-level shutdown
 *		(e.g. releasing our PGPROC); run after before_shmem_exit
 *		callbacks and before on_proc_exit callbacks.
 * ----------------------------------------------------------------
 */
/*
 * on_shmem_exit - (中文)注册普通共享内存退出回调(在 before 回调之后、proc 回调之前执行)
 *
 * 【作用】把 (function, arg) 追加进 on_shmem_exit_list(槽位用尽报
 * FATAL),并保证 atexit 兜底已注册。这类回调在 shmem_exit() 里、DSM
 * 收尾之后执行。
 *
 * 【设计思想】执行次序在三个层次中间:此时 before 层的用户级清理已完成,
 * 但进程级收尾尚未开始。典型用途是释放低层共享资源(如把本进程的
 * PGPROC 槽位还回共享内存),这些操作不能太早(依赖部分系统)也不能太晚
 * (需要共享内存仍可用)。
 *
 * 【参数】
 *   function —— 回调函数;
 *   arg      —— 随附 Datum 参数。
 * 【返回值】无。
 */
void
on_shmem_exit(pg_on_exit_callback function, Datum arg)
{
	if (on_shmem_exit_index >= MAX_ON_EXITS)
		ereport(FATAL,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg_internal("out of on_shmem_exit slots")));

	on_shmem_exit_list[on_shmem_exit_index].function = function;
	on_shmem_exit_list[on_shmem_exit_index].arg = arg;

	++on_shmem_exit_index;

	if (!atexit_callback_setup)
	{
		atexit(atexit_callback);
		atexit_callback_setup = true;
	}
}

/* ----------------------------------------------------------------
 *		cancel_before_shmem_exit
 *
 *		this function removes a previously-registered before_shmem_exit
 *		callback.  We only look at the latest entry for removal, as we
 * 		expect callers to add and remove temporary before_shmem_exit
 * 		callbacks in strict LIFO order.
 * ----------------------------------------------------------------
 */
/*
 * cancel_before_shmem_exit - (中文)撤销最近注册的一条 before_shmem_exit 回调
 *
 * 【作用】只检查"列表最新一条"是否与 (function, arg) 完全匹配,匹配则
 * 出栈(索引减一),不匹配则报 ERROR。
 *
 * 【设计思想】这是 LIFO 约定的严格化:调用方承诺"临时性 before 回调"
 * 一定按先进后出顺序成对注册/撤销(典型的配对用法是:函数开头注册、函数
 * 结尾撤销,保证异常路径也能恢复到干净状态)。因此本函数不支持任意位置
 * 删除——中间条目删除后,LIFO 语义就乱套了。报 ERROR 而非静默失败,
 * 让"撤销错了回调"的程序错误尽早暴露。
 *
 * 【参数】
 *   function —— 期待撤销的回调函数指针;
 *   arg      —— 期待撤销的随附参数。
 * 【返回值】无(不匹配即 ERROR)。
 */
void
cancel_before_shmem_exit(pg_on_exit_callback function, Datum arg)
{
	if (before_shmem_exit_index > 0 &&
		before_shmem_exit_list[before_shmem_exit_index - 1].function
		== function &&
		before_shmem_exit_list[before_shmem_exit_index - 1].arg == arg)
		--before_shmem_exit_index;
	else
		elog(ERROR, "before_shmem_exit callback (%p,0x%" PRIx64 ") is not the latest entry",
			 function, arg);
}

/* ----------------------------------------------------------------
 *		on_exit_reset
 *
 *		this function clears all on_proc_exit() and on_shmem_exit()
 *		registered functions.  This is used just after forking a backend,
 *		so that the backend doesn't believe it should call the postmaster's
 *		on-exit routines when it exits...
 * ----------------------------------------------------------------
 */
/*
 * on_exit_reset - (中文)清空全部退出回调(子进程 fork 后必须调用)
 *
 * 【作用】把 before_shmem_exit / on_shmem_exit / on_proc_exit 三张表
 * 的索引全部清零,并调用 reset_on_dsm_detach() 重置 DSM detach 回调
 * 状态。
 *
 * 【设计思想】子进程由 fork() 产生时,会继承 postmaster 已注册的整套
 * 退出回调。若不清理,子进程退出时会替 postmaster 执行那些清理(释放
 * postmaster 的 PGPROC、关 postmaster 的文件等),造成灾难性后果。
 * 因此每个子进程启动后、注册自己的回调之前,必须先调用本函数。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
on_exit_reset(void)
{
	before_shmem_exit_index = 0;
	on_shmem_exit_index = 0;
	on_proc_exit_index = 0;
	reset_on_dsm_detach();
}

/* ----------------------------------------------------------------
 *		check_on_shmem_exit_lists_are_empty
 *
 *		Debugging check that no shmem cleanup handlers have been registered
 *		prematurely in the current process.
 * ----------------------------------------------------------------
 */
/*
 * check_on_shmem_exit_lists_are_empty - (中文)调试检查:当前进程不应有已注册的共享内存清理回调
 *
 * 【作用】检查 before_shmem_exit 与 on_shmem_exit 两张表是否为空,若非空
 * 报 FATAL("prematurely")。
 *
 * 【设计思想】用于捕捉"注册过早"的程序错误:某些回调只能在特定启动
 * 阶段之后注册,提前注册意味着进程状态还没有就绪。FATAL 级别(而非
 * ERROR)确保这类结构性错误不会被事务回滚机制吞掉,直接终止进程。
 *
 * 【参数】无。
 * 【返回值】无(违规即 FATAL)。
 */
void
check_on_shmem_exit_lists_are_empty(void)
{
	if (before_shmem_exit_index)
		elog(FATAL, "before_shmem_exit has been called prematurely");
	if (on_shmem_exit_index)
		elog(FATAL, "on_shmem_exit has been called prematurely");
	/* Checking DSM detach state seems unnecessary given the above */
}
