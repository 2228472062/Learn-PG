/*-------------------------------------------------------------------------
 *
 * pgarch.c
 *
 *	PostgreSQL WAL archiver
 *
 *	All functions relating to archiver are included here
 *
 *	- All functions executed by archiver process
 *
 *	- archiver is forked from postmaster, and the two
 *	processes then communicate using signals. All functions
 *	executed by postmaster are included in this file.
 *
 *	Initial author: Simon Riggs		simon@2ndquadrant.com
 *
 * 【中文总述】
 * 本文件是 WAL 归档进程（archiver）的全部代码。
 * archiver 由 postmaster fork 出来，专门负责把已经写完的 WAL 段文件
 * （wal segment）复制到归档目的地（archive_command 或 archive_library
 * 指定的位置），供 PITR（时间点恢复）和备库搭建使用。
 * 归档机制的基本原理：
 *   1. WAL 段写满（或切换）后，XLog 写路径会在 archive_status 目录下
 *      留下 <段名>.ready 状态文件，表示"这段 WAL 可以归档了"
 *   2. archiver 主循环扫描 archive_status 目录，找到 .ready 文件，
 *      对每个 WAL 段执行归档（默认是执行 archive_command 这个 shell
 *      命令，也可加载 archive_library 插件）
 *   3. 归档成功：把 .ready 改名为 .done，检查点进程发现 .done 后
 *      就会回收删除该 WAL 段，避免磁盘被 WAL 撑爆
 *   4. 归档失败：保留 .ready 文件，稍后重试（NUM_ARCHIVE_RETRIES 次），
 *      仍失败则放弃，等下一轮循环再试——WAL 段会被一直保留
 *   5. archiver 平时睡眠，通过信号（SIGUSR2 停机、SIGTERM 停档、
 *      SIGHUP 重载配置、latch 唤醒）和定时（60 秒自动醒来）
 *      与 postmaster / 后端进程协作
 * 本文件还包含：进程间共享内存的注册初始化、插件式归档库的加载、
 * 崩溃后残留"孤儿" .ready 状态文件的清理等辅助逻辑。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/pgarch.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <time.h>
#include <sys/stat.h>
#include <unistd.h>

#include "access/xlog.h"
#include "access/xlog_internal.h"
#include "archive/archive_module.h"
#include "archive/shell_archive.h"
#include "lib/binaryheap.h"
#include "libpq/pqsignal.h"
#include "pgstat.h"
#include "postmaster/auxprocess.h"
#include "postmaster/interrupt.h"
#include "postmaster/pgarch.h"
#include "storage/condition_variable.h"
#include "storage/aio_subsys.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/latch.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/ps_status.h"
#include "utils/resowner.h"
#include "utils/timeout.h"
#include "utils/wait_event.h"


/* ----------
 * Timer definitions.
 * 【中文】定时器定义：archiver 平时睡眠等待信号，
 * 靠这些时间间隔"定时醒来"主动干活（proactive 策略）。
 * ----------
 */
#define PGARCH_AUTOWAKE_INTERVAL 60 /* How often to force a poll of the
									 * archive status directory; in seconds. */
/* 【中文】自动唤醒间隔 60 秒：即使没有任何信号到来，
 * 主循环每 60 秒也会强制醒来扫描一次归档状态目录，
 * 保证不依赖别人叫醒也能主动归档。 */
#define PGARCH_RESTART_INTERVAL 10	/* How often to attempt to restart a
									 * failed archiver; in seconds. */
/* 【中文】archiver 重启间隔 10 秒：postmaster 在 archiver 崩溃后
 * 是否允许立刻重新拉起，必须距上次启动满 10 秒才行，
 * 防止"刚启动就死"时无限快速重启（安全阀）。 */

/*
 * Maximum number of retries allowed when attempting to archive a WAL
 * file.
 * 【中文】单个 WAL 文件归档失败时的最大重试次数（3 次）。
 * 超过后本轮放弃该文件，等下一轮自动唤醒再试；
 * 失败期间 .ready 状态文件保留，WAL 段不会被回收。
 */
#define NUM_ARCHIVE_RETRIES 3

/*
 * Maximum number of retries allowed when attempting to remove an
 * orphan archive status file.
 * 【中文】清理"孤儿 .ready 状态文件"时的最大重试次数（3 次）。
 * 孤儿文件是系统崩溃后残留的（对应的 WAL 段已被回收），
 * 删不掉也只是多占用一个文件名，不影响正确性。
 */
#define NUM_ORPHAN_CLEANUP_RETRIES 3

/*
 * Maximum number of .ready files to gather per directory scan.
 * 【中文】每次扫描 archive_status 目录时，最多收集 64 个 .ready 文件。
 * 一次扫描多收一些文件，可减少目录扫描次数，
 * 显著提高大批量归档时的吞吐率。
 */
#define NUM_FILES_PER_DIRECTORY_SCAN 64

/* Shared memory area for archiver process */
/* 【中文】archiver 进程的共享内存结构：postmaster 与 archiver、
 * 以及其它进程通过这块共享内存 + 信号/锁机制协作。 */
typedef struct PgArchData
{
	int			pgprocno;		/* proc number of archiver process */
								/* 【中文】archiver 在共享内存 proc 数组中的编号。
								 * 其它进程（如后端）可据此找到 archiver 的 latch，
								 * 通过 PgArchWakeup() 叫醒正在睡觉的归档进程；
								 * archiver 未运行时为 INVALID_PROC_NUMBER。 */

	/*
	 * Forces a directory scan in pgarch_readyXlog().
	 * 【中文】"强制目录扫描"原子标志：其它进程置 1 后，
	 * 下一次 pgarch_readyXlog() 必须丢弃缓存的文件名列表、
	 * 重新扫描 archive_status 目录——用于紧急插入高优先级文件
	 * （如时间线切换产生的 .history 历史文件）时立刻生效。
	 */
	pg_atomic_uint32 force_dir_scan;
} PgArchData;

/* 【中文】GUC 全局变量：
 * XLogArchiveLibrary —— archive_library 参数：可加载的归档插件库名，
 *   空串表示使用内置 shell_archive（即执行 archive_command）；
 * arch_module_check_errdetail_string —— 归档插件的 check_configured_cb
 *   判定"未配置归档"时，可把详细原因写到这里，报错时展示给用户。 */
char	   *XLogArchiveLibrary = "";
char	   *arch_module_check_errdetail_string;


/* ----------
 * Local data
 * 【中文】archiver 进程的本地（进程私有）全局状态：
 *   last_sigterm_time —— 收到 SIGTERM 的时刻，主循环据此判断
 *     "已停止归档超过 60 秒"则主动退出，避免一条随机 SIGTERM
 *     把归档永久停摆；
 *   PgArch —— 指向共享内存中 PgArchData 的指针；
 *   ArchiveCallbacks / archive_module_state —— 已加载归档插件
 *     （模块）的回调函数表与状态，真正执行归档时都经它调用；
 *   archive_context —— 归档专用内存上下文，每次归档后整体
 *     Reset，防止插件等分配的内存无限泄漏。
 * ----------
 */
static time_t last_sigterm_time = 0;
static PgArchData *PgArch = NULL;
static const ArchiveModuleCallbacks *ArchiveCallbacks;
static ArchiveModuleState *archive_module_state;
static MemoryContext archive_context;


/*
 * Stuff for tracking multiple files to archive from each scan of
 * archive_status.  Minimizing the number of directory scans when there are
 * many files to archive can significantly improve archival rate.
 *
 * arch_heap is a max-heap that is used during the directory scan to track
 * the highest-priority files to archive.  After the directory scan
 * completes, the file names are stored in ascending order of priority in
 * arch_files.  pgarch_readyXlog() returns files from arch_files until it
 * is empty, at which point another directory scan must be performed.
 *
 * We only need this data in the archiver process, so make it a palloc'd
 * struct rather than a bunch of static arrays.
 *
 * 【中文】记录"一次目录扫描收集到的一批待归档文件"。
 * 批量取文件可大幅减少目录扫描次数，提高归档吞吐率。
 *   arch_heap —— 扫描过程中使用的最大堆：始终保留优先级最高的
 *     若干文件（.history 历史文件最优先，其次老文件优先）；
 *   arch_files[] —— 扫描完成后，把堆中文件按优先级从低到高
 *     依次取出存入该数组；pgarch_readyXlog() 每次从数组末尾
 *     （优先级最高者）取一个返回，取空后触发下一次目录扫描；
 *   arch_filenames[] —— 真正的字符串存储区，堆和数组里的
 *     指针都指向这里的缓冲区，避免反复 malloc。
 * 这些数据只有 archiver 进程自己用，所以用 palloc 分配
 * 一个结构体即可，不需要静态数组。
 */
struct arch_files_state
{
	binaryheap *arch_heap;
	int			arch_files_size;	/* number of live entries in arch_files[] */
	char	   *arch_files[NUM_FILES_PER_DIRECTORY_SCAN];
	/* buffers underlying heap, and later arch_files[], entries: */
	char		arch_filenames[NUM_FILES_PER_DIRECTORY_SCAN][MAX_XFN_CHARS + 1];
};

static struct arch_files_state *arch_files = NULL;
/* 【中文】上述结构的进程私有实例指针，在 PgArchiverMain() 中创建。 */

/*
 * Flags set by interrupt handlers for later service in the main loop.
 * 【中文】供信号处理器置位、主循环读取的"标志位"：
 *   ready_to_stop —— SIGUSR2 处理器置位，主循环发现后
 *     再完整执行一轮归档，然后退出进程（优雅停机方式）。
 * 用 volatile sig_atomic_t 保证信号处理器中的写入
 * 与主循环中的读取之间安全（原子、可见）。
 */
static volatile sig_atomic_t ready_to_stop = false;

/* ----------
 * Local function forward declarations
 * 【中文】本文件内部函数的前向声明（各函数作用见实现处的注释）。
 * ----------
 */
static void pgarch_waken_stop(SIGNAL_ARGS);
static void pgarch_MainLoop(void);
static void pgarch_ArchiverCopyLoop(void);
static bool pgarch_archiveXlog(char *xlog);
static bool pgarch_readyXlog(char *xlog);
static void pgarch_archiveDone(char *xlog);
static void pgarch_die(int code, Datum arg);
static void ProcessPgArchInterrupts(void);
static int	ready_file_comparator(Datum a, Datum b, void *arg);
static void LoadArchiveLibrary(void);
static void pgarch_call_module_shutdown_cb(int code, Datum arg);

static void PgArchShmemRequest(void *arg);
static void PgArchShmemInit(void *arg);

/* 【中文】共享内存回调注册表：postmaster 创建共享内存时依次回调
 * request_fn（各进程登记自己需要的区域大小）与
 * init_fn（内存段建成后初始化各自区域）。 */
const ShmemCallbacks PgArchShmemCallbacks = {
	.request_fn = PgArchShmemRequest,
	.init_fn = PgArchShmemInit,
};

/* Register shared memory space needed by the archiver */
/* 【中文】向共享内存管理器登记：需要 sizeof(PgArchData) 大小、
 * 名为 "Archiver Data" 的区域，段建成后其首地址写入全局指针 PgArch。 */
static void
PgArchShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "Archiver Data",
					   .size = sizeof(PgArchData),
					   .ptr = (void **) &PgArch,
		);
}

/* Initialize archiver-related shared memory */
/* 【中文】初始化归档进程的共享内存：整块清零、
 * proc 编号置为"无效"（archiver 还没启动）、
 * force_dir_scan 原子标志初始化为 0（无需强制扫描）。 */
static void
PgArchShmemInit(void *arg)
{
	MemSet(PgArch, 0, sizeof(PgArchData));
	PgArch->pgprocno = INVALID_PROC_NUMBER;
	pg_atomic_init_u32(&PgArch->force_dir_scan, 0);
}

/*
 * PgArchCanRestart
 *
 * Return true, indicating archiver is allowed to restart, if enough time has
 * passed since it was last launched to reach PGARCH_RESTART_INTERVAL.
 * Otherwise return false.
 *
 * This is a safety valve to protect against continuous respawn attempts if the
 * archiver is dying immediately at launch. Note that since we will retry to
 * launch the archiver from the postmaster main loop, we will get another
 * chance later.
 *
 * 【中文】判断 archiver 是否允许被重新拉起（由 postmaster 调用）。
 * 规则：距上次启动时间至少已过 PGARCH_RESTART_INTERVAL（10 秒）。
 * 这是防止"archiver 一启动就崩溃、postmaster 疯狂快速重启"的
 * 安全阀；即使这次返回 false，postmaster 主循环稍后还会再
 * 尝试拉起，所以不会永远错过。
 */
bool
PgArchCanRestart(void)
{
	static time_t last_pgarch_start_time = 0;
	time_t		curtime = time(NULL);

	/*
	 * If first time through, or time somehow went backwards, always update
	 * last_pgarch_start_time to match the current clock and allow archiver
	 * start.  Otherwise allow it only once enough time has elapsed.
	 * 【中文】首次调用、或系统时钟意外倒退时：无条件刷新记录时间
	 * 并允许启动；否则必须等满 10 秒才放行。
	 */
	if (last_pgarch_start_time == 0 ||
		curtime < last_pgarch_start_time ||
		curtime - last_pgarch_start_time >= PGARCH_RESTART_INTERVAL)
	{
		/* 【中文】更新启动时间并放行 */
		last_pgarch_start_time = curtime;
		return true;
	}
	/* 【中文】距上次启动不足 10 秒：暂不允许重启 */
	return false;
}


/* Main entry point for archiver process */
/* 【中文总述】archiver 进程的主入口（postmaster fork 后执行；
 * EXEC_BACKEND 平台下由 SubPostmasterMain 分发到本函数）。
 * 整个函数是"初始化 → 主循环 → 退出"的流程：
 *   1. 公共辅助进程初始化（AuxiliaryProcessMainCommon：进程标题、
 *      信号、GUC、内存上下文等）
 *   2. 重新安装信号处理器：只保留对 archiver 有意义的信号
 *      （SIGHUP 配置重载 / SIGTERM 停机请求 / SIGUSR1 procsignal /
 *      SIGUSR2 唤醒并优雅退出），其余一律忽略；
 *      然后解除 postmaster fork 时阻塞的信号屏蔽
 *   3. 断言 WAL 归档确实开启（archive_mode=on/always）；
 *      注册退出清理回调 pgarch_die
 *   4. 把本进程的 proc 编号写入共享内存，让后端进程能通过
 *      PgArchWakeup() 用 latch 唤醒正在睡眠的我们
 *   5. 分配归档工作区 arch_files、初始化"待归档文件"最大堆、
 *      创建归档专用内存上下文、加载归档插件库
 *   6. 进入 pgarch_MainLoop() 主循环（正常情况下不返回）
 *   7. 主循环退出后 proc_exit(0) 结束进程
 */
void
PgArchiverMain(const void *startup_data, size_t startup_data_len)
{
	Assert(startup_data_len == 0);

	/* 【中文】公共辅助进程初始化（所有 auxiliary 进程共用）：
	 * 设置进程标题、初始化信号/GUC/内存上下文等。 */
	AuxiliaryProcessMainCommon();

	/*
	 * Ignore all signals usually bound to some action in the postmaster,
	 * except for SIGHUP, SIGTERM, SIGUSR1, SIGUSR2, and SIGQUIT.
	 * 【中文】重设信号处理器（继承自 postmaster 的处理器只对
	 * postmaster 有意义，子进程必须换成自己的）：
	 *   SIGHUP  → 配置重载处理器（响应 pg_ctl reload，重读配置）
	 *   SIGINT  → 忽略（archiver 不需要交互中断）
	 *   SIGTERM → 停机请求处理器（置 ShutdownRequestPending 标志，
	 *             归档循环据此不再发起新的归档命令）
	 *   SIGQUIT → 不在这里设置：InitPostmasterChild 已装好
	 *             "立即退出"处理器（紧急停止用）
	 *   SIGALRM / SIGPIPE → 忽略（对 archiver 无意义）
	 *   SIGUSR1 → procsignal 处理器（其它进程发来的跨进程信号，
	 *             如"强制重新扫描目录"请求）
	 *   SIGUSR2 → pgarch_waken_stop（做完最后一轮归档后退出）
	 */
	pqsignal(SIGHUP, SignalHandlerForConfigReload);
	pqsignal(SIGINT, PG_SIG_IGN);
	pqsignal(SIGTERM, SignalHandlerForShutdownRequest);
	/* SIGQUIT handler was already set up by InitPostmasterChild */
	pqsignal(SIGALRM, PG_SIG_IGN);
	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, pgarch_waken_stop);

	/* Reset some signals that are accepted by postmaster but not here */
	/* 【中文】SIGCHLD 在 postmaster 里用于回收子进程，archiver
	 * 不 fork 任何子进程，用不上，恢复默认行为。 */
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/* Unblock signals (they were blocked when the postmaster forked us) */
	/* 【中文】postmaster fork 我们之前屏蔽了所有信号，
	 * 现在解除屏蔽，上面安装的处理器才真正生效。 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/* We shouldn't be launched unnecessarily. */
	/* 【中文】断言归档模式确实开启（archive_mode=on/always），
	 * 否则本进程根本不该被拉起（防御性检查）。 */
	Assert(XLogArchivingActive());

	/* Arrange to clean up at archiver exit */
	/* 【中文】注册退出清理回调（进程退出时执行）：
	 * 把共享内存里的 pgprocno 重置为无效，避免其它进程
	 * 对已退出的 archiver 做 SetLatch 等唤醒操作。 */
	on_shmem_exit(pgarch_die, 0);

	/*
	 * Advertise our proc number so that backends can use our latch to wake us
	 * up while we're sleeping.
	 * 【中文】公布我们的 proc 编号：后端进程产生新的待归档文件时，
	 * 可经 PgArchWakeup() 置位我们的 latch，把正在睡觉的我们
	 * 立刻叫醒去归档，不必干等 60 秒的自动唤醒。 */
	PgArch->pgprocno = MyProcNumber;

	/* Create workspace for pgarch_readyXlog() */
	/* 【中文】创建归档工作区（记录一批待归档文件名的结构），
	 * 文件数为 0 表示"下次调用先做目录扫描"。 */
	arch_files = palloc_object(struct arch_files_state);
	arch_files->arch_files_size = 0;

	/* Initialize our max-heap for prioritizing files to archive. */
	/* 【中文】初始化最大堆：扫描目录时用来保留优先级最高的
	 * NUM_FILES_PER_DIRECTORY_SCAN 个文件
	 * （历史文件最优先、较老的文件优先）。 */
	arch_files->arch_heap = binaryheap_allocate(NUM_FILES_PER_DIRECTORY_SCAN,
												ready_file_comparator, NULL);

	/* Initialize our memory context. */
	/* 【中文】创建归档专用内存上下文：每次归档后整体 Reset，
	 * 防止归档插件等分配的内存无限泄漏。 */
	archive_context = AllocSetContextCreate(TopMemoryContext,
											"archiver",
											ALLOCSET_DEFAULT_SIZES);

	/* Load the archive_library. */
	/* 【中文】加载归档插件库（archive_library）；默认加载内置的
	 * shell_archive（其归档实现就是执行 archive_command 命令）。 */
	LoadArchiveLibrary();

	/* 【中文】进入主循环：睡眠等待信号 / 定时醒来，反复执行归档，
	 * 直到收到 SIGUSR2 完成最后一轮后退出（详见该函数注释）。 */
	pgarch_MainLoop();

	/* 【中文】主循环返回（正常停机流程走完），结束进程。 */
	proc_exit(0);
}

/*
 * Wake up the archiver
 * 【中文】唤醒 archiver 进程（由其它进程调用：后端产生了新的
 * 待归档 WAL 文件、或 postmaster 有急事要 archiver 醒来时）。
 * 原理：置位 archiver 的 procLatch，正在 WaitLatch 中睡眠的
 * archiver 会立即被唤醒，无需等 60 秒自动唤醒。
 */
void
PgArchWakeup(void)
{
	int			arch_pgprocno = PgArch->pgprocno;

	/*
	 * We don't acquire ProcArrayLock here.  It's actually fine because
	 * procLatch isn't ever freed, so we just can potentially set the wrong
	 * process' (or no process') latch.  Even in that case the archiver will
	 * be relaunched shortly and will start archiving.
	 * 【中文】这里故意不加 ProcArrayLock：procLatch 不会被释放，
	 * 最坏情况只是"设置到了别的进程（或已退出的进程）的 latch"，
	 * 无伤大雅——即使没唤醒成功，archiver 也会被重新拉起、
	 * 或按 60 秒自动唤醒间隔醒来开始归档。
	 */
	if (arch_pgprocno != INVALID_PROC_NUMBER)
		SetLatch(&GetPGProcByNumber(arch_pgprocno)->procLatch);
}


/* SIGUSR2 signal handler for archiver process */
/* 【中文】SIGUSR2 信号处理器：postmaster 在停机流程中发出 SIGUSR2，
 * 通知 archiver"再做最后一轮归档，然后退出"。
 * 处理器里只做两件最小的事：置 ready_to_stop 标志 +
 * 唤醒正在等待中的主循环（不调用可能不安全的重型函数）。 */
static void
pgarch_waken_stop(SIGNAL_ARGS)
{
	/* set flag to do a final cycle and shut down afterwards */
	/* 【中文】置"准备停止"标志，主循环据此知道要退出了 */
	ready_to_stop = true;
	/* 【中文】唤醒睡眠中的主循环，让它立刻处理这个标志 */
	SetLatch(MyLatch);
}

/*
 * pgarch_MainLoop
 *
 * Main loop for archiver
 *
 * 【中文总述】archiver 主循环：平时除了"等待"无事可做，但 archiver
 * 是保护数据的关键角色，所以会定时（60 秒）醒来主动干活，
 * 不依赖别人叫醒（proactive）。一轮循环的流程：
 *   1. 清空本进程 latch（为新一轮等待做准备）
 *   2. 读取"是否该停"标志：收到过 SIGUSR2 则本轮是最后一轮
 *   3. ProcessPgArchInterrupts()：处理跨进程信号屏障、内存上下文
 *      日志请求、配置重载（SIGHUP 后立刻用上新 archive_command）
 *   4. 处理 SIGTERM 停机请求：正常情况下 archiver 收到 SIGTERM
 *      只是不再发起新的归档（见 ArchiverCopyLoop），原地等待
 *      SIGUSR2 来结束；但若 SIGTERM 后超过 60 秒 SIGUSR2 还没到
 *      （或时钟倒退），则自行退出，让 postmaster 决定是否重启
 *      ——防止一条随机 SIGTERM 把归档永久停摆
 *   5. pgarch_ArchiverCopyLoop()：把当前所有 .ready 的 WAL 文件
 *      归档一遍
 *   6. 睡眠等待（末轮不等待直接退出）：latch 被置位（收到信号 /
 *      被其它进程唤醒）、60 秒超时（定时主动轮询）、或
 *      postmaster 死亡（异常情况），任一发生即醒来
 *   7. 若 postmaster 已死：立即退出（postmaster 死亡不该发生）
 */
static void
pgarch_MainLoop(void)
{
	bool		time_to_stop;

	/*
	 * There shouldn't be anything for the archiver to do except to wait for a
	 * signal ... however, the archiver exists to protect our data, so it
	 * wakes up occasionally to allow itself to be proactive.
	 * 【中文】archiver 平时只需要等待信号……但它是"保护数据"的角色，
	 * 所以会定时醒来主动检查，而不是被动依赖别人提醒。
	 */
	do
	{
		/* 【中文】清空本进程 latch，为新一轮 WaitLatch 做准备 */
		ResetLatch(MyLatch);

		/* When we get SIGUSR2, we do one more archive cycle, then exit */
		/* 【中文】若收到过 SIGUSR2（ready_to_stop 被置位），
		 * 本轮将执行最后一次归档循环，然后退出。 */
		time_to_stop = ready_to_stop;

		/* Check for barrier events and config update */
		/* 【中文】处理积压的中断工作：跨进程信号屏障、内存上下文
		 * 日志请求、以及 SIGHUP 触发的配置重载
		 * （详见 ProcessPgArchInterrupts）。 */
		ProcessPgArchInterrupts();

		/*
		 * If we've gotten SIGTERM, we normally just sit and do nothing until
		 * SIGUSR2 arrives.  However, that means a random SIGTERM would
		 * disable archiving indefinitely, which doesn't seem like a good
		 * idea.  If more than 60 seconds pass since SIGTERM, exit anyway, so
		 * that the postmaster can start a new archiver if needed.  Also exit
		 * if time unexpectedly goes backward.
		 *
		 * 【中文】SIGTERM 处理策略：收到 SIGTERM 后通常原地待命，
		 * 直到 SIGUSR2 到来再退出。但那样一条随机的 SIGTERM 会让
		 * 归档永久停摆，不可取；所以若 SIGTERM 之后超过 60 秒仍
		 * 无后续指令（或系统时钟倒退），就直接退出循环，让
		 * postmaster 按需拉起一个新的 archiver。
		 */
		if (ShutdownRequestPending)
		{
			time_t		curtime = time(NULL);

			/* 【中文】第一次看到停机请求：记下当前时刻作为起点 */
			if (last_sigterm_time == 0)
				last_sigterm_time = curtime;
			/* 【中文】时钟倒退，或等待已超过 60 秒：退出主循环 */
			else if (curtime < last_sigterm_time ||
					 curtime - last_sigterm_time >= 60)
				break;
		}

		/* Do what we're here for */
		/* 【中文】核心工作：把当前所有待归档（.ready）的 WAL 文件
		 * 全部归档一遍（详见 pgarch_ArchiverCopyLoop 的注释）。 */
		pgarch_ArchiverCopyLoop();

		/*
		 * Sleep until a signal is received, or until a poll is forced by
		 * PGARCH_AUTOWAKE_INTERVAL, or until postmaster dies.
		 * 【中文】睡眠等待：latch 被置位（收到信号 / 被其它进程
		 * 唤醒）、或 60 秒超时（定时主动轮询）、或 postmaster 死亡，
		 * 任一发生即醒来。末轮（time_to_stop）不再等待，直接跳出。
		 */
		if (!time_to_stop)		/* Don't wait during last iteration */
		{
			int			rc;

			rc = WaitLatch(MyLatch,
						   WL_LATCH_SET | WL_TIMEOUT | WL_POSTMASTER_DEATH,
						   PGARCH_AUTOWAKE_INTERVAL * 1000L,
						   WAIT_EVENT_ARCHIVER_MAIN);
			/* 【中文】postmaster 意外死亡（异常场景）：立即终止，
			 * 等新 postmaster 重新拉起 archiver */
			if (rc & WL_POSTMASTER_DEATH)
				time_to_stop = true;
		}

		/*
		 * The archiver quits either when the postmaster dies (not expected)
		 * or after completing one more archiving cycle after receiving
		 * SIGUSR2.
		 * 【中文】archiver 只在两种情况下退出：
		 * postmaster 死亡（意外情况），
		 * 或收到 SIGUSR2 后完成最后一轮归档循环（正常停机）。
		 */
	} while (!time_to_stop);
}

/*
 * pgarch_ArchiverCopyLoop
 *
 * Archives all outstanding xlogs then returns
 *
 * 【中文总述】归档循环核心：把当前所有"待归档"的 WAL 文件依次
 * 归档，全部处理完（或遇到必须放弃的情况）后返回。流程：
 *   1. 清空本批文件列表，强制下一次 pgarch_readyXlog() 重新扫描
 *      archive_status 目录
 *   2. 外层循环调用 pgarch_readyXlog() 取出一个优先级最高的
 *      待归档文件（WAL 段文件名，其 .ready 状态文件存在）
 *   3. 对每个文件进入"内部重试循环"（for(;;)）：
 *      a. 已收到 SIGTERM 或 postmaster 已死：立即返回，不再发起
 *         新归档（前者避免 init/服务管理器 SIGKILL 归档命令，
 *         后者避免与新版 postmaster 拉起的 archiver 冲突）
 *      b. ProcessPgArchInterrupts() 处理中断，让 archive_command /
 *         archive_library 的新配置尽快生效（即使有大量积压）
 *      c. 检查归档确实已配置（check_configured_cb），否则告警返回
 *      d. 若 WAL 段文件本体已不存在（被回收/删除，只剩 .ready），
 *         说明是崩溃残留的孤儿状态文件：删除它并继续下一个；
 *         删除失败最多重试 NUM_ORPHAN_CLEANUP_RETRIES 次
 *      e. pgarch_archiveXlog() 执行归档：
 *         - 成功 → pgarch_archiveDone() 把 .ready 改名 .done、
 *           上报统计，跳出重试循环处理下一个文件
 *         - 失败 → 上报统计后睡 1 秒重试，超过
 *           NUM_ARCHIVE_RETRIES（3）次则告警放弃，返回等下一轮
 *  批处理期间后端进程可能不断追加新的 .ready 文件，
 *  所以外层循环会一直持续到"本批取完且重新扫描也无新文件"。
 */
static void
pgarch_ArchiverCopyLoop(void)
{
	char		xlog[MAX_XFN_CHARS + 1];

	/* force directory scan in the first call to pgarch_readyXlog() */
	/* 【中文】清空本批文件列表，保证下一次调用
	 * pgarch_readyXlog() 一定会重新扫描 archive_status 目录。 */
	arch_files->arch_files_size = 0;

	/*
	 * loop through all xlogs with archive_status of .ready and archive
	 * them...mostly we expect this to be a single file, though it is possible
	 * some backend will add files onto the list of those that need archiving
	 * while we are still copying earlier archives
	 *
	 * 【中文】遍历所有带 .ready 状态文件的 WAL 段并归档。
	 * 通常一轮只有一个文件，但归档期间其它后端可能不断
	 * 追加新的 .ready 文件，所以外层循环要一直处理到取空。
	 */
	while (pgarch_readyXlog(xlog))
	{
		int			failures = 0;
		int			failures_orphan = 0;

		/* 【中文】内部重试循环：对同一个文件反复尝试，直到成功、
		 * 或达到重试上限（failures / failures_orphan 记录次数）、
		 * 或触发上面的退出条件。 */
		for (;;)
		{
			struct stat stat_buf;
			char		pathname[MAXPGPATH];

			/*
			 * Do not initiate any more archive commands after receiving
			 * SIGTERM, nor after the postmaster has died unexpectedly. The
			 * first condition is to try to keep from having init SIGKILL the
			 * command, and the second is to avoid conflicts with another
			 * archiver spawned by a newer postmaster.
			 *
			 * 【中文】停止发起新归档命令的两个条件：
			 *  - 已收到 SIGTERM：停机流程中 init/服务管理器可能
			 *    直接 SIGKILL 归档命令，再发起只会白忙或出错；
			 *  - postmaster 意外死亡：避免与新版 postmaster
			 *    拉起的另一个 archiver 对同一批文件重复操作。
			 */
			if (ShutdownRequestPending || !PostmasterIsAlive())
				return;

			/*
			 * Check for barrier events and config update.  This is so that
			 * we'll adopt a new setting for archive_command as soon as
			 * possible, even if there is a backlog of files to be archived.
			 * 【中文】处理中断（跨进程屏障、配置重载等），使
			 * archive_command / archive_library 的新设置尽快生效
			 * ——即使还有大量积压文件排队归档，也要及时采纳新配置。
			 */
			ProcessPgArchInterrupts();

			/* Reset variables that might be set by the callback */
			/* 【中文】清空归档插件回调可能写入的错误详情变量 */
			arch_module_check_errdetail_string = NULL;

			/* can't do anything if not configured ... */
			/* 【中文】归档未配置（如 archive_mode=on 但既没有
			 * archive_command 也没有可用的归档插件）：告警并返回，
			 * 等配置好之后的下一次循环再试。 */
			if (ArchiveCallbacks->check_configured_cb != NULL &&
				!ArchiveCallbacks->check_configured_cb(archive_module_state))
			{
				ereport(WARNING,
						(errmsg("\"archive_mode\" enabled, yet archiving is not configured"),
						 arch_module_check_errdetail_string ?
						 errdetail_internal("%s", arch_module_check_errdetail_string) : 0));
				return;
			}

			/*
			 * Since archive status files are not removed in a durable manner,
			 * a system crash could leave behind .ready files for WAL segments
			 * that have already been recycled or removed.  In this case,
			 * simply remove the orphan status file and move on.  unlink() is
			 * used here as even on subsequent crashes the same orphan files
			 * would get removed, so there is no need to worry about
			 * durability.
			 *
			 * 【中文】孤儿状态文件处理：.ready 文件的删除没有做
			 * 持久化（不 fsync），所以系统崩溃后可能残留"对应
			 * WAL 段已被回收/删除"的孤儿 .ready 文件。此时直接
			 * 删掉状态文件继续处理下一个即可；unlink 不做持久化
			 * 也没关系——即使再次崩溃，同一批孤儿文件照样会被
			 * 再删一次，结果一致。
			 */
			snprintf(pathname, MAXPGPATH, XLOGDIR "/%s", xlog);
			/* 【中文】WAL 段本体已不存在（被回收/删除）：
			 * 判定当前是孤儿状态文件，走清理分支 */
			if (stat(pathname, &stat_buf) != 0 && errno == ENOENT)
			{
				char		xlogready[MAXPGPATH];

				StatusFilePath(xlogready, xlog, ".ready");
				if (unlink(xlogready) == 0)
				{
					ereport(WARNING,
							(errmsg("removed orphan archive status file \"%s\"",
									xlogready)));

					/* leave loop and move to the next status file */
					/* 【中文】孤儿文件删除成功：
					 * 跳出重试循环，继续处理下一个状态文件 */
					break;
				}

				if (++failures_orphan >= NUM_ORPHAN_CLEANUP_RETRIES)
				{
					ereport(WARNING,
							(errmsg("removal of orphan archive status file \"%s\" failed too many times, will try again later",
									xlogready)));

					/* give up cleanup of orphan status files */
					/* 【中文】多次删除仍失败：放弃本次清理，
					 * 返回等下一轮再试（不影响正确性） */
					return;
				}

				/* wait a bit before retrying */
				/* 【中文】睡 1 秒再重试删除 */
				pg_usleep(1000000L);
				continue;
			}

			if (pgarch_archiveXlog(xlog))
			{
				/* successful */
				/* 【中文】归档成功：把状态文件 .ready 改名为
				 * .done，通知检查点进程该 WAL 段可以回收了 */
				pgarch_archiveDone(xlog);

				/*
				 * Tell the cumulative stats system about the WAL file that we
				 * successfully archived
				 * 【中文】向统计系统上报"成功归档"（false = 成功） */
				pgstat_report_archiver(xlog, false);

				break;			/* out of inner retry loop */
				/* 【中文】跳出内部重试循环，去取下一个文件 */
			}
			else
			{
				/*
				 * Tell the cumulative stats system about the WAL file that we
				 * failed to archive
				 * 【中文】上报"归档失败"（true = 失败） */
				pgstat_report_archiver(xlog, true);

				if (++failures >= NUM_ARCHIVE_RETRIES)
				{
					ereport(WARNING,
							(errmsg("archiving write-ahead log file \"%s\" failed too many times, will try again later",
									xlog)));
					return;		/* give up archiving for now */
					/* 【中文】重试满 3 次仍失败：告警后放弃本文件。
					 * 数据不会丢——.ready 状态文件还在，WAL 段会
					 * 一直保留，下一轮自动唤醒时会再试归档 */
				}
				pg_usleep(1000000L);	/* wait a bit before retrying */
				/* 【中文】睡 1 秒再重试归档 */
			}
		}
	}
}

/*
 * pgarch_archiveXlog
 *
 * Invokes archive_file_cb to copy one archive file to wherever it should go
 *
 * Returns true if successful
 *
 * 【中文】对单个 WAL 文件执行归档：调用已加载归档插件的
 * archive_file_cb 回调（默认的 shell_archive 就是去执行
 * archive_command 命令字符串，把文件复制/发送到归档目的地）。
 * 成功返回 true。
 * 特殊之处：archiver 处于异常栈的最底层，普通 ERROR 会升级为
 * FATAL 导致整个进程重启；本函数用 sigsetjmp 建一个局部异常
 * 处理器，把归档回调里抛出的 ERROR 捕获住，清理后返回 false，
 * 这样归档失败只会触发上层重试，而不是重启 archiver 进程。
 */
static bool
pgarch_archiveXlog(char *xlog)
{
	sigjmp_buf	local_sigjmp_buf;
	MemoryContext oldcontext;
	char		pathname[MAXPGPATH];
	char		activitymsg[MAXFNAMELEN + 16];
	bool		ret;

	/* 【中文】拼接 WAL 文件的完整路径：$PGDATA/pg_wal/<文件名> */
	snprintf(pathname, MAXPGPATH, XLOGDIR "/%s", xlog);

	/* Report archive activity in PS display */
	/* 【中文】在 ps 进程标题里显示当前归档活动，便于 DBA 观察 */
	snprintf(activitymsg, sizeof(activitymsg), "archiving %s", xlog);
	set_ps_display(activitymsg);

	/* 【中文】切换到归档专用内存上下文：本次归档产生的内存都
	 * 记在它名下，之后可整体 Reset 清理 */
	oldcontext = MemoryContextSwitchTo(archive_context);

	/*
	 * Since the archiver operates at the bottom of the exception stack,
	 * ERRORs turn into FATALs and cause the archiver process to restart.
	 * However, using ereport(ERROR, ...) when there are problems is easy to
	 * code and maintain.  Therefore, we create our own exception handler to
	 * catch ERRORs and return false instead of restarting the archiver
	 * whenever there is a failure.
	 *
	 * We assume ERRORs from the archiving callback are the most common
	 * exceptions experienced by the archiver, so we opt to handle exceptions
	 * here instead of PgArchiverMain() to avoid reinitializing the archiver
	 * too frequently.  We could instead add a sigsetjmp() block to
	 * PgArchiverMain() and use PG_TRY/PG_CATCH here, but the extra code to
	 * avoid the odd archiver restart doesn't seem worth it.
	 *
	 * 【中文】如上所述：ERROR 在 archiver 中会升级成 FATAL 导致进程
	 * 重启，所以这里用 sigsetjmp 捕获归档回调抛出的 ERROR：
	 * 进入错误分支做清理并返回 false。选择在这里处理而不是在
	 * PgArchiverMain() 里，是为了避免偶发的归档错误频繁触发
	 * archiver 重启重初始化（归档错误是最常见的异常类型）。
	 */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/* Since not using PG_TRY, must reset error stack by hand */
		/* 【中文】错误分支（归档回调抛了 ERROR）：
		 * 没用 PG_TRY 宏，必须手工重置错误栈指针 */
		error_context_stack = NULL;

		/* Prevent interrupts while cleaning up */
		/* 【中文】清理期间屏蔽中断，防止清理过程被打断 */
		HOLD_INTERRUPTS();

		/* Report the error to the server log. */
		/* 【中文】把捕获到的错误输出到服务端日志 */
		EmitErrorReport();

		/*
		 * Try to clean up anything the archive module left behind.  We try to
		 * cover anything that an archive module could conceivably have left
		 * behind, but it is of course possible that modules could be doing
		 * unexpected things that require additional cleanup.  Module authors
		 * should be sure to do any extra required cleanup in a PG_CATCH block
		 * within the archiving callback, and they are encouraged to notify
		 * the pgsql-hackers mailing list so that we can add it here.
		 *
		 * 【中文】尽量清理归档插件可能遗留的各种资源：禁用所有
		 * 超时、释放所有锁、取消条件变量睡眠、结束统计等待、
		 * AIO 错误清理、释放辅助进程资源（资源所有者）、
		 * 文件描述符与哈希表清理等。插件若有额外资源，应在
		 * 归档回调内用 PG_CATCH 自行清理。
		 */
		disable_all_timeouts(false);
		LWLockReleaseAll();
		ConditionVariableCancelSleep();
		pgstat_report_wait_end();
		pgaio_error_cleanup();
		ReleaseAuxProcessResources(false);
		AtEOXact_Files(false);
		AtEOXact_HashTables(false);

		/*
		 * Return to the original memory context and clear ErrorContext for
		 * next time.
		 * 【中文】切回原内存上下文，清空 ErrorContext 以备下次使用 */
		MemoryContextSwitchTo(oldcontext);
		FlushErrorState();

		/* Flush any leaked data */
		/* 【中文】把本次归档泄漏在 archive_context 里的数据
		 * 整体清空（整个上下文 Reset） */
		MemoryContextReset(archive_context);

		/* Remove our exception handler */
		/* 【中文】摘除异常处理器 */
		PG_exception_stack = NULL;

		/* Now we can allow interrupts again */
		/* 【中文】恢复允许中断 */
		RESUME_INTERRUPTS();

		/* Report failure so that the archiver retries this file */
		/* 【中文】返回 false，上层据此重试该文件 */
		ret = false;
	}
	else
	{
		/* Enable our exception handler */
		/* 【中文】正常分支：先安装异常处理器，再调用归档回调；
		 * 回调内部若 ereport(ERROR)，会跳回上面 sigsetjmp 的错误分支 */
		PG_exception_stack = &local_sigjmp_buf;

		/* Archive the file! */
		/* 【中文】真正执行归档：调用插件的 archive_file_cb
		 * （shell_archive 在此 fork/执行 archive_command） */
		ret = ArchiveCallbacks->archive_file_cb(archive_module_state,
												xlog, pathname);

		/* Remove our exception handler */
		/* 【中文】正常返回后摘除异常处理器 */
		PG_exception_stack = NULL;

		/* Reset our memory context and switch back to the original one */
		/* 【中文】清理本文件归档产生的内存，并切回原内存上下文 */
		MemoryContextSwitchTo(oldcontext);
		MemoryContextReset(archive_context);
	}

	/* 【中文】更新进程标题：显示上一个文件的归档结果 */
	if (ret)
		snprintf(activitymsg, sizeof(activitymsg), "last was %s", xlog);
	else
		snprintf(activitymsg, sizeof(activitymsg), "failed on %s", xlog);
	set_ps_display(activitymsg);

	return ret;
}

/*
 * pgarch_readyXlog
 *
 * Return name of the oldest xlog file that has not yet been archived.
 * No notification is set that file archiving is now in progress, so
 * this would need to be extended if multiple concurrent archival
 * tasks were created. If a failure occurs, we will completely
 * re-copy the file at the next available opportunity.
 *
 * It is important that we return the oldest, so that we archive xlogs
 * in order that they were written, for two reasons:
 * 1) to maintain the sequential chain of xlogs required for recovery
 * 2) because the oldest ones will sooner become candidates for
 * recycling at time of checkpoint
 *
 * NOTE: the "oldest" comparison will consider any .history file to be older
 * than any other file except another .history file.  Segments on a timeline
 * with a smaller ID will be older than all segments on a timeline with a
 * larger ID; the net result being that past timelines are given higher
 * priority for archiving.  This seems okay, or at least not obviously worth
 * changing.
 *
 * 【中文】从 archive_status 目录中取出"最老（优先级最高）的待归档
 * 文件"名字，拷入 xlog 参数并返回 true；没有待归档文件则返回 false。
 * 要点：
 *  - 必须优先返回最老的文件，保证按写入顺序归档，原因有二：
 *    1) 保持恢复所需的 WAL 顺序链完整；
 *    2) 最老的文件在下次检查点时最早成为可回收的候选。
 *  - "最老"的比较规则：.history 时间线历史文件永远比任何 WAL 段
 *    优先（时间线恢复的前提）；时间线 ID 较小的段整体优先于
 *    时间线 ID 较大的段——即过去时间线的文件优先归档。
 *  - 本函数不发送"归档进行中"的通知，暂不支持多个并发归档任务；
 *    若某文件归档失败，下一次机会时会完整重拷。
 *  - 内部实现：先用最大堆在目录扫描中选出优先级最高的
 *    NUM_FILES_PER_DIRECTORY_SCAN 个文件，再按优先级从低到高
 *    存入 arch_files[]，此后每次调用从中取一个，取完才再次扫描。
 */
static bool
pgarch_readyXlog(char *xlog)
{
	char		XLogArchiveStatusDir[MAXPGPATH];
	DIR		   *rldir;
	struct dirent *rlde;

	/*
	 * If a directory scan was requested, clear the stored file names and
	 * proceed.
	 * 【中文】若有人请求了强制扫描（PgArchForceDirScan 置位标志），
	 * 先清空已缓存的文件名列表，本次就走目录扫描路径。
	 */
	if (pg_atomic_exchange_u32(&PgArch->force_dir_scan, 0) == 1)
		arch_files->arch_files_size = 0;

	/*
	 * If we still have stored file names from the previous directory scan,
	 * try to return one of those.  We check to make sure the status file is
	 * still present, as the archive_command for a previous file may have
	 * already marked it done.
	 * 【中文】优先从上次扫描缓存的文件列表里返回：
	 * 从优先级高到低逐个检查其 .ready 状态文件是否还在——
	 * 归档上一个文件时可能已把它的状态文件改名 .done，
	 * 此时跳过即可（避免重复归档）。
	 */
	while (arch_files->arch_files_size > 0)
	{
		struct stat st;
		char		status_file[MAXPGPATH];
		char	   *arch_file;

		arch_files->arch_files_size--;
		arch_file = arch_files->arch_files[arch_files->arch_files_size];
		StatusFilePath(status_file, arch_file, ".ready");

		if (stat(status_file, &st) == 0)
		{
			/* 【中文】状态文件仍在：该文件确实待归档，
			 * 把文件名拷给调用者 */
			strcpy(xlog, arch_file);
			return true;
		}
		else if (errno != ENOENT)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not stat file \"%s\": %m", status_file)));
	}

	/* arch_heap is probably empty, but let's make sure */
	/* 【中文】堆理论上已空，保险起见显式重置 */
	binaryheap_reset(arch_files->arch_heap);

	/*
	 * Open the archive status directory and read through the list of files
	 * with the .ready suffix, looking for the earliest files.
	 * 【中文】打开 archive_status 目录，逐个读条目，
	 * 筛选出 .ready 文件并挑出最老（优先级最高）的一批 */
	snprintf(XLogArchiveStatusDir, MAXPGPATH, XLOGDIR "/archive_status");
	rldir = AllocateDir(XLogArchiveStatusDir);

	while ((rlde = ReadDir(rldir, XLogArchiveStatusDir)) != NULL)
	{
		int			basenamelen = (int) strlen(rlde->d_name) - 6;
		char		basename[MAX_XFN_CHARS + 1];
		char	   *arch_file;

		/* Ignore entries with unexpected number of characters */
		/* 【中文】去掉 .ready 后缀（6 个字符）后，文件名长度不在
		 * WAL 段名合法范围内的条目直接忽略 */
		if (basenamelen < MIN_XFN_CHARS ||
			basenamelen > MAX_XFN_CHARS)
			continue;

		/* Ignore entries with unexpected characters */
		/* 【中文】含有不在 VALID_XFN_CHARS 集合内的非法字符：忽略 */
		if (strspn(rlde->d_name, VALID_XFN_CHARS) < basenamelen)
			continue;

		/* Ignore anything not suffixed with .ready */
		/* 【中文】只关心 .ready 后缀的文件
		 * （.done 是已归档的，不管） */
		if (strcmp(rlde->d_name + basenamelen, ".ready") != 0)
			continue;

		/* Truncate off the .ready */
		/* 【中文】去掉 .ready 后缀，得到真正的 WAL 段文件名 */
		memcpy(basename, rlde->d_name, basenamelen);
		basename[basenamelen] = '\0';

		/*
		 * Store the file in our max-heap if it has a high enough priority.
		 * 【中文】把该文件放进最大堆——只有优先级够高才保留：
		 * 堆未满直接加；堆满了且新文件比堆顶更"老/优先"时，
		 * 替换掉堆中优先级最低的那个（比较规则见
		 * ready_file_comparator）。 */
		if (binaryheap_size(arch_files->arch_heap) < NUM_FILES_PER_DIRECTORY_SCAN)
		{
			/* If the heap isn't full yet, quickly add it. */
			/* 【中文】堆未满：直接无序加入（速度快），
			 * 到填满的那一刻才统一建堆 */
			arch_file = arch_files->arch_filenames[binaryheap_size(arch_files->arch_heap)];
			strcpy(arch_file, basename);
			binaryheap_add_unordered(arch_files->arch_heap, CStringGetDatum(arch_file));

			/* If we just filled the heap, make it a valid one. */
			/* 【中文】刚填满 64 个：把无序数组建成合法的堆 */
			if (binaryheap_size(arch_files->arch_heap) == NUM_FILES_PER_DIRECTORY_SCAN)
				binaryheap_build(arch_files->arch_heap);
		}
		else if (ready_file_comparator(binaryheap_first(arch_files->arch_heap),
									   CStringGetDatum(basename), NULL) > 0)
		{
			/*
			 * Remove the lowest priority file and add the current one to the
			 * heap.
			 * 【中文】新文件优先级高于堆中优先级最低者：
			 * 踢掉最低的，把新文件放进来（复用其存储位置） */
			arch_file = DatumGetCString(binaryheap_remove_first(arch_files->arch_heap));
			strcpy(arch_file, basename);
			binaryheap_add(arch_files->arch_heap, CStringGetDatum(arch_file));
		}
	}
	FreeDir(rldir);

	/* If no files were found, simply return. */
	/* 【中文】一个待归档文件都没找到：返回 false，本轮归档结束 */
	if (binaryheap_empty(arch_files->arch_heap))
		return false;

	/*
	 * If we didn't fill the heap, we didn't make it a valid one.  Do that
	 * now.
	 * 【中文】堆没填满时还只是无序数组，现在补一次建堆 */
	if (binaryheap_size(arch_files->arch_heap) < NUM_FILES_PER_DIRECTORY_SCAN)
		binaryheap_build(arch_files->arch_heap);

	/*
	 * Fill arch_files array with the files to archive in ascending order of
	 * priority.
	 * 【中文】把堆里的文件按优先级从低到高依次取出，
	 * 存入 arch_files[] 数组（数组末尾即优先级最高的文件） */
	arch_files->arch_files_size = binaryheap_size(arch_files->arch_heap);
	for (int i = 0; i < arch_files->arch_files_size; i++)
		arch_files->arch_files[i] = DatumGetCString(binaryheap_remove_first(arch_files->arch_heap));

	/* Return the highest priority file. */
	/* 【中文】返回优先级最高的文件（数组最后一个），
	 * 数组长度减一，下次调用继续从新的末尾取 */
	arch_files->arch_files_size--;
	strcpy(xlog, arch_files->arch_files[arch_files->arch_files_size]);

	return true;
}

/*
 * ready_file_comparator
 *
 * Compares the archival priority of the given files to archive.  If "a"
 * has a higher priority than "b", a negative value will be returned.  If
 * "b" has a higher priority than "a", a positive value will be returned.
 * If "a" and "b" have equivalent values, 0 will be returned.
 *
 * 【中文】比较两个待归档文件的优先级（供最大堆排序使用）：
 * a 优先级更高返回负值，b 更高返回正值，相等返回 0。
 * 规则：
 *   1. .history 时间线历史文件永远最高优先级（时间线切换后
 *      必须优先归档，否则无法重建该时间线）；
 *   2. 其余按文件名 strcmp 字典序比较——WAL 段文件名随时间线/
 *      序号递增，字典序越小越老，因此老文件优先归档。
 */
static int
ready_file_comparator(Datum a, Datum b, void *arg)
{
	char	   *a_str = DatumGetCString(a);
	char	   *b_str = DatumGetCString(b);
	bool		a_history = IsTLHistoryFileName(a_str);
	bool		b_history = IsTLHistoryFileName(b_str);

	/* Timeline history files always have the highest priority. */
	/* 【中文】历史文件 vs 普通段：历史文件优先 */
	if (a_history != b_history)
		return a_history ? -1 : 1;

	/* Priority is given to older files. */
	/* 【中文】同类型文件：字典序比较，较老（序号小）的优先 */
	return strcmp(a_str, b_str);
}

/*
 * PgArchForceDirScan
 *
 * When called, the next call to pgarch_readyXlog() will perform a
 * directory scan.  This is useful for ensuring that important files such
 * as timeline history files are archived as quickly as possible.
 *
 * 【中文】请求强制目录扫描：置位共享内存里的原子标志后，
 * 下一次 pgarch_readyXlog() 无论是否还有缓存的文件名，
 * 都会重新扫描 archive_status 目录。用于确保重要文件
 * （如时间线切换产生的 .history 历史文件）能第一时间被归档。
 * 该函数由其它进程（如执行时间线切换的后端）调用，可在
 * 持有锁的情况下安全使用（原子写 + 内存屏障）。
 */
void
PgArchForceDirScan(void)
{
	/* 【中文】带内存屏障的原子写：确保其它进程立即可见置位结果 */
	pg_atomic_write_membarrier_u32(&PgArch->force_dir_scan, 1);
}

/*
 * pgarch_archiveDone
 *
 * Emit notification that an xlog file has been successfully archived.
 * We do this by renaming the status file from NNN.ready to NNN.done.
 * Eventually, a checkpoint process will notice this and delete both the
 * NNN.done file and the xlog file itself.
 *
 * 【中文】归档成功后的"收尾通知"：把状态文件由 NNN.ready 改名为
 * NNN.done。.done 文件是"该 WAL 段已安全归档"的凭证，
 * 检查点进程之后发现它，就会把 .done 文件和 WAL 段本体一起
 * 删除，从而回收磁盘空间（否则 WAL 会无限累积）。
 */
static void
pgarch_archiveDone(char *xlog)
{
	char		rlogready[MAXPGPATH];
	char		rlogdone[MAXPGPATH];

	StatusFilePath(rlogready, xlog, ".ready");
	StatusFilePath(rlogdone, xlog, ".done");

	/*
	 * To avoid extra overhead, we don't durably rename the .ready file to
	 * .done.  Archive commands and libraries must gracefully handle attempts
	 * to re-archive files (e.g., if the server crashes just before this
	 * function is called), so it should be okay if the .ready file reappears
	 * after a crash.
	 *
	 * 【中文】这个改名刻意不做持久化（不 fsync），以省开销。
	 * 代价是：若恰在本函数调用前系统崩溃，.ready 文件会"复活"，
	 * 导致同一文件被再次归档——所以归档命令/插件必须容忍
	 * 重复归档（幂等性），这是归档系统的既定约定。
	 */
	if (rename(rlogready, rlogdone) < 0)
		ereport(WARNING,
				(errcode_for_file_access(),
				 errmsg("could not rename file \"%s\" to \"%s\": %m",
						rlogready, rlogdone)));
}


/*
 * pgarch_die
 *
 * Exit-time cleanup handler
 * 【中文】archiver 进程退出时的清理回调（on_shmem_exit 注册）：
 * 把共享内存里的 proc 编号恢复为无效，避免其它进程对已退出的
 * archiver 继续执行 SetLatch 等唤醒操作。
 */
static void
pgarch_die(int code, Datum arg)
{
	PgArch->pgprocno = INVALID_PROC_NUMBER;
}

/*
 * Interrupt handler for WAL archiver process.
 *
 * This is called in the loops pgarch_MainLoop and pgarch_ArchiverCopyLoop.
 * It checks for barrier events, config update and request for logging of
 * memory contexts, but not shutdown request because how to handle
 * shutdown request is different between those loops.
 *
 * 【中文】archiver 的中断处理函数（主循环和归档循环都会调用）：
 * 处理三类事件——跨进程信号屏障、配置重载（SIGHUP）、内存上下文
 * 日志请求；但刻意不处理停机请求（SIGTERM）：主循环和归档循环
 * 对停机的处理方式不同，由各循环按需自行判断。
 */
static void
ProcessPgArchInterrupts(void)
{
	/* 【中文】处理跨进程信号屏障（如"全员重读共享目录"等广播事件） */
	if (ProcSignalBarrierPending)
		ProcessProcSignalBarrier();

	/* Perform logging of memory contexts of this process */
	/* 【中文】若有请求，打印本进程各内存上下文的占用情况（调试用） */
	if (LogMemoryContextPending)
		ProcessLogMemoryContextInterrupt();

	if (ConfigReloadPending)
	{
		/* 【中文】SIGHUP 配置重载：先备份当前 archive_library 值，
		 * 重读配置文件，再对比是否发生了变化 */
		char	   *archiveLib = pstrdup(XLogArchiveLibrary);
		bool		archiveLibChanged;

		ConfigReloadPending = false;
		ProcessConfigFile(PGC_SIGHUP);

		/* 【中文】archive_command 与 archive_library 同时设置是非法
		 * 配置（两者互斥、只能二选一），直接报 ERROR 终止 */
		if (XLogArchiveLibrary[0] != '\0' && XLogArchiveCommand[0] != '\0')
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("both \"archive_command\" and \"archive_library\" set"),
					 errdetail("Only one of \"archive_command\", \"archive_library\" may be set.")));

		archiveLibChanged = strcmp(XLogArchiveLibrary, archiveLib) != 0;
		pfree(archiveLib);

		if (archiveLibChanged)
		{
			/*
			 * Ideally, we would simply unload the previous archive module and
			 * load the new one, but there is presently no mechanism for
			 * unloading a library (see the comment above
			 * internal_load_library()).  To deal with this, we simply restart
			 * the archiver.  The new archive module will be loaded when the
			 * new archiver process starts up.  Note that this triggers the
			 * module's shutdown callback, if defined.
			 *
			 * 【中文】archive_library 被换掉了：
			 * PostgreSQL 没有"卸载动态库"的机制（见
			 * internal_load_library() 上方的注释），所以干脆重启
			 * archiver 进程——新进程启动时会加载新插件；
			 * 注意这会顺带触发旧插件的 shutdown 回调（若定义了）。
			 */
			ereport(LOG,
					(errmsg("restarting archiver process because value of "
							"\"archive_library\" was changed")));

			/* 【中文】直接退出进程（走正常 proc_exit 清理流程），
			 * postmaster 会很快拉起一个新的 archiver */
			proc_exit(0);
		}
	}
}

/*
 * LoadArchiveLibrary
 *
 * Loads the archiving callbacks into our local ArchiveCallbacks.
 *
 * 【中文】加载归档插件，把回调函数表填入局部变量 ArchiveCallbacks：
 *   1. 校验 archive_command 与 archive_library 不能同时设置（互斥）
 *   2. 默认（XLogArchiveLibrary 为空串）使用内置的 shell_archive：
 *      它的 archive_file_cb 就是去执行 archive_command 这个 shell
 *      命令；否则 dlopen 指定的 .so 库，取名为
 *      _PG_archive_module_init 的入口函数
 *   3. 调用入口函数拿到回调表，校验必须注册了 archive_file_cb
 *   4. 分配插件状态并调用其 startup_cb（如有）；
 *      注册进程退出时调用 shutdown_cb（如有）
 */
static void
LoadArchiveLibrary(void)
{
	ArchiveModuleInit archive_init;

	/* 【中文】两个参数互斥校验：同时设置则直接报错终止 */
	if (XLogArchiveLibrary[0] != '\0' && XLogArchiveCommand[0] != '\0')
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("both \"archive_command\" and \"archive_library\" set"),
				 errdetail("Only one of \"archive_command\", \"archive_library\" may be set.")));

	/*
	 * If shell archiving is enabled, use our special initialization function.
	 * Otherwise, load the library and call its _PG_archive_module_init().
	 * 【中文】archive_library 为空串 → 走 archive_command 方式，
	 * 用内置的 shell_archive_init；否则动态加载用户库，
	 * 找到并解析其 _PG_archive_module_init 入口。 */
	if (XLogArchiveLibrary[0] == '\0')
		archive_init = shell_archive_init;
	else
		archive_init = (ArchiveModuleInit)
			load_external_function(XLogArchiveLibrary,
								   "_PG_archive_module_init", false, NULL);

	if (archive_init == NULL)
		ereport(ERROR,
				(errmsg("archive modules have to define the symbol %s", "_PG_archive_module_init")));

	/* 【中文】调用插件入口函数，得到归档回调函数表 */
	ArchiveCallbacks = (*archive_init) ();

	if (ArchiveCallbacks->archive_file_cb == NULL)
		ereport(ERROR,
				(errmsg("archive modules must register an archive callback")));

	/* 【中文】分配插件状态；若有 startup 回调则调用（插件初始化） */
	archive_module_state = palloc0_object(ArchiveModuleState);
	if (ArchiveCallbacks->startup_cb != NULL)
		ArchiveCallbacks->startup_cb(archive_module_state);

	/* 【中文】注册退出回调：进程退出前调用插件的 shutdown 回调 */
	before_shmem_exit(pgarch_call_module_shutdown_cb, 0);
}

/*
 * Call the shutdown callback of the loaded archive module, if defined.
 * 【中文】调用已加载归档插件的 shutdown 回调（若定义了）。
 * 作为 before_shmem_exit 回调，在 archiver 进程退出前执行，
 * 给插件一个做收尾工作（关闭连接、释放资源等）的机会。
 */
static void
pgarch_call_module_shutdown_cb(int code, Datum arg)
{
	if (ArchiveCallbacks->shutdown_cb != NULL)
		ArchiveCallbacks->shutdown_cb(archive_module_state);
}
