/*-------------------------------------------------------------------------
 *
 * autovacuum.c
 *
 * PostgreSQL Integrated Autovacuum Daemon
 *
 * The autovacuum system is structured in two different kinds of processes: the
 * autovacuum launcher and the autovacuum worker.  The launcher is an
 * always-running process, started by the postmaster when the autovacuum GUC
 * parameter is set.  The launcher schedules autovacuum workers to be started
 * when appropriate.  The workers are the processes which execute the actual
 * vacuuming; they connect to a database as determined in the launcher, and
 * once connected they examine the catalogs to select the tables to vacuum.
 *
 * The autovacuum launcher cannot start the worker processes by itself,
 * because doing so would cause robustness issues (namely, failure to shut
 * them down on exceptional conditions, and also, since the launcher is
 * connected to shared memory and is thus subject to corruption there, it is
 * not as robust as the postmaster).  So it leaves that task to the postmaster.
 *
 * There is an autovacuum shared memory area, where the launcher stores
 * information about the database it wants vacuumed.  When it wants a new
 * worker to start, it sets a flag in shared memory and sends a signal to the
 * postmaster.  Then postmaster knows nothing more than it must start a worker;
 * so it forks a new child, which turns into a worker.  This new process
 * connects to shared memory, and there it can inspect the information that the
 * launcher has set up.
 *
 * If the fork() call fails in the postmaster, it sets a flag in the shared
 * memory area, and sends a signal to the launcher.  The launcher, upon
 * noticing the flag, can try starting the worker again by resending the
 * signal.  Note that the failure can only be transient (fork failure due to
 * high load, memory pressure, too many processes, etc); more permanent
 * problems, like failure to connect to a database, are detected later in the
 * worker and dealt with just by having the worker exit normally.  The launcher
 * will launch a new worker again later, per schedule.
 *
 * When the worker is done vacuuming it sends SIGUSR2 to the launcher.  The
 * launcher then wakes up and is able to launch another worker, if the schedule
 * is so tight that a new worker is needed immediately.  At this time the
 * launcher can also balance the settings for the various remaining workers'
 * cost-based vacuum delay feature.
 *
 * Note that there can be more than one worker in a database concurrently.
 * They will store the table they are currently vacuuming in shared memory, so
 * that other workers avoid being blocked waiting for the vacuum lock for that
 * table.  They will also fetch the last time the table was vacuumed from
 * pgstats just before vacuuming each table, to avoid vacuuming a table that
 * was just finished being vacuumed by another worker and thus is no longer
 * noted in shared memory.  However, there is a small window (due to not yet
 * holding the relation lock) during which a worker may choose a table that was
 * already vacuumed; this is a bug in the current design.
 *
 * 【中文总述】
 * 本文件实现 PostgreSQL 的"集成式自动清理守护进程"（autovacuum），
 * 整个机制由两类进程分工协作：
 *   - autovacuum launcher（启动者）：常驻进程，postmaster 在
 *     autovacuum GUC 开启时启动它。它负责"排班"：决定何时、对哪个
 *     数据库启动一个 worker，但自己绝不直接清理任何表。
 *   - autovacuum worker（工作进程）：由 postmaster fork 出来的短期进程，
 *     负责真正的 VACUUM/ANALYZE。它按 launcher 指定的数据库连接上去，
 *     扫描系统目录（pg_class/pg_statistic）挑选需要清理的表。
 *
 * launcher 与 postmaster 的协作方式（关键设计）：
 *   1. launcher 不能自己 fork worker，因为那会带来健壮性问题（异常时
 *      无法统一关闭子进程；且 launcher 连着共享内存，若它本身被损坏
 *      则不可靠）。所以"fork 子进程"这件事必须交给 postmaster。
 *   2. 共享内存区（AutoVacuumShmem）中存放 launcher 想清理的数据库信息：
 *      launcher 想启动 worker 时，置共享内存标志位并给 postmaster 发信号；
 *      postmaster 只管 fork，新子进程连上共享内存后自行读取任务信息。
 *   3. fork 失败时 postmaster 在共享内存置 AutoVacForkFailed 标志并通知
 *      launcher，launcher 稍后重试（这类失败通常是瞬时的：负载高、内存
 *      紧张、进程数超限等）；而"连不上数据库"这类持久性错误由 worker
 *      正常退出处理，launcher 按计划稍后再启动新 worker。
 *   4. worker 干完活后给 launcher 发 SIGUSR2，launcher 被唤醒，若排班
 *      很紧可立即再启动一个 worker，并顺势重新平衡各 worker 的成本
 *      限额（cost-based vacuum delay）。
 *
 * 同一数据库可以同时存在多个 worker。每个 worker 正在清理的表会记入
 * 共享内存，其他 worker 据此避免去抢同一张表的 vacuum 锁；清理每张表
 * 前还会从 pgstats 再取一次该表的上次清理时间，避免重复清理。
 * （文件头部注释承认仍存在一个小的竞态窗口，属于当前设计的已知缺陷。）
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/autovacuum.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <math.h>
#include <signal.h>
#include <sys/time.h>
#include <unistd.h>

#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/multixact.h"
#include "access/reloptions.h"
#include "access/tableam.h"
#include "access/transam.h"
#include "access/xact.h"
#include "catalog/dependency.h"
#include "catalog/namespace.h"
#include "catalog/pg_database.h"
#include "catalog/pg_namespace.h"
#include "commands/vacuum.h"
#include "common/int.h"
#include "funcapi.h"
#include "lib/ilist.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "pgstat.h"
#include "postmaster/autovacuum.h"
#include "postmaster/interrupt.h"
#include "postmaster/postmaster.h"
#include "storage/aio_subsys.h"
#include "storage/bufmgr.h"
#include "storage/ipc.h"
#include "storage/fd.h"
#include "storage/latch.h"
#include "storage/lmgr.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/smgr.h"
#include "storage/subsystems.h"
#include "tcop/tcopprot.h"
#include "utils/fmgroids.h"
#include "utils/fmgrprotos.h"
#include "utils/guc_hooks.h"
#include "utils/injection_point.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/ps_status.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"
#include "utils/syscache.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"
#include "utils/tuplestore.h"
#include "utils/wait_event.h"


/*
 * GUC parameters
 * 【中文】以下均为 autovacuum 相关的 GUC 配置变量（全局，可被 postgresql.conf
 * 或 ALTER SYSTEM 修改）。launcher 与 worker 各自在进程内持有这些值的副本，
 * 配置文件被 reload（SIGHUP）时通过 ProcessConfigFile() 刷新。
 * 分组说明：
 *  - autovacuum_start_daemon：总开关，launcher 是否启动；
 *  - autovacuum_max_workers / autovacuum_worker_slots：最大并发 worker 数
 *    与共享内存中 worker 槽位数（后者通常应不小于前者）；
 *  - autovacuum_naptime：launcher 两次唤醒之间的最小间隔；
 *  - autovacuum_vac_thresh/vac_scale/vac_max_thresh 等：VACUUM 触发阈值
 *    的基准值与比例系数（阈值 = 基准 + 比例 × 表行数，且不超上限）；
 *  - autovacuum_anl_thresh/anl_scale：ANALYZE 的同类参数；
 *  - autovacuum_freeze_max_age / multixact_freeze_max_age：防 XID/MXID
 *    回卷的强制清理年龄上限；
 *  - autovacuum_vac_cost_delay / vac_cost_limit：清理时的成本控制
 *    （限流 I/O），与 vacuum_cost_delay/limit 对应；
 *  - autovacuum_work_mem：每个 autovacuum worker 可用的内存
 *    （-1 表示回退用 maintenance_work_mem）。
 */
bool		autovacuum_start_daemon = false;
int			autovacuum_worker_slots;
int			autovacuum_max_workers;
int			autovacuum_work_mem = -1;
int			autovacuum_naptime;
int			autovacuum_vac_thresh;
int			autovacuum_vac_max_thresh;
double		autovacuum_vac_scale;
int			autovacuum_vac_ins_thresh;
double		autovacuum_vac_ins_scale;
int			autovacuum_anl_thresh;
double		autovacuum_anl_scale;
int			autovacuum_freeze_max_age;
int			autovacuum_multixact_freeze_max_age;
double		autovacuum_freeze_score_weight = 1.0;
double		autovacuum_multixact_freeze_score_weight = 1.0;
double		autovacuum_vacuum_score_weight = 1.0;
double		autovacuum_vacuum_insert_score_weight = 1.0;
double		autovacuum_analyze_score_weight = 1.0;
double		autovacuum_vac_cost_delay;
int			autovacuum_vac_cost_limit;

int			Log_autovacuum_min_duration = 600000;
int			Log_autoanalyze_min_duration = 600000;

/* the minimum allowed time between two awakenings of the launcher */
/* 【中文】launcher 两次唤醒之间允许的最小/最大睡眠时间：
 *  - MIN_AUTOVAC_SLEEPTIME（100 毫秒）：数据库过多时排班间隔不能无限小，
 *    低于此值就按此值睡；
 *  - MAX_AUTOVAC_SLEEPTIME（300 秒）：上限，防止系统时钟回拨等异常
 *    场景下 launcher 陷入"无限期睡眠"。 */
#define MIN_AUTOVAC_SLEEPTIME 100.0 /* milliseconds */
#define MAX_AUTOVAC_SLEEPTIME 300	/* seconds */

/*
 * Variables to save the cost-related storage parameters for the current
 * relation being vacuumed by this autovacuum worker. Using these, we can
 * ensure we don't overwrite the values of vacuum_cost_delay and
 * vacuum_cost_limit after reloading the configuration file. They are
 * initialized to "invalid" values to indicate that no cost-related storage
 * parameters were specified and will be set in do_autovacuum() after checking
 * the storage parameters in table_recheck_autovac().
 * 【中文】保存"当前正在清理的表"的 cost 相关存储参数（来自该表
 * reloptions 的 vacuum_cost_delay / vacuum_cost_limit）。之所以要单独保存，
 * 是为了在清理过程中 reload 配置文件时，不把表级参数误覆盖成全局 GUC 值。
 * 初始值 -1 表示"未指定"，table_recheck_autovac() 会按表实际设置再填充。
 */
static double av_storage_param_cost_delay = -1;
static int	av_storage_param_cost_limit = -1;

/* Flags set by signal handlers */
/* 【中文】信号处理函数置位的标志（sig_atomic_t 保证信号上下文读写安全）。
 * got_SIGUSR2：launcher 收到 SIGUSR2 —— 表示有 worker 已就绪/干完活，
 * 或 postmaster 通知 worker fork 失败，launcher 需要醒来处理。 */
static volatile sig_atomic_t got_SIGUSR2 = false;

/* Comparison points for determining whether freeze_max_age is exceeded */
/* 【中文】比较基准点：recentXid 是当前最新事务号，recentMulti 是当前最新
 * MultiXactId。判断某库/某表是否"逼近回卷"时，用它俩减去各自的
 * freeze_max_age 得到强制清理界限，再与 datfrozenxid/relfrozenxid 比较。 */
static TransactionId recentXid;
static MultiXactId recentMulti;

/* Default freeze ages to use for autovacuum (varies by database) */
/* 【中文】当前数据库默认的 freeze 参数。在 do_autovacuum() 里根据
 * pg_database 的 datistemplate/datallowconn 决定：模板库与不可连接库用 0
 * （不做正常冻结），普通库则取 vacuum_freeze_* 系列 GUC 的值。 */
static int	default_freeze_min_age;
static int	default_freeze_table_age;
static int	default_multixact_freeze_min_age;
static int	default_multixact_freeze_table_age;

/* Memory context for long-lived data */
/* 【中文】本进程（launcher 或 worker）的常驻内存上下文。错误恢复时整个
 * 上下文被重置，借以回收所有泄漏的内存；launcher/worker 各自重新创建。 */
static MemoryContext AutovacMemCxt;

/* struct to keep track of databases in launcher */
/* 【中文】launcher 侧"数据库排班表"元素（挂在 DatabaseList 双向链表上）：
 * adl_datid：数据库 OID（同时作为 hash 的 key）；
 * adl_next_worker：该库下一次应该被启动 worker 的时间；
 * adl_score：排班顺序分（值越小越先进入排班周期）；
 * adl_node：链表节点。整个列表按 adl_next_worker 降序排列，
 * 队尾（next_worker 最小）的库就是下一次要处理的库。 */
typedef struct avl_dbase
{
	Oid			adl_datid;		/* hash key -- must be first */
	TimestampTz adl_next_worker;
	int			adl_score;
	dlist_node	adl_node;
} avl_dbase;

/* struct to keep track of databases in worker */
/* 【中文】worker 侧/launcher 选库时用的"数据库候选"结构：
 * adw_datid：数据库 OID；adw_name：库名；
 * adw_frozenxid / adw_minmulti：该库的 datfrozenxid / datminmxid，
 * 用于判断是否逼近 XID/MultiXactId 回卷；
 * adw_entry：该库在 pgstats 中的统计项（无统计则视为无活动，可跳过）。 */
typedef struct avw_dbase
{
	Oid			adw_datid;
	char	   *adw_name;
	TransactionId adw_frozenxid;
	MultiXactId adw_minmulti;
	PgStat_StatDBEntry *adw_entry;
} avw_dbase;

/* struct to keep track of tables to vacuum and/or analyze, in 1st pass */
/* 【中文】第一遍扫描（收集主表 + 记录"主表→TOAST 表"映射）用的结构：
 * 以 ar_toastrelid（TOAST 表 OID）为 hash key，记录其主表 OID 与主表的
 * reloptions 副本；第二遍扫 TOAST 表时，若 TOAST 自身没配 autovacuum
 * 参数，就用主表的参数顶上。 */
typedef struct av_relation
{
	Oid			ar_toastrelid;	/* hash key - must be first */
	Oid			ar_relid;
	bool		ar_hasrelopts;
	AutoVacOpts ar_reloptions;	/* copy of AutoVacOpts from the main table's
								 * reloptions, or NULL if none */
} av_relation;

/* struct to keep track of tables to vacuum and/or analyze, after rechecking */
/* 【中文】复查通过、确定要清理的表（autovacuum 阶段二的核心产物）：
 * at_relid：表 OID；at_params：组装好的 VACUUM/ANALYZE 参数
 * （含 freeze 年龄、是否防回卷、并行度等，交给 vacuum() 使用）；
 * at_storage_param_vac_cost_delay/limit：表级 cost 参数（-1/0 表示未指定）；
 * at_dobalance：该表是否参与全局 cost 限额平衡；
 * at_relname/at_nspname/at_datname：表名/模式名/库名（预取用于日志与报错）。 */
typedef struct autovac_table
{
	Oid			at_relid;
	VacuumParams at_params;
	double		at_storage_param_vac_cost_delay;
	int			at_storage_param_vac_cost_limit;
	bool		at_dobalance;
	char	   *at_relname;
	char	   *at_nspname;
	char	   *at_datname;
} autovac_table;

/*-------------
 * This struct holds information about a single worker's whereabouts.  We keep
 * an array of these in shared memory, sized according to
 * autovacuum_worker_slots.
 *
 * wi_links		entry into free list or running list
 * wi_dboid		OID of the database this worker is supposed to work on
 * wi_tableoid	OID of the table currently being vacuumed, if any
 * wi_sharedrel flag indicating whether table is marked relisshared
 * wi_proc		pointer to PGPROC of the running worker, NULL if not started
 * wi_launchtime Time at which this worker was launched
 * wi_dobalance Whether this worker should be included in balance calculations
 *
 * All fields are protected by AutovacuumLock, except for wi_tableoid and
 * wi_sharedrel which are protected by AutovacuumScheduleLock (note these
 * two fields are read-only for everyone except that worker itself).
 *-------------
 * 【中文】共享内存中记录"每个 worker 的行踪"的结构（数组大小为
 * autovacuum_worker_slots）。字段说明：
 *  wi_links：链表节点，worker 挂在 free 链表（空闲）或 running 链表（运行中）；
 *  wi_dboid：该 worker 负责的数据库；
 *  wi_tableoid：当前正在清理的表（InvalidOid 表示没有）；
 *  wi_sharedrel：该表是否 relisshared（共享表会被其他库的 worker 看见）；
 *  wi_proc：运行中 worker 的 PGPROC，NULL 表示还没启动；
 *  wi_launchtime：启动时刻（launcher 据此判断启动是否超时）；
 *  wi_dobalance：该 worker 是否参与全局 cost 限额平衡。
 * 锁规则：除 wi_tableoid / wi_sharedrel 由 AutovacuumScheduleLock 保护外，
 * 其余字段全部受 AutovacuumLock 保护。
 */
typedef struct WorkerInfoData
{
	dlist_node	wi_links;
	Oid			wi_dboid;
	Oid			wi_tableoid;
	PGPROC	   *wi_proc;
	TimestampTz wi_launchtime;
	pg_atomic_flag wi_dobalance;
	bool		wi_sharedrel;
} WorkerInfoData;

typedef struct WorkerInfoData *WorkerInfo;

/*
 * Possible signals received by the launcher from remote processes.  These are
 * stored atomically in shared memory so that other processes can set them
 * without locking.
 * 【中文】其他进程（postmaster、worker）通过共享内存发给 launcher 的信号：
 *  - AutoVacForkFailed：postmaster fork worker 失败，launcher 应稍后重发
 *    启动信号（launcher 主循环里 sleep 1 秒再发 PMSIGNAL_START_AUTOVAC_WORKER）；
 *  - AutoVacRebalance：有 worker 退出或表级参数变化，需要重算
 *    av_nworkersForBalance（参与 cost 限额平衡的 worker 数）。
 * 用 sig_atomic_t 存共享内存，写方可免加锁原子置位。
 */
typedef enum
{
	AutoVacForkFailed,			/* failed trying to start a worker */
	AutoVacRebalance,			/* rebalance the cost limits */
}			AutoVacuumSignal;

#define AutoVacNumSignals (AutoVacRebalance + 1)

/*
 * Autovacuum workitem array, stored in AutoVacuumShmem->av_workItems.  This
 * list is mostly protected by AutovacuumLock, except that if an item is
 * marked 'active' other processes must not modify the work-identifying
 * members.
 * 【中文】"工作项"机制：普通后端在处理某些操作（如 BRIN summarize range）时
 * 想把一部分活外包给 autovacuum worker 干（因为 worker 有额外的成本控制），
 * 于是通过 AutoVacuumRequestWork() 在共享内存数组 av_workItems 里登记一条
 * 记录。worker 处理完表之后会遍历该数组，把属于本数据库且尚未被认领的
 * 工作项取出执行。avw_type：类型（目前只有 AVW_BRINSummarizeRange）；
 * avw_used：槽位被占用；avw_active：已被某 worker 认领、正在处理中；
 * avw_database/avw_relation/avw_blockNumber：目标库/表/块号。
 * 大部分情况下由 AutovacuumLock 保护；已被标记 active 的项，其他进程
 * 不得再修改其工作标识字段。
 */
typedef struct AutoVacuumWorkItem
{
	AutoVacuumWorkItemType avw_type;
	bool		avw_used;		/* below data is valid */
	bool		avw_active;		/* being processed */
	Oid			avw_database;
	Oid			avw_relation;
	BlockNumber avw_blockNumber;
} AutoVacuumWorkItem;

#define NUM_WORKITEMS	256

/*-------------
 * The main autovacuum shmem struct.  On shared memory we store this main
 * struct and the array of WorkerInfo structs.  This struct keeps:
 *
 * av_signal		set by other processes to indicate various conditions
 * av_freeWorkers	the WorkerInfo freelist
 * av_runningWorkers the WorkerInfo non-free queue
 * av_startingWorker pointer to WorkerInfo currently being started (cleared by
 *					the worker itself as soon as it's up and running)
 * av_workItems		work item array
 * av_nworkersForBalance the number of autovacuum workers to use when
 * 					calculating the per worker cost limit
 *
 * This struct is protected by AutovacuumLock, except for av_signal and parts
 * of the worker list (see above).
 *-------------
 * 【中文】autovacuum 的共享内存主结构（"launcher↔postmaster↔worker"三方
 * 通信的中枢，存放于名为 "AutoVacuum Data" 的共享内存段）：
 *  - av_signal[]：其他进程置位的信号标志（fork 失败 / 需要重平衡）；
 *  - av_freeWorkers / av_runningWorkers：worker 槽位的空闲链表/运行链表；
 *  - av_startingWorker：正在启动中的 worker 槽位（worker 就绪后自行清空）；
 *  - av_workItems[]：普通后端委托的工作项数组；
 *  - av_nworkersForBalance：参与 cost 限额平衡的 worker 数（原子读写）。
 * 除 av_signal 及部分链表外，其余字段均受 AutovacuumLock 保护。
 */
typedef struct
{
	sig_atomic_t av_signal[AutoVacNumSignals];
	dclist_head av_freeWorkers;
	dlist_head	av_runningWorkers;
	WorkerInfo	av_startingWorker;
	AutoVacuumWorkItem av_workItems[NUM_WORKITEMS];
	pg_atomic_uint32 av_nworkersForBalance;
} AutoVacuumShmemStruct;

static AutoVacuumShmemStruct *AutoVacuumShmem;

static void AutoVacuumShmemRequest(void *arg);
static void AutoVacuumShmemInit(void *arg);

const ShmemCallbacks AutoVacuumShmemCallbacks = {
	.request_fn = AutoVacuumShmemRequest,
	.init_fn = AutoVacuumShmemInit,
};

/*
 * the database list (of avl_dbase elements) in the launcher, and the context
 * that contains it
 * 【中文】launcher 的数据库排班链表 DatabaseList 及其所属内存上下文
 * DatabaseListCxt。链表按 adl_next_worker 从大到小排列，队尾就是要
 * 最先处理的库；reload 配置或排班被打乱时用 rebuild_database_list() 重建。
 */
static dlist_head DatabaseList = DLIST_STATIC_INIT(DatabaseList);
static MemoryContext DatabaseListCxt = NULL;

/*
 * This struct is used by relation_needs_vacanalyze() to return the table's
 * score (i.e., the maximum of the component scores) as well as the component
 * scores themselves.
 * 【中文】relation_needs_vacanalyze() 的输出：一张表的"紧急程度评分"。
 * max 是各分量得分中的最大值（用于给待清理表排序，分越高越先处理）：
 *  - xid / mxid：按 (XID/MXID 年龄 ÷ 各自 freeze_max_age) 计算；
 *  - vac / vac_ins：死元组数、插入量分别与其阈值之比；
 *  - anl：自上次 ANALYZE 以来的变更量与其阈值之比。
 * 各分量还受 autovacuum_*_score_weight 权重调节（默认 1.0）。
 */
typedef struct
{
	double		max;			/* maximum of all values below */
	double		xid;			/* transaction ID component */
	double		mxid;			/* multixact ID component */
	double		vac;			/* vacuum component */
	double		vac_ins;		/* vacuum insert component */
	double		anl;			/* analyze component */
} AutoVacuumScores;

/*
 * This struct is used to track and sort the list of tables to process.
 * 【中文】do_autovacuum() 中待处理表的排序载体：把表 OID 与其评分绑在一起，
 * 用 list_sort() + TableToProcessComparator 按 score 降序排列，
 * 保证"最急需清理的表"排在前面先做。
 */
typedef struct
{
	Oid			oid;
	double		score;
} TableToProcess;

/*
 * Dummy pointer to persuade Valgrind that we've not leaked the array of
 * avl_dbase structs.  Make it global to ensure the compiler doesn't
 * optimize it away.
 */
#ifdef USE_VALGRIND
extern avl_dbase *avl_dbase_array;
avl_dbase  *avl_dbase_array;
#endif

/* Pointer to my own WorkerInfo, valid on each worker */
static WorkerInfo MyWorkerInfo = NULL;

static Oid	do_start_worker(void);
static void ProcessAutoVacLauncherInterrupts(void);
pg_noreturn static void AutoVacLauncherShutdown(void);
static void launcher_determine_sleep(bool canlaunch, bool recursing,
									 struct timeval *nap);
static void launch_worker(TimestampTz now);
static List *get_database_list(void);
static void rebuild_database_list(Oid newdb);
static int	db_comparator(const void *a, const void *b);
static void autovac_recalculate_workers_for_balance(void);

static void do_autovacuum(void);
static void FreeWorkerInfo(int code, Datum arg);

static autovac_table *table_recheck_autovac(Oid relid, HTAB *table_toast_map,
											TupleDesc pg_class_desc,
											int effective_multixact_freeze_max_age);
static void relation_needs_vacanalyze(Oid relid, AutoVacOpts *relopts,
									  Form_pg_class classForm,
									  int effective_multixact_freeze_max_age,
									  int elevel,
									  bool *dovacuum, bool *doanalyze, bool *wraparound,
									  AutoVacuumScores *scores);

static void autovacuum_do_vac_analyze(autovac_table *tab,
									  BufferAccessStrategy bstrategy);
static AutoVacOpts *extract_autovac_opts(HeapTuple tup,
										 TupleDesc pg_class_desc);
static void perform_work_item(AutoVacuumWorkItem *workitem);
static void autovac_report_activity(autovac_table *tab);
static void autovac_report_workitem(AutoVacuumWorkItem *workitem,
									const char *nspname, const char *relname);
static void avl_sigusr2_handler(SIGNAL_ARGS);
static bool av_worker_available(void);
static void check_av_worker_gucs(void);



/********************************************************************
 *					  AUTOVACUUM LAUNCHER CODE
 *
 * 【中文】launcher（启动者）模块：负责"排班与调度"，不干实际的清理活。
 * 主要职责：
 *  - 维护数据库排班链表 DatabaseList，按 autovacuum_naptime 为周期
 *    把各库的下次启动时间均匀铺开；
 *  - 决定"现在该不该启动一个 worker、该处理哪个库"（do_start_worker）；
 *  - 与 postmaster 协作：发 PMSIGNAL_START_AUTOVAC_WORKER 信号让
 *    postmaster 真正 fork worker；处理 fork 失败、worker 完成等回调；
 *  - 在 worker 数变化时重算全局 cost 限额的平衡。
 ********************************************************************/

/*
 * Main entry point for the autovacuum launcher process.
 * 【中文总述】
 * launcher 进程的入口（postmaster fork 后由 B_AUTOVAC_LAUNCHER 分发进来）。
 * 执行阶段概览：
 *   1. 准备工作：释放 postmaster 的内存上下文、初始化信号处理、
 *      InitProcess() 申请共享内存里的 PGPROC 槽位、BaseInit() 基础初始化、
 *      InitPostgres()（不连接任何数据库，只建立事务等基础设施）
 *   2. 创建常驻内存上下文 AutovacMemCxt，并搭好 sigsetjmp 错误恢复框架
 *      （出错后清理现场、睡 1 秒、回到循环头部，避免刷爆错误日志）
 *   3. 强制若干安全设置（search_path 置空、禁用 zero_damaged_pages、
 *      关掉各种 timeout、强制 READ COMMITTED），防止危险配置被
 *      非交互地应用到清理过程
 *   4. 若 autovacuum 实际被禁用（比如 track_counts 关了）：处于紧急
 *      模式，直接启动一个 worker 处理回卷后退出（紧急兜底逻辑）
 *   5. 首次构建数据库排班链表 rebuild_database_list(InvalidOid)
 *   6. 主循环（本函数核心）：
 *      a. 根据排班表算出本次睡眠时长 launcher_determine_sleep()
 *      b. WaitLatch() 等待（超时 = 排班到期；信号 = 有人唤我们）
 *      c. ProcessAutoVacLauncherInterrupts() 处理 SIGHUP 配置重载、
 *         关闭请求等中断
 *      d. 处理 got_SIGUSR2（有 worker 完成 / fork 失败 → 重平衡或重试）
 *      e. 检查能否启动新 worker（有空闲槽位、没有 worker 正在启动中）
 *      f. 到点则从排班表队尾取最该处理的库 → launch_worker() →
 *         do_start_worker() 选库并通知 postmaster fork worker
 *   7. 收到关闭请求 → AutoVacLauncherShutdown() 正常退出
 *
 * 注意：launcher 不连接任何具体数据库，它对 pg_database 的访问仅发生在
 * get_database_list() 里那唯一的一次事务中（可做 pg_database 顺序扫描）。
 */
void
AutoVacLauncherMain(const void *startup_data, size_t startup_data_len)
{
	sigjmp_buf	local_sigjmp_buf;

	Assert(startup_data_len == 0);

	/* Release postmaster's working memory context */
	/* 【中文】释放从 postmaster fork 继承来的 PostmasterContext，
	 * 避免它成为长期驻留的"垃圾场"（launcher 会常驻运行） */
	if (PostmasterContext)
	{
		MemoryContextDelete(PostmasterContext);
		PostmasterContext = NULL;
	}

	init_ps_display(NULL);

	ereport(DEBUG1,
			(errmsg_internal("autovacuum launcher started")));

	if (PostAuthDelay)
		pg_usleep(PostAuthDelay * 1000000L);

	Assert(GetProcessingMode() == InitProcessing);

	/*
	 * Set up signal handlers.  We operate on databases much like a regular
	 * backend, so we use the same signal handling.  See equivalent code in
	 * tcop/postgres.c.
	 * 【中文】信号处理与普通后端一致（launcher 对数据库的操作类似普通
	 * 后端）：SIGHUP 重载配置、SIGINT 取消、SIGTERM 关闭请求；
	 * SIGUSR2 专门用于"worker 状态变化"通知（avl_sigusr2_handler）。
	 */
	pqsignal(SIGHUP, SignalHandlerForConfigReload);
	pqsignal(SIGINT, StatementCancelHandler);
	pqsignal(SIGTERM, SignalHandlerForShutdownRequest);
	/* SIGQUIT handler was already set up by InitPostmasterChild */

	InitializeTimeouts();		/* establishes SIGALRM handler */

	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, avl_sigusr2_handler);
	pqsignal(SIGFPE, FloatExceptionHandler);
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/*
	 * Create a per-backend PGPROC struct in shared memory.  We must do this
	 * before we can use LWLocks or access any shared memory.
	 * 【中文】InitProcess()：在共享内存申请本进程的 PGPROC 槽位，
	 * 之后才能使用 LWLocks 和访问任何共享内存结构。
	 */
	InitProcess();

	/* Early initialization */
	BaseInit();

	InitPostgres(NULL, InvalidOid, NULL, InvalidOid, 0, NULL);

	SetProcessingMode(NormalProcessing);

	/*
	 * Create a memory context that we will do all our work in.  We do this so
	 * that we can reset the context during error recovery and thereby avoid
	 * possible memory leaks.
	 * 【中文】创建"工作专用"内存上下文 AutovacMemCxt（launcher 版本）。
	 * 所有长期数据都放这里，出错恢复时整体 MemoryContextReset() 回收，
	 * 防止常驻进程因反复出错而泄漏内存。
	 */
	AutovacMemCxt = AllocSetContextCreate(TopMemoryContext,
										  "Autovacuum Launcher",
										  ALLOCSET_DEFAULT_SIZES);
	MemoryContextSwitchTo(AutovacMemCxt);

	/*
	 * If an exception is encountered, processing resumes here.
	 *
	 * This code is a stripped down version of PostgresMain error recovery.
	 *
	 * Note that we use sigsetjmp(..., 1), so that the prevailing signal mask
	 * (to wit, BlockSig) will be restored when longjmp'ing to here.  Thus,
	 * signals other than SIGQUIT will be blocked until we complete error
	 * recovery.  It might seem that this policy makes the HOLD_INTERRUPTS()
	 * call redundant, but it is not since InterruptPending might be set
	 * already.
	 * 【中文】sigsetjmp 错误恢复入口：任何 ereport(ERROR) 都会 longjmp 回
	 * 这里（PostgresMain 错误恢复的简化版）。恢复流程：清错误栈 →
	 * 禁止中断 → 报告错误日志 → 回滚当前事务 → 释放各种资源
	 * （LWLock、缓冲区、文件等）→ 切回 AutovacMemCxt 并整体重置 →
	 * 重建空的排班链表 → 若已收到关闭请求则直接退出，否则睡 1 秒
	 * 再回到主循环（防止错误刷屏）。
	 */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/* since not using PG_TRY, must reset error stack by hand */
		error_context_stack = NULL;

		/* Prevents interrupts while cleaning up */
		HOLD_INTERRUPTS();

		/* Forget any pending QueryCancel or timeout request */
		disable_all_timeouts(false);
		QueryCancelPending = false; /* second to avoid race condition */

		/* Report the error to the server log */
		EmitErrorReport();

		/* Abort the current transaction in order to recover */
		AbortCurrentTransaction();

		/*
		 * Release any other resources, for the case where we were not in a
		 * transaction.
		 */
		LWLockReleaseAll();
		pgstat_report_wait_end();
		pgaio_error_cleanup();
		UnlockBuffers();
		/* this is probably dead code, but let's be safe: */
		if (AuxProcessResourceOwner)
			ReleaseAuxProcessResources(false);
		AtEOXact_Buffers(false);
		AtEOXact_SMgr();
		AtEOXact_Files(false);
		AtEOXact_HashTables(false);

		/*
		 * Now return to normal top-level context and clear ErrorContext for
		 * next time.
		 */
		MemoryContextSwitchTo(AutovacMemCxt);
		FlushErrorState();

		/* Flush any leaked data in the top-level context */
		MemoryContextReset(AutovacMemCxt);

		/* don't leave dangling pointers to freed memory */
		DatabaseListCxt = NULL;
		dlist_init(&DatabaseList);

		/* Now we can allow interrupts again */
		RESUME_INTERRUPTS();

		/* if in shutdown mode, no need for anything further; just go away */
		if (ShutdownRequestPending)
			AutoVacLauncherShutdown();

		/*
		 * Sleep at least 1 second after any error.  We don't want to be
		 * filling the error logs as fast as we can.
		 */
		pg_usleep(1000000L);
	}

	/* We can now handle ereport(ERROR) */
	PG_exception_stack = &local_sigjmp_buf;

	/* must unblock signals before calling rebuild_database_list */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * Set always-secure search path.  Launcher doesn't connect to a database,
	 * so this has no effect.
	 * 【中文】把 search_path 置空（安全起见；launcher 不连库，实际无影响）。
	 */
	SetConfigOption("search_path", "", PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force zero_damaged_pages OFF in the autovac process, even if it is set
	 * in postgresql.conf.  We don't really want such a dangerous option being
	 * applied non-interactively.
	 * 【中文】强制关闭 zero_damaged_pages：即使配置文件里开了也不能让
	 * 这个危险选项在无人值守的清理中被悄悄启用。
	 */
	SetConfigOption("zero_damaged_pages", "false", PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force settable timeouts off to avoid letting these settings prevent
	 * regular maintenance from being executed.
	 * 【中文】把各类超时强制清零（statement/transaction/lock/idle 超时），
	 * 防止用户的超时设置让自动维护无法执行。
	 */
	SetConfigOption("statement_timeout", "0", PGC_SUSET, PGC_S_OVERRIDE);
	SetConfigOption("transaction_timeout", "0", PGC_SUSET, PGC_S_OVERRIDE);
	SetConfigOption("lock_timeout", "0", PGC_SUSET, PGC_S_OVERRIDE);
	SetConfigOption("idle_in_transaction_session_timeout", "0",
					PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force default_transaction_isolation to READ COMMITTED.  We don't want
	 * to pay the overhead of serializable mode, nor add any risk of causing
	 * deadlocks or delaying other transactions.
	 * 【中文】事务隔离级别强制为 READ COMMITTED：既省 serializable 的开销，
	 * 也避免与业务事务产生死锁或互相拖延。
	 */
	SetConfigOption("default_transaction_isolation", "read committed",
					PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Even when system is configured to use a different fetch consistency,
	 * for autovac we always want fresh stats.
	 * 【中文】强制 stats_fetch_consistency=none：autovacuum 永远要拿到
	 * 最新的统计信息，即使系统全局配置了别的取数一致性策略。
	 */
	SetConfigOption("stats_fetch_consistency", "none", PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * In emergency mode, just start a worker (unless shutdown was requested)
	 * and go away.
	 * 【中文】紧急模式兜底：如果 AutoVacuumingActive() 返回 false（比如
	 * autovacuum 配置为关、但防回卷任务仍刻不容缓），就不进入正常排班
	 * 循环——直接启动一个 worker 处理最危险的库，然后本进程退出。
	 */
	if (!AutoVacuumingActive())
	{
		if (!ShutdownRequestPending)
			do_start_worker();
		proc_exit(0);			/* done */
	}

	/*
	 * Create the initial database list.  The invariant we want this list to
	 * keep is that it's ordered by decreasing next_worker.  As soon as an
	 * entry is updated to a higher time, it will be moved to the front (which
	 * is correct because the only operation is to add autovacuum_naptime to
	 * the entry, and time always increases).
	 * 【中文】首次构建排班链表（InvalidOid 表示没有"新库"）。
	 * 链表不变式：按 adl_next_worker 降序排列；某库被处理过后，其
	 * next_worker 只会增加（+autovacuum_naptime），所以把它移到表头
	 * 即可维持不变式。表尾 = 最久没被清理的库 = 下一次优先处理的库。
	 */
	rebuild_database_list(InvalidOid);

	/* loop until shutdown request */
	/* 【中文】launcher 主循环：醒着时做"该不该启动 worker"的决策，
	 * 没事干就按排班睡到下一次该醒的时间。 */
	while (!ShutdownRequestPending)
	{
		struct timeval nap;
		TimestampTz current_time = 0;
		bool		can_launch;

		/*
		 * This loop is a bit different from the normal use of WaitLatch,
		 * because we'd like to sleep before the first launch of a child
		 * process.  So it's WaitLatch, then ResetLatch, then check for
		 * wakening conditions.
		 * 【中文】与常规 WaitLatch 用法略有不同：顺序是"算睡眠时长 →
		 * 等待 → 复位 latch → 检查唤醒原因"，并且第一次启动子进程前
		 * 也要先睡（防止刚启动就连发 worker）。
		 */

		launcher_determine_sleep(av_worker_available(), false, &nap);

		/*
		 * Wait until naptime expires or we get some type of signal (all the
		 * signal handlers will wake us by calling SetLatch).
		 * 【中文】阻塞等待：要么排班时间到（WL_TIMEOUT），要么被信号
		 * 唤醒（latch 被 SetLatch）；postmaster 死了也会立即醒来退出
		 * （WL_EXIT_ON_PM_DEATH）。等待事件标记为 AUTOVACUUM_MAIN，
		 * 可在 pg_stat_activity 中观察。
		 */
		(void) WaitLatch(MyLatch,
						 WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
						 (nap.tv_sec * 1000L) + (nap.tv_usec / 1000L),
						 WAIT_EVENT_AUTOVACUUM_MAIN);

		ResetLatch(MyLatch);

		ProcessAutoVacLauncherInterrupts();

		/*
		 * a worker finished, or postmaster signaled failure to start a worker
		 * 【中文】got_SIGUSR2：有 worker 完成 / 就绪，或 postmaster 通知
		 * fork worker 失败。逐项检查共享内存中的两个信号位。
		 */
		if (got_SIGUSR2)
		{
			got_SIGUSR2 = false;

			/* rebalance cost limits, if needed */
			/* 【中文】AutoVacRebalance 置位：说明有 worker 退出/参数变化，
			 * 重算参与全局 cost 限额平衡的 worker 数量。 */
			if (AutoVacuumShmem->av_signal[AutoVacRebalance])
			{
				LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);
				AutoVacuumShmem->av_signal[AutoVacRebalance] = false;
				autovac_recalculate_workers_for_balance();
				LWLockRelease(AutovacuumLock);
			}

			if (AutoVacuumShmem->av_signal[AutoVacForkFailed])
			{
				/*
				 * If the postmaster failed to start a new worker, we sleep
				 * for a little while and resend the signal.  The new worker's
				 * state is still in memory, so this is sufficient.  After
				 * that, we restart the main loop.
				 *
				 * XXX should we put a limit to the number of times we retry?
				 * I don't think it makes much sense, because a future start
				 * of a worker will continue to fail in the same way.
				 * 【中文】fork 失败处理：睡 1 秒后重发
				 * PMSIGNAL_START_AUTOVAC_WORKER 信号（worker 槽位状态还
				 * 留在共享内存 av_startingWorker 里，直接重试即可），
				 * 然后 continue 重启主循环。XXX 注释质疑是否该限制重试
				 * 次数——作者认为没必要，因为"会失败的环境"短期内
				 * 大概率还会失败，限制了也白搭。
				 */
				AutoVacuumShmem->av_signal[AutoVacForkFailed] = false;
				pg_usleep(1000000L);	/* 1s */
				SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_WORKER);
				continue;
			}
		}

		/*
		 * There are some conditions that we need to check before trying to
		 * start a worker.  First, we need to make sure that there is a worker
		 * slot available.  Second, we need to make sure that no other worker
		 * failed while starting up.
		 * 【中文】启动新 worker 前的两道检查：
		 *  1. 有没有空闲 worker 槽位（受 autovacuum_max_workers 约束）；
		 *  2. 是否已有 worker 正处于"启动中"（av_startingWorker 非空）——
		 *     若正在启动的那个迟迟没好（超过 naptime 上限 60 秒），
		 *     判定启动超时，把它的槽位回收回空闲链表并告警。
		 * 后者的超时判定只针对 AutoVacWorkerMain 早期阶段的错误（此时
		 * worker 尚未从 startingWorker 指针上摘除自己）；fork 失败由
		 * AutoVacForkFailed 位单独处理，连库失败则 worker 自己退出。
		 */

		current_time = GetCurrentTimestamp();
		LWLockAcquire(AutovacuumLock, LW_SHARED);

		can_launch = av_worker_available();

		if (AutoVacuumShmem->av_startingWorker != NULL)
		{
			int			waittime;
			WorkerInfo	worker = AutoVacuumShmem->av_startingWorker;

			/*
			 * We can't launch another worker when another one is still
			 * starting up (or failed while doing so), so just sleep for a bit
			 * more; that worker will wake us up again as soon as it's ready.
			 * We will only wait autovacuum_naptime seconds (up to a maximum
			 * of 60 seconds) for this to happen however.  Note that failure
			 * to connect to a particular database is not a problem here,
			 * because the worker removes itself from the startingWorker
			 * pointer before trying to connect.  Problems detected by the
			 * postmaster (like fork() failure) are also reported and handled
			 * differently.  The only problems that may cause this code to
			 * fire are errors in the earlier sections of AutoVacWorkerMain,
			 * before the worker removes the WorkerInfo from the
			 * startingWorker pointer.
			 * 【中文】已有 worker 正在启动时，不再启动新的：继续睡，
			 * 等那个 worker 就绪后发 SIGUSR2 叫醒我们。只等最多
			 * min(autovacuum_naptime, 60) 秒——超时就认为启动失败，
			 * 回收槽位。注释特别说明：连库失败不会走到这里（worker 在
			 * 尝试连库之前就摘除了 startingWorker）；只有 AutoVacWorkerMain
			 * 早期阶段的错误才会触发超时回收。
			 */
			waittime = Min(autovacuum_naptime, 60) * 1000;
			if (TimestampDifferenceExceeds(worker->wi_launchtime, current_time,
										   waittime))
			{
				LWLockRelease(AutovacuumLock);
				LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);

				/*
				 * No other process can put a worker in starting mode, so if
				 * startingWorker is still INVALID after exchanging our lock,
				 * we assume it's the same one we saw above (so we don't
				 * recheck the launch time).
				 * 【中文】升级为排他锁后确认 av_startingWorker 还在（别的
				 * 进程不可能把它改成"启动中"，所以仍是原来那个），
				 * 将其字段清空并推回空闲链表：该 worker 被判启动超时。
				 */
				if (AutoVacuumShmem->av_startingWorker != NULL)
				{
					worker = AutoVacuumShmem->av_startingWorker;
					worker->wi_dboid = InvalidOid;
					worker->wi_tableoid = InvalidOid;
					worker->wi_sharedrel = false;
					worker->wi_proc = NULL;
					worker->wi_launchtime = 0;
					dclist_push_head(&AutoVacuumShmem->av_freeWorkers,
									 &worker->wi_links);
					AutoVacuumShmem->av_startingWorker = NULL;
					ereport(WARNING,
							errmsg("autovacuum worker took too long to start; canceled"));
				}
			}
			else
				can_launch = false;
		}
		LWLockRelease(AutovacuumLock);	/* either shared or exclusive */

		/* if we can't do anything, just go back to sleep */
		/* 【中文】槽位不足或正在启动的 worker 还没超时：本轮不启动，直接
		 * continue 回到循环头部重新算睡眠时长。 */
		if (!can_launch)
			continue;

		/* We're OK to start a new worker */

		if (dlist_is_empty(&DatabaseList))
		{
			/*
			 * Special case when the list is empty: start a worker right away.
			 * This covers the initial case, when no database is in pgstats
			 * (thus the list is empty).  Note that the constraints in
			 * launcher_determine_sleep keep us from starting workers too
			 * quickly (at most once every autovacuum_naptime when the list is
			 * empty).
			 * 【中文】排班表为空（比如 pgstats 里还没有任何库的统计）的
			 * 特例：立即启动一个 worker（do_start_worker 会自己去选库）。
			 * 好在 launcher_determine_sleep 已保证空表时至少每隔
			 * autovacuum_naptime 才醒一次，不会疯狂启动 worker。
			 */
			launch_worker(current_time);
		}
		else
		{
			/*
			 * because rebuild_database_list constructs a list with most
			 * distant adl_next_worker first, we obtain our database from the
			 * tail of the list.
			 * 【中文】排班表非空：队尾元素的 adl_next_worker 最小（最久
			 * 没被清理的库），它就是下一个候选库。
			 */
			avl_dbase  *avdb;

			avdb = dlist_tail_element(avl_dbase, adl_node, &DatabaseList);

			/*
			 * launch a worker if next_worker is right now or it is in the
			 * past
			 * 【中文】若该库的"下次启动时间"已到（不晚于当前时刻），
			 * 就启动 worker 去处理它。
			 */
			if (TimestampDifferenceExceeds(avdb->adl_next_worker,
										   current_time, 0))
				launch_worker(current_time);
		}
	}

	AutoVacLauncherShutdown();
}

/*
 * Process any new interrupts.
 * 【中文】launcher 被唤醒后统一处理各类中断（信号处理器只负责置标志 +
 * SetLatch，真正的处理都在这里做）：
 *  - ShutdownRequestPending：收到关闭请求，直接退出；
 *  - ConfigReloadPending：重载配置文件；若配置里关了 autovacuum 也退出；
 *    autovacuum_max_workers 变化时检查与 worker_slots 的配合并告警；
 *    若 naptime 变了，重建排班链表；
 *  - ProcSignalBarrierPending：处理进程信号栅栏事件；
 *  - LogMemoryContextPending：输出本进程内存上下文（诊断用）；
 *  - ProcessCatchupInterrupt()：处理睡眠期间堆积的 sinval catchup。
 */
static void
ProcessAutoVacLauncherInterrupts(void)
{
	/* the normal shutdown case */
	if (ShutdownRequestPending)
		AutoVacLauncherShutdown();

	if (ConfigReloadPending)
	{
		int			autovacuum_max_workers_prev = autovacuum_max_workers;

		ConfigReloadPending = false;
		ProcessConfigFile(PGC_SIGHUP);

		/* shutdown requested in config file? */
		/* 【中文】配置里把 autovacuum 关掉了（比如 autovacuum=off），
		 * launcher 也就没有存在意义了，直接退出。 */
		if (!AutoVacuumingActive())
			AutoVacLauncherShutdown();

		/*
		 * If autovacuum_max_workers changed, emit a WARNING if
		 * autovacuum_worker_slots < autovacuum_max_workers.  If it didn't
		 * change, skip this to avoid too many repeated log messages.
		 * 【中文】只有 autovacuum_max_workers 真的变了才检查并告警，
		 * 否则每次 SIGHUP 都刷同样的 WARNING 会很烦人。
		 */
		if (autovacuum_max_workers_prev != autovacuum_max_workers)
			check_av_worker_gucs();

		/* rebuild the list in case the naptime changed */
		/* 【中文】naptime 可能被改：按新周期重建排班链表。 */
		rebuild_database_list(InvalidOid);
	}

	/* Process barrier events */
	/* 【中文】进程信号栅栏（用于需要全体进程协同的场景） */
	if (ProcSignalBarrierPending)
		ProcessProcSignalBarrier();

	/* Perform logging of memory contexts of this process */
	if (LogMemoryContextPending)
		ProcessLogMemoryContextInterrupt();

	/* Process sinval catchup interrupts that happened while sleeping */
	ProcessCatchupInterrupt();
}

/*
 * Perform a normal exit from the autovac launcher.
 * 【中文】launcher 正常退出：打 DEBUG1 日志后 proc_exit(0)。
 * proc_exit 会触发注册的 on_proc_exit/on_shmem_exit 回调做资源清理。
 */
static void
AutoVacLauncherShutdown(void)
{
	ereport(DEBUG1,
			(errmsg_internal("autovacuum launcher shutting down")));
	proc_exit(0);				/* done */
}

/*
 * Determine the time to sleep, based on the database list.
 *
 * The "canlaunch" parameter indicates whether we can start a worker right now,
 * for example due to the workers being all busy.  If this is false, we will
 * cause a long sleep, which will be interrupted when a worker exits.
 * 【中文】根据排班链表算出 launcher 本次该睡多久（输出到 nap）：
 *  - canlaunch=false（没有空闲 worker 槽位）：睡满一个
 *    autovacuum_naptime，等 worker 退出时被 SIGUSR2 打断；
 *  - 排班表非空：睡到队尾元素（最该处理的库）的 next_worker 时刻；
 *  - 排班表为空：睡满一个 autovacuum_naptime。
 * 边界处理：
 *  - 计算结果为 0（说明有库的 next_worker 已经过期）：重建排班表再
 *    递归算一次（最多递归一层，防止排班函数本身有缺陷导致死递归）；
 *  - 结果小于 MIN_AUTOVAC_SLEEPTIME（100ms）：按最小睡眠时间睡，
 *    防止数据库太多时把 launcher 忙死；
 *  - 结果大于 MAX_AUTOVAC_SLEEPTIME（300s）：截断，防止系统时钟
 *    回拨等异常导致无限期睡眠。
 */
static void
launcher_determine_sleep(bool canlaunch, bool recursing, struct timeval *nap)
{
	/*
	 * We sleep until the next scheduled vacuum.  We trust that when the
	 * database list was built, care was taken so that no entries have times
	 * in the past; if the first entry has too close a next_worker value, or a
	 * time in the past, we will sleep a small nominal time.
	 */
	if (!canlaunch)
	{
		nap->tv_sec = autovacuum_naptime;
		nap->tv_usec = 0;
	}
	else if (!dlist_is_empty(&DatabaseList))
	{
		TimestampTz current_time = GetCurrentTimestamp();
		TimestampTz next_wakeup;
		avl_dbase  *avdb;
		long		secs;
		int			usecs;

		avdb = dlist_tail_element(avl_dbase, adl_node, &DatabaseList);

		/* 【中文】队尾 = next_worker 最近的库，睡到它该被处理的时间 */
		next_wakeup = avdb->adl_next_worker;
		TimestampDifference(current_time, next_wakeup, &secs, &usecs);

		nap->tv_sec = secs;
		nap->tv_usec = usecs;
	}
	else
	{
		/* list is empty, sleep for whole autovacuum_naptime seconds  */
		nap->tv_sec = autovacuum_naptime;
		nap->tv_usec = 0;
	}

	/*
	 * If the result is exactly zero, it means a database had an entry with
	 * time in the past.  Rebuild the list so that the databases are evenly
	 * distributed again, and recalculate the time to sleep.  This can happen
	 * if there are more tables needing vacuum than workers, and they all take
	 * longer to vacuum than autovacuum_naptime.
	 *
	 * We only recurse once.  rebuild_database_list should always return times
	 * in the future, but it seems best not to trust too much on that.
	 * 【中文】睡眠时长为 0 说明有库的排班时间已过期（典型场景：需要清理
	 * 的表比 worker 多，单表耗时又超过 naptime）。解决办法：重建排班表
	 * 让各库重新均匀分布，然后递归重算；只递归一次，不信任
	 * rebuild_database_list 会永远返回未来时刻。
	 */
	if (nap->tv_sec == 0 && nap->tv_usec == 0 && !recursing)
	{
		rebuild_database_list(InvalidOid);
		launcher_determine_sleep(canlaunch, true, nap);
		return;
	}

	/* The smallest time we'll allow the launcher to sleep. */
	/* 【中文】睡眠时长下限：100ms，防止空转忙等 */
	if (nap->tv_sec <= 0 && nap->tv_usec <= MIN_AUTOVAC_SLEEPTIME * 1000)
	{
		nap->tv_sec = 0;
		nap->tv_usec = MIN_AUTOVAC_SLEEPTIME * 1000;
	}

	/*
	 * If the sleep time is too large, clamp it to an arbitrary maximum (plus
	 * any fractional seconds, for simplicity).  This avoids an essentially
	 * infinite sleep in strange cases like the system clock going backwards a
	 * few years.
	 * 【中文】睡眠时长上限：300 秒。防止系统时钟异常（如回拨数年）
	 * 导致 launcher 近乎无限期睡眠。
	 */
	if (nap->tv_sec > MAX_AUTOVAC_SLEEPTIME)
		nap->tv_sec = MAX_AUTOVAC_SLEEPTIME;
}

/*
 * Build an updated DatabaseList.  It must only contain databases that appear
 * in pgstats, and must be sorted by next_worker from highest to lowest,
 * distributed regularly across the next autovacuum_naptime interval.
 *
 * Receives the Oid of the database that made this list be generated (we call
 * this the "new" database, because when the database was already present on
 * the list, we expect that this function is not called at all).  The
 * preexisting list, if any, will be used to preserve the order of the
 * databases in the autovacuum_naptime period.  The new database is put at the
 * end of the interval.  The actual values are not saved, which should not be
 * much of a problem.
 * 【中文】重建 launcher 的数据库排班链表（launcher 启动时、naptime 变化、
 * 排班过期、数据库被删等场景都会调用）。核心思路（"打分 + 排序"）：
 *   1. 建一个临时 hash（key = 库 OID），给每个库打 adl_score 分：
 *      - "新库"（newdb 参数指定，launch_worker 找不到对应项时传入）
 *        得最低分 0；
 *      - 原链表里还在的库（按原顺序）接着加分；
 *      - get_database_list() 扫出来的其余合格库（有 pgstats 统计的）
 *        最后加分。没有 pgstats 统计的库一律跳过（含已删除的库）。
 *   2. 把 hash 元素拷进数组，按 score 排序（db_comparator，降序）；
 *   3. 把一个 autovacuum_naptime 周期按库数量均匀切分
 *      （millis_increment = naptime/库数，且不低于最小睡眠时间），
 *      从当前时刻起逐个累加得到各库的 adl_next_worker；
 *   4. 按"时间越远越靠表头"的规则把元素链进 DatabaseList，
 *      使链表保持"队尾 next_worker 最小"的不变式。
 * 最后回收旧链表的内存上下文，换成新链表所属的 newcxt。
 */
static void
rebuild_database_list(Oid newdb)
{
	List	   *dblist;
	ListCell   *cell;
	MemoryContext newcxt;
	MemoryContext oldcxt;
	MemoryContext tmpcxt;
	HASHCTL		hctl;
	int			score;
	int			nelems;
	HTAB	   *dbhash;
	dlist_iter	iter;

	/* 【中文】新排班表放 newcxt，中间计算放其子上下文 tmpcxt
	 * （结束后整体删除，不污染常驻上下文） */
	newcxt = AllocSetContextCreate(AutovacMemCxt,
								   "Autovacuum database list",
								   ALLOCSET_DEFAULT_SIZES);
	tmpcxt = AllocSetContextCreate(newcxt,
								   "Autovacuum database list (tmp)",
								   ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(tmpcxt);

	/*
	 * Implementing this is not as simple as it sounds, because we need to put
	 * the new database at the end of the list; next the databases that were
	 * already on the list, and finally (at the tail of the list) all the
	 * other databases that are not on the existing list.
	 *
	 * To do this, we build an empty hash table of scored databases.  We will
	 * start with the lowest score (zero) for the new database, then
	 * increasing scores for the databases in the existing list, in order, and
	 * lastly increasing scores for all databases gotten via
	 * get_database_list() that are not already on the hash.
	 *
	 * Then we will put all the hash elements into an array, sort the array by
	 * score, and finally put the array elements into the new doubly linked
	 * list.
	 */
	hctl.keysize = sizeof(Oid);
	hctl.entrysize = sizeof(avl_dbase);
	hctl.hcxt = tmpcxt;
	dbhash = hash_create("autovacuum db hash", 20, &hctl,	/* magic number here
															 * FIXME */
						 HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);

	/* start by inserting the new database */
	/* 【中文】第一步：新库（若有）得分 0，排在排班周期最前面 */
	score = 0;
	if (OidIsValid(newdb))
	{
		avl_dbase  *db;
		PgStat_StatDBEntry *entry;

		/* only consider this database if it has a pgstat entry */
		/* 【中文】没统计的库不考虑（说明它从没有被访问过/已被删） */
		entry = pgstat_fetch_stat_dbentry(newdb);
		if (entry != NULL)
		{
			/* we assume it isn't found because the hash was just created */
			db = hash_search(dbhash, &newdb, HASH_ENTER, NULL);

			/* hash_search already filled in the key */
			db->adl_score = score++;
			/* next_worker is filled in later */
		}
	}

	/* Now insert the databases from the existing list */
	/* 【中文】第二步：原链表中的库按原相对顺序依次加分，保持周期内
	 * 各库的先后次序（这些库是最需要维持顺序的） */
	dlist_foreach(iter, &DatabaseList)
	{
		avl_dbase  *avdb = dlist_container(avl_dbase, adl_node, iter.cur);
		avl_dbase  *db;
		bool		found;
		PgStat_StatDBEntry *entry;

		/*
		 * skip databases with no stat entries -- in particular, this gets rid
		 * of dropped databases
		 * 【中文】跳过没有统计项的库——尤其能借此淘汰已删除的库。
		 */
		entry = pgstat_fetch_stat_dbentry(avdb->adl_datid);
		if (entry == NULL)
			continue;

		db = hash_search(dbhash, &(avdb->adl_datid), HASH_ENTER, &found);

		if (!found)
		{
			/* hash_search already filled in the key */
			db->adl_score = score++;
			/* next_worker is filled in later */
		}
	}

	/* finally, insert all qualifying databases not previously inserted */
	/* 【中文】第三步：其余所有合格库（新出现、原来没在链表上的库）
	 * 最后加分——它们会被排到周期的末尾，保证新库不会插队抢占
	 * 已有库的排班时机 */
	dblist = get_database_list();
	foreach(cell, dblist)
	{
		avw_dbase  *avdb = lfirst(cell);
		avl_dbase  *db;
		bool		found;
		PgStat_StatDBEntry *entry;

		/* only consider databases with a pgstat entry */
		entry = pgstat_fetch_stat_dbentry(avdb->adw_datid);
		if (entry == NULL)
			continue;

		db = hash_search(dbhash, &(avdb->adw_datid), HASH_ENTER, &found);
		/* only update the score if the database was not already on the hash */
		if (!found)
		{
			/* hash_search already filled in the key */
			db->adl_score = score++;
			/* next_worker is filled in later */
		}
	}
	nelems = score;

	/* from here on, the allocated memory belongs to the new list */
	/* 【中文】切换回 newcxt 分配排班链表本身（tmpcxt 只留临时计算数据） */
	MemoryContextSwitchTo(newcxt);
	dlist_init(&DatabaseList);

	if (nelems > 0)
	{
		TimestampTz current_time;
		int			millis_increment;
		avl_dbase  *dbary;
		avl_dbase  *db;
		HASH_SEQ_STATUS seq;
		int			i;

		/* put all the hash elements into an array */
		/* 【中文】把 hash 里的元素全部拷进数组（后面要 qsort） */
		dbary = palloc(nelems * sizeof(avl_dbase));
		/* keep Valgrind quiet */
		/* 【中文】让 Valgrind 以为数组没泄漏（仅供 Valgrind 构建） */
#ifdef USE_VALGRIND
		avl_dbase_array = dbary;
#endif

		i = 0;
		hash_seq_init(&seq, dbhash);
		while ((db = hash_seq_search(&seq)) != NULL)
			memcpy(&(dbary[i++]), db, sizeof(avl_dbase));

		/* sort the array */
		/* 【中文】按 score 降序排序：score 小的（新库）排在数组后面 */
		qsort(dbary, nelems, sizeof(avl_dbase), db_comparator);

		/*
		 * Determine the time interval between databases in the schedule. If
		 * we see that the configured naptime would take us to sleep times
		 * lower than our min sleep time (which launcher_determine_sleep is
		 * coded not to allow), silently use a larger naptime (but don't touch
		 * the GUC variable).
		 * 【中文】库之间的排班间隔 = naptime ÷ 库数。若算出的间隔比
		 * 最小睡眠时间还小（库太多了），就悄悄放大间隔
		 * （MIN_AUTOVAC_SLEEPTIME × 1.1），不修改 GUC 变量本身。
		 */
		millis_increment = 1000.0 * autovacuum_naptime / nelems;
		if (millis_increment <= MIN_AUTOVAC_SLEEPTIME)
			millis_increment = MIN_AUTOVAC_SLEEPTIME * 1.1;

		current_time = GetCurrentTimestamp();

		/*
		 * move the elements from the array into the dlist, setting the
		 * next_worker while walking the array
		 * 【中文】数组元素逐个入链表：每个库的 next_worker = 当前时刻 +
		 * 累计间隔。注意这里"时间越晚越靠表头"：队尾反而是 next_worker
		 * 最小（最该先处理）的库，符合主循环的取数习惯。
		 */
		for (i = 0; i < nelems; i++)
		{
			db = &(dbary[i]);

			current_time = TimestampTzPlusMilliseconds(current_time,
													   millis_increment);
			db->adl_next_worker = current_time;

			/* later elements should go closer to the head of the list */
			dlist_push_head(&DatabaseList, &db->adl_node);
		}
	}

	/* all done, clean up memory */
	/* 【中文】回收旧链表上下文与临时上下文，换用新链表上下文 */
	if (DatabaseListCxt != NULL)
		MemoryContextDelete(DatabaseListCxt);
	MemoryContextDelete(tmpcxt);
	DatabaseListCxt = newcxt;
	MemoryContextSwitchTo(oldcxt);
}

/* qsort comparator for avl_dbase, using adl_score */
/* 【中文】排班表排序比较器：按 adl_score 降序（b 比 a，>0 则 b 在前），
 * 使得"分高（后来加入）的库"排在数组前面（后面链入链表时被 push_head
 * 到更靠近表头，即更晚处理）。 */
static int
db_comparator(const void *a, const void *b)
{
	return pg_cmp_s32(((const avl_dbase *) b)->adl_score,
					  ((const avl_dbase *) a)->adl_score);
}

/*
 * do_start_worker
 *
 * Bare-bones procedure for starting an autovacuum worker from the launcher.
 * It determines what database to work on, sets up shared memory stuff and
 * signals postmaster to start the worker.  It fails gracefully if invoked when
 * autovacuum_workers are already active.
 *
 * Return value is the OID of the database that the worker is going to process,
 * or InvalidOid if no worker was actually started.
 * 【中文】launcher 侧"真正选库并启动 worker"的函数（不依赖排班表，
 * 紧急模式也会直接调用它）。流程：
 *   1. 快速检查是否有空闲 worker 槽位，没有直接返回 InvalidOid；
 *   2. get_database_list() 拿到全部数据库候选（pg_database 扫描）；
 *   3. 算出 XID/MultiXactId 防回卷的强制界限
 *      （recentXid - autovacuum_freeze_max_age 等）；
 *   4. 遍历候选库选出一个：
 *      a. 若有库的 datfrozenxid 早于界限（XID 回卷风险），选其中最老的
 *         （优先级最高，> 处理 MultiXactId 回卷 > 常规轮换）；
 *      b. 否则若有库 datminmxid 早于界限（MultiXact 回卷风险），选最老的；
 *      c. 否则从"有 pgstats 统计"且"最近 naptime 内没被处理过"的库里，
 *         选 last_autovac_time 最久远的一个；
 *   5. 选到库后：从空闲链表取一个 WorkerInfo 槽位，填入库 OID 与
 *      启动时间，挂到 av_startingWorker，然后给 postmaster 发
 *      PMSIGNAL_START_AUTOVAC_WORKER 信号（fork 由 postmaster 做）；
 *   6. 若因 skipit 跳过了所有库（排班表里可能混入已删库），重建排班表。
 */
static Oid
do_start_worker(void)
{
	List	   *dblist;
	ListCell   *cell;
	TransactionId xidForceLimit;
	MultiXactId multiForceLimit;
	bool		for_xid_wrap;
	bool		for_multi_wrap;
	avw_dbase  *avdb;
	TimestampTz current_time;
	bool		skipit = false;
	Oid			retval = InvalidOid;
	MemoryContext tmpcxt,
				oldcxt;

	/* return quickly when there are no free workers */
	/* 【中文】没空闲槽位时快速返回，不做任何额外开销 */
	LWLockAcquire(AutovacuumLock, LW_SHARED);
	if (!av_worker_available())
	{
		LWLockRelease(AutovacuumLock);
		return InvalidOid;
	}
	LWLockRelease(AutovacuumLock);

	/*
	 * Create and switch to a temporary context to avoid leaking the memory
	 * allocated for the database list.
	 * 【中文】临时上下文装数据库列表，函数结束整体释放，防泄漏。
	 */
	tmpcxt = AllocSetContextCreate(CurrentMemoryContext,
								   "Autovacuum start worker (tmp)",
								   ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(tmpcxt);

	/* Get a list of databases */
	/* 【中文】扫描 pg_database（launcher 唯一一次使用事务的地方） */
	dblist = get_database_list();

	/*
	 * Determine the oldest datfrozenxid/relfrozenxid that we will allow to
	 * pass without forcing a vacuum.  (This limit can be tightened for
	 * particular tables, but not loosened.)
	 * 【中文】计算 XID 强制清理界限：最新事务号减去 autovacuum_freeze_max_age。
	 * 低于此界限的库必须立刻清（防止回卷导致数据丢失）；单个表的
	 * relfrozenxid 界限还可以更严（表级 reloptions 可收紧），但不能放宽。
	 */
	recentXid = ReadNextTransactionId();
	xidForceLimit = recentXid - autovacuum_freeze_max_age;
	/* ensure it's a "normal" XID, else TransactionIdPrecedes misbehaves */
	/* this can cause the limit to go backwards by 3, but that's OK */
	/* 【中文】把界限校正到"正常 XID"范围内，否则 TransactionIdPrecedes
	 * 的比较语义会出错（回绕 3 个号无妨，纯防御性修正） */
	if (xidForceLimit < FirstNormalTransactionId)
		xidForceLimit -= FirstNormalTransactionId;

	/* Also determine the oldest datminmxid we will consider. */
	/* 【中文】MultiXact 的强制界限同理（用 MultiXactMemberFreezeThreshold()
	 * 而非 GUC，因为成员空间膨胀时界限会被动态收紧） */
	recentMulti = ReadNextMultiXactId();
	multiForceLimit = recentMulti - MultiXactMemberFreezeThreshold();
	if (multiForceLimit < FirstMultiXactId)
		multiForceLimit -= FirstMultiXactId;

	/*
	 * Choose a database to connect to.  We pick the database that was least
	 * recently auto-vacuumed, or one that needs vacuuming to prevent Xid
	 * wraparound-related data loss.  If any db at risk of Xid wraparound is
	 * found, we pick the one with oldest datfrozenxid, independently of
	 * autovacuum times; similarly we pick the one with the oldest datminmxid
	 * if any is in MultiXactId wraparound.  Note that those in Xid wraparound
	 * danger are given more priority than those in multi wraparound danger.
	 *
	 * Note that a database with no stats entry is not considered, except for
	 * Xid wraparound purposes.  The theory is that if no one has ever
	 * connected to it since the stats were last initialized, it doesn't need
	 * vacuuming.
	 *
	 * XXX This could be improved if we had more info about whether it needs
	 * vacuuming before connecting to it.  Perhaps look through the pgstats
	 * data for the database's tables?  One idea is to keep track of the
	 * number of new and dead tuples per database in pgstats.  However it
	 * isn't clear how to construct a metric that measures that and not cause
	 * starvation for less busy databases.
	 * 【中文】选库优先级（这是"决定先清理哪个数据库"的核心逻辑）：
	 *   ① XID 回卷风险库 > ② MultiXact 回卷风险库 > ③ 常规轮换（最久未
	 *      自动清理的库）。风险库内部取"最老"（datfrozenxid/datminmxid
	 *      最早）的；注意 XID 风险永远压过 MultiXact 风险。
	 * 没有 pgstats 统计的库不参与常规轮换（理由：统计初始化后从没被
	 * 连接过的库不需要清理）；但若它处于回卷风险，仍会被选中（防丢失）。
	 * XXX 注释吐槽：如果在连库前就能拿到更多信息（比如按库统计新增/
	 * 死元组数），选库可以更聪明，但很难构造一个不会饿死冷门库的指标。
	 */
	avdb = NULL;
	for_xid_wrap = false;
	for_multi_wrap = false;
	current_time = GetCurrentTimestamp();
	foreach(cell, dblist)
	{
		avw_dbase  *tmp = lfirst(cell);
		dlist_iter	iter;

		/* Check to see if this one is at risk of wraparound */
		/* 【中文】命中 XID 回卷：记录"最老"的那个；一旦发现有 XID 风险
		 * 库，后面所有无风险库一律跳过（for_xid_wrap 标志） */
		if (TransactionIdPrecedes(tmp->adw_frozenxid, xidForceLimit))
		{
			if (avdb == NULL ||
				TransactionIdPrecedes(tmp->adw_frozenxid,
									  avdb->adw_frozenxid))
				avdb = tmp;
			for_xid_wrap = true;
			continue;
		}
		else if (for_xid_wrap)
			continue;			/* ignore not-at-risk DBs */
		/* 【中文】命中 MultiXact 回卷：逻辑同 XID 分支（优先级低一级） */
		else if (MultiXactIdPrecedes(tmp->adw_minmulti, multiForceLimit))
		{
			if (avdb == NULL ||
				MultiXactIdPrecedes(tmp->adw_minmulti, avdb->adw_minmulti))
				avdb = tmp;
			for_multi_wrap = true;
			continue;
		}
		else if (for_multi_wrap)
			continue;			/* ignore not-at-risk DBs */

		/* Find pgstat entry if any */
		tmp->adw_entry = pgstat_fetch_stat_dbentry(tmp->adw_datid);

		/*
		 * Skip a database with no pgstat entry; it means it hasn't seen any
		 * activity.
		 * 【中文】没有统计 = 从无活动，常规轮换跳过。
		 */
		if (!tmp->adw_entry)
			continue;

		/*
		 * Also, skip a database that appears on the database list as having
		 * been processed recently (less than autovacuum_naptime seconds ago).
		 * We do this so that we don't select a database which we just
		 * selected, but that pgstat hasn't gotten around to updating the last
		 * autovacuum time yet.
		 * 【中文】再排除"排班表里刚被处理过（不足 naptime）"的库：
		 * 防止刚选中过的库又被选中——pgstats 的 last_autovac_time 还没
		 * 来得及更新，直接看排班表的 next_worker 最可靠。
		 */
		skipit = false;

		dlist_reverse_foreach(iter, &DatabaseList)
		{
			avl_dbase  *dbp = dlist_container(avl_dbase, adl_node, iter.cur);

			if (dbp->adl_datid == tmp->adw_datid)
			{
				/*
				 * Skip this database if its next_worker value falls between
				 * the current time and the current time plus naptime.
				 * 【中文】next_worker 落在 [当前时刻, 当前时刻+naptime]
				 * 区间内 → 最近才处理过 → 跳过。
				 */
				if (!TimestampDifferenceExceeds(dbp->adl_next_worker,
												current_time, 0) &&
					!TimestampDifferenceExceeds(current_time,
												dbp->adl_next_worker,
												autovacuum_naptime * 1000))
					skipit = true;

				break;
			}
		}
		if (skipit)
			continue;

		/*
		 * Remember the db with oldest autovac time.  (If we are here, both
		 * tmp->entry and db->entry must be non-null.)
		 * 【中文】常规轮换：选 last_autovac_time 最久远的库（"最久没被
		 * 自动清理"的库）。
		 */
		if (avdb == NULL ||
			tmp->adw_entry->last_autovac_time < avdb->adw_entry->last_autovac_time)
			avdb = tmp;
	}

	/* Found a database -- process it */
	if (avdb != NULL)
	{
		WorkerInfo	worker;
		dlist_node *wptr;

		LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);

		/*
		 * Get a worker entry from the freelist.  We checked above, so there
		 * really should be a free slot.
		 * 【中文】从空闲链表取一个 WorkerInfo 槽位并初始化：
		 * 填库 OID、启动时间，然后挂到 av_startingWorker——这是
		 * "worker 正在启动中"的标志，主循环看到它就暂时不再启动新 worker。
		 */
		wptr = dclist_pop_head_node(&AutoVacuumShmem->av_freeWorkers);

		worker = dlist_container(WorkerInfoData, wi_links, wptr);
		worker->wi_dboid = avdb->adw_datid;
		worker->wi_proc = NULL;
		worker->wi_launchtime = GetCurrentTimestamp();

		AutoVacuumShmem->av_startingWorker = worker;

		LWLockRelease(AutovacuumLock);

		/* 【中文】通知 postmaster fork worker：
		 * 【调用链】SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_WORKER)
		 *   → 写共享内存 PMSIGNAL 槽位 → 给 postmaster 发信号
		 *   → postmaster 在 ServerLoop 里看到该请求
		 *   → StartAutovacuumWorker() → 处理 fork 失败/超时等逻辑
		 *   → fork 出的子进程进入 AutoVacWorkerMain() */
		SendPostmasterSignal(PMSIGNAL_START_AUTOVAC_WORKER);

		retval = avdb->adw_datid;
	}
	else if (skipit)
	{
		/*
		 * If we skipped all databases on the list, rebuild it, because it
		 * probably contains a dropped database.
		 * 【中文】所有库都被跳过（可能排班表里混入了已删除的库），
		 * 重建排班表让一切回到正轨。
		 */
		rebuild_database_list(InvalidOid);
	}

	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(tmpcxt);

	return retval;
}

/*
 * launch_worker
 *
 * Wrapper for starting a worker from the launcher.  Besides actually starting
 * it, update the database list to reflect the next time that another one will
 * need to be started on the selected database.  The actual database choice is
 * left to do_start_worker.
 *
 * This routine is also expected to insert an entry into the database list if
 * the selected database was previously absent from the list.
 * 【中文】launch_worker() 是 do_start_worker() 的封装：真正选库在
 * do_start_worker() 里，这里负责启动成功后的"排班记账"：
 *  - 若库已在排班表：把它的 adl_next_worker 更新为 now + naptime
 *    （即下一次再来处理这个库），并移到表头（维持"队尾最旧"不变式）；
 *  - 若库不在排班表（新库，如刚建成的库）：rebuild_database_list(dbid)
 *    重建整张表，把新库插入排班周期。
 */
static void
launch_worker(TimestampTz now)
{
	Oid			dbid;
	dlist_iter	iter;

	/* 【中文】真正选库 + 通知 postmaster fork worker */
	dbid = do_start_worker();
	if (OidIsValid(dbid))
	{
		bool		found = false;

		/*
		 * Walk the database list and update the corresponding entry.  If the
		 * database is not on the list, we'll recreate the list.
		 */
		dlist_foreach(iter, &DatabaseList)
		{
			avl_dbase  *avdb = dlist_container(avl_dbase, adl_node, iter.cur);

			if (avdb->adl_datid == dbid)
			{
				found = true;

				/*
				 * add autovacuum_naptime seconds to the current time, and use
				 * that as the new "next_worker" field for this database.
				 * 【中文】next_worker = now + naptime：这个库之后
				 * naptime 秒内不会再被自动选中。
				 */
				avdb->adl_next_worker =
					TimestampTzPlusMilliseconds(now, autovacuum_naptime * 1000);

				/* 【中文】移到表头：时间越新越靠前（队尾留给最旧的库） */
				dlist_move_head(&DatabaseList, iter.cur);
				break;
			}
		}

		/*
		 * If the database was not present in the database list, we rebuild
		 * the list.  It's possible that the database does not get into the
		 * list anyway, for example if it's a database that doesn't have a
		 * pgstat entry, but this is not a problem because we don't want to
		 * schedule workers regularly into those in any case.
		 * 【中文】库不在排班表 → 重建。即便重建后它仍进不了表（比如
		 * 无 pgstats 统计的库），也无所谓——我们本来就不想给这种库
		 * 安排定期 worker。
		 */
		if (!found)
			rebuild_database_list(dbid);
	}
}

/*
 * Called from postmaster to signal a failure to fork a process to become
 * worker.  The postmaster should kill(SIGUSR2) the launcher shortly
 * after calling this function.
 * 【中文】postmaster 专用回调：fork worker 失败时置 AutoVacForkFailed
 * 标志（随后 postmaster 会给 launcher 发 SIGUSR2 唤醒它处理）。
 */
void
AutoVacWorkerFailed(void)
{
	AutoVacuumShmem->av_signal[AutoVacForkFailed] = true;
}

/* SIGUSR2: a worker is up and running, or just finished, or failed to fork */
/* 【中文】launcher 的 SIGUSR2 处理器：置 got_SIGUSR2 标志并唤醒主循环。
 * 触发时机：worker 就绪/完成（worker 主动发）、fork 失败（postmaster 发）。
 * 真正的处理（重平衡、重试等）在 AutoVacLauncherMain 主循环里做。 */
static void
avl_sigusr2_handler(SIGNAL_ARGS)
{
	got_SIGUSR2 = true;
	SetLatch(MyLatch);
}


/********************************************************************
 *					  AUTOVACUUM WORKER CODE
 *
 * 【中文】worker（工作进程）模块：干真正的清理活。
 * worker 由 postmaster fork（受 launcher 的 PMSIGNAL 驱动），生命周期短暂：
 *  - 连上共享内存，认领自己的 WorkerInfo 槽位（av_startingWorker），
 *    挂进 running 链表，然后通知 launcher"我已就绪"；
 *  - 连接到 launcher 指定的数据库（忽略 datallowconn，防止回卷时必须
 *    连上；连不上的话——比如库刚被删——记录统计后正常退出）；
 *  - 核心工作交给 do_autovacuum()：扫 pg_class 选表、复查、逐个
 *    VACUUM/ANALYZE、清理孤儿临时表、处理委托工作项、更新
 *    datfrozenxid 并截断 pg_xact；
 *  - 退出时通过 on_shmem_exit 回调 FreeWorkerInfo() 把槽位还回空闲
 *    链表并置 AutoVacRebalance 信号（让 launcher 重算 cost 平衡）。
 ********************************************************************/

/*
 * Main entry point for autovacuum worker processes.
 * 【中文总述】
 * worker 进程的入口（postmaster fork 后由 B_AUTOVAC_WORKER 分发进来）。
 * 执行阶段概览：
 *   1. 基础设置：释放 PostmasterContext、安装信号处理器（SIGINT =
 *      取消当前表的清理、SIGTERM = 干净退出、SIGQUIT = 立即放弃）、
 *      InitProcess()、BaseInit()（与 launcher 相同的前置流程）
 *   2. 搭 sigsetjmp 错误恢复框架：与 launcher 不同，worker 出错后
 *      不尝试继续工作，而是清理现场后直接 proc_exit(0) 退出——
 *      重试的职责在 launcher（它会按排班再启动新 worker）
 *   3. 强制安全设置（同 launcher：search_path 置空、禁用
 *      zero_damaged_pages、清超时、READ COMMITTED），另加：
 *      若 synchronous_commit 高于 local，强制降到 local（保证防回卷
 *      任务不被同步复制等待卡住）
 *   4. 认领共享内存中的 worker 槽位：拿 av_startingWorker 里
 *      launcher 预置的库 OID，填上自己的 PGPROC，挂进 running 链表，
 *      清空 starting 指针（让 launcher 可以再启动别的 worker），
 *      注册退出回调 FreeWorkerInfo()，最后 kill(SIGUSR2) 通知 launcher
 *   5. 若没有槽位（异常情况）：告警后直接退出
 *   6. 有库要处理：先 pgstat_report_autovac(dbid) 上报
 *      last_autovac_time（故意放在 InitPostgres 之前——即使连库失败，
 *      时间戳也已更新，防止 launcher 反复选同一个连不上的库导致
 *      空转卡死）→ InitPostgres() 连接到目标库（忽略 datallowconn）
 *      → do_autovacuum() 干全部实际工作
 *   7. proc_exit(0) 退出，FreeWorkerInfo() 归还槽位
 */
void
AutoVacWorkerMain(const void *startup_data, size_t startup_data_len)
{
	sigjmp_buf	local_sigjmp_buf;
	Oid			dbid;

	Assert(startup_data_len == 0);

	/* Release postmaster's working memory context */
	/* 【中文】释放继承的 PostmasterContext（worker 也是短期进程，
	 * 但保持与 launcher 一致的处理方式） */
	if (PostmasterContext)
	{
		MemoryContextDelete(PostmasterContext);
		PostmasterContext = NULL;
	}

	init_ps_display(NULL);

	Assert(GetProcessingMode() == InitProcessing);

	/*
	 * Set up signal handlers.  We operate on databases much like a regular
	 * backend, so we use the same signal handling.  See equivalent code in
	 * tcop/postgres.c.
	 */
	pqsignal(SIGHUP, SignalHandlerForConfigReload);

	/*
	 * SIGINT is used to signal canceling the current table's vacuum; SIGTERM
	 * means abort and exit cleanly, and SIGQUIT means abandon ship.
	 * 【中文】信号分工：SIGINT → 取消当前表的清理（StatementCancelHandler）；
	 * SIGTERM → 干净退出（die）；SIGQUIT → 立即终止（前文已由
	 * InitPostmasterChild 设好）。注意 worker 用 die 而非
	 * SignalHandlerForShutdownRequest——worker 是短期进程，收到
	 * SIGTERM 就直接退出，不需要优雅关闭流程。
	 */
	pqsignal(SIGINT, StatementCancelHandler);
	pqsignal(SIGTERM, die);
	/* SIGQUIT handler was already set up by InitPostmasterChild */

	InitializeTimeouts();		/* establishes SIGALRM handler */

	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, PG_SIG_IGN);
	pqsignal(SIGFPE, FloatExceptionHandler);
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/*
	 * Create a per-backend PGPROC struct in shared memory.  We must do this
	 * before we can use LWLocks or access any shared memory.
	 */
	InitProcess();

	/* Early initialization */
	BaseInit();

	/*
	 * If an exception is encountered, processing resumes here.
	 *
	 * Unlike most auxiliary processes, we don't attempt to continue
	 * processing after an error; we just clean up and exit.  The autovac
	 * launcher is responsible for spawning another worker later.
	 *
	 * Note that we use sigsetjmp(..., 1), so that the prevailing signal mask
	 * (to wit, BlockSig) will be restored when longjmp'ing to here.  Thus,
	 * signals other than SIGQUIT will be blocked until we exit.  It might
	 * seem that this policy makes the HOLD_INTERRUPTS() call redundant, but
	 * it is not since InterruptPending might be set already.
	 * 【中文】worker 的错误恢复策略与 launcher 截然不同：出错后不重试、
	 * 不继续——报告错误日志后直接 proc_exit(0) 退出。原因是 worker 是
	 * "用完即弃"的短期进程，重新调度是 launcher 的职责；把复杂的状态
	 * 恢复逻辑留在 worker 里没有意义。退出时 ProcKill 回调（InitProcess
	 * 注册）会清理共享内存状态。
	 */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/* since not using PG_TRY, must reset error stack by hand */
		error_context_stack = NULL;

		/* Prevents interrupts while cleaning up */
		HOLD_INTERRUPTS();

		/* Report the error to the server log */
		EmitErrorReport();

		/*
		 * We can now go away.  Note that because we called InitProcess, a
		 * callback was registered to do ProcKill, which will clean up
		 * necessary state.
		 */
		proc_exit(0);
	}

	/* We can now handle ereport(ERROR) */
	PG_exception_stack = &local_sigjmp_buf;

	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * Set always-secure search path, so malicious users can't redirect user
	 * code (e.g. pg_index.indexprs).  (That code runs in a
	 * SECURITY_RESTRICTED_OPERATION sandbox, so malicious users could not
	 * take control of the entire autovacuum worker in any case.)
	 * 【中文】search_path 置空，防止恶意用户通过表名/函数名重定向
	 * autovacuum 要执行的用户代码（如 pg_index.indexprs 表达式）。
	 */
	SetConfigOption("search_path", "", PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force zero_damaged_pages OFF in the autovac process, even if it is set
	 * in postgresql.conf.  We don't really want such a dangerous option being
	 * applied non-interactively.
	 */
	SetConfigOption("zero_damaged_pages", "false", PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force settable timeouts off to avoid letting these settings prevent
	 * regular maintenance from being executed.
	 */
	SetConfigOption("statement_timeout", "0", PGC_SUSET, PGC_S_OVERRIDE);
	SetConfigOption("transaction_timeout", "0", PGC_SUSET, PGC_S_OVERRIDE);
	SetConfigOption("lock_timeout", "0", PGC_SUSET, PGC_S_OVERRIDE);
	SetConfigOption("idle_in_transaction_session_timeout", "0",
					PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force default_transaction_isolation to READ COMMITTED.  We don't want
	 * to pay the overhead of serializable mode, nor add any risk of causing
	 * deadlocks or delaying other transactions.
	 */
	SetConfigOption("default_transaction_isolation", "read committed",
					PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Force synchronous replication off to allow regular maintenance even if
	 * we are waiting for standbys to connect. This is important to ensure we
	 * aren't blocked from performing anti-wraparound tasks.
	 * 【中文】同步复制降到 local（若配置高于它）：即使主库正在等备库
	 * 连接，自动维护也不该被同步提交等待卡住——尤其防回卷任务不能拖。
	 */
	if (synchronous_commit > SYNCHRONOUS_COMMIT_LOCAL_FLUSH)
		SetConfigOption("synchronous_commit", "local",
						PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Even when system is configured to use a different fetch consistency,
	 * for autovac we always want fresh stats.
	 */
	SetConfigOption("stats_fetch_consistency", "none", PGC_SUSET, PGC_S_OVERRIDE);

	/*
	 * Get the info about the database we're going to work on.
	 * 【中文】认领任务：拿到 av_startingWorker（launcher 预置了库 OID）
	 * 的排他锁保护，填上自己的信息。
	 */
	LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);

	/*
	 * beware of startingWorker being INVALID; this should normally not
	 * happen, but if a worker fails after forking and before this, the
	 * launcher might have decided to remove it from the queue and start
	 * again.
	 * 【中文】av_startingWorker 理论上非空；若为空，说明 launcher 已把
	 * 超时的槽位回收（见主循环里的超时回收逻辑），本 worker 成了
	 * "没有任务"的孤儿，告警后退出即可。
	 */
	if (AutoVacuumShmem->av_startingWorker != NULL)
	{
		ProcNumber	launcherProc;

		MyWorkerInfo = AutoVacuumShmem->av_startingWorker;
		dbid = MyWorkerInfo->wi_dboid;
		MyWorkerInfo->wi_proc = MyProc;

		/* insert into the running list */
		/* 【中文】挂进 running 链表：此后其他 worker/launcher 能看见
		 * 本 worker 的存在（多 worker 并发协调的基础） */
		dlist_push_head(&AutoVacuumShmem->av_runningWorkers,
						&MyWorkerInfo->wi_links);

		/*
		 * remove from the "starting" pointer, so that the launcher can start
		 * a new worker if required
		 * 【中文】清空 starting 指针 = 告诉 launcher"我正式上岗了，
		 * 你可以再启动别的 worker"。
		 */
		AutoVacuumShmem->av_startingWorker = NULL;
		LWLockRelease(AutovacuumLock);

		/* 【中文】注册退出回调：worker 无论正常/异常退出都会触发
		 * FreeWorkerInfo()，把槽位还回空闲链表 */
		on_shmem_exit(FreeWorkerInfo, 0);

		/* wake up the launcher */
		/* 【中文】通知 launcher"我起来了"：
		 * 【调用链】从 ProcGlobal->avLauncherProc 找到 launcher 的
		 *   PGPROC 编号 → GetPGProcByNumber() 取 PID → kill(SIGUSR2)
		 *   → launcher 的 avl_sigusr2_handler 置 got_SIGUSR2 并唤醒主循环
		 *   （launcher 借此得知可以继续启动下一个 worker） */
		launcherProc = pg_atomic_read_u32(&ProcGlobal->avLauncherProc);
		if (launcherProc != INVALID_PROC_NUMBER)
		{
			int			pid = GetPGProcByNumber(launcherProc)->pid;

			if (pid != 0)
				kill(pid, SIGUSR2);
		}
	}
	else
	{
		/* no worker entry for me, go away */
		elog(WARNING, "autovacuum worker started without a worker entry");
		dbid = InvalidOid;
		LWLockRelease(AutovacuumLock);
	}

	if (OidIsValid(dbid))
	{
		char		dbname[NAMEDATALEN];

		/*
		 * Report autovac startup to the cumulative stats system.  We
		 * deliberately do this before InitPostgres, so that the
		 * last_autovac_time will get updated even if the connection attempt
		 * fails.  This is to prevent autovac from getting "stuck" repeatedly
		 * selecting an unopenable database, rather than making any progress
		 * on stuff it can connect to.
		 * 【中文】上报"开始清理本库"（更新 pgstats 的 last_autovac_time）。
		 * 故意放在 InitPostgres 之前：就算连库失败（库刚被删），时间戳
		 * 也已更新——否则 launcher 会反复选中这个连不上的库，其他能连
		 * 的库反而永远得不到清理（"卡死"问题）。
		 */
		pgstat_report_autovac(dbid);

		/*
		 * Connect to the selected database, specifying no particular user,
		 * and ignoring datallowconn.  Collect the database's name for
		 * display.
		 *
		 * Note: if we have selected a just-deleted database (due to using
		 * stale stats info), we'll fail and exit here.
		 * 【中文】连接目标数据库（不指定用户；忽略 datallowconn——
		 * 防回卷任务必须连进去）。若基于过期统计选了个刚删掉的库，
		 * 这里会失败退出（符合预期）。
		 */
		InitPostgres(NULL, dbid, NULL, InvalidOid,
					 INIT_PG_OVERRIDE_ALLOW_CONNS,
					 dbname);
		SetProcessingMode(NormalProcessing);
		set_ps_display(dbname);
		ereport(DEBUG1,
				(errmsg_internal("autovacuum: processing database \"%s\"", dbname)));

		if (PostAuthDelay)
			pg_usleep(PostAuthDelay * 1000000L);

		/* And do an appropriate amount of work */
		/* 【中文】干活前先取最新的 XID/MultiXact 基准（relation_needs_
		 * vacanalyze 里算回卷界限要用），然后进入本文件的核心函数。
		 * 【调用链】do_autovacuum()
		 *   → 扫 pg_class 选表 → 逐表 table_recheck_autovac() 复查
		 *   → autovacuum_do_vac_analyze() → vacuum()
		 *   → 处理孤儿临时表 / 委托工作项
		 *   → vac_update_datfrozenxid() 收尾 */
		recentXid = ReadNextTransactionId();
		recentMulti = ReadNextMultiXactId();
		do_autovacuum();
	}

	/* All done, go away */
	/* 【中文】正常流程结束：proc_exit(0) 触发 FreeWorkerInfo() 归还
	 * 槽位并置 Rebalance 信号。 */
	proc_exit(0);
}

/*
 * Return a WorkerInfo to the free list
 * 【中文】worker 退出回调（on_shmem_exit 注册）：把自己从 running 链表
 * 摘下，清空各字段，推回空闲链表，并置 AutoVacRebalance 信号——这样
 * launcher 醒来后能重算 cost 限额平衡（少了一个分 I/O 预算的 worker）。
 */
static void
FreeWorkerInfo(int code, Datum arg)
{
	if (MyWorkerInfo != NULL)
	{
		LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);

		dlist_delete(&MyWorkerInfo->wi_links);
		MyWorkerInfo->wi_dboid = InvalidOid;
		MyWorkerInfo->wi_tableoid = InvalidOid;
		MyWorkerInfo->wi_sharedrel = false;
		MyWorkerInfo->wi_proc = NULL;
		MyWorkerInfo->wi_launchtime = 0;
		pg_atomic_clear_flag(&MyWorkerInfo->wi_dobalance);
		dclist_push_head(&AutoVacuumShmem->av_freeWorkers,
						 &MyWorkerInfo->wi_links);
		/* not mine anymore */
		MyWorkerInfo = NULL;

		/*
		 * now that we're inactive, cause a rebalancing of the surviving
		 * workers
		 */
		/* 【中文】本 worker 已退出：置位让 launcher 重算剩余的
		 * "参与平衡的 worker 数"（退出后预算应重新分配）。 */
		AutoVacuumShmem->av_signal[AutoVacRebalance] = true;
		LWLockRelease(AutovacuumLock);
	}
}

/*
 * Update vacuum cost-based delay-related parameters for autovacuum workers and
 * backends executing VACUUM or ANALYZE using the value of relevant GUCs and
 * global state. This must be called during setup for vacuum and after every
 * config reload to ensure up-to-date values.
 * 【中文】刷新"成本控制"参数（vacuum_cost_delay / vacuum_cost_limit），
 * 在每次开始清表前和每次 reload 配置后都必须调用：
 *  - autovacuum worker：cost_delay 按"表级参数 > autovacuum GUC >
 *    VacuumCostDelay（普通 vacuum 的默认值）"的优先级取；
 *    cost_limit 交给 AutoVacuumUpdateCostLimit() 计算（含多 worker 分摊）；
 *  - 普通后端（手动 VACUUM/ANALYZE 或并行 autovacuum worker）：
 *    直接用普通 vacuum 的全局值，不参与 autovacuum 的分摊机制。
 * 最后按 cost_delay 是否 > 0 刷新 VacuumCostActive 开关
 * （failsafe 模式下 cost 控制强制关闭）。
 */
void
VacuumUpdateCosts(void)
{
	if (MyWorkerInfo)
	{
		if (av_storage_param_cost_delay >= 0)
			vacuum_cost_delay = av_storage_param_cost_delay;
		else if (autovacuum_vac_cost_delay >= 0)
			vacuum_cost_delay = autovacuum_vac_cost_delay;
		else
			/* fall back to VacuumCostDelay */
			vacuum_cost_delay = VacuumCostDelay;

		AutoVacuumUpdateCostLimit();
	}
	else
	{
		/* Must be explicit VACUUM or ANALYZE or parallel autovacuum worker */
		vacuum_cost_delay = VacuumCostDelay;
		vacuum_cost_limit = VacuumCostLimit;
	}

	/*
	 * If configuration changes are allowed to impact VacuumCostActive, make
	 * sure it is updated.
	 */
	if (VacuumFailsafeActive)
		Assert(!VacuumCostActive);
	else if (vacuum_cost_delay > 0)
		VacuumCostActive = true;
	else
	{
		VacuumCostActive = false;
		VacuumCostBalance = 0;
	}

	/*
	 * Since the cost logging requires a lock, avoid rendering the log message
	 * in case we are using a message level where the log wouldn't be emitted.
	 */
	if (MyWorkerInfo && message_level_is_interesting(DEBUG2))
	{
		Oid			dboid,
					tableoid;

		Assert(!LWLockHeldByMe(AutovacuumLock));

		LWLockAcquire(AutovacuumLock, LW_SHARED);
		dboid = MyWorkerInfo->wi_dboid;
		tableoid = MyWorkerInfo->wi_tableoid;
		LWLockRelease(AutovacuumLock);

		elog(DEBUG2,
			 "Autovacuum VacuumUpdateCosts(db=%u, rel=%u, dobalance=%s, cost_limit=%d, cost_delay=%g active=%s failsafe=%s)",
			 dboid, tableoid, pg_atomic_unlocked_test_flag(&MyWorkerInfo->wi_dobalance) ? "no" : "yes",
			 vacuum_cost_limit, vacuum_cost_delay,
			 vacuum_cost_delay > 0 ? "yes" : "no",
			 VacuumFailsafeActive ? "yes" : "no");
	}
}

/*
 * Update vacuum_cost_limit with the correct value for an autovacuum worker,
 * given the value of other relevant cost limit parameters and the number of
 * workers across which the limit must be balanced. Autovacuum workers must
 * call this regularly in case av_nworkersForBalance has been updated by
 * another worker or by the autovacuum launcher. They must also call it after a
 * config reload.
 * 【中文】计算 worker 的 cost_limit（"全局成本预算分摊"机制）：
 *   1. 表级 reloptions 指定了 vacuum_cost_limit → 直接用，不参与分摊；
 *   2. 否则基准 = autovacuum_vac_cost_limit（GUC）或 VacuumCostLimit，
 *      再除以参与平衡的 worker 数（av_nworkersForBalance，共享内存中
 *      原子读取）：limit = max(基准 ÷ 并发worker数, 1)。
 * 效果：N 个 worker 同时清理时，每个 worker 的 I/O 预算约为全局限额的
 * 1/N，避免自动清理把磁盘 I/O 吃满拖垮业务。
 * 注意：wi_dobalance 标志置位的 worker 不做分摊（该表自己配了 cost
 * 参数或声明不参与）；av_nworkersForBalance 可能被 launcher 或其他
 * worker 更新，所以每次开表前都要重新调用本函数。
 */
void
AutoVacuumUpdateCostLimit(void)
{
	if (!MyWorkerInfo)
		return;

	/*
	 * note: in cost_limit, zero also means use value from elsewhere, because
	 * zero is not a valid value.
	 */

	if (av_storage_param_cost_limit > 0)
		vacuum_cost_limit = av_storage_param_cost_limit;
	else
	{
		int			nworkers_for_balance;

		if (autovacuum_vac_cost_limit > 0)
			vacuum_cost_limit = autovacuum_vac_cost_limit;
		else
			vacuum_cost_limit = VacuumCostLimit;

		/* Only balance limit if no cost-related storage parameters specified */
		if (pg_atomic_unlocked_test_flag(&MyWorkerInfo->wi_dobalance))
			return;

		Assert(vacuum_cost_limit > 0);

		nworkers_for_balance = pg_atomic_read_u32(&AutoVacuumShmem->av_nworkersForBalance);

		/* There is at least 1 autovac worker (this worker) */
		if (nworkers_for_balance <= 0)
			elog(ERROR, "nworkers_for_balance must be > 0");

		vacuum_cost_limit = Max(vacuum_cost_limit / nworkers_for_balance, 1);
	}
}

/*
 * autovac_recalculate_workers_for_balance
 *		Recalculate the number of workers to consider, given cost-related
 *		storage parameters and the current number of active workers.
 *
 * Caller must hold the AutovacuumLock in at least shared mode to access
 * worker->wi_proc.
 * 【中文】重算"参与 cost 限额平衡的 worker 数"（av_nworkersForBalance）：
 * 遍历 running 链表，统计 wi_proc 非空（真正在跑）且 wi_dobalance 未置位
 * （没被表级参数排除）的 worker 个数；与当前值不同才写回（原子更新）。
 * 调用时机：worker 启动/退出、表级参数变化（do_autovacuum 每处理一张表
 * 前）。调用者必须至少持有 AutovacuumLock 的共享锁。
 */
static void
autovac_recalculate_workers_for_balance(void)
{
	dlist_iter	iter;
	int			orig_nworkers_for_balance;
	int			nworkers_for_balance = 0;

	Assert(LWLockHeldByMe(AutovacuumLock));

	orig_nworkers_for_balance =
		pg_atomic_read_u32(&AutoVacuumShmem->av_nworkersForBalance);

	dlist_foreach(iter, &AutoVacuumShmem->av_runningWorkers)
	{
		WorkerInfo	worker = dlist_container(WorkerInfoData, wi_links, iter.cur);

		/* 【中文】没起来（wi_proc 空）或声明不参与（wi_dobalance）
		 * 的 worker 不计入平衡 */
		if (worker->wi_proc == NULL ||
			pg_atomic_unlocked_test_flag(&worker->wi_dobalance))
			continue;

		nworkers_for_balance++;
	}

	if (nworkers_for_balance != orig_nworkers_for_balance)
		pg_atomic_write_u32(&AutoVacuumShmem->av_nworkersForBalance,
							nworkers_for_balance);
}

/*
 * get_database_list
 *		Return a list of all databases found in pg_database.
 *
 * The list and associated data is allocated in the caller's memory context,
 * which is in charge of ensuring that it's properly cleaned up afterwards.
 *
 * Note: this is the only function in which the autovacuum launcher uses a
 * transaction.  Although we aren't attached to any particular database and
 * therefore can't access most catalogs, we do have enough infrastructure
 * to do a seqscan on pg_database.
 * 【中文】扫描 pg_database 得到全部数据库的候选列表（launcher 和 worker
 * 都会用：launcher 用它重建排班表/选库，do_start_worker 用它选库）。
 * 这是 launcher 唯一使用事务的地方——launcher 不连接任何具体数据库，
 * 大部分系统目录看不了，但 pg_database 全库共享，顺序扫描足够。
 * 注意：结果分配在调用者的内存上下文里（谁调用谁负责释放）；
 * 已删除一半的库（database_is_invalid_form）会被跳过。
 */
static List *
get_database_list(void)
{
	List	   *dblist = NIL;
	Relation	rel;
	TableScanDesc scan;
	HeapTuple	tup;
	MemoryContext resultcxt;

	/* This is the context that we will allocate our output data in */
	resultcxt = CurrentMemoryContext;

	/*
	 * Start a transaction so we can access pg_database.
	 * 【中文】launcher 唯一一次开事务：读 pg_database 必需。
	 */
	StartTransactionCommand();

	rel = table_open(DatabaseRelationId, AccessShareLock);
	scan = table_beginscan_catalog(rel, 0, NULL);

	while (HeapTupleIsValid(tup = heap_getnext(scan, ForwardScanDirection)))
	{
		Form_pg_database pgdatabase = (Form_pg_database) GETSTRUCT(tup);
		avw_dbase  *avdb;
		MemoryContext oldcxt;

		/*
		 * If database has partially been dropped, we can't, nor need to,
		 * vacuum it.
		 * 【中文】库已被部分删除（DROP DATABASE 进行中），跳过。
		 */
		if (database_is_invalid_form(pgdatabase))
		{
			elog(DEBUG2,
				 "autovacuum: skipping invalid database \"%s\"",
				 NameStr(pgdatabase->datname));
			continue;
		}

		/*
		 * Allocate our results in the caller's context, not the
		 * transaction's. We do this inside the loop, and restore the original
		 * context at the end, so that leaky things like heap_getnext() are
		 * not called in a potentially long-lived context.
		 * 【中文】结果拷到调用者上下文（事务上下文会在提交时销毁）；
		 * 循环里临时切换上下文，避免 heap_getnext 等动作在常驻上下文里
		 * 累积分配。
		 */
		oldcxt = MemoryContextSwitchTo(resultcxt);

		avdb = palloc_object(avw_dbase);

		avdb->adw_datid = pgdatabase->oid;
		avdb->adw_name = pstrdup(NameStr(pgdatabase->datname));
		avdb->adw_frozenxid = pgdatabase->datfrozenxid;
		avdb->adw_minmulti = pgdatabase->datminmxid;
		/* this gets set later: */
		avdb->adw_entry = NULL;

		dblist = lappend(dblist, avdb);
		MemoryContextSwitchTo(oldcxt);
	}

	table_endscan(scan);
	table_close(rel, AccessShareLock);

	CommitTransactionCommand();

	/* Be sure to restore caller's memory context */
	MemoryContextSwitchTo(resultcxt);

	return dblist;
}

/*
 * List comparator for TableToProcess.  Note that this sorts the tables based
 * on their scores in descending order.
 * 【中文】待清理表的排序比较器：按 score 降序（评分高的表排前面）。
 * 配合 list_sort() 使用，用于 do_autovacuum() 里"最紧迫的表先清"。
 */
static int
TableToProcessComparator(const ListCell *a, const ListCell *b)
{
	TableToProcess *t1 = (TableToProcess *) lfirst(a);
	TableToProcess *t2 = (TableToProcess *) lfirst(b);

	return (t2->score < t1->score) ? -1 : (t2->score > t1->score) ? 1 : 0;
}

/*
 * Process a database table-by-table
 *
 * Note that CHECK_FOR_INTERRUPTS is supposed to be used in certain spots in
 * order not to ignore shutdown commands for too long.
 * 【中文总述】
 * autovacuum 的核心：worker 连上目标数据库后，对"该库的所有表"做一遍
 * 体检并清理。执行阶段概览：
 *   1. 准备：创建本 worker 的常驻上下文 AutovacMemCxt（表清单要跨
 *      多个事务存活）、开事务、根据 pg_database 决定默认 freeze 参数
 *      （模板库/不可连接库用 0，普通库用 GUC 默认值）
 *   2. 第一遍扫描 pg_class（只取普通表和物化视图）：
 *      - 跳过其他后端的临时表（孤儿临时表记入 orphan_oids 稍后删）；
 *      - extract_autovac_opts() 取表级 reloptions；
 *      - relation_needs_vacanalyze() 判定是否需要 VACUUM/ANALYZE，
 *        需要则连同评分（scores.max）加入 tables_to_process；
 *      - 同时把"主表→TOAST 表"映射记入 table_toast_map
 *      （无论主表是否要清，因为 TOAST 是独立判定、独立清理的）
 *   3. 第二遍扫描 pg_class（只扫 TOAST 表）：TOAST 自己没配 reloptions
 *      就用主表的；TOAST 表只做 VACUUM 不做 ANALYZE
 *   4. 复查并删除孤儿临时表（每删一张单独开一个事务，防止锁表膨胀；
 *      加锁失败/已不是孤儿就放弃）
 *   5. 按评分对 tables_to_process 降序排序（权重全 0 则跳过排序，
 *      这是官方提供的"退出评分系统"的逃生通道）
 *   6. 创建共享缓冲区访问策略对象（限制 autovacuum 能占用的缓冲量，
 *      防止把共享缓冲冲垮）与假的 PortalContext（按表回收内存）
 *   7. 逐表处理（do_autovacuum 的主体循环）：
 *      a. 检查中断；有配置 reload 则重载（但绝不因 autovacuum=off
 *         中途退出——可能正身处防回卷紧急任务）
 *      b. 查该表 relisshared；在 AutovacuumScheduleLock + AutovacuumLock
 *         保护下检查有没有其他 worker 正在清同一张表（并发协调），
 *         有则跳过；没有则把 wi_tableoid 写进共享内存"占坑"
 *         （其他 worker 看到坑位就不会来抢）
 *      c. table_recheck_autovac() 复查统计（表可能已被别人清过），
 *         复查通过才组装 autovac_table
 *      d. 保存表级 cost 参数 → 设置 wi_dobalance → 重算平衡数 →
 *         VacuumUpdateCosts() 刷新成本参数
 *      e. PG_TRY 里 autovacuum_do_vac_analyze()（即 vacuum()）真正清表；
 *         出错则回滚事务、清 PortalContext，继续处理下一张表
 *      f. 清完归还坑位（wi_tableoid = InvalidOid），置 wi_dobalance
 *   8. 处理普通后端委托的工作项（遍历 av_workItems[]，见 perform_work_item）
 *   9. 收尾：vac_update_datfrozenxid() 推进 datfrozenxid 并尽可能截断
 *      pg_xact（这是防回卷体系的关键一环，即使没清任何表也可能需要；
 *      但"无事可做 + 曾因并发跳过表"时会跳过，避免无限重启 launcher
 *      的循环），最后提交事务退出。
 */
static void
do_autovacuum(void)
{
	Relation	classRel;
	HeapTuple	tuple;
	TableScanDesc relScan;
	Form_pg_database dbForm;
	List	   *tables_to_process = NIL;
	List	   *orphan_oids = NIL;
	HASHCTL		ctl;
	HTAB	   *table_toast_map;
	ListCell   *volatile cell;
	BufferAccessStrategy bstrategy;
	ScanKeyData key;
	TupleDesc	pg_class_desc;
	int			effective_multixact_freeze_max_age;
	bool		did_vacuum = false;
	bool		found_concurrent_worker = false;
	int			i;

	/*
	 * StartTransactionCommand and CommitTransactionCommand will automatically
	 * switch to other contexts.  We need this one to keep the list of
	 * relations to vacuum/analyze across transactions.
	 * 【中文】表清单必须跨多个事务存活，所以数据放进独立创建的
	 * AutovacMemCxt（事务上下文会被提交/回滚销毁）。
	 */
	AutovacMemCxt = AllocSetContextCreate(TopMemoryContext,
										  "Autovacuum worker",
										  ALLOCSET_DEFAULT_SIZES);
	MemoryContextSwitchTo(AutovacMemCxt);

	/* Start a transaction so our commands have one to play into. */
	/* 【中文】开启整个 do_autovacuum 的事务（后面逐表处理时还会
	 * 不断提交/重启这个事务） */
	StartTransactionCommand();

	/*
	 * This injection point is put in a transaction block to work with a wait
	 * that uses a condition variable.
	 * 【中文】调试注入点（仅测试构建生效），配合条件变量等待使用。
	 */
	INJECTION_POINT("autovacuum-worker-start", NULL);

	/*
	 * Compute the multixact age for which freezing is urgent.  This is
	 * normally autovacuum_multixact_freeze_max_age, but may be less if
	 * multixact members are bloated.
	 * 【中文】MultiXact 的紧急冻结年龄：通常是 GUC 值，但如果 multixact
	 * 成员空间膨胀，MultiXactMemberFreezeThreshold() 会自动收紧。
	 */
	effective_multixact_freeze_max_age = MultiXactMemberFreezeThreshold();

	/*
	 * Find the pg_database entry and select the default freeze ages. We use
	 * zero in template and nonconnectable databases, else the system-wide
	 * default.
	 * 【中文】查本库的 pg_database 元组，确定默认 freeze 参数：
	 * 模板库/不可连接库用 0（它们不会被正常使用，无需主动冻结）；
	 * 普通库用 vacuum_freeze_* 系列 GUC 默认值。
	 */
	tuple = SearchSysCache1(DATABASEOID, ObjectIdGetDatum(MyDatabaseId));
	if (!HeapTupleIsValid(tuple))
		elog(ERROR, "cache lookup failed for database %u", MyDatabaseId);
	dbForm = (Form_pg_database) GETSTRUCT(tuple);

	if (dbForm->datistemplate || !dbForm->datallowconn)
	{
		default_freeze_min_age = 0;
		default_freeze_table_age = 0;
		default_multixact_freeze_min_age = 0;
		default_multixact_freeze_table_age = 0;
	}
	else
	{
		default_freeze_min_age = vacuum_freeze_min_age;
		default_freeze_table_age = vacuum_freeze_table_age;
		default_multixact_freeze_min_age = vacuum_multixact_freeze_min_age;
		default_multixact_freeze_table_age = vacuum_multixact_freeze_table_age;
	}

	ReleaseSysCache(tuple);

	/* StartTransactionCommand changed elsewhere */
	MemoryContextSwitchTo(AutovacMemCxt);

	classRel = table_open(RelationRelationId, AccessShareLock);

	/* create a copy so we can use it after closing pg_class */
	/* 【中文】pg_class 的 TupleDesc 拷贝一份——第一遍扫描后要关掉
	 * pg_class 关系，而 extract_autovac_opts 还要用它的描述符 */
	pg_class_desc = CreateTupleDescCopy(RelationGetDescr(classRel));

	/* create hash table for toast <-> main relid mapping */
	/* 【中文】哈希表：TOAST 表 OID → 主表信息（主表 OID + reloptions），
	 * 供第二遍扫描 TOAST 表时回溯其主表参数 */
	ctl.keysize = sizeof(Oid);
	ctl.entrysize = sizeof(av_relation);

	table_toast_map = hash_create("TOAST to main relid map",
								  100,
								  &ctl,
								  HASH_ELEM | HASH_BLOBS);

	/*
	 * Scan pg_class to determine which tables to vacuum.
	 *
	 * We do this in two passes: on the first one we collect the list of plain
	 * relations and materialized views, and on the second one we collect
	 * TOAST tables. The reason for doing the second pass is that during it we
	 * want to use the main relation's pg_class.reloptions entry if the TOAST
	 * table does not have any, and we cannot obtain it unless we know
	 * beforehand what's the main table OID.
	 *
	 * We need to check TOAST tables separately because in cases with short,
	 * wide tables there might be proportionally much more activity in the
	 * TOAST table than in its parent.
	 * 【中文】分两遍扫描 pg_class：
	 *  - 第一遍收集普通表/物化视图；
	 *  - 第二遍单独扫 TOAST 表——因为 TOAST 表没配 reloptions 时要用
	 *    主表的，必须先知道主表 OID。TOAST 必须单独体检的理由：
	 *    短而宽的表（一行很长）在 TOAST 里的活动可能远超主表。
	 */
	relScan = table_beginscan_catalog(classRel, 0, NULL);

	/*
	 * On the first pass, we collect main tables to vacuum, and also the main
	 * table relid to TOAST relid mapping.
	 * 【中文】第一遍：收集普通表/物化视图，同时建立主表→TOAST 映射。
	 */
	while ((tuple = heap_getnext(relScan, ForwardScanDirection)) != NULL)
	{
		Form_pg_class classForm = (Form_pg_class) GETSTRUCT(tuple);
		AutoVacOpts *relopts;
		Oid			relid;
		bool		dovacuum;
		bool		doanalyze;
		bool		wraparound;
		AutoVacuumScores scores;

		if (classForm->relkind != RELKIND_RELATION &&
			classForm->relkind != RELKIND_MATVIEW)
			continue;

		relid = classForm->oid;

		/*
		 * Check if it is a temp table (presumably, of some other backend's).
		 * We cannot safely process other backends' temp tables.
		 * 【中文】临时表不能碰（可能是别的后端的，我们没法安全处理）。
		 */
		if (classForm->relpersistence == RELPERSISTENCE_TEMP)
		{
			/*
			 * We just ignore it if the owning backend is still active and
			 * using the temporary schema.  Also, for safety, ignore it if the
			 * namespace doesn't exist or isn't a temp namespace after all.
			 * 【中文】所属后端还在用这个临时 schema → 忽略；只有确定
			 * 临时 namespace 已"空闲"（TEMP_NAMESPACE_IDLE）才算孤儿。
			 */
			if (checkTempNamespaceStatus(classForm->relnamespace) == TEMP_NAMESPACE_IDLE)
			{
				/*
				 * The table seems to be orphaned -- although it might be that
				 * the owning backend has already deleted it and exited; our
				 * pg_class scan snapshot is not necessarily up-to-date
				 * anymore, so we could be looking at a committed-dead entry.
				 * Remember it so we can try to delete it later.
				 * 【中文】疑似孤儿临时表：可能是所属后端崩溃留下的，
				 * 也可能快照过期看到的"已删残留"。先记入 orphan_oids，
				 * 后面用单独事务复查后再决定删不删。
				 */
				orphan_oids = lappend_oid(orphan_oids, relid);
			}
			continue;
		}

		/* Fetch reloptions and the pgstat entry for this table */
		/* 【中文】取表级 autovacuum 参数（NULL = 用全局 GUC 默认） */
		relopts = extract_autovac_opts(tuple, pg_class_desc);

		/* Check if it needs vacuum or analyze */
		/* 【中文】核心判定：是否需要 VACUUM / ANALYZE / 防回卷，
		 * 并给出评分（阈值计算见 relation_needs_vacanalyze） */
		relation_needs_vacanalyze(relid, relopts, classForm,
								  effective_multixact_freeze_max_age,
								  DEBUG3,
								  &dovacuum, &doanalyze, &wraparound,
								  &scores);

		/* Relations that need work are added to tables_to_process */
		/* 【中文】需要干活（清或分析）的表连同评分加入待处理列表 */
		if (dovacuum || doanalyze)
		{
			TableToProcess *table = palloc_object(TableToProcess);

			table->oid = relid;
			table->score = scores.max;
			tables_to_process = lappend(tables_to_process, table);
		}

		/*
		 * Remember TOAST associations for the second pass.  Note: we must do
		 * this whether or not the table is going to be vacuumed, because we
		 * don't automatically vacuum toast tables along the parent table.
		 * 【中文】无论主表是否要清，都必须登记它的 TOAST 关联——主表
		 * 的 VACUUM 并不会自动带上 TOAST 表，TOAST 要单独处理。
		 */
		if (OidIsValid(classForm->reltoastrelid))
		{
			av_relation *hentry;
			bool		found;

			hentry = hash_search(table_toast_map,
								 &classForm->reltoastrelid,
								 HASH_ENTER, &found);

			if (!found)
			{
				/* hash_search already filled in the key */
				hentry->ar_relid = relid;
				hentry->ar_hasrelopts = false;
				if (relopts != NULL)
				{
					/* 【中文】把主表的 reloptions 副本存进映射项，
					 * 第二遍给 TOAST 表当"兜底参数" */
					hentry->ar_hasrelopts = true;
					memcpy(&hentry->ar_reloptions, relopts,
						   sizeof(AutoVacOpts));
				}
			}
		}

		/* Release stuff to avoid per-relation leakage */
		if (relopts)
			pfree(relopts);
	}

	table_endscan(relScan);

	/* second pass: check TOAST tables */
	/* 【中文】第二遍：只扫 relkind = TOAST 的表 */
	ScanKeyInit(&key,
				Anum_pg_class_relkind,
				BTEqualStrategyNumber, F_CHAREQ,
				CharGetDatum(RELKIND_TOASTVALUE));

	relScan = table_beginscan_catalog(classRel, 1, &key);
	while ((tuple = heap_getnext(relScan, ForwardScanDirection)) != NULL)
	{
		Form_pg_class classForm = (Form_pg_class) GETSTRUCT(tuple);
		Oid			relid;
		AutoVacOpts *relopts;
		bool		free_relopts = false;
		bool		dovacuum;
		bool		doanalyze;
		bool		wraparound;
		AutoVacuumScores scores;

		/*
		 * We cannot safely process other backends' temp tables, so skip 'em.
		 * 【中文】TOAST 表没有 temp 类型，理论上不会走到；防御性跳过。
		 */
		if (classForm->relpersistence == RELPERSISTENCE_TEMP)
			continue;

		relid = classForm->oid;

		/*
		 * fetch reloptions -- if this toast table does not have them, try the
		 * main rel
		 * 【中文】TOAST 表自身没配 reloptions 时，从第一遍登记的映射里
		 * 取主表的参数兜底。
		 */
		relopts = extract_autovac_opts(tuple, pg_class_desc);
		if (relopts)
			free_relopts = true;
		else
		{
			av_relation *hentry;
			bool		found;

			hentry = hash_search(table_toast_map, &relid, HASH_FIND, &found);
			if (found && hentry->ar_hasrelopts)
				relopts = &hentry->ar_reloptions;
		}

		relation_needs_vacanalyze(relid, relopts, classForm,
								  effective_multixact_freeze_max_age,
								  DEBUG3,
								  &dovacuum, &doanalyze, &wraparound,
								  &scores);

		/* ignore analyze for toast tables */
		/* 【中文】TOAST 表只考虑 VACUUM（analyze 对 TOAST 无意义，
		 * 统计信息在主表上维护） */
		if (dovacuum)
		{
			TableToProcess *table = palloc_object(TableToProcess);

			table->oid = relid;
			table->score = scores.max;
			tables_to_process = lappend(tables_to_process, table);
		}

		/* Release stuff to avoid leakage */
		if (free_relopts)
			pfree(relopts);
	}

	table_endscan(relScan);
	table_close(classRel, AccessShareLock);

	/*
	 * Recheck orphan temporary tables, and if they still seem orphaned, drop
	 * them.  We'll eat a transaction per dropped table, which might seem
	 * excessive, but we should only need to do anything as a result of a
	 * previous backend crash, so this should not happen often enough to
	 * justify "optimizing".  Using separate transactions ensures that we
	 * don't bloat the lock table if there are many temp tables to be dropped,
	 * and it ensures that we don't lose work if a deletion attempt fails.
	 * 【中文】复查孤儿临时表：仍确认是孤儿才删。每删一张用一个独立
	 * 事务——这种清理只在后端崩溃后才会发生，频率低，不值得优化；
	 * 分开事务一是防止大量删除把锁表撑爆，二是单张删除失败不会
	 * 影响其他表。
	 */
	foreach(cell, orphan_oids)
	{
		Oid			relid = lfirst_oid(cell);
		Form_pg_class classForm;
		ObjectAddress object;

		/*
		 * Check for user-requested abort.
		 */
		CHECK_FOR_INTERRUPTS();

		/*
		 * Try to lock the table.  If we can't get the lock immediately,
		 * somebody else is using (or dropping) the table, so it's not our
		 * concern anymore.  Having the lock prevents race conditions below.
		 * 【中文】先尝试立即拿到 AccessExclusiveLock（拿不到说明有人
		 * 正在用/正在删，那不是我们该管的了）；有锁才能防下面的竞态。
		 */
		if (!ConditionalLockRelationOid(relid, AccessExclusiveLock))
			continue;

		/*
		 * Re-fetch the pg_class tuple and re-check whether it still seems to
		 * be an orphaned temp table.  If it's not there or no longer the same
		 * relation, ignore it.
		 * 【中文】重取 pg_class 元组复查：防止 OID 复用（计数回绕后
		 * 同名元组可能是完全无关的表）。
		 */
		tuple = SearchSysCacheCopy1(RELOID, ObjectIdGetDatum(relid));
		if (!HeapTupleIsValid(tuple))
		{
			/* be sure to drop useless lock so we don't bloat lock table */
			UnlockRelationOid(relid, AccessExclusiveLock);
			continue;
		}
		classForm = (Form_pg_class) GETSTRUCT(tuple);

		/*
		 * Make all the same tests made in the loop above.  In event of OID
		 * counter wraparound, the pg_class entry we have now might be
		 * completely unrelated to the one we saw before.
		 */
		if (!((classForm->relkind == RELKIND_RELATION ||
			   classForm->relkind == RELKIND_MATVIEW) &&
			  classForm->relpersistence == RELPERSISTENCE_TEMP))
		{
			UnlockRelationOid(relid, AccessExclusiveLock);
			continue;
		}

		if (checkTempNamespaceStatus(classForm->relnamespace) != TEMP_NAMESPACE_IDLE)
		{
			UnlockRelationOid(relid, AccessExclusiveLock);
			continue;
		}

		/*
		 * Try to lock the temp namespace, too.  Even though we have lock on
		 * the table itself, there's a risk of deadlock against an incoming
		 * backend trying to clean out the temp namespace, in case this table
		 * has dependencies (such as sequences) that the backend's
		 * performDeletion call might visit in a different order.  If we can
		 * get AccessShareLock on the namespace, that's sufficient to ensure
		 * we're not running concurrently with RemoveTempRelations.  If we
		 * can't, back off and let RemoveTempRelations do its thing.
		 * 【中文】再锁临时 namespace：防止与"正在清理临时 schema 的
		 * 后端"死锁（表的依赖对象如序列可能被对方以不同顺序访问）。
		 * 拿不到 AccessShareLock 就放弃，让 RemoveTempRelations 去处理。
		 */
		if (!ConditionalLockDatabaseObject(NamespaceRelationId,
										   classForm->relnamespace, 0,
										   AccessShareLock))
		{
			UnlockRelationOid(relid, AccessExclusiveLock);
			continue;
		}

		/* OK, let's delete it */
		/* 【中文】确认孤儿：打日志后执行删除（级联 DROP） */
		ereport(LOG,
				(errmsg("autovacuum: dropping orphan temp table \"%s.%s.%s\"",
						get_database_name(MyDatabaseId),
						get_namespace_name(classForm->relnamespace),
						NameStr(classForm->relname))));

		/*
		 * Deletion might involve TOAST table access, so ensure we have a
		 * valid snapshot.
		 */
		PushActiveSnapshot(GetTransactionSnapshot());

		object.classId = RelationRelationId;
		object.objectId = relid;
		object.objectSubId = 0;
		performDeletion(&object, DROP_CASCADE,
						PERFORM_DELETION_INTERNAL |
						PERFORM_DELETION_QUIETLY |
						PERFORM_DELETION_SKIP_EXTENSIONS);

		/*
		 * To commit the deletion, end current transaction and start a new
		 * one.  Note this also releases the locks we took.
		 * 【中文】提交本次删除（同时释放所有锁），开启新事务。
		 */
		PopActiveSnapshot();
		CommitTransactionCommand();
		StartTransactionCommand();

		/* StartTransactionCommand changed current memory context */
		MemoryContextSwitchTo(AutovacMemCxt);
	}

	/*
	 * In case list_sort() would modify the list even when all the scores are
	 * 0.0, skip sorting if all the weight parameters are set to 0.0.  This is
	 * probably not necessary, but we want to ensure folks have a guaranteed
	 * escape hatch from the scoring system.
	 * 【中文】所有 score 权重都设 0.0 = 关闭评分排序（恢复 PG 早期
	 * 的遍历顺序）；这是官方留给用户的"退出评分系统"保证性出口。
	 */
	if (autovacuum_freeze_score_weight != 0.0 ||
		autovacuum_multixact_freeze_score_weight != 0.0 ||
		autovacuum_vacuum_score_weight != 0.0 ||
		autovacuum_vacuum_insert_score_weight != 0.0 ||
		autovacuum_analyze_score_weight != 0.0)
		list_sort(tables_to_process, TableToProcessComparator);

	/*
	 * Optionally, create a buffer access strategy object for VACUUM to use.
	 * We use the same BufferAccessStrategy object for all tables VACUUMed by
	 * this worker to prevent autovacuum from blowing out shared buffers.
	 *
	 * VacuumBufferUsageLimit being set to 0 results in
	 * GetAccessStrategyWithSize returning NULL, effectively meaning we can
	 * use up to all of shared buffers.
	 *
	 * If we later enter failsafe mode on any of the tables being vacuumed, we
	 * will cease use of the BufferAccessStrategy only for that table.
	 *
	 * XXX should we consider adding code to adjust the size of this if
	 * VacuumBufferUsageLimit changes?
	 * 【中文】为本次 worker 的所有表共用同一套 BufferAccessStrategy
	 * （限制 VACUUM 可占用的共享缓冲页数量，防止自动清理把共享缓冲
	 * 挤爆）；VacuumBufferUsageLimit=0 时返回 NULL（即不限制）；
	 * 某表进入 failsafe 模式时会单独停用这套策略。
	 */
	bstrategy = GetAccessStrategyWithSize(BAS_VACUUM, VacuumBufferUsageLimit);

	/*
	 * create a memory context to act as fake PortalContext, so that the
	 * contexts created in the vacuum code are cleaned up for each table.
	 * 【中文】伪造一个 PortalContext：vacuum 代码里按 portal 建的上下文
	 * 都挂它下面，每处理完一张表 MemoryContextReset 一次即可回收。
	 */
	PortalContext = AllocSetContextCreate(AutovacMemCxt,
										  "Autovacuum Portal",
										  ALLOCSET_DEFAULT_SIZES);

	/*
	 * Perform operations on collected tables.
	 * 【中文】主体循环：按评分从高到低逐表处理。
	 */
	foreach_ptr(TableToProcess, table, tables_to_process)
	{
		Oid			relid = table->oid;
		HeapTuple	classTup;
		autovac_table *tab;
		bool		isshared;
		bool		skipit;
		dlist_iter	iter;

		CHECK_FOR_INTERRUPTS();

		/*
		 * Check for config changes before processing each collected table.
		 * 【中文】每张表开工前检查配置 reload。
		 */
		if (ConfigReloadPending)
		{
			ConfigReloadPending = false;
			ProcessConfigFile(PGC_SIGHUP);

			/*
			 * You might be tempted to bail out if we see autovacuum is now
			 * disabled.  Must resist that temptation -- this might be a
			 * for-wraparound emergency worker, in which case that would be
			 * entirely inappropriate.
			 * 【中文】注意：即使配置把 autovacuum 关了，也绝不能中途
			 * 退出——本 worker 可能是防回卷的"紧急任务"，退出会
			 * 导致回卷风险无法解除。
			 */
		}

		/*
		 * Find out whether the table is shared or not.  (It's slightly
		 * annoying to fetch the syscache entry just for this, but in typical
		 * cases it adds little cost because table_recheck_autovac would
		 * refetch the entry anyway.  We could buy that back by copying the
		 * tuple here and passing it to table_recheck_autovac, but that
		 * increases the odds of that function working with stale data.)
		 * 【中文】查 relisshared：共享表会被其他数据库的 worker 也看到
		 * （并发检查时不能只按库过滤）。反正 table_recheck_autovac
		 * 稍后也会再取一次，这里多查一次代价很小。
		 */
		classTup = SearchSysCache1(RELOID, ObjectIdGetDatum(relid));
		if (!HeapTupleIsValid(classTup))
			continue;			/* somebody deleted the rel, forget it */
		isshared = ((Form_pg_class) GETSTRUCT(classTup))->relisshared;
		ReleaseSysCache(classTup);

		/*
		 * Hold schedule lock from here until we've claimed the table.  We
		 * also need the AutovacuumLock to walk the worker array, but that one
		 * can just be a shared lock.
		 * 【中文】"占坑"协议：先持 AutovacuumScheduleLock 排他锁
		 * （防止两个 worker 同时认领同一张表），再用共享锁遍历
		 * running 链表做并发检查。
		 */
		LWLockAcquire(AutovacuumScheduleLock, LW_EXCLUSIVE);
		LWLockAcquire(AutovacuumLock, LW_SHARED);

		/*
		 * Check whether the table is being vacuumed concurrently by another
		 * worker.
		 * 【中文】并发协调：遍历所有在跑 worker，看有没有人正在清同一
		 * 张表（共享表还要忽略数据库不同的限制）。有 → 跳过本表，
		 * 交给那个 worker 处理，避免互相等 vacuum 锁。
		 */
		skipit = false;
		dlist_foreach(iter, &AutoVacuumShmem->av_runningWorkers)
		{
			WorkerInfo	worker = dlist_container(WorkerInfoData, wi_links, iter.cur);

			/* ignore myself */
			if (worker == MyWorkerInfo)
				continue;

			/* ignore workers in other databases (unless table is shared) */
			if (!worker->wi_sharedrel && worker->wi_dboid != MyDatabaseId)
				continue;

			if (worker->wi_tableoid == relid)
			{
				skipit = true;
				found_concurrent_worker = true;
				break;
			}
		}
		LWLockRelease(AutovacuumLock);
		if (skipit)
		{
			LWLockRelease(AutovacuumScheduleLock);
			continue;
		}

		/*
		 * Store the table's OID in shared memory before releasing the
		 * schedule lock, so that other workers don't try to vacuum it
		 * concurrently.  (We claim it here so as not to hold
		 * AutovacuumScheduleLock while rechecking the stats.)
		 * 【中文】把 wi_tableoid 写进共享内存"占坑"再释放排程锁：
		 * 其他 worker 看到坑位就不会再来抢（占坑之后才做复查，
		 * 避免长时间持有排程锁）。
		 */
		MyWorkerInfo->wi_tableoid = relid;
		MyWorkerInfo->wi_sharedrel = isshared;
		LWLockRelease(AutovacuumScheduleLock);

		/*
		 * Check whether pgstat data still says we need to vacuum this table.
		 * It could have changed if something else processed the table while
		 * we weren't looking. This doesn't entirely close the race condition,
		 * but it is very small.
		 * 【中文】复查：占坑期间统计可能已变（别的进程刚清过这张表）。
		 * 复查能缩小竞态窗口但无法完全消除——文件头注释里提到的
		 * 已知缺陷（复查与真正加表锁之间仍有小窗口）。
		 */
		MemoryContextSwitchTo(AutovacMemCxt);
		tab = table_recheck_autovac(relid, table_toast_map, pg_class_desc,
									effective_multixact_freeze_max_age);
		if (tab == NULL)
		{
			/* someone else vacuumed the table, or it went away */
			/* 【中文】复查不过：别人已经清过或表没了，归还坑位走人 */
			LWLockAcquire(AutovacuumScheduleLock, LW_EXCLUSIVE);
			MyWorkerInfo->wi_tableoid = InvalidOid;
			MyWorkerInfo->wi_sharedrel = false;
			LWLockRelease(AutovacuumScheduleLock);
			continue;
		}

		/*
		 * Save the cost-related storage parameter values in global variables
		 * for reference when updating vacuum_cost_delay and vacuum_cost_limit
		 * during vacuuming this table.
		 * 【中文】保存表级 cost 参数到全局（清表过程中 reload 配置时
		 * 不会被全局值覆盖，见 VacuumUpdateCosts）。
		 */
		av_storage_param_cost_delay = tab->at_storage_param_vac_cost_delay;
		av_storage_param_cost_limit = tab->at_storage_param_vac_cost_limit;

		/*
		 * We only expect this worker to ever set the flag, so don't bother
		 * checking the return value. We shouldn't have to retry.
		 * 【中文】按本表是否参与 cost 平衡设置 wi_dobalance 标志，
		 * 并立刻重算"参与平衡的 worker 数"（多/少一个都会改变
		 * 每个 worker 的分摊预算）。
		 */
		if (tab->at_dobalance)
			pg_atomic_test_set_flag(&MyWorkerInfo->wi_dobalance);
		else
			pg_atomic_clear_flag(&MyWorkerInfo->wi_dobalance);

		LWLockAcquire(AutovacuumLock, LW_SHARED);
		autovac_recalculate_workers_for_balance();
		LWLockRelease(AutovacuumLock);

		/*
		 * We wait until this point to update cost delay and cost limit
		 * values, even though we reloaded the configuration file above, so
		 * that we can take into account the cost-related storage parameters.
		 * 【中文】到这一步才刷新 cost 参数（前面 reload 过配置，但那时
		 * 表级参数还没读出来，必须等 table_recheck_autovac 之后）。
		 */
		VacuumUpdateCosts();


		/* clean up memory before each iteration */
		MemoryContextReset(PortalContext);

		/*
		 * Save the relation name for a possible error message, to avoid a
		 * catalog lookup in case of an error.  If any of these return NULL,
		 * then the relation has been dropped since last we checked; skip it.
		 * Note: they must live in a long-lived memory context because we call
		 * vacuum and analyze in different transactions.
		 * 【中文】预取库名/模式名/表名（出错信息要用；若取不到说明表
		 * 已被删，跳过去）。必须放常驻上下文——VACUUM 和 ANALYZE 在
		 * 不同事务里执行，这些名字要活到报错的时候。
		 */

		tab->at_relname = get_rel_name(tab->at_relid);
		tab->at_nspname = get_namespace_name(get_rel_namespace(tab->at_relid));
		tab->at_datname = get_database_name(MyDatabaseId);
		if (!tab->at_relname || !tab->at_nspname || !tab->at_datname)
			goto deleted;

		/*
		 * We will abort vacuuming the current table if something errors out,
		 * and continue with the next one in schedule; in particular, this
		 * happens if we are interrupted with SIGINT.
		 * 【中文】PG_TRY：单张表清理失败只影响本表——回滚事务、重置
		 * PortalContext，继续下一张；SIGINT（取消）也是走这条路。
		 */
		PG_TRY();
		{
			/* Use PortalContext for any per-table allocations */
			MemoryContextSwitchTo(PortalContext);

			/* have at it */
			/* 【中文】真正开工：
			 * 【调用链】autovacuum_do_vac_analyze()
			 *   → autovac_report_activity() 上报 pg_stat_activity
			 *   → makeVacuumRelation() 组装目标 → vacuum()
			 *   → vacuum_rel() → 表加锁 → 真正清理/统计 */
			autovacuum_do_vac_analyze(tab, bstrategy);

			/*
			 * Clear a possible query-cancel signal, to avoid a late reaction
			 * to an automatically-sent signal because of vacuuming the
			 * current table (we're done with it, so it would make no sense to
			 * cancel at this point.)
			 * 【中文】清掉可能残留的取消信号：本表已清完，此时取消
			 * 毫无意义（避免"迟到的反应"误伤下一张表）。
			 */
			QueryCancelPending = false;
		}
		PG_CATCH();
		{
			/*
			 * Abort the transaction, start a new one, and proceed with the
			 * next table in our list.
			 * 【中文】异常处理：带上下文（库.模式.表）报告错误 →
			 * 回滚整个事务（顺带重置状态标志）→ 清理内存 → 开新事务
			 * → 继续下一张表。
			 */
			HOLD_INTERRUPTS();
			if (tab->at_params.options & VACOPT_VACUUM)
				errcontext("automatic vacuum of table \"%s.%s.%s\"",
						   tab->at_datname, tab->at_nspname, tab->at_relname);
			else
				errcontext("automatic analyze of table \"%s.%s.%s\"",
						   tab->at_datname, tab->at_nspname, tab->at_relname);
			EmitErrorReport();

			/* this resets ProcGlobal->statusFlags[i] too */
			AbortOutOfAnyTransaction();
			FlushErrorState();
			MemoryContextReset(PortalContext);

			/* restart our transaction for the following operations */
			StartTransactionCommand();
			RESUME_INTERRUPTS();
		}
		PG_END_TRY();

		/* Make sure we're back in AutovacMemCxt */
		MemoryContextSwitchTo(AutovacMemCxt);

		did_vacuum = true;

		/* ProcGlobal->statusFlags[i] are reset at the next end of xact */

		/* be tidy */
deleted:
		if (tab->at_datname != NULL)
			pfree(tab->at_datname);
		if (tab->at_nspname != NULL)
			pfree(tab->at_nspname);
		if (tab->at_relname != NULL)
			pfree(tab->at_relname);
		pfree(tab);

		/*
		 * Remove my info from shared memory.  We set wi_dobalance on the
		 * assumption that we are more likely than not to vacuum a table with
		 * no cost-related storage parameters next, so we want to claim our
		 * share of I/O as soon as possible to avoid thrashing the global
		 * balance.
		 * 【中文】归还坑位（wi_tableoid = InvalidOid）；置 wi_dobalance
		 * 的理由：预估下一张表大概率不带表级 cost 参数（需要参与分摊），
		 * 提前置位尽快恢复"参与平衡"身份，避免全局平衡被反复抖动。
		 */
		LWLockAcquire(AutovacuumScheduleLock, LW_EXCLUSIVE);
		MyWorkerInfo->wi_tableoid = InvalidOid;
		MyWorkerInfo->wi_sharedrel = false;
		LWLockRelease(AutovacuumScheduleLock);
		pg_atomic_test_set_flag(&MyWorkerInfo->wi_dobalance);
	}

	list_free_deep(tables_to_process);

	/*
	 * Perform additional work items, as requested by backends.
	 * 【中文】主体清理结束后，顺带处理普通后端委托的工作项
	 * （遍历 av_workItems[]，认领属于本库且未被处理的）。
	 */
	LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);
	for (i = 0; i < NUM_WORKITEMS; i++)
	{
		AutoVacuumWorkItem *workitem = &AutoVacuumShmem->av_workItems[i];

		if (!workitem->avw_used)
			continue;
		if (workitem->avw_active)
			continue;
		if (workitem->avw_database != MyDatabaseId)
			continue;

		/* claim this one, and release lock while performing it */
		/* 【中文】标记 active 认领后释放锁再执行（执行期较长，
		 * 不能一直占着全局锁） */
		workitem->avw_active = true;
		LWLockRelease(AutovacuumLock);

		PushActiveSnapshot(GetTransactionSnapshot());
		perform_work_item(workitem);
		if (ActiveSnapshotSet())	/* transaction could have aborted */
			PopActiveSnapshot();

		/*
		 * Check for config changes before acquiring lock for further jobs.
		 */
		CHECK_FOR_INTERRUPTS();
		if (ConfigReloadPending)
		{
			ConfigReloadPending = false;
			ProcessConfigFile(PGC_SIGHUP);
			VacuumUpdateCosts();
		}

		LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);

		/* and mark it done */
		/* 【中文】执行完毕，清空槽位 */
		workitem->avw_active = false;
		workitem->avw_used = false;
	}
	LWLockRelease(AutovacuumLock);

	/*
	 * We leak table_toast_map here (among other things), but since we're
	 * going away soon, it's not a problem normally.  But when using Valgrind,
	 * release some stuff to reduce complaints about leaked storage.
	 */
#ifdef USE_VALGRIND
	hash_destroy(table_toast_map);
	FreeTupleDesc(pg_class_desc);
	if (bstrategy)
		pfree(bstrategy);
#endif

	/* Run the rest in xact context, mainly to avoid Valgrind leak warnings */
	MemoryContextSwitchTo(TopTransactionContext);

	/*
	 * Update pg_database.datfrozenxid, and truncate pg_xact if possible. We
	 * only need to do this once, not after each table.
	 *
	 * Even if we didn't vacuum anything, it may still be important to do
	 * this, because one indirect effect of vac_update_datfrozenxid() is to
	 * update TransamVariables->xidVacLimit.  That might need to be done even
	 * if we haven't vacuumed anything, because relations with older
	 * relfrozenxid values or other databases with older datfrozenxid values
	 * might have been dropped, allowing xidVacLimit to advance.
	 *
	 * However, it's also important not to do this blindly in all cases,
	 * because when autovacuum=off this will restart the autovacuum launcher.
	 * If we're not careful, an infinite loop can result, where workers find
	 * no work to do and restart the launcher, which starts another worker in
	 * the same database that finds no work to do.  To prevent that, we skip
	 * this if (1) we found no work to do and (2) we skipped at least one
	 * table due to concurrent autovacuum activity.  In that case, the other
	 * worker has already done it, or will do so when it finishes.
	 * 【中文】收尾：推进 datfrozenxid 并截断 pg_xact（整库只做一次）。
	 * 即使没清任何表也可能要做——vac_update_datfrozenxid() 的副作用是
	 * 推进 TransamVariables->xidVacLimit，某些表/库的 frozenxid 可能因
	 * 对象被删而允许前移。
	 * 但"盲目执行"有陷阱：autovacuum=off 时调用它会重启 launcher！
	 * 若不谨慎会形成死循环：worker 没事干 → 重启 launcher → launcher
	 * 又派新 worker 进同一个库 → 又没事干 → 又重启…… 因此当
	 * "本次没干活"且"曾因并发跳过表"时跳过（另一 worker 已经做了
	 * 或等它收尾时再做）。
	 */
	if (did_vacuum || !found_concurrent_worker)
		vac_update_datfrozenxid();

	/* Finally close out the last transaction. */
	/* 【中文】提交最后一个事务，do_autovacuum 完成。 */
	CommitTransactionCommand();
}

/*
 * Execute a previously registered work item.
 * 【中文】执行一个委托工作项（被 do_autovacuum 调用，处理 BRIN
 * summarize range 这类请求）：预取对象名供报错用 → 上报 pgstat 活动 →
 * 按类型分发执行（目前只有 AVW_BRINSummarizeRange，直接调用
 * brin_summarize_range()）→ 出错则回滚事务、重置内存、继续下一个。
 * 与逐表清理一样用 PG_TRY 隔离单个工作项的失败（工作项列表可能
 * 因此"丢项"，注释明示这是可接受的）。
 */
static void
perform_work_item(AutoVacuumWorkItem *workitem)
{
	char	   *cur_datname = NULL;
	char	   *cur_nspname = NULL;
	char	   *cur_relname = NULL;

	/*
	 * Note we do not store table info in MyWorkerInfo, since this is not
	 * vacuuming proper.
	 * 【中文】注意：这不属于真正的 VACUUM，所以不写 wi_tableoid 占坑。
	 */

	/*
	 * Save the relation name for a possible error message, to avoid a catalog
	 * lookup in case of an error.  If any of these return NULL, then the
	 * relation has been dropped since last we checked; skip it.
	 * 【中文】预取对象名（出错日志用）；取不到说明对象已被删，跳过。
	 */
	Assert(CurrentMemoryContext == AutovacMemCxt);

	cur_relname = get_rel_name(workitem->avw_relation);
	cur_nspname = get_namespace_name(get_rel_namespace(workitem->avw_relation));
	cur_datname = get_database_name(MyDatabaseId);
	if (!cur_relname || !cur_nspname || !cur_datname)
		goto deleted2;

	autovac_report_workitem(workitem, cur_nspname, cur_relname);

	/* clean up memory before each work item */
	MemoryContextReset(PortalContext);

	/*
	 * We will abort the current work item if something errors out, and
	 * continue with the next one; in particular, this happens if we are
	 * interrupted with SIGINT.  Note that this means that the work item list
	 * can be lossy.
	 * 【中文】PG_TRY 隔离单个工作项失败（出错/SIGINT 都放弃当前项，
	 * 继续下一个；已认领的项被放弃 = 列表"丢项"，可接受）。
	 */
	PG_TRY();
	{
		/* Use PortalContext for any per-work-item allocations */
		MemoryContextSwitchTo(PortalContext);

		/*
		 * Have at it.  Functions called here are responsible for any required
		 * user switch and sandbox.
		 */
		switch (workitem->avw_type)
		{
			case AVW_BRINSummarizeRange:
				/* 【中文】BRIN 索引页范围汇总（由 brin_summarize_range
				 * 前端函数注册的委托任务） */
				DirectFunctionCall2(brin_summarize_range,
									ObjectIdGetDatum(workitem->avw_relation),
									Int64GetDatum((int64) workitem->avw_blockNumber));
				break;
			default:
				elog(WARNING, "unrecognized work item found: type %d",
					 workitem->avw_type);
				break;
		}

		/*
		 * Clear a possible query-cancel signal, to avoid a late reaction to
		 * an automatically-sent signal because of vacuuming the current table
		 * (we're done with it, so it would make no sense to cancel at this
		 * point.)
		 */
		QueryCancelPending = false;
	}
	PG_CATCH();
	{
		/*
		 * Abort the transaction, start a new one, and proceed with the next
		 * table in our list.
		 */
		HOLD_INTERRUPTS();
		errcontext("processing work entry for relation \"%s.%s.%s\"",
				   cur_datname, cur_nspname, cur_relname);
		EmitErrorReport();

		/* this resets ProcGlobal->statusFlags[i] too */
		AbortOutOfAnyTransaction();
		FlushErrorState();
		MemoryContextReset(PortalContext);

		/* restart our transaction for the following operations */
		StartTransactionCommand();
		RESUME_INTERRUPTS();
	}
	PG_END_TRY();

	/* Make sure we're back in AutovacMemCxt */
	MemoryContextSwitchTo(AutovacMemCxt);

	/* We intentionally do not set did_vacuum here */
	/* 【中文】注意：工作项不算"vacuum 过"，不置 did_vacuum
	 * （否则会影响收尾 vac_update_datfrozenxid 的调用决策） */

	/* be tidy */
deleted2:
	if (cur_datname)
		pfree(cur_datname);
	if (cur_nspname)
		pfree(cur_nspname);
	if (cur_relname)
		pfree(cur_relname);
}

/*
 * extract_autovac_opts
 *
 * Given a relation's pg_class tuple, return a palloc'd copy of the
 * AutoVacOpts portion of reloptions, if set; otherwise, return NULL.
 *
 * Note: callers do not have a relation lock on the table at this point,
 * so the table could have been dropped, and its catalog rows gone, after
 * we acquired the pg_class row.  If pg_class had a TOAST table, this would
 * be a risk; fortunately, it doesn't.
 * 【中文】从 pg_class 元组的 reloptions 里抽出 AutoVacOpts 子结构
 * （表的 autovacuum 相关存储参数，如 autovacuum_enabled、
 * autovacuum_vacuum_threshold 等），未设置则返回 NULL（= 用全局 GUC）。
 * 注意：调用者此刻没有持表锁，表可能已被删——好在 pg_class 本身
 * 没有 TOAST 表，读它的 reloptions 没有二级依赖风险。
 */
static AutoVacOpts *
extract_autovac_opts(HeapTuple tup, TupleDesc pg_class_desc)
{
	bytea	   *relopts;
	AutoVacOpts *av;

	Assert(((Form_pg_class) GETSTRUCT(tup))->relkind == RELKIND_RELATION ||
		   ((Form_pg_class) GETSTRUCT(tup))->relkind == RELKIND_MATVIEW ||
		   ((Form_pg_class) GETSTRUCT(tup))->relkind == RELKIND_TOASTVALUE);

	relopts = extractRelOptions(tup, pg_class_desc, NULL);
	if (relopts == NULL)
		return NULL;

	/* 【中文】拷贝出 StdRdOptions 里的 autovacuum 子结构并释放原数据 */
	av = palloc_object(AutoVacOpts);
	memcpy(av, &(((StdRdOptions *) relopts)->autovacuum), sizeof(AutoVacOpts));
	pfree(relopts);

	return av;
}


/*
 * table_recheck_autovac
 *
 * Recheck whether a table still needs vacuum or analyze.  Return value is a
 * valid autovac_table pointer if it does, NULL otherwise.
 *
 * Note that the returned autovac_table does not have the name fields set.
 * 【中文】对单张表做"复查"（do_autovacuum 主体循环里、真正开工前调用）：
 * 重新取 pg_class 元组和 pgstats 统计，再次调用 relation_needs_vacanalyze
 * 确认这张表"仍然"需要清理（第一遍扫描到复查之间，表可能已被别的
 * worker/后端清过）。仍需要则组装出 autovac_table：
 *  - 逐项确定 VACUUM/ANALYZE 参数：freeze 年龄（表级 reloptions >
 *    GUC 默认值）、日志时长（-1 = 用 autovacuum 自己的 Log_* 默认）、
 *    防回卷选项、并行度（reloption 的 autovacuum_parallel_workers）等；
 *  - 关键：不带 VACOPT_PROCESS_TOAST（TOAST 单独排班）、带
 *    VACOPT_SKIP_DATABASE_STATS（datfrozenxid 由 do_autovacuum 统一推进）、
 *    非回卷时带 VACOPT_SKIP_LOCKED（拿不到锁就跳过，别阻塞业务）；
 *  - at_dobalance：表级配了 cost 参数（limit>0 或 delay>=0）就不参与
 *    全局 cost 平衡。
 * 返回的 autovac_table 的 name 字段（库/模式/表名）由调用者填充。
 */
static autovac_table *
table_recheck_autovac(Oid relid, HTAB *table_toast_map,
					  TupleDesc pg_class_desc,
					  int effective_multixact_freeze_max_age)
{
	Form_pg_class classForm;
	HeapTuple	classTup;
	bool		dovacuum;
	bool		doanalyze;
	autovac_table *tab = NULL;
	bool		wraparound;
	AutoVacOpts *avopts;
	bool		free_avopts = false;
	AutoVacuumScores scores;

	/* fetch the relation's relcache entry */
	classTup = SearchSysCacheCopy1(RELOID, ObjectIdGetDatum(relid));
	if (!HeapTupleIsValid(classTup))
		return NULL;
	classForm = (Form_pg_class) GETSTRUCT(classTup);

	/*
	 * Get the applicable reloptions.  If it is a TOAST table, try to get the
	 * main table reloptions if the toast table itself doesn't have.
	 * 【中文】取 reloptions：TOAST 表自身没有时回溯主表的参数。
	 */
	avopts = extract_autovac_opts(classTup, pg_class_desc);
	if (avopts)
		free_avopts = true;
	else if (classForm->relkind == RELKIND_TOASTVALUE &&
			 table_toast_map != NULL)
	{
		av_relation *hentry;
		bool		found;

		hentry = hash_search(table_toast_map, &relid, HASH_FIND, &found);
		if (found && hentry->ar_hasrelopts)
			avopts = &hentry->ar_reloptions;
	}

	relation_needs_vacanalyze(relid, avopts, classForm,
							  effective_multixact_freeze_max_age,
							  DEBUG3,
							  &dovacuum, &doanalyze, &wraparound,
							  &scores);

	/* OK, it needs something done */
	if (doanalyze || dovacuum)
	{
		int			freeze_min_age;
		int			freeze_table_age;
		int			multixact_freeze_min_age;
		int			multixact_freeze_table_age;
		int			log_vacuum_min_duration;
		int			log_analyze_min_duration;

		/*
		 * Calculate the vacuum cost parameters and the freeze ages.  If there
		 * are options set in pg_class.reloptions, use them; in the case of a
		 * toast table, try the main table too.  Otherwise use the GUC
		 * defaults, autovacuum's own first and plain vacuum second.
		 * 【中文】参数解析优先级：表级 reloptions > autovacuum GUC >
		 * 普通 vacuum 默认（autovacuum 专用参数没有则回退普通 vacuum）。
		 */

		/* -1 in autovac setting means use log_autovacuum_min_duration */
		/* 【中文】log 时长 -1 = 用 Log_autovacuum_min_duration 全局默认 */
		log_vacuum_min_duration = (avopts && avopts->log_vacuum_min_duration >= 0)
			? avopts->log_vacuum_min_duration
			: Log_autovacuum_min_duration;

		/* -1 in autovac setting means use log_autoanalyze_min_duration */
		log_analyze_min_duration = (avopts && avopts->log_analyze_min_duration >= 0)
			? avopts->log_analyze_min_duration
			: Log_autoanalyze_min_duration;

		/* these do not have autovacuum-specific settings */
		/* 【中文】freeze 参数没有 autovacuum 专用 GUC，回退到
		 * 本库默认值（do_autovacuum 开头根据库性质定的） */
		freeze_min_age = (avopts && avopts->freeze_min_age >= 0)
			? avopts->freeze_min_age
			: default_freeze_min_age;

		freeze_table_age = (avopts && avopts->freeze_table_age >= 0)
			? avopts->freeze_table_age
			: default_freeze_table_age;

		multixact_freeze_min_age = (avopts &&
									avopts->multixact_freeze_min_age >= 0)
			? avopts->multixact_freeze_min_age
			: default_multixact_freeze_min_age;

		multixact_freeze_table_age = (avopts &&
									  avopts->multixact_freeze_table_age >= 0)
			? avopts->multixact_freeze_table_age
			: default_multixact_freeze_table_age;

		tab = palloc_object(autovac_table);
		tab->at_relid = relid;

		/*
		 * Select VACUUM options.  Note we don't say VACOPT_PROCESS_TOAST, so
		 * that vacuum() skips toast relations.  Also note we tell vacuum() to
		 * skip vac_update_datfrozenxid(); we'll do that separately.
		 * 【中文】组装 VACUUM 选项：
		 *  - 不带 VACOPT_PROCESS_TOAST：TOAST 表由 worker 单独排班；
		 *  - 带 VACOPT_SKIP_DATABASE_STATS：datfrozenxid 统一在
		 *    do_autovacuum 收尾时推进，避免每张表都做一遍；
		 *  - 非回卷任务带 VACOPT_SKIP_LOCKED：表锁被业务占着就跳过
		 *    清这张表（绝不阻塞业务），回卷任务则必须等待拿到锁。
		 */
		tab->at_params.options =
			(dovacuum ? (VACOPT_VACUUM |
						 VACOPT_PROCESS_MAIN |
						 VACOPT_SKIP_DATABASE_STATS) : 0) |
			(doanalyze ? VACOPT_ANALYZE : 0) |
			(!wraparound ? VACOPT_SKIP_LOCKED : 0);

		/*
		 * index_cleanup and truncate are unspecified at first in autovacuum.
		 * They will be filled in with usable values using their reloptions
		 * (or reloption defaults) later.
		 * 【中文】index_cleanup/truncate 先置"未指定"，vacuum 内部会
		 * 按 reloptions（或默认值）填成可用值。
		 */
		tab->at_params.index_cleanup = VACOPTVALUE_UNSPECIFIED;
		tab->at_params.truncate = VACOPTVALUE_UNSPECIFIED;
		tab->at_params.freeze_min_age = freeze_min_age;
		tab->at_params.freeze_table_age = freeze_table_age;
		tab->at_params.multixact_freeze_min_age = multixact_freeze_min_age;
		tab->at_params.multixact_freeze_table_age = multixact_freeze_table_age;
		tab->at_params.is_wraparound = wraparound;
		tab->at_params.log_vacuum_min_duration = log_vacuum_min_duration;
		tab->at_params.log_analyze_min_duration = log_analyze_min_duration;
		tab->at_params.toast_parent = InvalidOid;

		/* Determine the number of parallel vacuum workers to use */
		/* 【中文】并行清理 worker 数：reloption 的
		 * autovacuum_parallel_workers：0 = 显式禁用并行（-1），
		 * >0 = 用指定度数，-1 = 未设置（保持 nworkers=0 交给
		 * vacuum 内部决定） */
		tab->at_params.nworkers = 0;
		if (avopts)
		{
			if (avopts->autovacuum_parallel_workers == 0)
			{
				/*
				 * Disable parallel vacuum, if the reloption sets the parallel
				 * degree as zero.
				 */
				tab->at_params.nworkers = -1;
			}
			else if (avopts->autovacuum_parallel_workers > 0)
				tab->at_params.nworkers = avopts->autovacuum_parallel_workers;

			/*
			 * autovacuum_parallel_workers == -1 falls through, keep
			 * nworkers=0
			 */
		}

		/*
		 * Later, in vacuum_rel(), we check reloptions for any
		 * vacuum_max_eager_freeze_failure_rate override.
		 * 【中文】max_eager_freeze_failure_rate 的 reloptions 覆盖
		 * 由 vacuum_rel() 内部自行处理，这里先传全局默认值。
		 */
		tab->at_params.max_eager_freeze_failure_rate = vacuum_max_eager_freeze_failure_rate;
		tab->at_storage_param_vac_cost_limit = avopts ?
			avopts->vacuum_cost_limit : 0;
		tab->at_storage_param_vac_cost_delay = avopts ?
			avopts->vacuum_cost_delay : -1;
		tab->at_relname = NULL;
		tab->at_nspname = NULL;
		tab->at_datname = NULL;

		/*
		 * If any of the cost delay parameters has been set individually for
		 * this table, disable the balancing algorithm.
		 * 【中文】表级配了 cost 参数（limit>0 或 delay>=0）→ 该表
		 * 不参与全局 cost 分摊（它有自己的预算主张）。
		 */
		tab->at_dobalance =
			!(avopts && (avopts->vacuum_cost_limit > 0 ||
						 avopts->vacuum_cost_delay >= 0));
	}

	if (free_avopts)
		pfree(avopts);
	heap_freetuple(classTup);
	return tab;
}

/*
 * relation_needs_vacanalyze
 *
 * Check whether a relation needs to be vacuumed or analyzed; return each into
 * "dovacuum" and "doanalyze", respectively.  Also return whether the vacuum is
 * being forced because of Xid or multixact wraparound.
 *
 * relopts is a pointer to the AutoVacOpts options (either for itself in the
 * case of a plain table, or for either itself or its parent table in the case
 * of a TOAST table), NULL if none.
 *
 * A table needs to be vacuumed if the number of dead tuples exceeds a
 * threshold.  This threshold is calculated as
 *
 * threshold = vac_base_thresh + vac_scale_factor * reltuples
 * if (threshold > vac_max_thresh)
 *     threshold = vac_max_thresh;
 *
 * For analyze, the analysis done is that the number of tuples inserted,
 * deleted and updated since the last analyze exceeds a threshold calculated
 * in the same fashion as above.  Note that the cumulative stats system stores
 * the number of tuples (both live and dead) that there were as of the last
 * analyze.  This is asymmetric to the VACUUM case.
 *
 * We also force vacuum if the table's relfrozenxid is more than freeze_max_age
 * transactions back, and if its relminmxid is more than
 * multixact_freeze_max_age multixacts back.
 *
 * A table whose autovacuum_enabled option is false is
 * automatically skipped (unless we have to vacuum it due to freeze_max_age).
 * Thus autovacuum can be disabled for specific tables. Also, when the cumulative
 * stats system does not have data about a table, it will be skipped.
 *
 * A table whose vac_base_thresh value is < 0 takes the base value from the
 * autovacuum_vacuum_threshold GUC variable.  Similarly, a vac_scale_factor
 * value < 0 is substituted with the value of
 * autovacuum_vacuum_scale_factor GUC variable.  Ditto for analyze.
 *
 * This function also returns scores that can be used to sort the list of
 * tables to process.  The idea is to have autovacuum prioritize tables that
 * are furthest beyond their thresholds (e.g., a table nearing transaction ID
 * wraparound should be vacuumed first).  This prioritization scheme is
 * certainly far from perfect; there are simply too many possibilities for any
 * scoring technique to work across all workloads, and the situation might
 * change significantly between the time we calculate the score and the time
 * that autovacuum processes it.  However, we have attempted to develop
 * something that is expected to work for a large portion of workloads with
 * reasonable parameter settings.
 *
 * The autovacuum table score is calculated as the maximum of the ratios of
 * each of the table's relevant values to its threshold.  For example, if the
 * number of inserted tuples is 100, and the insert threshold for the table is
 * 80, the insert score is 1.25.  If all other scores are below that value, the
 * returned score will be 1.25.  The other criteria considered for the score
 * are the table ages (both relfrozenxid and relminmxid) compared to the
 * corresponding freeze-max-age setting, the number of updated/deleted tuples
 * compared to the vacuum threshold, and the number of inserted/updated/deleted
 * tuples compared to the analyze threshold.
 *
 * One exception to the previous paragraph is for tables nearing wraparound,
 * i.e., those that have surpassed the effective failsafe ages.  In that case,
 * the relfrozenxid/relminmxid-based score is scaled aggressively so that the
 * table has a decent chance of sorting to the front of the list.  Furthermore,
 * the relminmxid-based score is scaled aggressively as
 * effective_multixact_freeze_max_age is lowered due to high multixact member
 * space usage.
 *
 * To adjust how strongly each component contributes to the score, the
 * following parameters can be adjusted from their default of 1.0 to anywhere
 * between 0.0 and 10.0 (inclusive).  Setting all of these to 0.0 restores
 * pre-v19 prioritization behavior:
 *
 *     autovacuum_freeze_score_weight
 *     autovacuum_multixact_freeze_score_weight
 *     autovacuum_vacuum_score_weight
 *     autovacuum_vacuum_insert_score_weight
 *     autovacuum_analyze_score_weight
 *
 * The autovacuum table score is returned in scores->max.  The component scores
 * are also returned in the "scores" argument via the other members of the
 * AutoVacuumScores struct.
 * 【中文】单表体检函数（"是否需要自动清理"判定 + 紧迫度评分的核心）：
 *  - 参数解析：表级 reloptions 优先，未设置回退 autovacuum GUC
 *    （阈值 = vac_base_thresh + vac_scale_factor × reltuples，
 *     上限 vac_max_thresh 封顶；vacuum_ins/analyze 同理）；
 *  - 强制清理：relfrozenxid 早于 recentXid - freeze_max_age（XID 回卷）
 *    或 relminmxid 早于 recentMulti - multixact_freeze_max_age
 *    （MultiXact 回卷）→ 无条件 dovacuum（即使 autovacuum_enabled=false
 *    或 autovacuum 被整体关闭，这是防数据丢失的底线）；
 *  - 常规判定：autovacuum_enabled 表参数 + AutoVacuumingActive() 全局开关
 *    都打开、且 pgstats 里有该表数据时，按阈值比较：
 *      dead_tuples > vacthresh → 要 VACUUM
 *      ins_since_vacuum > vacinsthresh（插入量，按未冻结页占比修正）→ 要 VACUUM
 *      mod_since_analyze > anlthresh → 要 ANALYZE（TOAST 与 pg_statistic 除外）
 *  - 评分（供排序）：各分量得分 = 实际值 ÷ 阈值（xid/mxid 为年龄 ÷
 *    freeze_max_age）；越逼近回卷（超过 failsafe 年龄）得分按指数
 *    急剧放大（pow 放大），确保回卷表排到最前；
 *    分量再乘各自的 *_score_weight 权重，max 作为总评分。
 */
static void
relation_needs_vacanalyze(Oid relid,
						  AutoVacOpts *relopts,
						  Form_pg_class classForm,
						  int effective_multixact_freeze_max_age,
						  int elevel,
 /* output params below */
						  bool *dovacuum,
						  bool *doanalyze,
						  bool *wraparound,
						  AutoVacuumScores *scores)
{
	PgStat_StatTabEntry *tabentry;
	bool		force_vacuum;
	bool		av_enabled;
	bool		may_free = false;

	/* constants from reloptions or GUC variables */
	int			vac_base_thresh,
				vac_max_thresh,
				vac_ins_base_thresh,
				anl_base_thresh;
	float4		vac_scale_factor,
				vac_ins_scale_factor,
				anl_scale_factor;

	/* thresholds calculated from above constants */
	float4		vacthresh,
				vacinsthresh,
				anlthresh;

	/* number of vacuum (resp. analyze) tuples at this time */
	float4		vactuples,
				instuples,
				anltuples;

	/* freeze parameters */
	int			freeze_max_age;
	int			multixact_freeze_max_age;
	TransactionId xidForceLimit;
	TransactionId relfrozenxid;
	MultiXactId relminmxid;
	MultiXactId multiForceLimit;
	uint32		xid_age;
	uint32		mxid_age;
	int			effective_xid_failsafe_age;
	int			effective_mxid_failsafe_age;

	float4		pcnt_unfrozen = 1;
	float4		reltuples = classForm->reltuples;
	int32		relpages = classForm->relpages;
	int32		relallfrozen = classForm->relallfrozen;

	Assert(classForm != NULL);
	Assert(OidIsValid(relid));

	memset(scores, 0, sizeof(AutoVacuumScores));
	*dovacuum = false;
	*doanalyze = false;

	/*
	 * Determine vacuum/analyze equation parameters.  We have two possible
	 * sources: the passed reloptions (which could be a main table or a toast
	 * table), or the autovacuum GUC variables.
	 * 【中文】阈值公式参数确定：表级 reloptions（主表或 TOAST 的）
	 * 优先，否则用 autovacuum GUC 全局值。
	 */

	/* -1 in autovac setting means use plain vacuum_scale_factor */
	/* 【中文】-1 = 未设置，回退到普通 vacuum 的 scale factor */
	vac_scale_factor = (relopts && relopts->vacuum_scale_factor >= 0)
		? relopts->vacuum_scale_factor
		: autovacuum_vac_scale;

	vac_base_thresh = (relopts && relopts->vacuum_threshold >= 0)
		? relopts->vacuum_threshold
		: autovacuum_vac_thresh;

	/* -1 is used to disable max threshold */
	/* 【中文】vacuum_max_threshold：-1 表示不设上限（v19 新增参数，
	 * 防止大表被阈值公式算出天文数字） */
	vac_max_thresh = (relopts && relopts->vacuum_max_threshold >= -1)
		? relopts->vacuum_max_threshold
		: autovacuum_vac_max_thresh;

	vac_ins_scale_factor = (relopts && relopts->vacuum_ins_scale_factor >= 0)
		? relopts->vacuum_ins_scale_factor
		: autovacuum_vac_ins_scale;

	/* -1 is used to disable insert vacuums */
	/* 【中文】vacuum_ins_threshold：-1 表示禁用"按插入量触发 VACUUM" */
	vac_ins_base_thresh = (relopts && relopts->vacuum_ins_threshold >= -1)
		? relopts->vacuum_ins_threshold
		: autovacuum_vac_ins_thresh;

	anl_scale_factor = (relopts && relopts->analyze_scale_factor >= 0)
		? relopts->analyze_scale_factor
		: autovacuum_anl_scale;

	anl_base_thresh = (relopts && relopts->analyze_threshold >= 0)
		? relopts->analyze_threshold
		: autovacuum_anl_thresh;

	freeze_max_age = (relopts && relopts->freeze_max_age >= 0)
		? Min(relopts->freeze_max_age, autovacuum_freeze_max_age)
		: autovacuum_freeze_max_age;

	multixact_freeze_max_age = (relopts && relopts->multixact_freeze_max_age >= 0)
		? Min(relopts->multixact_freeze_max_age, effective_multixact_freeze_max_age)
		: effective_multixact_freeze_max_age;

	/* 【中文】表级 autovacuum_enabled（默认 true）∧ 全局 autovacuum
	 * 开关：常规触发（非回卷）必须两者都开 */
	av_enabled = (relopts ? relopts->enabled : true);
	av_enabled &= AutoVacuumingActive();

	relfrozenxid = classForm->relfrozenxid;
	relminmxid = classForm->relminmxid;

	/* Force vacuum if table is at risk of wraparound */
	/* 【中文】回卷检查：表的 relfrozenxid 早于
	 * (recentXid - freeze_max_age) → 必须清（force_vacuum） */
	xidForceLimit = recentXid - freeze_max_age;
	if (xidForceLimit < FirstNormalTransactionId)
		xidForceLimit -= FirstNormalTransactionId;
	force_vacuum = (TransactionIdIsNormal(relfrozenxid) &&
					TransactionIdPrecedes(relfrozenxid, xidForceLimit));
	if (!force_vacuum)
	{
		/* 【中文】XID 没超限再看 MultiXact：relminmxid 早于界限同样强制 */
		multiForceLimit = recentMulti - multixact_freeze_max_age;
		if (multiForceLimit < FirstMultiXactId)
			multiForceLimit -= FirstMultiXactId;
		force_vacuum = MultiXactIdIsValid(relminmxid) &&
			MultiXactIdPrecedes(relminmxid, multiForceLimit);
	}
	*wraparound = force_vacuum;

	/*
	 * To calculate the (M)XID age portion of the score, divide the age by its
	 * respective *_freeze_max_age parameter.  The multixact_freeze_max_age
	 * variable might be 0 here (i.e., a division-by-zero hazard), so in that
	 * case we use the mxid_age as the MXID score.
	 */
	xid_age = TransactionIdIsNormal(relfrozenxid) ? recentXid - relfrozenxid : 0;
	mxid_age = MultiXactIdIsValid(relminmxid) ? recentMulti - relminmxid : 0;

	scores->xid = (double) xid_age / freeze_max_age;
	scores->mxid = (double) mxid_age / Max(1, multixact_freeze_max_age);

	/*
	 * To ensure tables are given increased priority once they begin
	 * approaching wraparound, we scale the score aggressively if the ages
	 * surpass vacuum_failsafe_age or vacuum_multixact_failsafe_age.
	 *
	 * As in vacuum_xid_failsafe_check(), the effective failsafe age is no
	 * less than 105% the value of the respective *_freeze_max_age parameter.
	 * Note that per-table settings could result in a low score even if the
	 * table surpasses the failsafe settings.  However, this is a strange
	 * enough corner case that we don't bother trying to handle it.
	 *
	 * We further adjust the effective failsafe ages with the weight
	 * parameters so that increasing them lowers the ages at which we begin
	 * scaling aggressively.
	 * 【中文】回卷逼近时的"分数急剧放大"策略：一旦年龄超过 failsafe
	 * 年龄（取 max(vacuum_failsafe_age, freeze_max_age×1.05)），
	 * xid/mxid 得分就按 pow() 指数放大——年龄越大放大越狠，保证
	 * 濒临回卷的表稳稳排到待处理列表最前面。
	 */
	effective_xid_failsafe_age = Max(vacuum_failsafe_age,
									 autovacuum_freeze_max_age * 1.05);
	effective_mxid_failsafe_age = Max(vacuum_multixact_failsafe_age,
									  autovacuum_multixact_freeze_max_age * 1.05);

	if (autovacuum_freeze_score_weight > 1.0)
		effective_xid_failsafe_age /= autovacuum_freeze_score_weight;
	if (autovacuum_multixact_freeze_score_weight > 1.0)
		effective_mxid_failsafe_age /= autovacuum_multixact_freeze_score_weight;

	if (xid_age >= effective_xid_failsafe_age)
		scores->xid = pow(scores->xid, Max(1.0, (double) xid_age / 100000000));
	if (mxid_age >= effective_mxid_failsafe_age)
		scores->mxid = pow(scores->mxid, Max(1.0, (double) mxid_age / 100000000));

	scores->xid *= autovacuum_freeze_score_weight;
	scores->mxid *= autovacuum_multixact_freeze_score_weight;

	scores->max = Max(scores->xid, scores->mxid);
	if (force_vacuum)
		*dovacuum = true;

	/*
	 * If we found stats for the table, and autovacuum is currently enabled,
	 * make a threshold-based decision whether to vacuum and/or analyze.  If
	 * autovacuum is currently disabled, we must be here for anti-wraparound
	 * vacuuming only, so don't vacuum (or analyze) anything that's not being
	 * forced.
	 * 【中文】常规阈值判定开始：无 pgstats 统计 → 直接返回（只保留
	 * 回卷强制结论）；autovacuum 被关时本函数只会因回卷被调用，
	 * 不做任何非强制的清理。
	 */
	tabentry = pgstat_fetch_stat_tabentry_ext(classForm->relisshared,
											  relid, &may_free);
	if (!tabentry)
		return;

	vactuples = tabentry->dead_tuples;
	instuples = tabentry->ins_since_vacuum;
	anltuples = tabentry->mod_since_analyze;

	/* If the table hasn't yet been vacuumed, take reltuples as zero */
	if (reltuples < 0)
		reltuples = 0;

	/*
	 * If we have data for relallfrozen, calculate the unfrozen percentage of
	 * the table to modify insert scale factor. This helps us decide whether
	 * or not to vacuum an insert-heavy table based on the number of inserts
	 * to the more "active" part of the table.
	 * 【中文】用"未冻结页占比"修正插入量阈值：INSERT 大量落在表的
	 * 未冻结部分（活跃区），按比例修正后判断更准确。
	 */
	if (relpages > 0 && relallfrozen > 0)
	{
		/*
		 * It could be the stats were updated manually and relallfrozen >
		 * relpages. Clamp relallfrozen to relpages to avoid nonsensical
		 * calculations.
		 * 【中文】防御：统计被手工改过导致 relallfrozen > relpages，
		 * 先截断再算。
		 */
		relallfrozen = Min(relallfrozen, relpages);
		pcnt_unfrozen = 1 - ((float4) relallfrozen / relpages);
	}

	/* 【中文】三个阈值：vac（死元组）、vac_ins（插入量）、anl（变更量） */
	vacthresh = (float4) vac_base_thresh + vac_scale_factor * reltuples;
	if (vac_max_thresh >= 0 && vacthresh > (float4) vac_max_thresh)
		vacthresh = (float4) vac_max_thresh;

	vacinsthresh = (float4) vac_ins_base_thresh +
		vac_ins_scale_factor * reltuples * pcnt_unfrozen;
	anlthresh = (float4) anl_base_thresh + anl_scale_factor * reltuples;

	/* Determine if this table needs vacuum, and update the score. */
	/* 【中文】死元组超阈值 → 需要 VACUUM；得分 = 死元组/阈值 */
	scores->vac = (double) vactuples / Max(vacthresh, 1);
	scores->vac *= autovacuum_vacuum_score_weight;
	scores->max = Max(scores->max, scores->vac);
	if (av_enabled && vactuples > vacthresh)
		*dovacuum = true;

	if (vac_ins_base_thresh >= 0)
	{
		/* 【中文】插入量超阈值 → 也需要 VACUUM（insert-only 表场景） */
		scores->vac_ins = (double) instuples / Max(vacinsthresh, 1);
		scores->vac_ins *= autovacuum_vacuum_insert_score_weight;
		scores->max = Max(scores->max, scores->vac_ins);
		if (av_enabled && instuples > vacinsthresh)
			*dovacuum = true;
	}

	/*
	 * Determine if this table needs analyze, and update the score.  Note that
	 * we don't analyze TOAST tables and pg_statistic.
	 * 【中文】变更量超阈值 → 需要 ANALYZE。TOAST 表与 pg_statistic
	 * 本身不做 analyze。
	 */
	if (relid != StatisticRelationId &&
		classForm->relkind != RELKIND_TOASTVALUE)
	{
		scores->anl = (double) anltuples / Max(anlthresh, 1);
		scores->anl *= autovacuum_analyze_score_weight;
		scores->max = Max(scores->max, scores->anl);
		if (av_enabled && anltuples > anlthresh)
			*doanalyze = true;
	}

	if (vac_ins_base_thresh >= 0)
		elog(elevel, "%s: vac: %.0f (thresh %.0f, score %.2f), ins: %.0f (thresh %.0f, score %.2f), anl: %.0f (thresh %.0f, score %.2f), xid score: %.2f, mxid score: %.2f",
			 NameStr(classForm->relname),
			 vactuples, vacthresh, scores->vac,
			 instuples, vacinsthresh, scores->vac_ins,
			 anltuples, anlthresh, scores->anl,
			 scores->xid, scores->mxid);
	else
		elog(elevel, "%s: vac: %.0f (thresh %.0f, score %.2f), ins: (disabled), anl: %.0f (thresh %.0f, score %.2f), xid score: %.2f, mxid score: %.2f",
			 NameStr(classForm->relname),
			 vactuples, vacthresh, scores->vac,
			 anltuples, anlthresh, scores->anl,
			 scores->xid, scores->mxid);

	/* Avoid leaking pgstat entries until the end of autovacuum. */
	if (may_free)
		pfree(tabentry);
}

/*
 * autovacuum_do_vac_analyze
 *		Vacuum and/or analyze the specified table
 *
 * We expect the caller to have switched into a memory context that won't
 * disappear at transaction commit.
 * 【中文】对单张表执行 VACUUM/ANALYZE 的最后一跳：
 *   1. autovac_report_activity() 上报活动（pg_stat_activity 里能看到
 *      "autovacuum: VACUUM 库.模式.表"）；
 *   2. 创建"Vacuum"上下文作为 vacuum() 跨事务存储的容器；
 *   3. 组装 VacuumRelation（按 OID 定位目标，不按名字——名字只是
 *      日志显示用）；
 *   4. 调用真正的 vacuum() 干活（与手动 VACUUM 完全同一条代码路径）。
 */
static void
autovacuum_do_vac_analyze(autovac_table *tab, BufferAccessStrategy bstrategy)
{
	RangeVar   *rangevar;
	VacuumRelation *rel;
	List	   *rel_list;
	MemoryContext vac_context;
	MemoryContext old_context;

	/* Let pgstat know what we're doing */
	autovac_report_activity(tab);

	/* Create a context that vacuum() can use as cross-transaction storage */
	/* 【中文】vacuum() 内部会开/关事务，需要一个不受事务影响的
	 * 上下文放跨事务数据 */
	vac_context = AllocSetContextCreate(CurrentMemoryContext,
										"Vacuum",
										ALLOCSET_DEFAULT_SIZES);

	/* Set up one VacuumRelation target, identified by OID, for vacuum() */
	old_context = MemoryContextSwitchTo(vac_context);
	rangevar = makeRangeVar(tab->at_nspname, tab->at_relname, -1);
	rel = makeVacuumRelation(rangevar, tab->at_relid, NIL);
	rel_list = list_make1(rel);
	MemoryContextSwitchTo(old_context);

	/* 【调用链】vacuum()（commands/vacuum.c）
	 *   → vacuum() 里逐 relation：先取 OID → 检查权限/owner
	 *   → vacuum_rel()：加锁、开事务、按 reloptions 计算各项参数
	 *   → heap_vacuum_rel() 实际扫描清理（或 do_analyze_rel() 做统计）
	 *   → 手动 VACUUM 与自动清理共用这条路径，只是参数来源不同 */
	vacuum(rel_list, &tab->at_params, bstrategy, vac_context, true);

	MemoryContextDelete(vac_context);
}

/*
 * autovac_report_activity
 *		Report to pgstat what autovacuum is doing
 *
 * We send a SQL string corresponding to what the user would see if the
 * equivalent command was to be issued manually.
 *
 * Note we assume that we are going to report the next command as soon as we're
 * done with the current one, and exit right after the last one, so we don't
 * bother to report "<IDLE>" or some such.
 * 【中文】把当前动作上报给 pgstats / pg_stat_activity：
 * 拼出类似手动执行 "VACUUM ANALYZE 库.模式.表 (to prevent wraparound)"
 * 的字符串（wraparound 任务会附注 "(to prevent wraparound)"）。
 * 因为做完当前动作立刻会报下一个动作、最后直接退出，所以不需要
 * 上报 "<IDLE>" 之类的空闲状态。
 */
static void
autovac_report_activity(autovac_table *tab)
{
#define MAX_AUTOVAC_ACTIV_LEN (NAMEDATALEN * 2 + 56)
	char		activity[MAX_AUTOVAC_ACTIV_LEN];
	int			len;

	/* Report the command and possible options */
	/* 【中文】命令名：VACUUM / VACUUM ANALYZE / ANALYZE */
	if (tab->at_params.options & VACOPT_VACUUM)
		snprintf(activity, MAX_AUTOVAC_ACTIV_LEN,
				 "autovacuum: VACUUM%s",
				 tab->at_params.options & VACOPT_ANALYZE ? " ANALYZE" : "");
	else
		snprintf(activity, MAX_AUTOVAC_ACTIV_LEN,
				 "autovacuum: ANALYZE");

	/*
	 * Report the qualified name of the relation.
	 * 【中文】追加限定名：模式.表，回卷任务附注说明。
	 */
	len = strlen(activity);

	snprintf(activity + len, MAX_AUTOVAC_ACTIV_LEN - len,
			 " %s.%s%s", tab->at_nspname, tab->at_relname,
			 tab->at_params.is_wraparound ? " (to prevent wraparound)" : "");

	/* Set statement_timestamp() to current time for pg_stat_activity */
	SetCurrentStatementStartTimestamp();

	pgstat_report_activity(STATE_RUNNING, activity);
}

/*
 * autovac_report_workitem
 *		Report to pgstat that autovacuum is processing a work item
 * 【中文】工作项版本的活动上报：拼 "autovacuum: BRIN summarize 模式.表 [块号]"
 * （avw_blockNumber 有效时带上块号），同样写进 pg_stat_activity。
 */
static void
autovac_report_workitem(AutoVacuumWorkItem *workitem,
						const char *nspname, const char *relname)
{
	char		activity[MAX_AUTOVAC_ACTIV_LEN + 12 + 2];
	char		blk[12 + 2];
	int			len;

	switch (workitem->avw_type)
	{
		case AVW_BRINSummarizeRange:
			snprintf(activity, MAX_AUTOVAC_ACTIV_LEN,
					 "autovacuum: BRIN summarize");
			break;
	}

	/*
	 * Report the qualified name of the relation, and the block number if any
	 */
	len = strlen(activity);

	if (BlockNumberIsValid(workitem->avw_blockNumber))
		snprintf(blk, sizeof(blk), " %u", workitem->avw_blockNumber);
	else
		blk[0] = '\0';

	snprintf(activity + len, MAX_AUTOVAC_ACTIV_LEN - len,
			 " %s.%s%s", nspname, relname, blk);

	/* Set statement_timestamp() to current time for pg_stat_activity */
	SetCurrentStatementStartTimestamp();

	pgstat_report_activity(STATE_RUNNING, activity);
}

/*
 * AutoVacuumingActive
 *		Check GUC vars and report whether the autovacuum process should be
 *		running.
 * 【中文】autovacuum 是否"处于激活状态"的全局判断：
 * 需要 autovacuum_start_daemon=true 且 pgstat_track_counts=true 同时成立
 * （统计采集关了，autovacuum 就成了"瞎子"，无法工作）。
 * launcher 启动前的紧急兜底、SIGHUP 后判断是否该退出、以及
 * relation_needs_vacanalyze 里的常规触发开关都依赖它。
 */
bool
AutoVacuumingActive(void)
{
	if (!autovacuum_start_daemon || !pgstat_track_counts)
		return false;
	return true;
}

/*
 * Request one work item to the next autovacuum run processing our database.
 * Return false if the request can't be recorded.
 */
/* 【中文】普通后端注册"委托工作项"的入口（如 BRIN summarize range
 * 想借助 autovacuum worker 执行）：在共享内存 av_workItems[] 里找一个
 * 空槽位填入类型/库/表/块号。槽位用满（256 个）则返回 false。
 * 【调用链】AutoVacuumRequestWork()
 *   → AutovacuumLock 保护下遍历 av_workItems[] 找 avw_used=false 槽位
 *   → 填充并置 avw_used=true → 下个处理本库的 worker 在
 *     do_autovacuum() 的收尾阶段认领执行 */
bool
AutoVacuumRequestWork(AutoVacuumWorkItemType type, Oid relationId,
					  BlockNumber blkno)
{
	int			i;
	bool		result = false;

	LWLockAcquire(AutovacuumLock, LW_EXCLUSIVE);

	/*
	 * Locate an unused work item and fill it with the given data.
	 */
	for (i = 0; i < NUM_WORKITEMS; i++)
	{
		AutoVacuumWorkItem *workitem = &AutoVacuumShmem->av_workItems[i];

		if (workitem->avw_used)
			continue;

		workitem->avw_used = true;
		workitem->avw_active = false;
		workitem->avw_type = type;
		workitem->avw_database = MyDatabaseId;
		workitem->avw_relation = relationId;
		workitem->avw_blockNumber = blkno;
		result = true;

		/* done */
		break;
	}

	LWLockRelease(AutovacuumLock);

	return result;
}

/*
 * autovac_init
 *		This is called at postmaster initialization.
 *
 * All we do here is annoy the user if he got it wrong.
 * 【中文】postmaster 初始化时调用：不做任何实事，只做配置体检——
 * autovacuum 开着但 track_counts 关了 → 警告并提示；参数正常则
 * 检查 worker_slots 与 max_workers 的配合。注释自嘲"唯一的职责
 * 就是用户配错了就烦他一下"。
 */
void
autovac_init(void)
{
	if (!autovacuum_start_daemon)
		return;
	else if (!pgstat_track_counts)
		ereport(WARNING,
				(errmsg("autovacuum not started because of misconfiguration"),
				 errhint("Enable the \"track_counts\" option.")));
	else
		check_av_worker_gucs();
}

/*
 * AutoVacuumShmemRequest
 *		Register shared memory space needed for autovacuum
 * 【中文】共享内存申请回调（postmaster 建共享内存时按需回调）：
 * 申请"主结构 + 每个 worker 一个 WorkerInfoData"大小的共享内存段，
 * 名为 "AutoVacuum Data"，挂到全局指针 AutoVacuumShmem。
 */
static void
AutoVacuumShmemRequest(void *arg)
{
	Size		size;

	/*
	 * Need the fixed struct and the array of WorkerInfoData.
	 */
	size = sizeof(AutoVacuumShmemStruct);
	size = MAXALIGN(size);
	size = add_size(size, mul_size(autovacuum_worker_slots,
								   sizeof(WorkerInfoData)));

	ShmemRequestStruct(.name = "AutoVacuum Data",
					   .size = size,
					   .ptr = (void **) &AutoVacuumShmem,
		);
}

/*
 * AutoVacuumShmemInit
 *		Initialize autovacuum-related shared memory
 * 【中文】共享内存初始化回调：初始化空闲/运行链表与起始指针、
 * 清空工作项数组；把所有 WorkerInfoData 槽位（共 autovacuum_worker_slots
 * 个，紧跟在主结构之后）链进空闲链表并初始化 dobalance 原子标志；
 * 平衡计数 av_nworkersForBalance 清零。
 */
static void
AutoVacuumShmemInit(void *arg)
{
	WorkerInfo	worker;

	dclist_init(&AutoVacuumShmem->av_freeWorkers);
	dlist_init(&AutoVacuumShmem->av_runningWorkers);
	AutoVacuumShmem->av_startingWorker = NULL;
	memset(AutoVacuumShmem->av_workItems, 0,
		   sizeof(AutoVacuumWorkItem) * NUM_WORKITEMS);

	/* 【中文】worker 数组紧挨着主结构存放 */
	worker = (WorkerInfo) ((char *) AutoVacuumShmem +
						   MAXALIGN(sizeof(AutoVacuumShmemStruct)));

	/* initialize the WorkerInfo free list */
	/* 【中文】所有槽位先全部放进空闲链表（启动时没有 worker 在跑） */
	for (int i = 0; i < autovacuum_worker_slots; i++)
	{
		dclist_push_head(&AutoVacuumShmem->av_freeWorkers,
						 &worker[i].wi_links);
		pg_atomic_init_flag(&worker[i].wi_dobalance);
	}

	pg_atomic_init_u32(&AutoVacuumShmem->av_nworkersForBalance, 0);
}

/*
 * GUC check_hook for autovacuum_work_mem
 * 【中文】autovacuum_work_mem 的 GUC 校验钩子：
 * -1 = 未设置（回退 maintenance_work_mem），放行；
 * 手工设置的值下限 64kB（与 maintenance_work_mem 的下限保持一致）。
 */
bool
check_autovacuum_work_mem(int *newval, void **extra, GucSource source)
{
	/*
	 * -1 indicates fallback.
	 *
	 * If we haven't yet changed the boot_val default of -1, just let it be.
	 * Autovacuum will look to maintenance_work_mem instead.
	 * 【中文】保持 -1：worker 直接用 maintenance_work_mem。
	 */
	if (*newval == -1)
		return true;

	/*
	 * We clamp manually-set values to at least 64kB.  Since
	 * maintenance_work_mem is always set to at least this value, do the same
	 * here.
	 */
	if (*newval < 64)
		*newval = 64;

	return true;
}

/*
 * Returns whether there is a free autovacuum worker slot available.
 * 【中文】是否还有空闲 worker 槽位。注意"空闲"的判定：空闲数必须
 * 严格大于 reserved_slots（= worker_slots - max_workers，即留给非
 * autovacuum 用途的保留槽位数），否则即使有空闲槽位也不能用——
 * 保留槽位是给并行 VACUUM 等其他用途留的。
 */
static bool
av_worker_available(void)
{
	int			free_slots;
	int			reserved_slots;

	free_slots = dclist_count(&AutoVacuumShmem->av_freeWorkers);

	reserved_slots = autovacuum_worker_slots - autovacuum_max_workers;
	reserved_slots = Max(0, reserved_slots);

	return free_slots > reserved_slots;
}

/*
 * Emits a WARNING if autovacuum_worker_slots < autovacuum_max_workers.
 * 【中文】配置体检：worker_slots（共享内存槽位）小于 max_workers
 * （并发上限）时发 WARNING——服务端最多只能同时跑 worker_slots 个
 * autovacuum worker，max_workers 设再大也白搭。
 */
static void
check_av_worker_gucs(void)
{
	if (autovacuum_worker_slots < autovacuum_max_workers)
		ereport(WARNING,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("\"%s\" (%d) should be less than or equal to \"%s\" (%d)",
						"autovacuum_max_workers", autovacuum_max_workers,
						"autovacuum_worker_slots", autovacuum_worker_slots),
				 errdetail("The server will only start up to \"%s\" (%d) autovacuum workers at a given time.",
						   "autovacuum_worker_slots", autovacuum_worker_slots)));
}

/*
 * pg_stat_get_autovacuum_scores
 *
 * Returns current autovacuum scores for all relevant tables in the current
 * database.
 * 【中文】系统视图函数（pg_stat_get_autovacuum_scores，对应 v19 新增的
 * pg_stat_get_autovacuum_scores() 可查询函数）：遍历当前库 pg_class，
 * 对每张普通表/物化视图/TOAST 表（跳过临时表）跑一遍
 * relation_needs_vacanalyze，把评分与"是否需要清理"结论按
 * (oid, score.max/xid/mxid/vac/vac_ins/anl, dovacuum, doanalyze,
 * wraparound) 输出成结果集。elevel 传 LOG_NEVER：内部诊断日志不输出。
 */
Datum
pg_stat_get_autovacuum_scores(PG_FUNCTION_ARGS)
{
	int			effective_multixact_freeze_max_age;
	Relation	rel;
	TableScanDesc scan;
	HeapTuple	tup;
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;

	InitMaterializedSRF(fcinfo, 0);

	/* some prerequisite initialization */
	/* 【中文】与 worker 相同的基准：MultiXact 紧急年龄 + 最新
	 * XID/MultiXact（relation_needs_vacanalyze 计算回卷界限要用） */
	effective_multixact_freeze_max_age = MultiXactMemberFreezeThreshold();
	recentXid = ReadNextTransactionId();
	recentMulti = ReadNextMultiXactId();

	/* scan pg_class */
	rel = table_open(RelationRelationId, AccessShareLock);
	scan = table_beginscan_catalog(rel, 0, NULL);
	while ((tup = heap_getnext(scan, ForwardScanDirection)) != NULL)
	{
		Form_pg_class form = (Form_pg_class) GETSTRUCT(tup);
		AutoVacOpts *avopts;
		bool		dovacuum;
		bool		doanalyze;
		bool		wraparound;
		AutoVacuumScores scores;
		Datum		vals[10];
		bool		nulls[10] = {false};

		/* skip ineligible entries */
		/* 【中文】只关心普通表/物化视图/TOAST 表，跳过临时表 */
		if (form->relkind != RELKIND_RELATION &&
			form->relkind != RELKIND_MATVIEW &&
			form->relkind != RELKIND_TOASTVALUE)
			continue;
		if (form->relpersistence == RELPERSISTENCE_TEMP)
			continue;

		avopts = extract_autovac_opts(tup, RelationGetDescr(rel));
		relation_needs_vacanalyze(form->oid, avopts, form,
								  effective_multixact_freeze_max_age,
								  LOG_NEVER,
								  &dovacuum, &doanalyze, &wraparound,
								  &scores);
		if (avopts)
			pfree(avopts);

		/* 【中文】组装一行结果：oid + 5 个分量评分 + 3 个布尔结论 */
		vals[0] = ObjectIdGetDatum(form->oid);
		vals[1] = Float8GetDatum(scores.max);
		vals[2] = Float8GetDatum(scores.xid);
		vals[3] = Float8GetDatum(scores.mxid);
		vals[4] = Float8GetDatum(scores.vac);
		vals[5] = Float8GetDatum(scores.vac_ins);
		vals[6] = Float8GetDatum(scores.anl);
		vals[7] = BoolGetDatum(dovacuum);
		vals[8] = BoolGetDatum(doanalyze);
		vals[9] = BoolGetDatum(wraparound);

		tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc, vals, nulls);
	}
	table_endscan(scan);
	table_close(rel, AccessShareLock);

	return (Datum) 0;
}
