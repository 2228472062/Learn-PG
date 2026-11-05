/*-------------------------------------------------------------------------
 *
 * parallel.c
 *	  Infrastructure for launching parallel workers
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/access/transam/parallel.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 并行查询（parallel query）的公共基础设施，负责在 leader
 * 后端与若干 parallel worker 之间建立、运行和销毁一次并行操作。虽然文件位于
 * access/transam 目录（因为需要序列化和恢复事务状态），它本身不实现执行器逻辑，
 * 而是提供被 executor、索引构建、VACUUM 等共同复用的框架。
 *
 * 主要职责：
 *   1. ParallelContext 生命周期：CreateParallelContext() 建立后端本地上下文，
 *      InitializeParallelDSM() 估算并创建 DSM 段、在 shm_toc 中登记各类状态，
 *      LaunchParallelWorkers() 注册并启动 background worker，最后
 *      DestroyParallelContext() 强制终止并回收资源；
 *   2. 状态同步：把 leader 的 GUC、已加载库、事务状态（XID、command ID、隔离级别）、
 *      snapshot、combo CID、reindex/relmapper 状态、未提交 enum、会话级 DSM 等
 *      序列化进 DSM，worker 在 ParallelWorkerMain() 中按严格顺序恢复；worker 不
 *      自行标记 XID 提交，最终由 leader 统一提交；
 *   3. 错误传播（error propagation）：每个 worker 有一条 shm_mq 错误队列，worker 的
 *      ErrorResponse/NoticeResponse/NotificationResponse/Progress/Terminate
 *      协议消息经队列送到 leader；leader 在 CHECK_FOR_INTERRUPTS() 中调用
 *      ProcessParallelMessages() 解析，并用 ThrowErrorData() 重新抛出错误；
 *   4. 生命周期同步：WaitForParallelWorkersToAttach() 等待 worker 完成初始化，
 *      WaitForParallelWorkersToFinish() 等待其结束并收集 WAL 末尾位置，
 *      AtEOXact_Parallel()/AtEOSubXact_Parallel() 在事务/子事务边界兜底清理。
 *
 * 核心数据结构：
 *   - ParallelContext（见 include/access/parallel.h）：leader 侧的句柄，保存 DSM
 *     段、TOC、worker 数组、已启动 worker 数、入口函数名等；
 *   - FixedParallelState：放在 DSM 固定位置的共享状态，包含数据库/用户/角色 OID、
 *     leader 的 PGPROC/PID/ProcNumber、事务与语句时间戳、可序列化事务句柄，以及
 *     由 spinlock 保护的 last_xlog_end；
 *   - ParallelWorkerInfo：每个 worker 的 BackgroundWorkerHandle 与 error_mqh；
 *   - PARALLEL_KEY_*：本模块在 shm_toc 中占用的 TOC key，对应各个序列化 chunk。
 *
 * 与其他模块的关系：
 *   - postmaster/bgworker.c 负责真正 fork worker；worker 入口固定为
 *     ParallelWorkerMain，通过 bgw_extra 传入 worker 编号；
 *   - storage/ipc/dsm.c、shm_toc.c 提供 DSM 与表结构；storage/ipc/shm_mq.c 提供
 *     单读单写消息队列；libpq/pqmq.c 把 libpq 协议输出重定向到该队列；
 *   - access/transam/xact.c 提供 EnterParallelMode/ExitParallelMode、
 *     StartParallelWorkerTransaction/EndParallelWorkerTransaction 及
 *     XactLastRecEnd；worker 不自行提交 XID，由 leader 统一提交；
 *   - executor/execParallel.c 负责计划、元组队列等执行器私有状态，本文件只提供
 *     通用框架；nbtree/BRIN/GIN 的并行构建与 vacuumparallel.c 也复用本框架。
 *
 * 设计思想：
 *   - 所有跨进程状态都必须显式序列化，不能传递指针（EXEC_BACKEND 下地址可能不同），
 *     因此入口点以“库名 + 函数名”字符串传递，内建函数再查表还原为地址；
 *   - leader 必须在进入 parallel mode 后创建 context，并保证在退出当前子事务前
 *     销毁；否则 AtEOSubXact_Parallel 会发出 WARNING 并强制清理；
 *   - worker 的失败尽量转化为 leader 中的普通 ERROR，而不是让 leader 直接崩溃：
 *     错误级别被压到不超过 ERROR，且可以通过错误上下文看出错误来自 parallel worker；
 *   - worker 启动阶段在错误队列建立之前发生的错误无法回传，因此初始化顺序必须
 *     谨慎；错误队列建立后，所有 elog/ereport 输出都会被 pqmq 重定向；
 *   - DSM 创建失败（达到 max_dsm_segments）时降级为后端私有内存并放弃启动 worker，
 *     让查询以非并行方式继续，而不是直接报错。
 */

#include "postgres.h"

#include "access/brin.h"
#include "access/gin.h"
#include "access/nbtree.h"
#include "access/parallel.h"
#include "access/session.h"
#include "access/xact.h"
#include "access/xlog.h"
#include "catalog/index.h"
#include "catalog/namespace.h"
#include "catalog/pg_enum.h"
#include "catalog/storage.h"
#include "commands/async.h"
#include "commands/vacuum.h"
#include "executor/execParallel.h"
#include "libpq/libpq.h"
#include "libpq/pqformat.h"
#include "libpq/pqmq.h"
#include "miscadmin.h"
#include "optimizer/optimizer.h"
#include "pgstat.h"
#include "storage/ipc.h"
#include "storage/predicate.h"
#include "storage/proc.h"
#include "storage/spin.h"
#include "tcop/tcopprot.h"
#include "utils/combocid.h"
#include "utils/guc.h"
#include "utils/inval.h"
#include "utils/memutils.h"
#include "utils/relmapper.h"
#include "utils/snapmgr.h"
#include "utils/wait_event.h"

/*
 * We don't want to waste a lot of memory on an error queue which, most of
 * the time, will process only a handful of small messages.  However, it is
 * desirable to make it large enough that a typical ErrorResponse can be sent
 * without blocking.  That way, a worker that errors out can write the whole
 * message into the queue and terminate without waiting for the user backend.
 */
/*
 * 中文注释：
 * 每个 parallel worker 专用错误队列（shm_mq）的字节数。队列只承载
 * ErrorResponse/NoticeResponse/NotificationResponse/Progress/Terminate 等小型协议
 * 消息，不承载元组数据（元组走执行器另行建立的元组队列）。取 16KB 是在“不浪费
 * 共享内存”与“典型 ErrorResponse 能一次性写入、worker 不必等待 leader 消费即可
 * 退出”之间折中；InitializeParallelDSM() 中的 StaticAssertDecl 保证该大小满足
 * BUFFERALIGN 对齐要求，因为 shm_mq_create() 要求队列起始地址按缓冲区边界对齐。
 */
#define PARALLEL_ERROR_QUEUE_SIZE			16384

/* Magic number for parallel context TOC. */
/*
 * 中文注释：
 * ParallelContext 的 shm_toc magic number。worker 在 ParallelWorkerMain() 中调用
 * shm_toc_attach() 时用它校验 DSM 头部；magic 不匹配说明 attach 到了错误的 DSM
 * 段或段内容已损坏，直接报 ERROR，避免按错误的 TOC 布局解释共享内存。
 */
#define PARALLEL_MAGIC						0x50477c7c

/*
 * Magic numbers for per-context parallel state sharing.  Higher-level code
 * should use smaller values, leaving these very large ones for use by this
 * module.
 */
/*
 * 中文注释：
 * 本模块在 ParallelContext 的 shm_toc 中使用的 TOC key。key 的高位几乎全为 1，
 * 把低位数值空间留给上层模块（executor、索引构建、VACUUM 等）使用，避免 key
 * 冲突；扩展代码应使用更小的值。各 key 对应的 chunk 内容如下：
 *   PARALLEL_KEY_FIXED                FixedParallelState
 *   PARALLEL_KEY_ERROR_QUEUE          nworkers 个 PARALLEL_ERROR_QUEUE_SIZE 的 shm_mq
 *   PARALLEL_KEY_LIBRARY              SerializeLibraryState() 的输出
 *   PARALLEL_KEY_GUC                  SerializeGUCState() 的输出
 *   PARALLEL_KEY_COMBO_CID            SerializeComboCIDState() 的输出
 *   PARALLEL_KEY_TRANSACTION_SNAPSHOT 事务级 snapshot（仅 REPEATABLE READ/SERIALIZABLE）
 *   PARALLEL_KEY_ACTIVE_SNAPSHOT      当前 active snapshot
 *   PARALLEL_KEY_TRANSACTION_STATE    SerializeTransactionState() 的输出
 *   PARALLEL_KEY_ENTRYPOINT           "库名\0函数名" 字符串
 *   PARALLEL_KEY_SESSION_DSM          dsm_handle（会话级 DSM，用于共享 record typmod）
 *   PARALLEL_KEY_PENDING_SYNCS        SerializePendingSyncs() 的输出
 *   PARALLEL_KEY_REINDEX_STATE        SerializeReindexState() 的输出
 *   PARALLEL_KEY_RELMAPPER_STATE      SerializeRelationMap() 的输出
 *   PARALLEL_KEY_UNCOMMITTEDENUMS     SerializeUncommittedEnums() 的输出
 *   PARALLEL_KEY_CLIENTCONNINFO       SerializeClientConnectionInfo() 的输出
 * key 的数值顺序本身没有语义，worker 一律通过 shm_toc_lookup() 按 key 查找。
 */
#define PARALLEL_KEY_FIXED					UINT64CONST(0xFFFFFFFFFFFF0001)
#define PARALLEL_KEY_ERROR_QUEUE			UINT64CONST(0xFFFFFFFFFFFF0002)
#define PARALLEL_KEY_LIBRARY				UINT64CONST(0xFFFFFFFFFFFF0003)
#define PARALLEL_KEY_GUC					UINT64CONST(0xFFFFFFFFFFFF0004)
#define PARALLEL_KEY_COMBO_CID				UINT64CONST(0xFFFFFFFFFFFF0005)
#define PARALLEL_KEY_TRANSACTION_SNAPSHOT	UINT64CONST(0xFFFFFFFFFFFF0006)
#define PARALLEL_KEY_ACTIVE_SNAPSHOT		UINT64CONST(0xFFFFFFFFFFFF0007)
#define PARALLEL_KEY_TRANSACTION_STATE		UINT64CONST(0xFFFFFFFFFFFF0008)
#define PARALLEL_KEY_ENTRYPOINT				UINT64CONST(0xFFFFFFFFFFFF0009)
#define PARALLEL_KEY_SESSION_DSM			UINT64CONST(0xFFFFFFFFFFFF000A)
#define PARALLEL_KEY_PENDING_SYNCS			UINT64CONST(0xFFFFFFFFFFFF000B)
#define PARALLEL_KEY_REINDEX_STATE			UINT64CONST(0xFFFFFFFFFFFF000C)
#define PARALLEL_KEY_RELMAPPER_STATE		UINT64CONST(0xFFFFFFFFFFFF000D)
#define PARALLEL_KEY_UNCOMMITTEDENUMS		UINT64CONST(0xFFFFFFFFFFFF000E)
#define PARALLEL_KEY_CLIENTCONNINFO			UINT64CONST(0xFFFFFFFFFFFF000F)

/* Fixed-size parallel state. */
/*
 * 中文注释：
 * 放在 DSM 固定 chunk 中的“每上下文一份”共享状态，leader 在
 * InitializeParallelDSM() 中填写，所有 worker 只读（last_xlog_end 除外）。
 * 这些字段集中存放，是为了让 worker attach DSM 后能用一次
 * shm_toc_lookup(PARALLEL_KEY_FIXED) 取到启动所需的全部身份和会话信息。
 *
 * 字段说明：
 *   database_id/authenticated_user_id/session_user_id/outer_user_id/
 *   current_user_id：恢复数据库连接与权限身份；worker 不再做认证，直接沿用
 *     leader 的值；
 *   temp_namespace_id/temp_toast_namespace_id：临时命名空间，保证 worker 的
 *     search_path 与 leader 一致；
 *   sec_context：GetUserIdAndSecContext() 保存的安全上下文标志；
 *   session_user_is_superuser/role_is_superuser：恢复角色时使用的超级用户标志；
 *   parallel_leader_pgproc/parallel_leader_pid/parallel_leader_proc_number：
 *     leader 的 PGPROC 与进程标识，worker 用它加入锁组（lock group）并向 leader
 *     发送信号；
 *   xact_ts/stmt_ts：事务与语句开始时间戳，worker 必须继承而不是重新取当前时间；
 *   serializable_xact_handle：SERIALIZABLE 事务的共享句柄，用于
 *     AttachSerializableXact()；
 *   mutex：保护 last_xlog_end 的自旋锁；本结构其余字段初始化完成后只读；
 *   last_xlog_end：所有 worker 已写入 WAL 的最大结束位置，由
 *     ParallelWorkerReportLastRecEnd() 在自旋锁内取最大值，leader 在
 *     WaitForParallelWorkersToFinish() 中读取并合并到 XactLastRecEnd。
 *
 * 注意：本结构位于 DSM 中，不能包含指向后端私有内存的指针；PGPROC 指针指向共享
 * 内存，因而可以跨进程使用。
 */
typedef struct FixedParallelState
{
	/* Fixed-size state that workers must restore. */
	Oid			database_id;
	Oid			authenticated_user_id;
	Oid			session_user_id;
	Oid			outer_user_id;
	Oid			current_user_id;
	Oid			temp_namespace_id;
	Oid			temp_toast_namespace_id;
	int			sec_context;
	bool		session_user_is_superuser;
	bool		role_is_superuser;
	PGPROC	   *parallel_leader_pgproc;
	pid_t		parallel_leader_pid;
	ProcNumber	parallel_leader_proc_number;
	TimestampTz xact_ts;
	TimestampTz stmt_ts;
	SerializableXactHandle serializable_xact_handle;

	/* Mutex protects remaining fields. */
	slock_t		mutex;

	/* Maximum XactLastRecEnd of any worker. */
	XLogRecPtr	last_xlog_end;
} FixedParallelState;

/*
 * Our parallel worker number.  We initialize this to -1, meaning that we are
 * not a parallel worker.  In parallel workers, it will be set to a value >= 0
 * and < the number of workers before any user code is invoked; each parallel
 * worker will get a different parallel worker number.
 */
/*
 * 中文注释：
 * 当前进程的 parallel worker 编号：非 worker 后端为 -1；worker 在
 * ParallelWorkerMain() 中从 MyBgworkerEntry->bgw_extra 取出 0..nworkers-1 的值。
 * 执行器用它索引共享的 instrumentation、buffer usage 等数组，因此必须在调用任何
 * 用户代码之前设置好，且同一并行操作内每个 worker 的编号互不相同。
 * include/access/parallel.h 中的 IsParallelWorker() 即以此判断（>= 0）。
 */
int			ParallelWorkerNumber = -1;

/* Is there a parallel message pending which we need to receive? */
/*
 * 中文注释：
 * “有 parallel worker 消息待接收”的标志。worker 通过
 * SendProcSignal(PROCSIG_PARALLEL_MESSAGE) 通知 leader，信号处理器
 * HandleParallelMessageInterrupt() 只能设置该 volatile sig_atomic_t 标志；
 * 真正的读取与解析推迟到下一次 CHECK_FOR_INTERRUPTS() -> ProcessInterrupts() ->
 * ProcessParallelMessages() 中完成。这样保证信号处理函数是 async-signal-safe 的。
 */
volatile sig_atomic_t ParallelMessagePending = false;

/* Are we initializing a parallel worker? */
/*
 * 中文注释：
 * 当前进程是否正处于 parallel worker 的初始化阶段（从 ParallelWorkerMain 开始到
 * 所有状态恢复完毕）。GUC/角色相关代码借此放宽或跳过某些检查：例如恢复
 * session_authorization/role 时不做权限校验，因为 worker 必须盲目继承 leader 的
 * 状态。调用入口函数之前会把它清为 false。
 */
bool		InitializingParallelWorker = false;

/* Pointer to our fixed parallel state. */
/*
 * 中文注释：
 * worker 本地指向 DSM 中 FixedParallelState 的指针；leader 中为 NULL。
 * ParallelWorkerReportLastRecEnd() 依赖它写入 last_xlog_end。
 */
static FixedParallelState *MyFixedParallelState;

/* List of active parallel contexts. */
/*
 * 中文注释：
 * 当前后端所有活跃 ParallelContext 的双向链表，按创建顺序头插（LIFO）。
 * AtEOXact_Parallel()/AtEOSubXact_Parallel() 依赖 LIFO 顺序从表头开始清理当前
 * （子）事务创建的 context；ProcessParallelMessages() 遍历它处理所有 worker 消息。
 * 链表节点嵌入 ParallelContext，context 在 DestroyParallelContext() 中先摘除节点，
 * 避免清理过程中再次被引用。该链表只属于 leader，worker 不使用。
 */
static dlist_head pcxt_list = DLIST_STATIC_INIT(pcxt_list);

/* Backend-local copy of data from FixedParallelState. */
/*
 * 中文注释：
 * worker 在 ParallelWorkerMain() 中保存的 leader PID 本地副本，仅供
 * ParallelWorkerShutdown() 在 before_shmem_exit 阶段发送
 * PROCSIG_PARALLEL_MESSAGE 使用。此时 DSM 可能即将被拆除，不能再去读取共享状态，
 * 因此必须提前缓存。leader 的 ProcNumber 保存在全局 ParallelLeaderProcNumber
 * （storage/procnumber.h）中，SendProcSignal() 需要两者共同定位目标进程。
 */
static pid_t ParallelLeaderPid;

/*
 * List of internal parallel worker entry points.  We need this for
 * reasons explained in LookupParallelWorkerFunction(), below.
 */
/*
 * 中文注释：
 * 内建 parallel worker 入口函数名到函数地址的映射表。库名为 "postgres" 时，
 * LookupParallelWorkerFunction() 在此表中查找，找不到即视为编程错误。
 * 之所以不直接传递函数指针：EXEC_BACKEND 构建（如 Windows）中不同进程的函数
 * 地址可能不同，跨进程传地址不安全；传递名字后由每个 worker 自行解析。
 * 新增核心入口点时必须同步登记到此表，否则 worker 启动会失败。表用 lengthof
 * 遍历，不需要哨兵项。
 */
static const struct
{
	const char *fn_name;
	parallel_worker_main_type fn_addr;
}			InternalParallelWorkers[] =

{
	{
		"ParallelQueryMain", ParallelQueryMain
	},
	{
		"_bt_parallel_build_main", _bt_parallel_build_main
	},
	{
		"_brin_parallel_build_main", _brin_parallel_build_main
	},
	{
		"_gin_parallel_build_main", _gin_parallel_build_main
	},
	{
		"parallel_vacuum_main", parallel_vacuum_main
	}
};

/* Private functions. */
/*
 * 中文注释：
 * 本文件内部辅助函数的前置声明，具体语义见各自定义处：
 *   ProcessParallelMessage     解析单条 worker 协议消息；
 *   WaitForParallelWorkersToExit 等待 worker 真正退出（销毁路径使用）；
 *   LookupParallelWorkerFunction 把入口点名字解析为当前进程内的函数地址；
 *   ParallelWorkerShutdown     worker 的 before_shmem_exit 回调。
 */
static void ProcessParallelMessage(ParallelContext *pcxt, int i, StringInfo msg);
static void WaitForParallelWorkersToExit(ParallelContext *pcxt);
static parallel_worker_main_type LookupParallelWorkerFunction(const char *libraryname, const char *funcname);
static void ParallelWorkerShutdown(int code, Datum arg);


/*
 * Establish a new parallel context.  This should be done after entering
 * parallel mode, and (unless there is an error) the context should be
 * destroyed before exiting the current subtransaction.
 */
/*
 * 中文注释：
 * 创建一个 ParallelContext（仅后端本地簿记，不分配 DSM、不启动 worker）。
 *
 * 调用场景：调用方先 EnterParallelMode()，再调用本函数；executor 的
 * ExecInitParallelPlan()、nbtree/BRIN/GIN 并行构建、parallel VACUUM 等均如此。
 * library_name/function_name 指定 worker 入口（核心函数传 "postgres" 加函数名），
 * nworkers 是期望的最大 worker 数（>= 0）。
 *
 * 关键行为：
 *   - 断言当前处于 parallel mode，否则并行模式的状态约束会被破坏；
 *   - 上下文及字符串分配在 TopTransactionContext，保证在整个事务（而非短命的
 *     语句/表达式上下文）中存活；pcxt->subid 记录当前子事务 ID，供
 *     AtEOSubXact_Parallel() 精确清理本子事务创建的 context；
 *   - 保存创建时的 error_context_stack，worker 错误回传时用它补充上下文，
 *     而不是使用收到消息时的调用栈；
 *   - 初始化 shm_toc 估算器，并把 context 头插到 pcxt_list；
 *   - nworkers_to_launch 先设为 nworkers，后续 InitializeParallelDSM() 可能因
 *     资源限制把它降为 0，ReinitializeParallelWorkers() 也可再调整。
 *
 * 返回值：新分配的 ParallelContext 指针。调用方必须在退出当前子事务前
 * DestroyParallelContext()；若提交时仍有泄漏，会收到 WARNING 并被强制清理。
 * 副作用：修改 pcxt_list；不涉及共享内存和并发。
 */
ParallelContext *
CreateParallelContext(const char *library_name, const char *function_name,
					  int nworkers)
{
	MemoryContext oldcontext;
	ParallelContext *pcxt;

	/* It is unsafe to create a parallel context if not in parallel mode. */
	Assert(IsInParallelMode());

	/* Number of workers should be non-negative. */
	Assert(nworkers >= 0);

	/* We might be running in a short-lived memory context. */
	oldcontext = MemoryContextSwitchTo(TopTransactionContext);

	/* Initialize a new ParallelContext. */
	pcxt = palloc0_object(ParallelContext);
	pcxt->subid = GetCurrentSubTransactionId();
	pcxt->nworkers = nworkers;
	pcxt->nworkers_to_launch = nworkers;
	pcxt->library_name = pstrdup(library_name);
	pcxt->function_name = pstrdup(function_name);
	pcxt->error_context_stack = error_context_stack;
	shm_toc_initialize_estimator(&pcxt->estimator);
	dlist_push_head(&pcxt_list, &pcxt->node);

	/* Restore previous memory context. */
	MemoryContextSwitchTo(oldcontext);

	return pcxt;
}

/*
 * Establish the dynamic shared memory segment for a parallel context and
 * copy state and other bookkeeping information that will be needed by
 * parallel workers into it.
 */
/*
 * 中文注释：
 * 为 ParallelContext 创建 DSM 段，并把 worker 启动所需的状态序列化进 shm_toc。
 * 这是 leader 侧最关键的初始化步骤：调用前，上层模块已经通过 pcxt->estimator
 * 估算并登记了自己的 chunk/key；本函数在此基础上再追加公共状态。
 *
 * 调用场景：CreateParallelContext() 之后、LaunchParallelWorkers() 之前，由
 * execParallel.c、nbtsort.c、gininsert.c、brin.c、vacuumparallel.c 等调用。
 *
 * 主要流程：
 *   1. 固定状态：先为 FixedParallelState 估算一个 chunk 和一个 key；
 *   2. 并行能力检查：若当前处于不可处理中断的状态
 *      （!INTERRUPTS_CAN_BE_PROCESSED()），则把 nworkers 降为 0——否则 worker
 *      发来的信号无法及时处理，错误传播和等待都可能失效；
 *   3. 会话级 DSM：调用 GetSessionDsmHandle() 取得（或创建）跨并行操作复用的
 *      per-session DSM，其中保存共享 record typmod registry；若创建失败
 *      （DSM_HANDLE_INVALID），同样放弃 worker，因为 worker 间无法交换 row type，
 *      元组传输会不兼容；
 *   4. 估算并登记 library、GUC、combo CID、事务/活跃 snapshot、事务状态、
 *      pending syncs、reindex、relmapper、未提交 enum、ClientConnectionInfo、
 *      错误队列、入口点信息等 chunk；
 *   5. 调用 shm_toc_estimate() 得到总大小后 dsm_create()。若达到动态共享内存段
 *      上限，DSM_CREATE_NULL_IF_MAXSEGMENTS 会返回 NULL，此时降级为
 *      TopMemoryContext 中的后端私有内存，并把 nworkers 设为 0，让查询以非并行
 *      方式继续；这种降级只影响性能，不影响正确性；
 *   6. 填写 FixedParallelState：数据库/认证/会话/当前用户、安全上下文、临时
 *      namespace、leader 的 PGPROC/PID/ProcNumber、事务与语句时间戳、
 *      ShareSerializableXact() 的句柄，初始化自旋锁并把 last_xlog_end 置为
 *      InvalidXLogRecPtr；
 *   7. 仅当 nworkers > 0 时，逐项 Serialize*() 并 shm_toc_insert()；错误队列为
 *      每个 worker 建一个 shm_mq，receiver 设为 leader 的 MyProc，attach 时
 *      resource owner 传 NULL；入口点保存“库名\0函数名”而不是函数指针。
 *
 * 参数：pcxt 为已创建的上下文；函数直接修改其 seg/toc/worker/nworkers 等字段。
 * 返回值：无。
 * 副作用/错误处理：会创建 DSM 段和后端内存；若中途 ERROR，事务/子事务回滚路径
 * 中的 AtEOXact_Parallel()/AtEOSubXact_Parallel() 会通过 pcxt_list 找到并销毁
 * 尚未完成的 context，DSM 也会由 ResourceOwner 清理机制释放。函数结束时把
 * nworkers_to_launch 同步为最终可启动的 worker 数。
 * 并发：只在 leader 中执行，无并发调用问题；但 DSM 内容会被随后启动的 worker
 * 并发读取，因此所有写入必须在 LaunchParallelWorkers() 之前完成。
 */
void
InitializeParallelDSM(ParallelContext *pcxt)
{
	MemoryContext oldcontext;
	Size		library_len = 0;
	Size		guc_len = 0;
	Size		combocidlen = 0;
	Size		tsnaplen = 0;
	Size		asnaplen = 0;
	Size		tstatelen = 0;
	Size		pendingsyncslen = 0;
	Size		reindexlen = 0;
	Size		relmapperlen = 0;
	Size		uncommittedenumslen = 0;
	Size		clientconninfolen = 0;
	Size		segsize = 0;
	int			i;
	FixedParallelState *fps;
	dsm_handle	session_dsm_handle = DSM_HANDLE_INVALID;
	Snapshot	transaction_snapshot = GetTransactionSnapshot();
	Snapshot	active_snapshot = GetActiveSnapshot();

	/* We might be running in a very short-lived memory context. */
	oldcontext = MemoryContextSwitchTo(TopTransactionContext);

	/* Allow space to store the fixed-size parallel state. */
	shm_toc_estimate_chunk(&pcxt->estimator, sizeof(FixedParallelState));
	shm_toc_estimate_keys(&pcxt->estimator, 1);

	/*
	 * If we manage to reach here while non-interruptible, it's unsafe to
	 * launch any workers: we would fail to process interrupts sent by them.
	 * We can deal with that edge case by pretending no workers were
	 * requested.
	 */
	if (!INTERRUPTS_CAN_BE_PROCESSED())
		pcxt->nworkers = 0;

	/*
	 * Normally, the user will have requested at least one worker process, but
	 * if by chance they have not, we can skip a bunch of things here.
	 */
	if (pcxt->nworkers > 0)
	{
		/* Get (or create) the per-session DSM segment's handle. */
		session_dsm_handle = GetSessionDsmHandle();

		/*
		 * If we weren't able to create a per-session DSM segment, then we can
		 * continue but we can't safely launch any workers because their
		 * record typmods would be incompatible so they couldn't exchange
		 * tuples.
		 */
		if (session_dsm_handle == DSM_HANDLE_INVALID)
			pcxt->nworkers = 0;
	}

	if (pcxt->nworkers > 0)
	{
		StaticAssertDecl(BUFFERALIGN(PARALLEL_ERROR_QUEUE_SIZE) ==
						 PARALLEL_ERROR_QUEUE_SIZE,
						 "parallel error queue size not buffer-aligned");

		/* Estimate space for various kinds of state sharing. */
		library_len = EstimateLibraryStateSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, library_len);
		guc_len = EstimateGUCStateSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, guc_len);
		combocidlen = EstimateComboCIDStateSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, combocidlen);
		if (IsolationUsesXactSnapshot())
		{
			tsnaplen = EstimateSnapshotSpace(transaction_snapshot);
			shm_toc_estimate_chunk(&pcxt->estimator, tsnaplen);
		}
		asnaplen = EstimateSnapshotSpace(active_snapshot);
		shm_toc_estimate_chunk(&pcxt->estimator, asnaplen);
		tstatelen = EstimateTransactionStateSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, tstatelen);
		shm_toc_estimate_chunk(&pcxt->estimator, sizeof(dsm_handle));
		pendingsyncslen = EstimatePendingSyncsSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, pendingsyncslen);
		reindexlen = EstimateReindexStateSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, reindexlen);
		relmapperlen = EstimateRelationMapSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, relmapperlen);
		uncommittedenumslen = EstimateUncommittedEnumsSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, uncommittedenumslen);
		clientconninfolen = EstimateClientConnectionInfoSpace();
		shm_toc_estimate_chunk(&pcxt->estimator, clientconninfolen);
		/* If you add more chunks here, you probably need to add keys. */
		shm_toc_estimate_keys(&pcxt->estimator, 12);

		/* Estimate space need for error queues. */
		shm_toc_estimate_chunk(&pcxt->estimator,
							   mul_size(PARALLEL_ERROR_QUEUE_SIZE,
										pcxt->nworkers));
		shm_toc_estimate_keys(&pcxt->estimator, 1);

		/* Estimate how much we'll need for the entrypoint info. */
		shm_toc_estimate_chunk(&pcxt->estimator, strlen(pcxt->library_name) +
							   strlen(pcxt->function_name) + 2);
		shm_toc_estimate_keys(&pcxt->estimator, 1);
	}

	/*
	 * Create DSM and initialize with new table of contents.  But if the user
	 * didn't request any workers, then don't bother creating a dynamic shared
	 * memory segment; instead, just use backend-private memory.
	 *
	 * Also, if we can't create a dynamic shared memory segment because the
	 * maximum number of segments have already been created, then fall back to
	 * backend-private memory, and plan not to use any workers.  We hope this
	 * won't happen very often, but it's better to abandon the use of
	 * parallelism than to fail outright.
	 */
	segsize = shm_toc_estimate(&pcxt->estimator);
	if (pcxt->nworkers > 0)
		pcxt->seg = dsm_create(segsize, DSM_CREATE_NULL_IF_MAXSEGMENTS);
	if (pcxt->seg != NULL)
		pcxt->toc = shm_toc_create(PARALLEL_MAGIC,
								   dsm_segment_address(pcxt->seg),
								   segsize);
	else
	{
		pcxt->nworkers = 0;
		pcxt->private_memory = MemoryContextAlloc(TopMemoryContext, segsize);
		pcxt->toc = shm_toc_create(PARALLEL_MAGIC, pcxt->private_memory,
								   segsize);
	}

	/* Initialize fixed-size state in shared memory. */
	fps = (FixedParallelState *)
		shm_toc_allocate(pcxt->toc, sizeof(FixedParallelState));
	fps->database_id = MyDatabaseId;
	fps->authenticated_user_id = GetAuthenticatedUserId();
	fps->session_user_id = GetSessionUserId();
	fps->outer_user_id = GetCurrentRoleId();
	GetUserIdAndSecContext(&fps->current_user_id, &fps->sec_context);
	fps->session_user_is_superuser = GetSessionUserIsSuperuser();
	fps->role_is_superuser = current_role_is_superuser;
	GetTempNamespaceState(&fps->temp_namespace_id,
						  &fps->temp_toast_namespace_id);
	fps->parallel_leader_pgproc = MyProc;
	fps->parallel_leader_pid = MyProcPid;
	fps->parallel_leader_proc_number = MyProcNumber;
	fps->xact_ts = GetCurrentTransactionStartTimestamp();
	fps->stmt_ts = GetCurrentStatementStartTimestamp();
	fps->serializable_xact_handle = ShareSerializableXact();
	SpinLockInit(&fps->mutex);
	fps->last_xlog_end = InvalidXLogRecPtr;
	shm_toc_insert(pcxt->toc, PARALLEL_KEY_FIXED, fps);

	/* We can skip the rest of this if we're not budgeting for any workers. */
	if (pcxt->nworkers > 0)
	{
		char	   *libraryspace;
		char	   *gucspace;
		char	   *combocidspace;
		char	   *tsnapspace;
		char	   *asnapspace;
		char	   *tstatespace;
		char	   *pendingsyncsspace;
		char	   *reindexspace;
		char	   *relmapperspace;
		char	   *error_queue_space;
		char	   *session_dsm_handle_space;
		char	   *entrypointstate;
		char	   *uncommittedenumsspace;
		char	   *clientconninfospace;
		Size		lnamelen;

		/* Serialize shared libraries we have loaded. */
		libraryspace = shm_toc_allocate(pcxt->toc, library_len);
		SerializeLibraryState(library_len, libraryspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_LIBRARY, libraryspace);

		/* Serialize GUC settings. */
		gucspace = shm_toc_allocate(pcxt->toc, guc_len);
		SerializeGUCState(guc_len, gucspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_GUC, gucspace);

		/* Serialize combo CID state. */
		combocidspace = shm_toc_allocate(pcxt->toc, combocidlen);
		SerializeComboCIDState(combocidlen, combocidspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_COMBO_CID, combocidspace);

		/*
		 * Serialize the transaction snapshot if the transaction isolation
		 * level uses a transaction snapshot.
		 */
		if (IsolationUsesXactSnapshot())
		{
			tsnapspace = shm_toc_allocate(pcxt->toc, tsnaplen);
			SerializeSnapshot(transaction_snapshot, tsnapspace);
			shm_toc_insert(pcxt->toc, PARALLEL_KEY_TRANSACTION_SNAPSHOT,
						   tsnapspace);
		}

		/* Serialize the active snapshot. */
		asnapspace = shm_toc_allocate(pcxt->toc, asnaplen);
		SerializeSnapshot(active_snapshot, asnapspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_ACTIVE_SNAPSHOT, asnapspace);

		/* Provide the handle for per-session segment. */
		session_dsm_handle_space = shm_toc_allocate(pcxt->toc,
													sizeof(dsm_handle));
		*(dsm_handle *) session_dsm_handle_space = session_dsm_handle;
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_SESSION_DSM,
					   session_dsm_handle_space);

		/* Serialize transaction state. */
		tstatespace = shm_toc_allocate(pcxt->toc, tstatelen);
		SerializeTransactionState(tstatelen, tstatespace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_TRANSACTION_STATE, tstatespace);

		/* Serialize pending syncs. */
		pendingsyncsspace = shm_toc_allocate(pcxt->toc, pendingsyncslen);
		SerializePendingSyncs(pendingsyncslen, pendingsyncsspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_PENDING_SYNCS,
					   pendingsyncsspace);

		/* Serialize reindex state. */
		reindexspace = shm_toc_allocate(pcxt->toc, reindexlen);
		SerializeReindexState(reindexlen, reindexspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_REINDEX_STATE, reindexspace);

		/* Serialize relmapper state. */
		relmapperspace = shm_toc_allocate(pcxt->toc, relmapperlen);
		SerializeRelationMap(relmapperlen, relmapperspace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_RELMAPPER_STATE,
					   relmapperspace);

		/* Serialize uncommitted enum state. */
		uncommittedenumsspace = shm_toc_allocate(pcxt->toc,
												 uncommittedenumslen);
		SerializeUncommittedEnums(uncommittedenumsspace, uncommittedenumslen);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_UNCOMMITTEDENUMS,
					   uncommittedenumsspace);

		/* Serialize our ClientConnectionInfo. */
		clientconninfospace = shm_toc_allocate(pcxt->toc, clientconninfolen);
		SerializeClientConnectionInfo(clientconninfolen, clientconninfospace);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_CLIENTCONNINFO,
					   clientconninfospace);

		/* Allocate space for worker information. */
		pcxt->worker = palloc0_array(ParallelWorkerInfo, pcxt->nworkers);

		/*
		 * Establish error queues in dynamic shared memory.
		 *
		 * These queues should be used only for transmitting ErrorResponse,
		 * NoticeResponse, and NotifyResponse protocol messages.  Tuple data
		 * should be transmitted via separate (possibly larger?) queues.
		 */
		error_queue_space =
			shm_toc_allocate(pcxt->toc,
							 mul_size(PARALLEL_ERROR_QUEUE_SIZE,
									  pcxt->nworkers));
		for (i = 0; i < pcxt->nworkers; ++i)
		{
			char	   *start;
			shm_mq	   *mq;

			start = error_queue_space + i * PARALLEL_ERROR_QUEUE_SIZE;
			mq = shm_mq_create(start, PARALLEL_ERROR_QUEUE_SIZE);
			shm_mq_set_receiver(mq, MyProc);
			pcxt->worker[i].error_mqh = shm_mq_attach(mq, pcxt->seg, NULL);
		}
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_ERROR_QUEUE, error_queue_space);

		/*
		 * Serialize entrypoint information.  It's unsafe to pass function
		 * pointers across processes, as the function pointer may be different
		 * in each process in EXEC_BACKEND builds, so we always pass library
		 * and function name.  (We use library name "postgres" for functions
		 * in the core backend.)
		 */
		lnamelen = strlen(pcxt->library_name);
		entrypointstate = shm_toc_allocate(pcxt->toc, lnamelen +
										   strlen(pcxt->function_name) + 2);
		strcpy(entrypointstate, pcxt->library_name);
		strcpy(entrypointstate + lnamelen + 1, pcxt->function_name);
		shm_toc_insert(pcxt->toc, PARALLEL_KEY_ENTRYPOINT, entrypointstate);
	}

	/* Update nworkers_to_launch, in case we changed nworkers above. */
	pcxt->nworkers_to_launch = pcxt->nworkers;

	/* Restore previous memory context. */
	MemoryContextSwitchTo(oldcontext);
}

/*
 * Reinitialize the dynamic shared memory segment for a parallel context such
 * that we could launch workers for it again.
 */
/*
 * 中文注释：
 * 复用已有 ParallelContext 的 DSM 段与 TOC，把共享状态恢复为可以再次启动 worker
 * 的初始状态。用于需要以相同并行计划反复执行的情形，例如并行查询的 rescan
 * （ExecParallelReinitialize）以及 parallel VACUUM 的多轮清理。
 *
 * 前提：调用方必须已经对上一轮 worker 调用过 WaitForParallelWorkersToFinish()；
 * 本函数自身也会先 WaitForParallelWorkersToFinish() 和
 * WaitForParallelWorkersToExit()，确保旧 worker 完全退出后再重用 TOC，避免新旧
 * worker 同时读写同一段共享内存。
 *
 * 具体工作：
 *   - 把 nworkers_launched 清零；
 *   - 释放并清空 known_attached_workers 数组（worker 集合会重新建立）；
 *   - 把 FixedParallelState.last_xlog_end 重置为 InvalidXLogRecPtr，防止上一轮
 *     的 WAL 位置影响本轮 XactLastRecEnd 的统计；
 *   - 如果 nworkers > 0，就地为每个 worker 重新 shm_mq_create() 错误队列，并重新
 *     set_receiver/attach；其他序列化状态（GUC、snapshot、transaction state 等）
 *     保持不变，因为同一并行操作中它们仍然有效。
 *
 * 参数：pcxt 为已初始化（InitializeParallelDSM 过）的上下文。
 * 返回值：无。副作用：修改共享内存和 pcxt 字段；不重新注册 worker。
 * 注意：本函数不会重新序列化事务状态/snapshot；如果调用方需要反映新状态，必须
 * 自行保证 TOC 中的内容仍然正确，或重新创建 context。
 */
void
ReinitializeParallelDSM(ParallelContext *pcxt)
{
	MemoryContext oldcontext;
	FixedParallelState *fps;

	/* We might be running in a very short-lived memory context. */
	oldcontext = MemoryContextSwitchTo(TopTransactionContext);

	/* Wait for any old workers to exit. */
	if (pcxt->nworkers_launched > 0)
	{
		WaitForParallelWorkersToFinish(pcxt);
		WaitForParallelWorkersToExit(pcxt);
		pcxt->nworkers_launched = 0;
		if (pcxt->known_attached_workers)
		{
			pfree(pcxt->known_attached_workers);
			pcxt->known_attached_workers = NULL;
			pcxt->nknown_attached_workers = 0;
		}
	}

	/* Reset a few bits of fixed parallel state to a clean state. */
	fps = shm_toc_lookup(pcxt->toc, PARALLEL_KEY_FIXED, false);
	fps->last_xlog_end = InvalidXLogRecPtr;

	/* Recreate error queues (if they exist). */
	if (pcxt->nworkers > 0)
	{
		char	   *error_queue_space;
		int			i;

		error_queue_space =
			shm_toc_lookup(pcxt->toc, PARALLEL_KEY_ERROR_QUEUE, false);
		for (i = 0; i < pcxt->nworkers; ++i)
		{
			char	   *start;
			shm_mq	   *mq;

			start = error_queue_space + i * PARALLEL_ERROR_QUEUE_SIZE;
			mq = shm_mq_create(start, PARALLEL_ERROR_QUEUE_SIZE);
			shm_mq_set_receiver(mq, MyProc);
			pcxt->worker[i].error_mqh = shm_mq_attach(mq, pcxt->seg, NULL);
		}
	}

	/* Restore previous memory context. */
	MemoryContextSwitchTo(oldcontext);
}

/*
 * Reinitialize parallel workers for a parallel context such that we could
 * launch a different number of workers.  This is required for cases where
 * we need to reuse the same DSM segment, but the number of workers can
 * vary from run-to-run.
 */
/*
 * 中文注释：
 * 调整下次 LaunchParallelWorkers() 实际启动的 worker 数，而不重建 DSM。
 * 典型场景：parallel VACUUM 或需要复用同一 DSM、但每轮可用 worker 数不同的
 * 调用方。
 *
 * 参数 nworkers_to_launch 为期望值；函数取 Min(pcxt->nworkers, ...)，因为
 * InitializeParallelDSM() 可能已因资源限制把 pcxt->nworkers 降为 0，而调用方
 * 未必知道；静默截断比报错更符合“尽力并行”的语义。
 * 返回值：无。必须在 LaunchParallelWorkers() 之前调用；否则本次修改不会生效。
 * 并发：仅修改 leader 本地字段，无共享内存副作用。
 */
void
ReinitializeParallelWorkers(ParallelContext *pcxt, int nworkers_to_launch)
{
	/*
	 * The number of workers that need to be launched must be less than the
	 * number of workers with which the parallel context is initialized.  But
	 * the caller might not know that InitializeParallelDSM reduced nworkers,
	 * so just silently trim the request.
	 */
	pcxt->nworkers_to_launch = Min(pcxt->nworkers, nworkers_to_launch);
}

/*
 * Launch parallel workers.
 */
/*
 * 中文注释：
 * 按 pcxt->nworkers_to_launch 注册并启动 parallel worker。
 *
 * 前置条件：pcxt 已由 InitializeParallelDSM() 建立 DSM（seg 非 NULL），且调用方
 * 已处于 parallel mode。函数首先 BecomeLockGroupLeader()：leader 成为锁组组长，
 * 之后启动的 worker 通过 BecomeLockGroupMember() 加入同一锁组，使重量级锁、
 * 死锁检测和并行 worker 的退出能够作为一个整体处理。
 *
 * 每个 worker 通过 BackgroundWorker 描述符注册：
 *   - bgw_name/bgw_type 用于日志和 pg_stat_activity 展示；
 *   - BGWORKER_SHMEM_ACCESS | BGWORKER_BACKEND_DATABASE_CONNECTION |
 *     BGWORKER_CLASS_PARALLEL 表明需要共享内存、数据库连接和并行 worker 槽位；
 *   - BgWorkerStart_ConsistentState 保证数据库已恢复到一致状态；
 *   - BGW_NEVER_RESTART：worker 异常退出后不自动重启，由 leader 感知并报错；
 *   - bgw_main_arg 传 DSM handle，bgw_extra 传 worker 编号 i；
 *   - bgw_notify_pid 设为 leader PID，使 postmaster 在 worker 状态变化时唤醒
 *     leader。
 *
 * 注册失败（通常达到 max_worker_processes）不会抛错，而是把
 * any_registrations_failed 置真并跳过后续注册；对失败槽位 detach 并清空
 * error_mqh，防止 WaitForParallelWorkersTo* 永远等待一个从未启动的 worker。
 * 因此调用方必须能接受“实际 worker 数少于请求数”。
 *
 * 成功注册后调用 shm_mq_set_handle() 把 BackgroundWorkerHandle 关联到错误队列
 * 句柄，后续 shm_mq 等待可以借它检测对端死亡；nworkers_launched 只在成功后
 * 递增。最后按最终数量分配 known_attached_workers 数组。
 *
 * 参数：pcxt 为已初始化的上下文。返回值：无。
 * 副作用：向 postmaster 注册后台进程并修改 pcxt 字段；worker 会立即开始执行
 * ParallelWorkerMain()，因此本函数返回时 worker 可能已经运行甚至结束。
 * 并发/错误处理：注册本身是异步的，无法保证 worker 成功初始化；初始化失败会在
 * WaitForParallelWorkersToAttach()/Finish() 中通过错误队列或 bgworker 状态发现。
 */
void
LaunchParallelWorkers(ParallelContext *pcxt)
{
	MemoryContext oldcontext;
	BackgroundWorker worker;
	int			i;
	bool		any_registrations_failed = false;

	/* Skip this if we have no workers. */
	if (pcxt->nworkers == 0 || pcxt->nworkers_to_launch == 0)
		return;

	/* We need to be a lock group leader. */
	BecomeLockGroupLeader();

	/* If we do have workers, we'd better have a DSM segment. */
	Assert(pcxt->seg != NULL);

	/* We might be running in a short-lived memory context. */
	oldcontext = MemoryContextSwitchTo(TopTransactionContext);

	/* Configure a worker. */
	memset(&worker, 0, sizeof(worker));
	snprintf(worker.bgw_name, BGW_MAXLEN, "parallel worker for PID %d",
			 MyProcPid);
	snprintf(worker.bgw_type, BGW_MAXLEN, "parallel worker");
	worker.bgw_flags =
		BGWORKER_SHMEM_ACCESS | BGWORKER_BACKEND_DATABASE_CONNECTION
		| BGWORKER_CLASS_PARALLEL;
	worker.bgw_start_time = BgWorkerStart_ConsistentState;
	worker.bgw_restart_time = BGW_NEVER_RESTART;
	sprintf(worker.bgw_library_name, "postgres");
	sprintf(worker.bgw_function_name, "ParallelWorkerMain");
	worker.bgw_main_arg = UInt32GetDatum(dsm_segment_handle(pcxt->seg));
	worker.bgw_notify_pid = MyProcPid;

	/*
	 * Start workers.
	 *
	 * The caller must be able to tolerate ending up with fewer workers than
	 * expected, so there is no need to throw an error here if registration
	 * fails.  It wouldn't help much anyway, because registering the worker in
	 * no way guarantees that it will start up and initialize successfully.
	 */
	for (i = 0; i < pcxt->nworkers_to_launch; ++i)
	{
		memcpy(worker.bgw_extra, &i, sizeof(int));
		if (!any_registrations_failed &&
			RegisterDynamicBackgroundWorker(&worker,
											&pcxt->worker[i].bgwhandle))
		{
			shm_mq_set_handle(pcxt->worker[i].error_mqh,
							  pcxt->worker[i].bgwhandle);
			pcxt->nworkers_launched++;
		}
		else
		{
			/*
			 * If we weren't able to register the worker, then we've bumped up
			 * against the max_worker_processes limit, and future
			 * registrations will probably fail too, so arrange to skip them.
			 * But we still have to execute this code for the remaining slots
			 * to make sure that we forget about the error queues we budgeted
			 * for those workers.  Otherwise, we'll wait for them to start,
			 * but they never will.
			 */
			any_registrations_failed = true;
			pcxt->worker[i].bgwhandle = NULL;
			shm_mq_detach(pcxt->worker[i].error_mqh);
			pcxt->worker[i].error_mqh = NULL;
		}
	}

	/*
	 * Now that nworkers_launched has taken its final value, we can initialize
	 * known_attached_workers.
	 */
	if (pcxt->nworkers_launched > 0)
	{
		pcxt->known_attached_workers = palloc0_array(bool, pcxt->nworkers_launched);
		pcxt->nknown_attached_workers = 0;
	}

	/* Restore previous memory context. */
	MemoryContextSwitchTo(oldcontext);
}

/*
 * Wait for all workers to attach to their error queues, and throw an error if
 * any worker fails to do this.
 *
 * Callers can assume that if this function returns successfully, then the
 * number of workers given by pcxt->nworkers_launched have initialized and
 * attached to their error queues.  Whether or not these workers are guaranteed
 * to still be running depends on what code the caller asked them to run;
 * this function does not guarantee that they have not exited.  However, it
 * does guarantee that any workers which exited must have done so cleanly and
 * after successfully performing the work with which they were tasked.
 *
 * If this function is not called, then some of the workers that were launched
 * may not have been started due to a fork() failure, or may have exited during
 * early startup prior to attaching to the error queue, so nworkers_launched
 * cannot be viewed as completely reliable.  It will never be less than the
 * number of workers which actually started, but it might be more.  Any workers
 * that failed to start will still be discovered by
 * WaitForParallelWorkersToFinish and an error will be thrown at that time,
 * provided that function is eventually reached.
 *
 * In general, the leader process should do as much work as possible before
 * calling this function.  fork() failures and other early-startup failures
 * are very uncommon, and having the leader sit idle when it could be doing
 * useful work is undesirable.  However, if the leader needs to wait for
 * all of its workers or for a specific worker, it may want to call this
 * function before doing so.  If not, it must make some other provision for
 * the failure-to-start case, lest it wait forever.  On the other hand, a
 * leader which never waits for a worker that might not be started yet, or
 * at least never does so prior to WaitForParallelWorkersToFinish(), need not
 * call this function at all.
 */
/*
 * 中文注释：
 * 等待所有已启动 worker 完成初始化并 attach 到各自的 error queue；若有 worker
 * 在 attach 之前就退出，则抛出 ERROR（"parallel worker failed to initialize"）。
 *
 * 调用场景：leader 在需要确保 worker 已就绪后才能安全等待其输出/结束时调用，
 * 例如并行索引构建在开始收集结果前调用；普通 Gather 通常直接依赖
 * WaitForParallelWorkersToFinish()，因为 fork 失败很少见，leader 可以先干活。
 *
 * 实现要点：
 *   - 每次循环先 CHECK_FOR_INTERRUPTS()，借 ProcessInterrupts() ->
 *     ProcessParallelMessages() 读取 worker 消息；worker 回传的 ERROR 会在这里
 *     直接抛出；
 *   - known_attached_workers[i] 为真表示已确认该 worker 上线；error_mqh 为 NULL
 *     表示 worker 已经干净退出（收到 Terminate），也视为“已 attach”；
 *   - GetBackgroundWorkerPid() 返回 BGWH_STARTED 时，通过
 *     shm_mq_get_sender(mq) 判断 worker 是否已经把自己登记为发送方；
 *   - BGWH_STOPPED 且 sender 仍为 NULL，说明 worker 在初始化完成前死亡，必须
 *     报错，否则调用方可能永远等待；
 *   - 其他状态表示 worker 尚未启动，leader 在 MyLatch 上等待 postmaster 通知；
 *     被其他原因唤醒时会重试同一个 worker。
 *
 * 参数：pcxt。返回值：无；成功返回时 nknown_attached_workers ==
 * nworkers_launched，且这些 worker 至少曾经成功初始化。函数不保证它们仍然存活，
 * 也不保证它们没有正常退出——只保证退出是干净的。
 * 并发：leader 与 worker 通过 shm_mq/latch 同步；会处理中断和错误。
 */
void
WaitForParallelWorkersToAttach(ParallelContext *pcxt)
{
	int			i;

	/* Skip this if we have no launched workers. */
	if (pcxt->nworkers_launched == 0)
		return;

	for (;;)
	{
		/*
		 * This will process any parallel messages that are pending and it may
		 * also throw an error propagated from a worker.
		 */
		CHECK_FOR_INTERRUPTS();

		for (i = 0; i < pcxt->nworkers_launched; ++i)
		{
			BgwHandleStatus status;
			shm_mq	   *mq;
			int			rc;
			pid_t		pid;

			if (pcxt->known_attached_workers[i])
				continue;

			/*
			 * If error_mqh is NULL, then the worker has already exited
			 * cleanly.
			 */
			if (pcxt->worker[i].error_mqh == NULL)
			{
				pcxt->known_attached_workers[i] = true;
				++pcxt->nknown_attached_workers;
				continue;
			}

			status = GetBackgroundWorkerPid(pcxt->worker[i].bgwhandle, &pid);
			if (status == BGWH_STARTED)
			{
				/* Has the worker attached to the error queue? */
				mq = shm_mq_get_queue(pcxt->worker[i].error_mqh);
				if (shm_mq_get_sender(mq) != NULL)
				{
					/* Yes, so it is known to be attached. */
					pcxt->known_attached_workers[i] = true;
					++pcxt->nknown_attached_workers;
				}
			}
			else if (status == BGWH_STOPPED)
			{
				/*
				 * If the worker stopped without attaching to the error queue,
				 * throw an error.
				 */
				mq = shm_mq_get_queue(pcxt->worker[i].error_mqh);
				if (shm_mq_get_sender(mq) == NULL)
					ereport(ERROR,
							(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
							 errmsg("parallel worker failed to initialize"),
							 errhint("More details may be available in the server log.")));

				pcxt->known_attached_workers[i] = true;
				++pcxt->nknown_attached_workers;
			}
			else
			{
				/*
				 * Worker not yet started, so we must wait.  The postmaster
				 * will notify us if the worker's state changes.  Our latch
				 * might also get set for some other reason, but if so we'll
				 * just end up waiting for the same worker again.
				 */
				rc = WaitLatch(MyLatch,
							   WL_LATCH_SET | WL_EXIT_ON_PM_DEATH,
							   -1, WAIT_EVENT_BGWORKER_STARTUP);

				if (rc & WL_LATCH_SET)
					ResetLatch(MyLatch);
			}
		}

		/* If all workers are known to have started, we're done. */
		if (pcxt->nknown_attached_workers >= pcxt->nworkers_launched)
		{
			Assert(pcxt->nknown_attached_workers == pcxt->nworkers_launched);
			break;
		}
	}
}

/*
 * Wait for all workers to finish computing.
 *
 * Even if the parallel operation seems to have completed successfully, it's
 * important to call this function afterwards.  We must not miss any errors
 * the workers may have thrown during the parallel operation, or any that they
 * may yet throw while shutting down.
 *
 * Also, we want to update our notion of XactLastRecEnd based on worker
 * feedback.
 */
/*
 * 中文注释：
 * 等待所有已启动 worker 完成计算并退出（更准确地说：等到每个 worker 的 error
 * queue 都被 detach，即收到 Terminate 或检测到异常断开），并把 worker 报告的
 * WAL 末尾位置合并进 leader 的 XactLastRecEnd。
 *
 * 为什么即使并行操作“看起来成功”也必须调用：worker 可能在最后阶段才抛出错误，
 * 这些 ErrorResponse 只能通过 error queue 回传；不调用本函数就会漏掉错误。
 * 另外，leader 提交事务前必须知道所有 worker 写过的 WAL 的最大结束位置，否则
 * commit record 的 LSN 可能早于 worker 的 WAL，破坏 WAL 顺序和恢复语义。
 *
 * 循环逻辑：
 *   - 先 CHECK_FOR_INTERRUPTS() 处理待决消息（可能抛出 worker 错误）；
 *   - 统计 error_mqh == NULL 的 worker（已干净结束）；若某个 worker 的
 *     error_mqh 仍非 NULL 且 known_attached_workers[i] 为真，则说明它可能还活着，
 *     继续等待；
 *   - 若没有发现活着的 worker 但并非所有 worker 都干净结束，则检查 bgworker
 *     状态：对 BGWH_STOPPED 且从未 attach 的 worker 抛出初始化失败错误；对已经
 *     attach 的 worker，可能只是消息尚未被处理，下一轮循环会读取；
 *   - 在 MyLatch 上等待（WAIT_EVENT_PARALLEL_FINISH），醒来后 ResetLatch。
 *
 * 结束后从共享 FixedParallelState 读取 last_xlog_end（由各 worker 在提交时通过
 * ParallelWorkerReportLastRecEnd() 在自旋锁内取最大值），若大于 leader 的
 * XactLastRecEnd 则更新之。
 *
 * 参数：pcxt。返回值：无。错误处理：worker 的错误会以 ERROR 形式传播；若 worker
 * 异常断开，ProcessParallelMessages() 会报 "lost connection to parallel worker"。
 * 调用后仍应调用 DestroyParallelContext() 回收资源。
 */
void
WaitForParallelWorkersToFinish(ParallelContext *pcxt)
{
	for (;;)
	{
		bool		anyone_alive = false;
		int			nfinished = 0;
		int			i;

		/*
		 * This will process any parallel messages that are pending, which may
		 * change the outcome of the loop that follows.  It may also throw an
		 * error propagated from a worker.
		 */
		CHECK_FOR_INTERRUPTS();

		for (i = 0; i < pcxt->nworkers_launched; ++i)
		{
			/*
			 * If error_mqh is NULL, then the worker has already exited
			 * cleanly.  If we have received a message through error_mqh from
			 * the worker, we know it started up cleanly, and therefore we're
			 * certain to be notified when it exits.
			 */
			if (pcxt->worker[i].error_mqh == NULL)
				++nfinished;
			else if (pcxt->known_attached_workers[i])
			{
				anyone_alive = true;
				break;
			}
		}

		if (!anyone_alive)
		{
			/* If all workers are known to have finished, we're done. */
			if (nfinished >= pcxt->nworkers_launched)
			{
				Assert(nfinished == pcxt->nworkers_launched);
				break;
			}

			/*
			 * We didn't detect any living workers, but not all workers are
			 * known to have exited cleanly.  Either not all workers have
			 * launched yet, or maybe some of them failed to start or
			 * terminated abnormally.
			 */
			for (i = 0; i < pcxt->nworkers_launched; ++i)
			{
				pid_t		pid;
				shm_mq	   *mq;

				/*
				 * If the worker is BGWH_NOT_YET_STARTED or BGWH_STARTED, we
				 * should just keep waiting.  If it is BGWH_STOPPED, then
				 * further investigation is needed.
				 */
				if (pcxt->worker[i].error_mqh == NULL ||
					pcxt->worker[i].bgwhandle == NULL ||
					GetBackgroundWorkerPid(pcxt->worker[i].bgwhandle,
										   &pid) != BGWH_STOPPED)
					continue;

				/*
				 * Check whether the worker ended up stopped without ever
				 * attaching to the error queue.  If so, the postmaster was
				 * unable to fork the worker or it exited without initializing
				 * properly.  We must throw an error, since the caller may
				 * have been expecting the worker to do some work before
				 * exiting.
				 */
				mq = shm_mq_get_queue(pcxt->worker[i].error_mqh);
				if (shm_mq_get_sender(mq) == NULL)
					ereport(ERROR,
							(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
							 errmsg("parallel worker failed to initialize"),
							 errhint("More details may be available in the server log.")));

				/*
				 * The worker is stopped, but is attached to the error queue.
				 * Unless there's a bug somewhere, this will only happen when
				 * the worker writes messages and terminates after the
				 * CHECK_FOR_INTERRUPTS() near the top of this function and
				 * before the call to GetBackgroundWorkerPid().  In that case,
				 * our latch should have been set as well and the right things
				 * will happen on the next pass through the loop.
				 */
			}
		}

		(void) WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH, -1,
						 WAIT_EVENT_PARALLEL_FINISH);
		ResetLatch(MyLatch);
	}

	if (pcxt->toc != NULL)
	{
		FixedParallelState *fps;

		fps = shm_toc_lookup(pcxt->toc, PARALLEL_KEY_FIXED, false);
		if (fps->last_xlog_end > XactLastRecEnd)
			XactLastRecEnd = fps->last_xlog_end;
	}
}

/*
 * Wait for all workers to exit.
 *
 * This function ensures that workers have been completely shutdown.  The
 * difference between WaitForParallelWorkersToFinish and this function is
 * that the former just ensures that last message sent by a worker backend is
 * received by the leader backend whereas this ensures the complete shutdown.
 */
/*
 * 中文注释：
 * 等待所有已启动的并行 worker 完全退出。
 *
 * 与 WaitForParallelWorkersToFinish 的区别：后者只保证收到 worker 发来的最后一条
 * 消息，此时 worker 可能仍在做清理；本函数通过 WaitForBackgroundWorkerShutdown
 * 等到进程真正结束，确保后续事务提交/中止不会与 worker 的资源释放竞争。
 * 每个 bgwhandle 等待后立即释放并把指针置空，避免重复等待。若 postmaster 已退出，
 * 无法确认 worker 状态，只能 FATAL 终止当前会话。
 */
static void
WaitForParallelWorkersToExit(ParallelContext *pcxt)
{
	int			i;

	/* Wait until the workers actually die. */
	for (i = 0; i < pcxt->nworkers_launched; ++i)
	{
		BgwHandleStatus status;

		if (pcxt->worker == NULL || pcxt->worker[i].bgwhandle == NULL)
			continue;

		status = WaitForBackgroundWorkerShutdown(pcxt->worker[i].bgwhandle);

		/*
		 * If the postmaster kicked the bucket, we have no chance of cleaning
		 * up safely -- we won't be able to tell when our workers are actually
		 * dead.  This doesn't necessitate a PANIC since they will all abort
		 * eventually, but we can't safely continue this session.
		 */
		if (status == BGWH_POSTMASTER_DIED)
			ereport(FATAL,
					(errcode(ERRCODE_ADMIN_SHUTDOWN),
					 errmsg("postmaster exited during a parallel transaction")));

		/* Release memory. */
		pfree(pcxt->worker[i].bgwhandle);
		pcxt->worker[i].bgwhandle = NULL;
	}
}

/*
 * Destroy a parallel context.
 *
 * If expecting a clean exit, you should use WaitForParallelWorkersToFinish()
 * first, before calling this function.  When this function is invoked, any
 * remaining workers are forcibly killed; the dynamic shared memory segment
 * is unmapped; and we then wait (uninterruptibly) for the workers to exit.
 */
/*
 * 中文注释：
 * 销毁一个并行上下文，终止残留 worker、解除 DSM 映射并释放内存。
 *
 * 正常退出路径应先调用 WaitForParallelWorkersToFinish，再调用本函数；如果仍有
 * worker 活着，这里会强制 TerminateBackgroundWorker 并 detach 其错误队列。
 * 操作顺序很重要：先从全局 pcxt_list 摘除节点，防止后续步骤报错时 AtEOXact_Parallel
 * 再次销毁同一上下文；然后 detach DSM（会隐式 detach 其中的 shm_mq），释放私有
 * 内存，最后在 HOLD_INTERRUPTS 保护下等待 worker 退出——因为事务提交/中止前必须
 * 确保所有 worker 已消失，此阶段不能响应中断。
 */
void
DestroyParallelContext(ParallelContext *pcxt)
{
	int			i;

	/*
	 * Be careful about order of operations here!  We remove the parallel
	 * context from the list before we do anything else; otherwise, if an
	 * error occurs during a subsequent step, we might try to nuke it again
	 * from AtEOXact_Parallel or AtEOSubXact_Parallel.
	 */
	dlist_delete(&pcxt->node);

	/* Kill each worker in turn, and forget their error queues. */
	if (pcxt->worker != NULL)
	{
		for (i = 0; i < pcxt->nworkers_launched; ++i)
		{
			if (pcxt->worker[i].error_mqh != NULL)
			{
				TerminateBackgroundWorker(pcxt->worker[i].bgwhandle);

				shm_mq_detach(pcxt->worker[i].error_mqh);
				pcxt->worker[i].error_mqh = NULL;
			}
		}
	}

	/*
	 * If we have allocated a shared memory segment, detach it.  This will
	 * implicitly detach the error queues, and any other shared memory queues,
	 * stored there.
	 */
	if (pcxt->seg != NULL)
	{
		dsm_detach(pcxt->seg);
		pcxt->seg = NULL;
	}

	/*
	 * If this parallel context is actually in backend-private memory rather
	 * than shared memory, free that memory instead.
	 */
	if (pcxt->private_memory != NULL)
	{
		pfree(pcxt->private_memory);
		pcxt->private_memory = NULL;
	}

	/*
	 * We can't finish transaction commit or abort until all of the workers
	 * have exited.  This means, in particular, that we can't respond to
	 * interrupts at this stage.
	 */
	HOLD_INTERRUPTS();
	WaitForParallelWorkersToExit(pcxt);
	RESUME_INTERRUPTS();

	/* Free the worker array itself. */
	if (pcxt->worker != NULL)
	{
		pfree(pcxt->worker);
		pcxt->worker = NULL;
	}

	/* Free memory. */
	pfree(pcxt->library_name);
	pfree(pcxt->function_name);
	pfree(pcxt);
}

/*
 * Are there any parallel contexts currently active?
 */
/*
 * 中文注释：
 * 判断当前后端是否还有任何活跃的并行上下文。
 *
 * 直接检查全局 pcxt_list 是否为空。该列表保存本后端发起的、尚未销毁的
 * ParallelContext，用于事务/子事务结束时统一清理，也用于 ProcessParallelMessages
 * 遍历各 worker 的错误队列。
 */
bool
ParallelContextActive(void)
{
	return !dlist_is_empty(&pcxt_list);
}

/*
 * Handle receipt of an interrupt indicating a parallel worker message.
 *
 * Note: this is called within a signal handler!  All we can do is set
 * a flag that will cause the next CHECK_FOR_INTERRUPTS() to invoke
 * ProcessParallelMessages().
 */
/*
 * 中文注释：
 * 并行 worker 消息到达时的信号处理入口。
 *
 * 该函数在信号处理函数中被调用，因此只能做最低限度的工作：设置 InterruptPending
 * 和 ParallelMessagePending 两个标志，然后返回。下一次 CHECK_FOR_INTERRUPTS()
 * 会调用 ProcessParallelMessages() 真正读取消息。latch 由 procsignal_sigusr1_handler
 * 负责唤醒，不能在这里做内存分配、加锁或 ereport 等不安全操作。
 */
void
HandleParallelMessageInterrupt(void)
{
	InterruptPending = true;
	ParallelMessagePending = true;
	/* latch will be set by procsignal_sigusr1_handler */
}

/*
 * Process any queued protocol messages received from parallel workers.
 */
/*
 * 中文注释：
 * 处理所有并行 worker 已排队的协议消息。
 *
 * 由 ProcessInterrupts() 在 ParallelMessagePending 置位时调用。函数先 HOLD_INTERRUPTS，
 * 防止处理过程中又收到信号导致递归进入；然后切换到一个私有、每次复用的内存上下文，
 * 避免把临时数据泄漏到长生命周期上下文中。随后遍历 pcxt_list 中的每个上下文和每个
 * worker，用非阻塞方式从 shm_mq 错误队列读取消息，交给 ProcessParallelMessage()
 * 解析。队列被 detach 或暂时无数据时停止读取。最后恢复内存上下文和中断状态。
 */
void
ProcessParallelMessages(void)
{
	dlist_iter	iter;
	MemoryContext oldcontext;

	static MemoryContext hpm_context = NULL;

	/*
	 * This is invoked from ProcessInterrupts(), and since some of the
	 * functions it calls contain CHECK_FOR_INTERRUPTS(), there is a potential
	 * for recursive calls if more signals are received while this runs.  It's
	 * unclear that recursive entry would be safe, and it doesn't seem useful
	 * even if it is safe, so let's block interrupts until done.
	 */
	HOLD_INTERRUPTS();

	/*
	 * Moreover, CurrentMemoryContext might be pointing almost anywhere.  We
	 * don't want to risk leaking data into long-lived contexts, so let's do
	 * our work here in a private context that we can reset on each use.
	 */
	if (hpm_context == NULL)	/* first time through? */
		hpm_context = AllocSetContextCreate(TopMemoryContext,
											"ProcessParallelMessages",
											ALLOCSET_DEFAULT_SIZES);
	else
		MemoryContextReset(hpm_context);

	oldcontext = MemoryContextSwitchTo(hpm_context);

	/* OK to process messages.  Reset the flag saying there are more to do. */
	ParallelMessagePending = false;

	dlist_foreach(iter, &pcxt_list)
	{
		ParallelContext *pcxt;
		int			i;

		pcxt = dlist_container(ParallelContext, node, iter.cur);
		if (pcxt->worker == NULL)
			continue;

		for (i = 0; i < pcxt->nworkers_launched; ++i)
		{
			/*
			 * Read as many messages as we can from each worker, but stop when
			 * either (1) the worker's error queue goes away, which can happen
			 * if we receive a Terminate message from the worker; or (2) no
			 * more messages can be read from the worker without blocking.
			 */
			while (pcxt->worker[i].error_mqh != NULL)
			{
				shm_mq_result res;
				Size		nbytes;
				void	   *data;

				res = shm_mq_receive(pcxt->worker[i].error_mqh, &nbytes,
									 &data, true);
				if (res == SHM_MQ_WOULD_BLOCK)
					break;
				else if (res == SHM_MQ_SUCCESS)
				{
					StringInfoData msg;

					initStringInfo(&msg);
					appendBinaryStringInfo(&msg, data, nbytes);
					ProcessParallelMessage(pcxt, i, &msg);
					pfree(msg.data);
				}
				else
					ereport(ERROR,
							(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
							 errmsg("lost connection to parallel worker")));
			}
		}
	}

	MemoryContextSwitchTo(oldcontext);

	/* Might as well clear the context on our way out */
	MemoryContextReset(hpm_context);

	RESUME_INTERRUPTS();
}

/*
 * Process a single protocol message received from a single parallel worker.
 */
/*
 * 中文注释：
 * 解析并处理来自第 i 个并行 worker 的一条协议消息。
 *
 * 消息类型包括：
 *   - ErrorResponse/NoticeResponse：解析为 ErrorData，把错误级别限制在 ERROR 以内
 *     （worker 死亡不应让 leader 直接 PANIC），必要时加上 "parallel worker" 上下文，
 *     并使用创建 ParallelContext 时的 error_context_stack 重新抛出，保证错误位置和
 *     上下文与 leader 一致；
 *   - NotificationResponse：把 NOTIFY 的 pid/channel/payload 转发给前端；
 *   - Progress：把增量进度值累加到 pgstat 的进度参数；
 *   - Terminate：worker 正常结束，detach 并清空其错误队列。
 * 未知消息类型视为协议错误。函数还会维护 known_attached_workers 计数，供等待逻辑
 * 判断哪些 worker 已经建立过连接。
 */
static void
ProcessParallelMessage(ParallelContext *pcxt, int i, StringInfo msg)
{
	char		msgtype;

	if (pcxt->known_attached_workers != NULL &&
		!pcxt->known_attached_workers[i])
	{
		pcxt->known_attached_workers[i] = true;
		pcxt->nknown_attached_workers++;
	}

	msgtype = pq_getmsgbyte(msg);

	switch (msgtype)
	{
		case PqMsg_ErrorResponse:
		case PqMsg_NoticeResponse:
			{
				ErrorData	edata;
				ErrorContextCallback *save_error_context_stack;

				/* Parse ErrorResponse or NoticeResponse. */
				pq_parse_errornotice(msg, &edata);

				/* Death of a worker isn't enough justification for suicide. */
				edata.elevel = Min(edata.elevel, ERROR);

				/*
				 * If desired, add a context line to show that this is a
				 * message propagated from a parallel worker.  Otherwise, it
				 * can sometimes be confusing to understand what actually
				 * happened.  (We don't do this in DEBUG_PARALLEL_REGRESS mode
				 * because it causes test-result instability depending on
				 * whether a parallel worker is actually used or not.)
				 */
				if (debug_parallel_query != DEBUG_PARALLEL_REGRESS)
				{
					if (edata.context)
						edata.context = psprintf("%s\n%s", edata.context,
												 _("parallel worker"));
					else
						edata.context = pstrdup(_("parallel worker"));
				}

				/*
				 * Context beyond that should use the error context callbacks
				 * that were in effect when the ParallelContext was created,
				 * not the current ones.
				 */
				save_error_context_stack = error_context_stack;
				error_context_stack = pcxt->error_context_stack;

				/* Rethrow error or print notice. */
				ThrowErrorData(&edata);

				/* Not an error, so restore previous context stack. */
				error_context_stack = save_error_context_stack;

				break;
			}

		case PqMsg_NotificationResponse:
			{
				/* Propagate NotifyResponse. */
				int32		pid;
				const char *channel;
				const char *payload;

				pid = pq_getmsgint(msg, 4);
				channel = pq_getmsgrawstring(msg);
				payload = pq_getmsgrawstring(msg);
				pq_endmessage(msg);

				NotifyMyFrontEnd(channel, payload, pid);

				break;
			}

		case PqMsg_Progress:
			{
				/*
				 * Only incremental progress reporting is currently supported.
				 * However, it's possible to add more fields to the message to
				 * allow for handling of other backend progress APIs.
				 */
				int			index = pq_getmsgint(msg, 4);
				int64		incr = pq_getmsgint64(msg);

				pq_getmsgend(msg);

				pgstat_progress_incr_param(index, incr);

				break;
			}

		case PqMsg_Terminate:
			{
				shm_mq_detach(pcxt->worker[i].error_mqh);
				pcxt->worker[i].error_mqh = NULL;
				break;
			}

		default:
			{
				elog(ERROR, "unrecognized message type received from parallel worker: %c (message length %d bytes)",
					 msgtype, msg->len);
			}
	}
}

/*
 * End-of-subtransaction cleanup for parallel contexts.
 *
 * Here we remove only parallel contexts initiated within the current
 * subtransaction.
 */
/*
 * 中文注释：
 * 子事务结束时的并行上下文清理。
 *
 * 只销毁 subid 等于当前子事务 ID 的上下文：这些上下文是在本子事务中创建的，不能
 * 跨子事务边界存活。pcxt_list 按创建顺序排列，因此从头部开始遇到第一个不属于本
 * 子事务的节点即可停止。提交时若仍存在上下文，说明调用者泄漏了 ParallelContext，
 * 发出 WARNING 后仍然强制销毁，避免资源泄漏；中止时则静默清理。
 */
void
AtEOSubXact_Parallel(bool isCommit, SubTransactionId mySubId)
{
	while (!dlist_is_empty(&pcxt_list))
	{
		ParallelContext *pcxt;

		pcxt = dlist_head_element(ParallelContext, node, &pcxt_list);
		if (pcxt->subid != mySubId)
			break;
		if (isCommit)
			elog(WARNING, "leaked parallel context");
		DestroyParallelContext(pcxt);
	}
}

/*
 * End-of-transaction cleanup for parallel contexts.
 *
 * We nuke all remaining parallel contexts.
 */
/*
 * 中文注释：
 * 顶层事务结束时的并行上下文清理。
 *
 * 销毁 pcxt_list 中所有剩余的并行上下文。正常情况下调用者应在事务结束前显式
 * 调用 DestroyParallelContext；若提交时仍有残留，说明存在泄漏，发出 WARNING 并
 * 强制清理。中止路径同样全部销毁，确保 worker、DSM 和错误队列不会跨事务存活。
 */
void
AtEOXact_Parallel(bool isCommit)
{
	while (!dlist_is_empty(&pcxt_list))
	{
		ParallelContext *pcxt;

		pcxt = dlist_head_element(ParallelContext, node, &pcxt_list);
		if (isCommit)
			elog(WARNING, "leaked parallel context");
		DestroyParallelContext(pcxt);
	}
}

/*
 * Main entrypoint for parallel workers.
 */
/*
 * 中文注释：
 * 并行 worker 的主入口，负责把 worker 初始化成与 leader 尽可能一致的后端环境。
 *
 * 初始化顺序经过精心设计，依赖关系如下：
 *   1. 设置信号处理、worker 编号和私有内存上下文；
 *   2. attach leader 创建的 DSM 段并取得 TOC，找到 FixedParallelState；
 *   3. 建立错误队列并重定向 libpq 消息，使 worker 的错误能回传 leader；
 *   4. 加入 leader 的 lock group（必须早于任何可能获取重量级锁的操作，否则可能
 *      产生 leader 无法检测的死锁）；
 *   5. 恢复事务/语句时间戳、入口函数、用户/角色、数据库连接、客户端编码；
 *   6. 加载 leader 已加载的库，启动 parallel worker 事务，恢复 pending syncs、
 *      relmap、reindex、combo CID、session DSM、快照、GUC、临时命名空间、
 *      未提交 enum、客户端连接信息等状态；
 *   7. 进入并行模式，调用入口函数执行真正工作；
 *   8. 退出并行模式、弹出快照、结束事务、detach session DSM，最后发送 Terminate。
 * 该函数体现了并行查询的核心设计：worker 不是独立事务，而是 leader 事务的延伸，
 * 必须继承足够的状态才能看到相同的 catalog、快照和 GUC，同时通过 lock group 与
 * leader 共享锁所有权。
 */
void
ParallelWorkerMain(Datum main_arg)
{
	dsm_segment *seg;
	shm_toc    *toc;
	FixedParallelState *fps;
	char	   *error_queue_space;
	shm_mq	   *mq;
	shm_mq_handle *mqh;
	char	   *libraryspace;
	char	   *entrypointstate;
	char	   *library_name;
	char	   *function_name;
	parallel_worker_main_type entrypt;
	char	   *gucspace;
	char	   *combocidspace;
	char	   *tsnapspace;
	char	   *asnapspace;
	char	   *tstatespace;
	char	   *pendingsyncsspace;
	char	   *reindexspace;
	char	   *relmapperspace;
	char	   *uncommittedenumsspace;
	char	   *clientconninfospace;
	char	   *session_dsm_handle_space;
	Snapshot	tsnapshot;
	Snapshot	asnapshot;

	/* Set flag to indicate that we're initializing a parallel worker. */
	InitializingParallelWorker = true;

	/* Establish signal handlers. */
	BackgroundWorkerUnblockSignals();

	/* Determine and set our parallel worker number. */
	Assert(ParallelWorkerNumber == -1);
	memcpy(&ParallelWorkerNumber, MyBgworkerEntry->bgw_extra, sizeof(int));

	/* Set up a memory context to work in, just for cleanliness. */
	CurrentMemoryContext = AllocSetContextCreate(TopMemoryContext,
												 "Parallel worker",
												 ALLOCSET_DEFAULT_SIZES);

	/*
	 * Attach to the dynamic shared memory segment for the parallel query, and
	 * find its table of contents.
	 *
	 * Note: at this point, we have not created any ResourceOwner in this
	 * process.  This will result in our DSM mapping surviving until process
	 * exit, which is fine.  If there were a ResourceOwner, it would acquire
	 * ownership of the mapping, but we have no need for that.
	 */
	seg = dsm_attach(DatumGetUInt32(main_arg));
	if (seg == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("could not map dynamic shared memory segment")));
	toc = shm_toc_attach(PARALLEL_MAGIC, dsm_segment_address(seg));
	if (toc == NULL)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("invalid magic number in dynamic shared memory segment")));

	/* Look up fixed parallel state. */
	fps = shm_toc_lookup(toc, PARALLEL_KEY_FIXED, false);
	MyFixedParallelState = fps;

	/* Arrange to signal the leader if we exit. */
	ParallelLeaderPid = fps->parallel_leader_pid;
	ParallelLeaderProcNumber = fps->parallel_leader_proc_number;
	before_shmem_exit(ParallelWorkerShutdown, PointerGetDatum(seg));

	/*
	 * Now we can find and attach to the error queue provided for us.  That's
	 * good, because until we do that, any errors that happen here will not be
	 * reported back to the process that requested that this worker be
	 * launched.
	 */
	error_queue_space = shm_toc_lookup(toc, PARALLEL_KEY_ERROR_QUEUE, false);
	mq = (shm_mq *) (error_queue_space +
					 ParallelWorkerNumber * PARALLEL_ERROR_QUEUE_SIZE);
	shm_mq_set_sender(mq, MyProc);
	mqh = shm_mq_attach(mq, seg, NULL);
	pq_redirect_to_shm_mq(seg, mqh);
	pq_set_parallel_leader(fps->parallel_leader_pid,
						   fps->parallel_leader_proc_number);

	/*
	 * Hooray! Primary initialization is complete.  Now, we need to set up our
	 * backend-local state to match the original backend.
	 */

	/*
	 * Join locking group.  We must do this before anything that could try to
	 * acquire a heavyweight lock, because any heavyweight locks acquired to
	 * this point could block either directly against the parallel group
	 * leader or against some process which in turn waits for a lock that
	 * conflicts with the parallel group leader, causing an undetected
	 * deadlock.  (If we can't join the lock group, the leader has gone away,
	 * so just exit quietly.)
	 */
	if (!BecomeLockGroupMember(fps->parallel_leader_pgproc,
							   fps->parallel_leader_pid))
		return;

	/*
	 * Restore transaction and statement start-time timestamps.  This must
	 * happen before anything that would start a transaction, else asserts in
	 * xact.c will fire.
	 */
	SetParallelStartTimestamps(fps->xact_ts, fps->stmt_ts);

	/*
	 * Identify the entry point to be called.  In theory this could result in
	 * loading an additional library, though most likely the entry point is in
	 * the core backend or in a library we just loaded.
	 */
	entrypointstate = shm_toc_lookup(toc, PARALLEL_KEY_ENTRYPOINT, false);
	library_name = entrypointstate;
	function_name = entrypointstate + strlen(library_name) + 1;

	entrypt = LookupParallelWorkerFunction(library_name, function_name);

	/*
	 * Restore current session authorization and role id.  No verification
	 * happens here, we just blindly adopt the leader's state.  Note that this
	 * has to happen before InitPostgres, since InitializeSessionUserId will
	 * not set these variables.
	 */
	SetAuthenticatedUserId(fps->authenticated_user_id);
	SetSessionAuthorization(fps->session_user_id,
							fps->session_user_is_superuser);
	SetCurrentRoleId(fps->outer_user_id, fps->role_is_superuser);

	/*
	 * Restore database connection.  We skip connection authorization checks,
	 * reasoning that (a) the leader checked these things when it started, and
	 * (b) we do not want parallel mode to cause these failures, because that
	 * would make use of parallel query plans not transparent to applications.
	 */
	BackgroundWorkerInitializeConnectionByOid(fps->database_id,
											  fps->authenticated_user_id,
											  BGWORKER_BYPASS_ALLOWCONN |
											  BGWORKER_BYPASS_ROLELOGINCHECK);

	/*
	 * Set the client encoding to the database encoding, since that is what
	 * the leader will expect.  (We're cheating a bit by not calling
	 * PrepareClientEncoding first.  It's okay because this call will always
	 * result in installing a no-op conversion.  No error should be possible,
	 * but check anyway.)
	 */
	if (SetClientEncoding(GetDatabaseEncoding()) < 0)
		elog(ERROR, "SetClientEncoding(%d) failed", GetDatabaseEncoding());

	/*
	 * Load libraries that were loaded by original backend.  We want to do
	 * this before restoring GUCs, because the libraries might define custom
	 * variables.
	 */
	libraryspace = shm_toc_lookup(toc, PARALLEL_KEY_LIBRARY, false);
	StartTransactionCommand();
	RestoreLibraryState(libraryspace);
	CommitTransactionCommand();

	/* Crank up a transaction state appropriate to a parallel worker. */
	tstatespace = shm_toc_lookup(toc, PARALLEL_KEY_TRANSACTION_STATE, false);
	StartParallelWorkerTransaction(tstatespace);

	/*
	 * Restore state that affects catalog access.  Ideally we'd do this even
	 * before calling InitPostgres, but that has order-of-initialization
	 * problems, and also the relmapper would get confused during the
	 * CommitTransactionCommand call above.
	 */
	pendingsyncsspace = shm_toc_lookup(toc, PARALLEL_KEY_PENDING_SYNCS,
									   false);
	RestorePendingSyncs(pendingsyncsspace);
	relmapperspace = shm_toc_lookup(toc, PARALLEL_KEY_RELMAPPER_STATE, false);
	RestoreRelationMap(relmapperspace);
	reindexspace = shm_toc_lookup(toc, PARALLEL_KEY_REINDEX_STATE, false);
	RestoreReindexState(reindexspace);
	combocidspace = shm_toc_lookup(toc, PARALLEL_KEY_COMBO_CID, false);
	RestoreComboCIDState(combocidspace);

	/* Attach to the per-session DSM segment and contained objects. */
	session_dsm_handle_space =
		shm_toc_lookup(toc, PARALLEL_KEY_SESSION_DSM, false);
	AttachSession(*(dsm_handle *) session_dsm_handle_space);

	/*
	 * If the transaction isolation level is REPEATABLE READ or SERIALIZABLE,
	 * the leader has serialized the transaction snapshot and we must restore
	 * it. At lower isolation levels, there is no transaction-lifetime
	 * snapshot, but we need TransactionXmin to get set to a value which is
	 * less than or equal to the xmin of every snapshot that will be used by
	 * this worker. The easiest way to accomplish that is to install the
	 * active snapshot as the transaction snapshot. Code running in this
	 * parallel worker might take new snapshots via GetTransactionSnapshot()
	 * or GetLatestSnapshot(), but it shouldn't have any way of acquiring a
	 * snapshot older than the active snapshot.
	 */
	asnapspace = shm_toc_lookup(toc, PARALLEL_KEY_ACTIVE_SNAPSHOT, false);
	tsnapspace = shm_toc_lookup(toc, PARALLEL_KEY_TRANSACTION_SNAPSHOT, true);
	asnapshot = RestoreSnapshot(asnapspace);
	tsnapshot = tsnapspace ? RestoreSnapshot(tsnapspace) : asnapshot;
	RestoreTransactionSnapshot(tsnapshot,
							   fps->parallel_leader_pgproc);
	PushActiveSnapshot(asnapshot);

	/*
	 * We've changed which tuples we can see, and must therefore invalidate
	 * system caches.
	 */
	InvalidateSystemCaches();

	/*
	 * Restore GUC values from launching backend.  We can't do this earlier,
	 * because GUC check hooks that do catalog lookups need to see the same
	 * database state as the leader.  Also, the check hooks for
	 * session_authorization and role assume we already set the correct role
	 * OIDs.
	 */
	gucspace = shm_toc_lookup(toc, PARALLEL_KEY_GUC, false);
	RestoreGUCState(gucspace);

	/*
	 * Restore current user ID and security context.  No verification happens
	 * here, we just blindly adopt the leader's state.  We can't do this till
	 * after restoring GUCs, else we'll get complaints about restoring
	 * session_authorization and role.  (In effect, we're assuming that all
	 * the restored values are okay to set, even if we are now inside a
	 * restricted context.)
	 */
	SetUserIdAndSecContext(fps->current_user_id, fps->sec_context);

	/* Restore temp-namespace state to ensure search path matches leader's. */
	SetTempNamespaceState(fps->temp_namespace_id,
						  fps->temp_toast_namespace_id);

	/* Restore uncommitted enums. */
	uncommittedenumsspace = shm_toc_lookup(toc, PARALLEL_KEY_UNCOMMITTEDENUMS,
										   false);
	RestoreUncommittedEnums(uncommittedenumsspace);

	/* Restore the ClientConnectionInfo. */
	clientconninfospace = shm_toc_lookup(toc, PARALLEL_KEY_CLIENTCONNINFO,
										 false);
	RestoreClientConnectionInfo(clientconninfospace);

	/*
	 * Initialize SystemUser now that MyClientConnectionInfo is restored. Also
	 * ensure that auth_method is actually valid, aka authn_id is not NULL.
	 */
	if (MyClientConnectionInfo.authn_id)
		InitializeSystemUser(MyClientConnectionInfo.authn_id,
							 hba_authname(MyClientConnectionInfo.auth_method));

	/* Attach to the leader's serializable transaction, if SERIALIZABLE. */
	AttachSerializableXact(fps->serializable_xact_handle);

	/*
	 * We've initialized all of our state now; nothing should change
	 * hereafter.
	 */
	InitializingParallelWorker = false;
	EnterParallelMode();

	/*
	 * Time to do the real work: invoke the caller-supplied code.
	 */
	entrypt(seg, toc);

	/* Must exit parallel mode to pop active snapshot. */
	ExitParallelMode();

	/* Must pop active snapshot so snapmgr.c doesn't complain. */
	PopActiveSnapshot();

	/* Shut down the parallel-worker transaction. */
	EndParallelWorkerTransaction();

	/* Detach from the per-session DSM segment. */
	DetachSession();

	/* Report success. */
	pq_putmessage(PqMsg_Terminate, NULL, 0);
}

/*
 * Update shared memory with the ending location of the last WAL record we
 * wrote, if it's greater than the value already stored there.
 */
/*
 * 中文注释：
 * 把 worker 写过的最后一条 WAL 记录的结束位置报告给 leader。
 *
 * worker 在并行操作中也可能写 WAL（例如并行建索引），leader 事务结束时需要知道
 * 所有 worker 的最大 WAL 位置，以便正确设置 XactLastRecEnd、处理同步提交和复制。
 * FixedParallelState 位于共享内存，用 spinlock 保护 last_xlog_end，并只允许增大，
 * 因此多个 worker 可以安全地并发报告。leader 在 WaitForParallelWorkersToFinish
 * 中读取该值并合并到自己的 XactLastRecEnd。
 */
void
ParallelWorkerReportLastRecEnd(XLogRecPtr last_xlog_end)
{
	FixedParallelState *fps = MyFixedParallelState;

	Assert(fps != NULL);
	SpinLockAcquire(&fps->mutex);
	if (fps->last_xlog_end < last_xlog_end)
		fps->last_xlog_end = last_xlog_end;
	SpinLockRelease(&fps->mutex);
}

/*
 * Make sure the leader tries to read from our error queue one more time.
 * This guards against the case where we exit uncleanly without sending an
 * ErrorResponse to the leader, for example because some code calls proc_exit
 * directly.
 *
 * Also explicitly detach from dsm segment so that subsystems using
 * on_dsm_detach() have a chance to send stats before the stats subsystem is
 * shut down as part of a before_shmem_exit() hook.
 *
 * One might think this could instead be solved by carefully ordering the
 * attaching to dsm segments, so that the pgstats segments get detached from
 * later than the parallel query one. That turns out to not work because the
 * stats hash might need to grow which can cause new segments to be allocated,
 * which then will be detached from earlier.
 */
/*
 * 中文注释：
 * worker 退出前的 before_shmem_exit 回调。
 *
 * 两个目的：
 *   1. 向 leader 发送 PROCSIG_PARALLEL_MESSAGE，确保 leader 再读一次错误队列；
 *      这样即使 worker 没有发送 ErrorResponse 就 proc_exit，leader 也能察觉并
 *      清理，而不是永久等待；
 *   2. 显式 detach 并行查询的 DSM 段，让注册了 on_dsm_detach 的子系统（尤其是
 *      pgstats）有机会在统计系统关闭前发送数据。不能依赖退出钩子的注册顺序来
 *      解决这个问题，因为统计哈希扩容可能动态创建新的 DSM 段。
 */
static void
ParallelWorkerShutdown(int code, Datum arg)
{
	SendProcSignal(ParallelLeaderPid,
				   PROCSIG_PARALLEL_MESSAGE,
				   ParallelLeaderProcNumber);

	dsm_detach((dsm_segment *) DatumGetPointer(arg));
}

/*
 * Look up (and possibly load) a parallel worker entry point function.
 *
 * For functions contained in the core code, we use library name "postgres"
 * and consult the InternalParallelWorkers array.  External functions are
 * looked up, and loaded if necessary, using load_external_function().
 *
 * The point of this is to pass function names as strings across process
 * boundaries.  We can't pass actual function addresses because of the
 * possibility that the function has been loaded at a different address
 * in a different process.  This is obviously a hazard for functions in
 * loadable libraries, but it can happen even for functions in the core code
 * on platforms using EXEC_BACKEND (e.g., Windows).
 *
 * At some point it might be worthwhile to get rid of InternalParallelWorkers[]
 * in favor of applying load_external_function() for core functions too;
 * but that raises portability issues that are not worth addressing now.
 */
/*
 * 中文注释：
 * 根据库名和函数名查找并行 worker 的入口函数地址。
 *
 * 进程之间不能传递函数指针（ASLR、EXEC_BACKEND 等都可能导致同一函数在不同进程中
 * 地址不同），因此 leader 只把字符串形式的库名/函数名放进 DSM。若库名为
 * "postgres"，先在 InternalParallelWorkers 静态表中查找核心内置入口；否则用
 * load_external_function 动态加载扩展库并解析符号。找不到内置函数属于编程错误，
 * 直接 ERROR。
 */
static parallel_worker_main_type
LookupParallelWorkerFunction(const char *libraryname, const char *funcname)
{
	/*
	 * If the function is to be loaded from postgres itself, search the
	 * InternalParallelWorkers array.
	 */
	if (strcmp(libraryname, "postgres") == 0)
	{
		for (size_t i = 0; i < lengthof(InternalParallelWorkers); i++)
		{
			if (strcmp(InternalParallelWorkers[i].fn_name, funcname) == 0)
				return InternalParallelWorkers[i].fn_addr;
		}

		/* We can only reach this by programming error. */
		elog(ERROR, "internal function \"%s\" not found", funcname);
	}

	/* Otherwise load from external library. */
	return (parallel_worker_main_type)
		load_external_function(libraryname, funcname, true, NULL);
}
