/*
 * rmgr.c
 *
 * Resource managers definition
 *
 * src/backend/access/transam/rmgr.c
 */
/*
 * 中文注释：
 * 本文件定义 WAL（预写式日志）的“资源管理器”（Resource Manager，简称 rmgr）注册表。
 *
 * WAL 记录的第一个字节是 RmgrId，用来标识这条记录属于哪一类资源，例如堆表、B-tree、
 * 事务提交、CLOG、表空间等。每种资源管理器提供一组回调：
 *   rm_redo     重做一条 WAL 记录；
 *   rm_desc     把记录格式化成可读文本（用于 pg_waldump 等工具）；
 *   rm_identify 返回记录子类型名称；
 *   rm_startup  启动时初始化；
 *   rm_cleanup  关闭时清理；
 *   rm_mask     在检查点后对页内容做一致性掩码处理；
 *   rm_decode   逻辑解码时把记录转换为逻辑变更。
 *
 * RmgrTable 由 access/rmgrlist.h 通过 X-macro（PG_RMGR）展开生成，保证“资源管理器
 * 编号、名称、回调”三者在编译期集中维护；新增内置资源管理器时只需修改 rmgrlist.h。
 * RegisterCustomRmgr 则允许扩展在 shared_preload_libraries 阶段注册自定义 rmgr。
 */
#include "postgres.h"

#include "access/rmgr.h"
#include "access/xlog_internal.h"
#include "fmgr.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/execnodes.h"
#include "utils/builtins.h"
#include "utils/fmgrprotos.h"
#include "utils/tuplestore.h"

/* includes needed for "access/rmgrlist.h" */
/* IWYU pragma: begin_keep */
#include "access/brin_xlog.h"
#include "access/clog.h"
#include "access/commit_ts.h"
#include "access/generic_xlog.h"
#include "access/ginxlog.h"
#include "access/gistxlog.h"
#include "access/hash_xlog.h"
#include "access/heapam_xlog.h"
#include "access/multixact.h"
#include "access/nbtxlog.h"
#include "access/spgxlog.h"
#include "access/xact.h"
#include "catalog/storage_xlog.h"
#include "commands/dbcommands_xlog.h"
#include "commands/sequence_xlog.h"
#include "commands/tablespace.h"
#include "replication/decode.h"
#include "replication/message.h"
#include "replication/origin.h"
#include "storage/standby.h"
#include "utils/relmapper.h"
/* IWYU pragma: end_keep */


/*
 * 中文注释：
 * PG_RMGR 是 X-macro 的展开规则：每遇到 rmgrlist.h 中的一条 PG_RMGR(...) 声明，就
 * 生成一个 RmgrData 结构体初始化项。字段顺序必须与 xlog_internal.h 中的 RmgrData
 * 定义严格一致，否则会导致函数指针错位、恢复时调用错误的回调。
 */
/* must be kept in sync with RmgrData definition in xlog_internal.h */
#define PG_RMGR(symname,name,redo,desc,identify,startup,cleanup,mask,decode) \
	{ name, redo, desc, identify, startup, cleanup, mask, decode },

/*
 * 中文注释：
 * 全局资源管理器表，下标就是 WAL 记录中的 RmgrId。数组长度为 RM_MAX_ID + 1，
 * 未注册的槽位保持全零（rm_name == NULL），由 RmgrIdExists 判断是否存在。
 * 这张表在 postmaster 启动早期建立，之后基本只读；自定义 rmgr 也直接写入对应槽位。
 */
RmgrData	RmgrTable[RM_MAX_ID + 1] = {
#include "access/rmgrlist.h"
};

/*
 * Start up all resource managers.
 */
/*
 * 中文注释：
 * 启动所有已注册资源管理器。
 *
 * 遍历整个 RmgrTable，跳过不存在的 ID，对提供了 rm_startup 回调的模块调用它。
 * 典型用途是初始化需要跨进程共享的资源或注册后台设施。该函数只在系统启动阶段
 * （postmaster 或单用户模式）调用一次，因此回调中不应做与具体事务相关的工作。
 */
void
RmgrStartup(void)
{
	for (int rmid = 0; rmid <= RM_MAX_ID; rmid++)
	{
		if (!RmgrIdExists(rmid))
			continue;

		if (RmgrTable[rmid].rm_startup != NULL)
			RmgrTable[rmid].rm_startup();
	}
}

/*
 * Clean up all resource managers.
 */
/*
 * 中文注释：
 * 清理所有已注册资源管理器。
 *
 * 与 RmgrStartup 对称，在系统正常关闭阶段遍历 RmgrTable，调用各模块的 rm_cleanup。
 * 它用于释放启动时申请的资源、刷新缓冲区或注销后台设施；不存在的 rmgr 直接跳过。
 */
void
RmgrCleanup(void)
{
	for (int rmid = 0; rmid <= RM_MAX_ID; rmid++)
	{
		if (!RmgrIdExists(rmid))
			continue;

		if (RmgrTable[rmid].rm_cleanup != NULL)
			RmgrTable[rmid].rm_cleanup();
	}
}

/*
 * Emit ERROR when we encounter a record with an RmgrId we don't
 * recognize.
 */
/*
 * 中文注释：
 * 遇到未知 RmgrId 时的统一报错函数。
 *
 * 恢复过程读取 WAL 时，如果记录头中的 RmgrId 没有对应实现（例如 WAL 来自安装了某扩展
 * 的实例，而当前实例没有加载该扩展），继续解析会得到错误结果，因此这里直接 ERROR。
 * 错误提示建议把实现该资源管理器的扩展加入 shared_preload_libraries，因为扩展必须
 * 在恢复开始前完成注册。
 */
void
RmgrNotFound(RmgrId rmid)
{
	ereport(ERROR, (errmsg("resource manager with ID %d not registered", rmid),
					errhint("Include the extension module that implements this resource manager in \"shared_preload_libraries\".")));
}

/*
 * Register a new custom WAL resource manager.
 *
 * Resource manager IDs must be globally unique across all extensions. Refer
 * to https://wiki.postgresql.org/wiki/CustomWALResourceManagers to reserve a
 * unique RmgrId for your extension, to avoid conflicts with other extension
 * developers. During development, use RM_EXPERIMENTAL_ID to avoid needlessly
 * reserving a new ID.
 */
/*
 * 中文注释：
 * 注册一个自定义 WAL 资源管理器。
 *
 * 参数 rmid 必须落在扩展专用 ID 区间（RM_MIN_CUSTOM_ID..RM_MAX_CUSTOM_ID），rmgr 指向
 * 调用者提供的回调集合。函数依次校验：
 *   1. rm_name 非空；
 *   2. ID 属于自定义区间；
 *   3. 当前正处于 shared_preload_libraries 初始化阶段——因为恢复可能在任意时刻读取
 *      WAL，扩展的 rmgr 必须在恢复开始前就位；
 *   4. 该 ID 尚未被占用；
 *   5. 没有其他 rmgr 使用相同名称（名称用于日志和 pg_get_wal_resource_managers）。
 * 全部通过后把结构体复制进 RmgrTable。ID 需要在 PostgreSQL wiki 上申请，开发阶段可
 * 先用 RM_EXPERIMENTAL_ID，避免与其他扩展冲突。
 */
void
RegisterCustomRmgr(RmgrId rmid, const RmgrData *rmgr)
{
	if (rmgr->rm_name == NULL || strlen(rmgr->rm_name) == 0)
		ereport(ERROR, (errmsg("custom resource manager name is invalid"),
						errhint("Provide a non-empty name for the custom resource manager.")));

	if (!RmgrIdIsCustom(rmid))
		ereport(ERROR, (errmsg("custom resource manager ID %d is out of range", rmid),
						errhint("Provide a custom resource manager ID between %d and %d.",
								RM_MIN_CUSTOM_ID, RM_MAX_CUSTOM_ID)));

	if (!process_shared_preload_libraries_in_progress)
		ereport(ERROR,
				(errmsg("failed to register custom resource manager \"%s\" with ID %d", rmgr->rm_name, rmid),
				 errdetail("Custom resource manager must be registered while initializing modules in \"shared_preload_libraries\".")));

	if (RmgrTable[rmid].rm_name != NULL)
		ereport(ERROR,
				(errmsg("failed to register custom resource manager \"%s\" with ID %d", rmgr->rm_name, rmid),
				 errdetail("Custom resource manager \"%s\" already registered with the same ID.",
						   RmgrTable[rmid].rm_name)));

	/* check for existing rmgr with the same name */
	for (int existing_rmid = 0; existing_rmid <= RM_MAX_ID; existing_rmid++)
	{
		if (!RmgrIdExists(existing_rmid))
			continue;

		if (!pg_strcasecmp(RmgrTable[existing_rmid].rm_name, rmgr->rm_name))
			ereport(ERROR,
					(errmsg("failed to register custom resource manager \"%s\" with ID %d", rmgr->rm_name, rmid),
					 errdetail("Existing resource manager with ID %d has the same name.", existing_rmid)));
	}

	/* register it */
	RmgrTable[rmid] = *rmgr;
	ereport(LOG,
			(errmsg("registered custom resource manager \"%s\" with ID %d",
					rmgr->rm_name, rmid)));
}

/* SQL SRF showing loaded resource managers */
/*
 * 中文注释：
 * SQL 集返回函数（SRF）：列出当前实例已注册的 WAL 资源管理器。
 *
 * 输出三列：rmid（整数 ID）、name（资源管理器名称）、built-in（是否为 PostgreSQL
 * 内置）。函数通过 InitMaterializedSRF 建立物化结果集，然后扫描 RmgrTable，跳过空槽位。
 * 它是 pg_waldump 之外让用户从 SQL 层检查 rmgr 注册情况的入口，也便于确认扩展是否
 * 成功注册。
 */
Datum
pg_get_wal_resource_managers(PG_FUNCTION_ARGS)
{
#define PG_GET_RESOURCE_MANAGERS_COLS 3
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	Datum		values[PG_GET_RESOURCE_MANAGERS_COLS];
	bool		nulls[PG_GET_RESOURCE_MANAGERS_COLS] = {0};

	InitMaterializedSRF(fcinfo, 0);

	for (int rmid = 0; rmid <= RM_MAX_ID; rmid++)
	{
		if (!RmgrIdExists(rmid))
			continue;
		values[0] = Int32GetDatum(rmid);
		values[1] = CStringGetTextDatum(GetRmgr(rmid).rm_name);
		values[2] = BoolGetDatum(RmgrIdIsBuiltin(rmid));
		tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc, values, nulls);
	}

	return (Datum) 0;
}
