/*-------------------------------------------------------------------------
 *
 * dsm_registry.c
 *	  Functions for interfacing with the dynamic shared memory registry.
 *
 * This provides a way for libraries to use shared memory without needing
 * to request it at startup time via a shmem_request_hook.  The registry
 * stores dynamic shared memory (DSM) segment handles keyed by a
 * library-specified string.
 *
 * The registry is accessed by calling GetNamedDSMSegment().  If a segment
 * with the provided name does not yet exist, it is created and initialized
 * with the provided init_callback callback function.  Otherwise,
 * GetNamedDSMSegment() simply ensures that the segment is attached to the
 * current backend.  This function guarantees that only one backend
 * initializes the segment and that all other backends just attach it.
 *
 * A DSA can be created in or retrieved from the registry by calling
 * GetNamedDSA().  As with GetNamedDSMSegment(), if a DSA with the provided
 * name does not yet exist, it is created.  Otherwise, GetNamedDSA()
 * ensures the DSA is attached to the current backend.  This function
 * guarantees that only one backend initializes the DSA and that all other
 * backends just attach it.
 *
 * A dshash table can be created in or retrieved from the registry by
 * calling GetNamedDSHash().  As with GetNamedDSMSegment(), if a hash
 * table with the provided name does not yet exist, it is created.
 * Otherwise, GetNamedDSHash() ensures the hash table is attached to the
 * current backend.  This function guarantees that only one backend
 * initializes the table and that all other backends just attach it.
 *
 * 【模块总览(中文)】
 * 本文件实现"DSM 注册表":一个位于动态共享内存里的"命名对象目录"。
 *
 * 【要解决的问题】库(如扩展、复制相关组件)想在多个后端之间共享
 * 内存,传统做法是在启动时经 shmem_request_hook 申请固定共享内存;
 * 但很多组件是"运行到某时刻才需要"且用量不固定,静态申请要么浪费、
 * 要么不够。注册表提供第三种方式:在运行期动态创建"命名对象",
 * 别的后端凭名字找到并附着。
 *
 * 【核心机制】
 * 1. 注册表自身由三个层次构成:
 *    - 一块传统共享内存结构 DSMRegistryCtxStruct(经 ShmemRequest 机制
 *      申请),只存放两个"句柄":DSMRegistryCtx->dsah(DSA 区域的句柄)
 *      与 DSMRegistryCtx->dshh(dshash 哈希表的句柄);
 *    - 一个"注册表 DSA"(dynamic shared memory area,由 dsa_create 在
 *      DSM 段之上建立),注册表的所有数据都存在这块 DSA 里;
 *    - 一张"注册表 dshash"(基于该 DSA 的动态哈希表),条目是
 *      DSMRegistryEntry:键为名字(NAMEDATALEN 定长字符串),值为"类型 +
 *      句柄/大小"。三种条目类型:DSM 段、DSA 区域、dshash 表。
 * 2. init_dsm_registry():懒初始化——第一次访问时,在 DSMRegistryLock
 *    独占锁保护下,由"第一个进程"创建 DSA 与哈希表并把句柄写回共享
 *    内存,后续进程凭句柄 attach,保证"创建只有一个、其余都附着"。
 *    创建后 DSA 被 dsa_pin(活到 postmaster 关闭)与 dsa_pin_mapping
 *    (本进程映射保留)双重钉住。
 * 3. 三个 Get* 入口(GetNamedDSMSegment/GetNamedDSA/GetNamedDSHash)
 *    语义一致:凭名字在注册表中"查找或插入";不存在则创建并执行
 *    调用方给的初始化回调,存在则附着到当前后端;返回的 *found 告知
 *    是"新建"还是"已有"。类型/大小不匹配时报错。
 *
 * 【设计思想】把"命名 → 句柄"的映射放在共享内存,句柄本身是跨进程
 * 的段标识,因此任意后端只需一次哈希查找就能拿到对象;条目内容不变、
 * 注册表本身永远不释放。注意各 Get* 入口要求"每个后端对同一名字
 * 至多调用一次"(DSA/dshash 不允许重复附着)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/dsm_registry.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "funcapi.h"
#include "lib/dshash.h"
#include "storage/dsm_registry.h"
#include "storage/lwlock.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
#include "utils/tuplestore.h"

/* (中文)注册表控制结构(位于传统共享内存,经 ShmemRequest 机制申请):
 * 只保存两个句柄——注册表 DSA 的句柄(dsah)与注册表 dshash 哈希表
 * 的句柄(dshh)。所有实际数据都在 DSA/哈希表里,这里只是"定位锚"。 */
typedef struct DSMRegistryCtxStruct
{
	dsa_handle	dsah;
	dshash_table_handle dshh;
} DSMRegistryCtxStruct;

/* (中文)指向共享内存中注册表控制结构的指针(init 阶段建立)。 */
static DSMRegistryCtxStruct *DSMRegistryCtx;

static void DSMRegistryShmemRequest(void *arg);
static void DSMRegistryShmemInit(void *arg);

/* (中文)本文件向共享内存子系统登记的 request/init 回调:request 阶段
 * 申请 sizeof(DSMRegistryCtxStruct);init 阶段把两个句柄置为"无效"
 * 哨兵值(真正的创建交给首次访问的进程,见 init_dsm_registry)。 */
const ShmemCallbacks DSMRegistryShmemCallbacks = {
	.request_fn = DSMRegistryShmemRequest,
	.init_fn = DSMRegistryShmemInit,
};

/* (中文)注册表条目中"命名 DSM 段"部分:handle 是段句柄(未创建时
 * DSM_HANDLE_INVALID),size 是段大小(仅创建者写入,其余进程据此校验
 * 一致性)。 */
typedef struct NamedDSMState
{
	dsm_handle	handle;
	size_t		size;
} NamedDSMState;

/* (中文)注册表条目中"命名 DSA"部分:handle 是 DSA 句柄(未创建时
 * DSA_HANDLE_INVALID),tranche 是为该 DSA 分配的 LWLock tranche ID
 * (-1 表示未分配)。 */
typedef struct NamedDSAState
{
	dsa_handle	handle;
	int			tranche;
} NamedDSAState;

/* (中文)注册表条目中"命名 dshash 表"部分:dsa_handle 是承载该表的
 * DSA 句柄,dsh_handle 是哈希表句柄,tranche 是专属 LWLock tranche ID
 * (-1 表示未分配)。 */
typedef struct NamedDSHState
{
	dsa_handle dsa_handle;
	dshash_table_handle dsh_handle;
	int			tranche;
} NamedDSHState;

/* (中文)注册表条目的类型:决定 union 里哪个成员有效、以及附着的
 * 方式。 */
typedef enum DSMREntryType
{
	DSMR_ENTRY_TYPE_DSM,
	DSMR_ENTRY_TYPE_DSA,
	DSMR_ENTRY_TYPE_DSH,
} DSMREntryType;

/* (中文)类型 → 显示名 的映射(供 pg_get_dsm_registry_allocations
 * 输出):segment/area/hash。 */
static const char *const DSMREntryTypeNames[] =
{
	[DSMR_ENTRY_TYPE_DSM] = "segment",
	[DSMR_ENTRY_TYPE_DSA] = "area",
	[DSMR_ENTRY_TYPE_DSH] = "hash",
};

/* (中文)注册表的一个条目:name 是键(定长字符串,长度受
 * offsetof(DSMRegistryEntry, type) 限制,保证键之后的数据区不被
 * 越界读),type 是条目类型,union 按类型保存段/区域/哈希表的句柄
 * 状态。 */
typedef struct DSMRegistryEntry
{
	char		name[NAMEDATALEN];
	DSMREntryType type;
	union
	{
		NamedDSMState dsm;
		NamedDSAState dsa;
		NamedDSHState dsh;
	};
} DSMRegistryEntry;

/* (中文)注册表 dshash 的建表参数:键 = 从条目偏移 0 开始的定长字符串
 * (hash/比较/拷贝都用 dshash_str* 系列,key_offset 为
 * offsetof(DSMRegistryEntry, type) 即 name 结束处),分区锁 tranche
 * 用 LWTRANCHE_DSM_REGISTRY_HASH。 */
static const dshash_parameters dsh_params = {
	offsetof(DSMRegistryEntry, type),
	sizeof(DSMRegistryEntry),
	dshash_strcmp,
	dshash_strhash,
	dshash_strcpy,
	LWTRANCHE_DSM_REGISTRY_HASH
};

/* (中文)本进程对"注册表 DSA"与"注册表 dshash"的局部引用(经
 * init_dsm_registry 建立,进程私有)。 */
static dsa_area *dsm_registry_dsa;
static dshash_table *dsm_registry_table;

/*
 * DSMRegistryShmemRequest - (中文)登记注册表控制结构的共享内存需求(request 阶段)
 *
 * 【作用】request 回调:申请 sizeof(DSMRegistryCtxStruct) 的传统共享
 * 内存,指针槽指向 DSMRegistryCtx。
 *
 * 【参数】arg —— 回调 opaque 参数(未使用)。
 * 【返回值】无。
 */
static void
DSMRegistryShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "DSM Registry Data",
					   .size = sizeof(DSMRegistryCtxStruct),
					   .ptr = (void **) &DSMRegistryCtx,
		);
}

/*
 * DSMRegistryShmemInit - (中文)初始化注册表控制结构(init 阶段)
 *
 * 【作用】把控制结构里的两个句柄置为"无效"哨兵值,表示"注册表本体
 * 尚未创建";真正的创建推迟到某个后端第一次使用时
 * (init_dsm_registry 的懒初始化)。
 *
 * 【参数】arg —— 回调 opaque 参数(未使用)。
 * 【返回值】无。
 */
static void
DSMRegistryShmemInit(void *arg)
{
	DSMRegistryCtx->dsah = DSA_HANDLE_INVALID;
	DSMRegistryCtx->dshh = DSHASH_HANDLE_INVALID;
}

/*
 * init_dsm_registry - (中文)初始化或附着注册表本体(懒初始化,进程内只做一次)
 *
 * 【作用】保证本进程拿到 dsm_registry_dsa / dsm_registry_table 两个
 * 局部引用。第一次调用时在 DSMRegistryLock 独占锁保护下创建 DSA 与
 * dshash 表并把句柄写入共享内存的 DSMRegistryCtx;后续进程凭句柄
 * 附着。访问注册表前必须先调用本函数。
 *
 * 【设计思想】"创建者唯一"靠双保险:进程内以 dsm_registry_table
 * 是否非空做快速返回(避免反复取锁);跨进程以 DSMRegistryCtx->dshh
 * 是否仍为 DSHASH_HANDLE_INVALID 判断"是否已有人建好"。dshh 由
 * DSMRegistryShmemInit 初始化为哨兵值,创建者在持有独占锁时一次性
 * 写完两个句柄,因此读者不会看到中间状态。DSA 创建后 dsa_pin 使其
 * 在 postmaster 生命周期内存活,dsa_pin_mapping 使本进程的地址映射
 * 一直保留(即使 DSA 被其他进程放弃)。
 *
 * 【参数】arg —— 未使用。
 * 【返回值】无。
 */
static void
init_dsm_registry(void)
{
	/* Quick exit if we already did this. */
	if (dsm_registry_table)
		return;

	/* Otherwise, use a lock to ensure only one process creates the table. */
	LWLockAcquire(DSMRegistryLock, LW_EXCLUSIVE);

	if (DSMRegistryCtx->dshh == DSHASH_HANDLE_INVALID)
	{
		/* Initialize dynamic shared hash table for registry. */
		dsm_registry_dsa = dsa_create(LWTRANCHE_DSM_REGISTRY_DSA);
		dsm_registry_table = dshash_create(dsm_registry_dsa, &dsh_params, NULL);

		dsa_pin(dsm_registry_dsa);
		dsa_pin_mapping(dsm_registry_dsa);

		/* Store handles in shared memory for other backends to use. */
		DSMRegistryCtx->dsah = dsa_get_handle(dsm_registry_dsa);
		DSMRegistryCtx->dshh = dshash_get_hash_table_handle(dsm_registry_table);
	}
	else
	{
		/* Attach to existing dynamic shared hash table. */
		dsm_registry_dsa = dsa_attach(DSMRegistryCtx->dsah);
		dsa_pin_mapping(dsm_registry_dsa);
		dsm_registry_table = dshash_attach(dsm_registry_dsa, &dsh_params,
										   DSMRegistryCtx->dshh, NULL);
	}

	LWLockRelease(DSMRegistryLock);
}

/*
 * GetNamedDSMSegment - (中文)按名字获取(创建或附着)一个命名 DSM 段
 *
 * 【作用】注册表里以 name 为键"查找或插入"条目:若条目不存在则创建
 * 一个 size 大小的 DSM 段,调用 init_callback 完成用户初始化,并把段
 * 钉住(防释放、防解除映射),句柄存回条目;若已存在则校验类型与大小
 * 一致后,把段附着到当前后端(本进程已附着则直接复用)。返回段的
 * 基地址,*found 置 true 表示"已存在"、false 表示"本调用新创建"。
 *
 * 【设计思想】"只让一个后端初始化"靠 dshash 的 find_or_insert 加
 * 条目锁(整个函数持锁期间完成创建并把句柄写回,其他后端要么看到
 * 旧条目、要么在锁上等待后读到新句柄)。段被 dsm_pin_segment +
 * dsm_pin_mapping 双重钉住:即使创建者退出,注册表条目仍持有句柄,
 * 后续进程可以继续附着。
 *
 * 【参数】
 *   name         —— 段名字(不能为空、长度 < offsetof(DSMRegistryEntry,
 *                   type),保证名字定长存放下不越界);
 *   size         —— 新建段的字节数(必须非零;已存在时用于一致性校验);
 *   init_callback —— 仅"首次创建"时调用,入参为段基地址与 arg;
 *   found        —— 输出:true = 段已存在(本次仅附着);
 *   arg          —— 透传给 init_callback 的 opaque 参数。
 * 【返回值】DSM 段基地址(调用方无需另行 dsm_find_mapping)。
 */
void *
GetNamedDSMSegment(const char *name, size_t size,
				   void (*init_callback) (void *ptr, void *arg),
				   bool *found, void *arg)
{
	DSMRegistryEntry *entry;
	MemoryContext oldcontext;
	void	   *ret;
	NamedDSMState *state;
	dsm_segment *seg;

	Assert(found);

	if (!name || *name == '\0')
		ereport(ERROR,
				(errmsg("DSM segment name cannot be empty")));

	if (strlen(name) >= offsetof(DSMRegistryEntry, type))
		ereport(ERROR,
				(errmsg("DSM segment name too long")));

	if (size == 0)
		ereport(ERROR,
				(errmsg("DSM segment size must be nonzero")));

	/* Be sure any local memory allocated by DSM/DSA routines is persistent. */
	oldcontext = MemoryContextSwitchTo(TopMemoryContext);

	/* Connect to the registry. */
	init_dsm_registry();

	entry = dshash_find_or_insert(dsm_registry_table, name, found);
	state = &entry->dsm;
	if (!(*found))
	{
		entry->type = DSMR_ENTRY_TYPE_DSM;
		state->handle = DSM_HANDLE_INVALID;
		state->size = size;
	}
	else if (entry->type != DSMR_ENTRY_TYPE_DSM)
		ereport(ERROR,
				(errmsg("requested DSM segment does not match type of existing entry")));
	else if (state->size != size)
		ereport(ERROR,
				(errmsg("requested DSM segment size does not match size of existing segment")));

	if (state->handle == DSM_HANDLE_INVALID)
	{
		*found = false;

		/* Initialize the segment. */
		seg = dsm_create(size, 0);

		if (init_callback)
			(*init_callback) (dsm_segment_address(seg), arg);

		dsm_pin_segment(seg);
		dsm_pin_mapping(seg);
		state->handle = dsm_segment_handle(seg);
	}
	else
	{
		/* If the existing segment is not already attached, attach it now. */
		seg = dsm_find_mapping(state->handle);
		if (seg == NULL)
		{
			seg = dsm_attach(state->handle);
			if (seg == NULL)
				elog(ERROR, "could not map dynamic shared memory segment");

			dsm_pin_mapping(seg);
		}
	}

	ret = dsm_segment_address(seg);
	dshash_release_lock(dsm_registry_table, entry);
	MemoryContextSwitchTo(oldcontext);

	return ret;
}

/*
 * GetNamedDSA - (中文)按名字获取(创建或附着)一个命名 DSA 区域
 *
 * 【作用】注册表里以 name 为键查找条目:不存在则先为该 DSA 分配一个
 * 专属 LWLock tranche(注册为 name),再 dsa_create 建区域并双重钉住,
 * 句柄写回条目;已存在则把区域附着到当前后端。返回 dsa_area 指针,
 * *found 置 true 表示"已存在"。注意:每个后端对同一名字最多调用
 * 一次——若本进程已经附着过该区域则报错。
 *
 * 【设计思想】tranche 与区域一样"谁先来谁创建":tranche 是否为 -1
 * 与 handle 是否无效分别表示"未分配/未创建",并在持条目锁期间完成
 * 写入,保证并发下只初始化一次。DSA 句柄也存进注册表,故其他进程
 * 无需事先知道句柄即可附着。
 *
 * 【参数】
 *   name  —— 区域名字(非空、长度受限);
 *   found —— 输出:true = 区域已存在(本次仅附着)。
 * 【返回值】dsa_area 指针;失败(类型冲突、重复附着)报 ERROR。
 */
dsa_area *
GetNamedDSA(const char *name, bool *found)
{
	DSMRegistryEntry *entry;
	MemoryContext oldcontext;
	dsa_area   *ret;
	NamedDSAState *state;

	Assert(found);

	if (!name || *name == '\0')
		ereport(ERROR,
				(errmsg("DSA name cannot be empty")));

	if (strlen(name) >= offsetof(DSMRegistryEntry, type))
		ereport(ERROR,
				(errmsg("DSA name too long")));

	/* Be sure any local memory allocated by DSM/DSA routines is persistent. */
	oldcontext = MemoryContextSwitchTo(TopMemoryContext);

	/* Connect to the registry. */
	init_dsm_registry();

	entry = dshash_find_or_insert(dsm_registry_table, name, found);
	state = &entry->dsa;
	if (!(*found))
	{
		entry->type = DSMR_ENTRY_TYPE_DSA;
		state->handle = DSA_HANDLE_INVALID;
		state->tranche = -1;
	}
	else if (entry->type != DSMR_ENTRY_TYPE_DSA)
		ereport(ERROR,
				(errmsg("requested DSA does not match type of existing entry")));

	if (state->tranche == -1)
	{
		*found = false;

		/* Initialize the LWLock tranche for the DSA. */
		state->tranche = LWLockNewTrancheId(name);
	}

	if (state->handle == DSA_HANDLE_INVALID)
	{
		*found = false;

		/* Initialize the DSA. */
		ret = dsa_create(state->tranche);
		dsa_pin(ret);
		dsa_pin_mapping(ret);

		/* Store handle for other backends to use. */
		state->handle = dsa_get_handle(ret);
	}
	else if (dsa_is_attached(state->handle))
		ereport(ERROR,
				(errmsg("requested DSA already attached to current process")));
	else
	{
		/* Attach to existing DSA. */
		ret = dsa_attach(state->handle);
		dsa_pin_mapping(ret);
	}

	dshash_release_lock(dsm_registry_table, entry);
	MemoryContextSwitchTo(oldcontext);

	return ret;
}

/*
 * GetNamedDSHash - (中文)按名字获取(创建或附着)一个命名 dshash 表
 *
 * 【作用】注册表里以 name 为键查找条目:不存在则分配专属 tranche、
 * 创建承载的 DSA、用 params 创建哈希表(忽略其 tranche_id,改用
 * 注册表分配的),双重钉住后把两个句柄写回条目;已存在则附着 DSA 并
 * 依句柄附着哈希表。返回 dshash_table 指针,*found 置 true 表示
 * "已存在"。注意:每个后端对同一名字最多调用一次(重复附着报错)。
 *
 * 【参数】
 *   name   —— 表名字(非空、长度受限);
 *   params —— 建表参数:创建时使用(键布局、比较函数等);附着时也
 *             传入以便 dshash_attach 校验布局,tranche_id 字段在两种
 *             情况下都被忽略;
 *   found  —— 输出:true = 表已存在(本次仅附着)。
 * 【返回值】dshash_table 指针;失败(类型冲突、重复附着)报 ERROR。
 */
dshash_table *
GetNamedDSHash(const char *name, const dshash_parameters *params, bool *found)
{
	DSMRegistryEntry *entry;
	MemoryContext oldcontext;
	dshash_table *ret;
	NamedDSHState *dsh_state;

	Assert(params);
	Assert(found);

	if (!name || *name == '\0')
		ereport(ERROR,
				(errmsg("DSHash name cannot be empty")));

	if (strlen(name) >= offsetof(DSMRegistryEntry, type))
		ereport(ERROR,
				(errmsg("DSHash name too long")));

	/* Be sure any local memory allocated by DSM/DSA routines is persistent. */
	oldcontext = MemoryContextSwitchTo(TopMemoryContext);

	/* Connect to the registry. */
	init_dsm_registry();

	entry = dshash_find_or_insert(dsm_registry_table, name, found);
	dsh_state = &entry->dsh;
	if (!(*found))
	{
		entry->type = DSMR_ENTRY_TYPE_DSH;
		dsh_state->dsa_handle = DSA_HANDLE_INVALID;
		dsh_state->dsh_handle = DSHASH_HANDLE_INVALID;
		dsh_state->tranche = -1;
	}
	else if (entry->type != DSMR_ENTRY_TYPE_DSH)
		ereport(ERROR,
				(errmsg("requested DSHash does not match type of existing entry")));

	if (dsh_state->tranche == -1)
	{
		*found = false;

		/* Initialize the LWLock tranche for the hash table. */
		dsh_state->tranche = LWLockNewTrancheId(name);
	}

	if (dsh_state->dsa_handle == DSA_HANDLE_INVALID)
	{
		dshash_parameters params_copy;
		dsa_area   *dsa;

		*found = false;

		/* Initialize the DSA for the hash table. */
		dsa = dsa_create(dsh_state->tranche);

		/* Initialize the dshash table. */
		memcpy(&params_copy, params, sizeof(dshash_parameters));
		params_copy.tranche_id = dsh_state->tranche;
		ret = dshash_create(dsa, &params_copy, NULL);

		dsa_pin(dsa);
		dsa_pin_mapping(dsa);

		/* Store handles for other backends to use. */
		dsh_state->dsa_handle = dsa_get_handle(dsa);
		dsh_state->dsh_handle = dshash_get_hash_table_handle(ret);
	}
	else if (dsa_is_attached(dsh_state->dsa_handle))
		ereport(ERROR,
				(errmsg("requested DSHash already attached to current process")));
	else
	{
		dsa_area   *dsa;

		/* XXX: Should we verify params matches what table was created with? */

		/* Attach to existing DSA for the hash table. */
		dsa = dsa_attach(dsh_state->dsa_handle);
		dsa_pin_mapping(dsa);

		/* Attach to existing dshash table. */
		ret = dshash_attach(dsa, params, dsh_state->dsh_handle, NULL);
	}

	dshash_release_lock(dsm_registry_table, entry);
	MemoryContextSwitchTo(oldcontext);

	return ret;
}

/*
 * pg_get_dsm_registry_allocations - (中文)系统函数:列出注册表全部命名对象的占用
 *
 * 【作用】实现 pg_dsm_registry 视图(initdb 内置系统函数,无参):
 * 顺序遍历注册表 dshash 的全部条目,输出三列——name(名字)、type
 * (segment/area/hash 的显示名)、size(字节数)。size 只对"已初始化"
 * 的条目返回:DSA/dshash 用 dsa_get_total_size_from_handle 统计承载
 * DSA 的总大小;段则直接返回注册的 size;尚未初始化的条目该列为 NULL。
 *
 * 【设计思想】用于运维诊断:检查运行期动态共享内存都被哪些命名对象
 * 占用、各占多少。因表条目由注册表自身钉住、不会凭空消失,遍历时
 * 无需上锁(顺序扫描按条目粒度加分区锁,由 dshash 序列化 API 保证)。
 * 结果集经 tuplestore 物化输出(InitMaterializedSRF),内存上下文切换
 * 到 TopMemoryContext 保证遍历期间 dshash 分配的内存不被清理。
 *
 * 【参数】PG_FUNCTION_ARGS(标准 V1 调用框架,无输入参数)。
 * 【返回值】Datum 0(物化 SRF 约定;实际结果经 rsinfo 输出)。
 */
Datum
pg_get_dsm_registry_allocations(PG_FUNCTION_ARGS)
{
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	DSMRegistryEntry *entry;
	MemoryContext oldcontext;
	dshash_seq_status status;

	InitMaterializedSRF(fcinfo, MAT_SRF_USE_EXPECTED_DESC);

	/* Be sure any local memory allocated by DSM/DSA routines is persistent. */
	oldcontext = MemoryContextSwitchTo(TopMemoryContext);
	init_dsm_registry();
	MemoryContextSwitchTo(oldcontext);

	dshash_seq_init(&status, dsm_registry_table, false);
	while ((entry = dshash_seq_next(&status)) != NULL)
	{
		Datum		vals[3];
		bool		nulls[3] = {0};

		vals[0] = CStringGetTextDatum(entry->name);
		vals[1] = CStringGetTextDatum(DSMREntryTypeNames[entry->type]);

		/* Be careful to only return the sizes of initialized entries. */
		if (entry->type == DSMR_ENTRY_TYPE_DSM &&
			entry->dsm.handle != DSM_HANDLE_INVALID)
			vals[2] = Int64GetDatum(entry->dsm.size);
		else if (entry->type == DSMR_ENTRY_TYPE_DSA &&
				 entry->dsa.handle != DSA_HANDLE_INVALID)
			vals[2] = Int64GetDatum(dsa_get_total_size_from_handle(entry->dsa.handle));
		else if (entry->type == DSMR_ENTRY_TYPE_DSH &&
				 entry->dsh.dsa_handle != DSA_HANDLE_INVALID)
			vals[2] = Int64GetDatum(dsa_get_total_size_from_handle(entry->dsh.dsa_handle));
		else
			nulls[2] = true;

		tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc, vals, nulls);
	}
	dshash_seq_term(&status);

	return (Datum) 0;
}
