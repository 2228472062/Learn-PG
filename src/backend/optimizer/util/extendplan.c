/*-------------------------------------------------------------------------
 *
 * extendplan.c
 *	  Extend core planner objects with additional private state
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994-5, Regents of the University of California
 *
 * The interfaces defined in this file make it possible for loadable
 * modules to store their own private state inside of key planner data
 * structures -- specifically, the PlannerGlobal, PlannerInfo, and
 * RelOptInfo structures. This can make it much easier to write
 * reasonably efficient planner extensions; for instance, code that
 * uses set_join_pathlist_hook can arrange to compute a key intermediate
 * result once per joinrel rather than on every call.
 *
 * 【模块总览(中文)】
 * 本文件为"可加载规划器扩展"提供基础设施:允许外部模块(如 extension)
 * 在规划器关键数据结构——PlannerGlobal、PlannerInfo、RelOptInfo——内部
 * 保存自己的私有状态,而不必修改 PostgreSQL 核心代码。
 *
 * 【设计思想】
 * 规划器在规划过程中会反复构建/销毁这些结构(尤其是 RelOptInfo,每个
 * join 关系都会新建一个),若扩展需要在其中保存中间计算结果(例如
 * set_join_pathlist_hook 中某个关键中间结果只算一次),就必须有地方存放。
 * 本文件在每个结构里维护一个"扩展状态数组"(void * 数组),并用一个
 * 字符串名字映射到整数 ID:扩展先调用 GetPlannerExtensionId 拿到稳定 ID,
 * 再调用 SetPlannerGlobalExtensionState 等把私有指针塞进数组对应槽位。
 *
 * 【核心数据结构】
 * - 静态全局数组 PlannerExtensionNameArray:进程内"扩展名 → ID"的映射表,
 *   保存在 TopMemoryContext,后端进程生命周期内名字到 ID 的映射恒定;
 * - PlannerGlobal.extension_state / PlannerInfo.extension_state /
 *   RelOptInfo.extension_state:三个指针数组,分别按 ID 存放扩展私有状态。
 *
 * 【主要函数关系】
 * GetPlannerExtensionId 负责"名字 → ID"映射;三个 SetXxxExtensionState
 * 函数负责把私有状态写入对应结构的扩展状态数组。数组按需惰性创建,并在
 * 装满时用 pg_nextpower2_32 按 2 的幂扩容。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/util/extendplan.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "optimizer/extendplan.h"
#include "port/pg_bitutils.h"
#include "utils/memutils.h"

static const char **PlannerExtensionNameArray = NULL;
static int	PlannerExtensionNamesAssigned = 0;
static int	PlannerExtensionNamesAllocated = 0;

/*
 * Map the name of a planner extension to an integer ID.
 *
 * Within the lifetime of a particular backend, the same name will be mapped
 * to the same ID every time. IDs are not stable across backends. Use the ID
 * that you get from this function to call the remaining functions in this
 * file.
 */
/*
 * GetPlannerExtensionId - (中文)把扩展名字映射为一个整型 ID
 *
 * 【作用】在规划期间为"可加载扩展"分配/查找到一个整数 ID。后端进程
 * 内同一名字永远映射到同一 ID(进程间不稳定)。扩展先用本函数取得 ID,
 * 再用该 ID 调用本文件其余函数把私有状态写入规划器结构。
 *
 * 【设计思想】用静态全局数组 PlannerExtensionNameArray 保存进程内所有
 * 已注册的扩展名。线性扫描匹配名字,命中即返回下标;未命中则分配新槽位。
 * 数组惰性创建(首次使用时分配 16 项),装满时按 2 的幂扩容(用
 * pg_nextpower2_32 计算新容量)。名字指针由调用者持有(通常指向静态
 * 字符串),本函数不复制、也不负责释放,故数组存 const char * 即可。
 *
 * 【参数】extension_name —— 扩展的名字(C 字符串),用于查找/登记。
 * 【返回值】与 extension_name 对应的整型 ID(非负)。
 */
int
GetPlannerExtensionId(const char *extension_name)
{
	/* Search for an existing extension by this name; if found, return ID. */
	for (int i = 0; i < PlannerExtensionNamesAssigned; ++i)
		if (strcmp(PlannerExtensionNameArray[i], extension_name) == 0)
			return i;

	/* If there is no array yet, create one. */
	if (PlannerExtensionNameArray == NULL)
	{
		PlannerExtensionNamesAllocated = 16;
		PlannerExtensionNameArray = (const char **)
			MemoryContextAlloc(TopMemoryContext,
							   PlannerExtensionNamesAllocated
							   * sizeof(char *));
	}

	/* If there's an array but it's currently full, expand it. */
	if (PlannerExtensionNamesAssigned >= PlannerExtensionNamesAllocated)
	{
		int			i = pg_nextpower2_32(PlannerExtensionNamesAssigned + 1);

		PlannerExtensionNameArray = (const char **)
			repalloc(PlannerExtensionNameArray, i * sizeof(char *));
		PlannerExtensionNamesAllocated = i;
	}

	/* Assign and return new ID. */
	PlannerExtensionNameArray[PlannerExtensionNamesAssigned] = extension_name;
	return PlannerExtensionNamesAssigned++;
}

/*
 * Store extension-specific state into a PlannerGlobal.
 */
/*
 * SetPlannerGlobalExtensionState - (中文)把扩展私有状态写入 PlannerGlobal
 *
 * 【作用】把 opaque 指针存入 glob->extension_state[extension_id] 槽位,
 * 供本后端进程后续规划阶段使用。PlannerGlobal 贯穿整个规划过程并在
 * 顶层查询及其所有子计划间共享,因此存在这里的状态会被所有子查询看到。
 *
 * 【设计思想】与 SetPlannerInfoExtensionState / SetRelOptInfoExtensionState
 * 是同一模式:若数组尚不存在则惰性创建(初始容量 Max(4, 下一个 2 的幂)),
 * 装满时用 repalloc0_array 扩容并把新区域清零。数组用 void * 数组实现,
 * 任何扩展都能把自己的私有对象指针塞进去。注意内存分配上下文取
 * GetMemoryChunkContext(glob),即与 PlannerGlobal 本身相同的上下文,
 * 生命周期与 PlannerGlobal 一致。
 *
 * 【参数】
 *   glob         —— 目标 PlannerGlobal 结构;
 *   extension_id —— 由 GetPlannerExtensionId 获得的扩展 ID(须 >= 0);
 *   opaque       —— 扩展私有状态指针(可为 NULL)。
 * 【返回值】无。
 */
void
SetPlannerGlobalExtensionState(PlannerGlobal *glob, int extension_id,
							   void *opaque)
{
	Assert(extension_id >= 0);

	/* If there is no array yet, create one. */
	if (glob->extension_state == NULL)
	{
		MemoryContext planner_cxt;
		Size		sz;

		planner_cxt = GetMemoryChunkContext(glob);
		glob->extension_state_allocated =
			Max(4, pg_nextpower2_32(extension_id + 1));
		sz = glob->extension_state_allocated * sizeof(void *);
		glob->extension_state = MemoryContextAllocZero(planner_cxt, sz);
	}

	/* If there's an array but it's currently full, expand it. */
	if (extension_id >= glob->extension_state_allocated)
	{
		int			i;

		i = pg_nextpower2_32(extension_id + 1);
		glob->extension_state = repalloc0_array(glob->extension_state, void *,
												glob->extension_state_allocated, i);
		glob->extension_state_allocated = i;
	}

	glob->extension_state[extension_id] = opaque;
}

/*
 * Store extension-specific state into a PlannerInfo.
 */
/*
 * SetPlannerInfoExtensionState - (中文)把扩展私有状态写入 PlannerInfo
 *
 * 【作用】把 opaque 指针存入 root->extension_state[extension_id] 槽位。
 * PlannerInfo 描述单个查询层的规划上下文,因此存在这里的状态只在该
 * 查询层(及其子规划过程)内可见;不同查询层有各自的 PlannerInfo。
 *
 * 【设计思想】与 SetPlannerGlobalExtensionState 完全同构,区别仅在于
 * 分配上下文取 root->planner_cxt(该查询层专用的规划内存上下文),这样
 * 状态随该层规划结束被整体回收,无需逐项释放。
 *
 * 【参数】
 *   root         —— 目标 PlannerInfo;
 *   extension_id —— 扩展 ID(须 >= 0);
 *   opaque       —— 扩展私有状态指针(可为 NULL)。
 * 【返回值】无。
 */
void
SetPlannerInfoExtensionState(PlannerInfo *root, int extension_id,
							 void *opaque)
{
	Assert(extension_id >= 0);

	/* If there is no array yet, create one. */
	if (root->extension_state == NULL)
	{
		Size		sz;

		root->extension_state_allocated =
			Max(4, pg_nextpower2_32(extension_id + 1));
		sz = root->extension_state_allocated * sizeof(void *);
		root->extension_state = MemoryContextAllocZero(root->planner_cxt, sz);
	}

	/* If there's an array but it's currently full, expand it. */
	if (extension_id >= root->extension_state_allocated)
	{
		int			i;

		i = pg_nextpower2_32(extension_id + 1);
		root->extension_state = repalloc0_array(root->extension_state, void *,
												root->extension_state_allocated, i);
		root->extension_state_allocated = i;
	}

	root->extension_state[extension_id] = opaque;
}

/*
 * Store extension-specific state into a RelOptInfo.
 */
/*
 * SetRelOptInfoExtensionState - (中文)把扩展私有状态写入 RelOptInfo
 *
 * 【作用】把 opaque 指针存入 rel->extension_state[extension_id] 槽位。
 * RelOptInfo 是单个(基表或连接)关系的规划元数据;连接关系是规划过程
 * 中按需反复创建的,若扩展在每个 joinrel 上都保存一次中间结果,就可
 * 避免重复计算(这正是本文件头注释举例的 set_join_pathlist_hook 场景)。
 *
 * 【设计思想】与 SetPlannerGlobalExtensionState 同构,分配上下文取
 * GetMemoryChunkContext(rel),即与该 RelOptInfo 相同的内存上下文,随其
 * 一并回收。
 *
 * 【参数】
 *   rel          —— 目标 RelOptInfo;
 *   extension_id —— 扩展 ID(须 >= 0);
 *   opaque       —— 扩展私有状态指针(可为 NULL)。
 * 【返回值】无。
 */
void
SetRelOptInfoExtensionState(RelOptInfo *rel, int extension_id,
							void *opaque)
{
	Assert(extension_id >= 0);

	/* If there is no array yet, create one. */
	if (rel->extension_state == NULL)
	{
		MemoryContext planner_cxt;
		Size		sz;

		planner_cxt = GetMemoryChunkContext(rel);
		rel->extension_state_allocated =
			Max(4, pg_nextpower2_32(extension_id + 1));
		sz = rel->extension_state_allocated * sizeof(void *);
		rel->extension_state = MemoryContextAllocZero(planner_cxt, sz);
	}

	/* If there's an array but it's currently full, expand it. */
	if (extension_id >= rel->extension_state_allocated)
	{
		int			i;

		i = pg_nextpower2_32(extension_id + 1);
		rel->extension_state = repalloc0_array(rel->extension_state, void *,
											   rel->extension_state_allocated, i);
		rel->extension_state_allocated = i;
	}

	rel->extension_state[extension_id] = opaque;
}
