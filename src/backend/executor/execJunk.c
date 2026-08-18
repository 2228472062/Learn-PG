/*-------------------------------------------------------------------------
 *
 * execJunk.c
 *	  Junk attribute support stuff....
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execJunk.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execJunk.c —— "垃圾属性"（junk attribute）过滤机制
 * ----------------------------------------------------------------------------
 * 业务含义：
 *   执行器内部元组里有一部分列是"给执行器自己用的、绝不出门"的数据，
 *   称为 junk 属性：例如系统列 ctid（UPDATE/DELETE 定位行用）、子查询
 *   内部用的排序键/分组键列、SELECT DISTINCT 的重分组列等。它们仍随
 *   计划节点到处传递，但在最外层输出、或写入磁盘前必须被剥掉。
 *
 * 实现思路（JunkFilter）：
 *   - 顶层初始化时用 ExecInitJunkFilter 依据 targetlist 建过滤对象：
 *     由非 junk 项生成"干净"元组描述符，并计算映射表 cleanMap
 *     （clean 第 i 列 ← 原元组第 cleanMap[i] 列）；
 *   - 输出前用 ExecFilterJunk 按映射表把数据"转置"成一个不含 junk 列的
 *     虚拟槽（纯内存搬运，无元组重组）；
 *   - 需要取某个 junk 列的值时用 ExecFindJunkAttribute（按 resname 找
 *     resno，如 "ctid"/"junk_sort"）再 slot_getattr 读取。
 *
 * 变体：ExecInitJunkFilterConversion 用于"行类型转换"场景——干净描述符
 * 由调用方给定（可含已删除列，映射为 NULL 输出），用于触发器新旧行
 * 转换等场合。
 * ============================================================================
 */
#include "postgres.h"

#include "executor/executor.h"

/*-------------------------------------------------------------------------
 *		XXX this stuff should be rewritten to take advantage
 *			of ExecProject() and the ProjectionInfo node.
 *			-cim 6/3/91
 *
 * An attribute of a tuple living inside the executor, can be
 * either a normal attribute or a "junk" attribute. "junk" attributes
 * never make it out of the executor, i.e. they are never printed,
 * returned or stored on disk. Their only purpose in life is to
 * store some information useful only to the executor, mainly the values
 * of system attributes like "ctid", or sort key columns that are not to
 * be output.
 *
 * The general idea is the following: A target list consists of a list of
 * TargetEntry nodes containing expressions. Each TargetEntry has a field
 * called 'resjunk'. If the value of this field is true then the
 * corresponding attribute is a "junk" attribute.
 *
 * When we initialize a plan we call ExecInitJunkFilter to create a filter.
 *
 * We then execute the plan, treating the resjunk attributes like any others.
 *
 * Finally, when at the top level we get back a tuple, we can call
 * ExecFindJunkAttribute/ExecGetJunkAttribute to retrieve the values of the
 * junk attributes we are interested in, and ExecFilterJunk to remove all the
 * junk attributes from a tuple.  This new "clean" tuple is then printed,
 * inserted, or updated.
 *
 *-------------------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】ExecInitJunkFilter —— 建立 junk 过滤器
 * ----------------------------------------------------------------------------
 * 参数：
 *   targetList：源计划的 targetlist（junk 项由 tle->resjunk 标识）；
 *   slot：可选——调用方预置的结果槽，否则内部新建虚拟槽。
 * 返回：JunkFilter{干净描述符, 映射表, 结果槽}。
 *
 * 映射表语义：cleanMap[clean第i列] = 原元组属性号（tle->resno）。
 * 注意"干净长度"来自 ExecCleanTypeFromTL（剔除 junk 项后重建描述符），
 * 与"非 junk 项个数"严格一致（断言校验）。
 * ============================================================================
 */
JunkFilter *
ExecInitJunkFilter(List *targetList, TupleTableSlot *slot)
{
	JunkFilter *junkfilter;
	TupleDesc	cleanTupType;
	int			cleanLength;
	AttrNumber *cleanMap;

	/*
	 * Compute the tuple descriptor for the cleaned tuple.
	 */
	cleanTupType = ExecCleanTypeFromTL(targetList);

	/*
	 * Use the given slot, or make a new slot if we weren't given one.
	 */
	if (slot)
		ExecSetSlotDescriptor(slot, cleanTupType);
	else
		slot = MakeSingleTupleTableSlot(cleanTupType, &TTSOpsVirtual);

	/*
	 * Now calculate the mapping between the original tuple's attributes and
	 * the "clean" tuple's attributes.
	 *
	 * The "map" is an array of "cleanLength" attribute numbers, i.e. one
	 * entry for every attribute of the "clean" tuple. The value of this entry
	 * is the attribute number of the corresponding attribute of the
	 * "original" tuple.  (Zero indicates a NULL output attribute, but we do
	 * not use that feature in this routine.)
	 */
	cleanLength = cleanTupType->natts;
	if (cleanLength > 0)
	{
		AttrNumber	cleanResno;
		ListCell   *t;

		cleanMap = (AttrNumber *) palloc(cleanLength * sizeof(AttrNumber));
		cleanResno = 0;
		foreach(t, targetList)
		{
			TargetEntry *tle = lfirst(t);

			if (!tle->resjunk)
			{
				cleanMap[cleanResno] = tle->resno;
				cleanResno++;
			}
		}
		Assert(cleanResno == cleanLength);
	}
	else
		cleanMap = NULL;

	/*
	 * Finally create and initialize the JunkFilter struct.
	 */
	junkfilter = makeNode(JunkFilter);

	junkfilter->jf_targetList = targetList;
	junkfilter->jf_cleanTupType = cleanTupType;
	junkfilter->jf_cleanMap = cleanMap;
	junkfilter->jf_resultSlot = slot;

	return junkfilter;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitJunkFilterConversion —— 行类型转换版过滤器
 * ----------------------------------------------------------------------------
 * 差异点：
 *   干净描述符不推导，由调用方直接给定（cleanTupType，可能含已删除列）；
 *   调用方须自行保证"非删除列与非 junk 项逐列对应"。映射表用 palloc0
 *   初始化——已删除列映射保持 0，ExecFilterJunk 见 0 即输出 NULL。
 *
 * 业务场景：触发器行类型转换（RI 触发器新旧行 → 目标表行类型）等
 * "原行类型 → 目标行类型"的搬运。
 * ============================================================================
 */
JunkFilter *
ExecInitJunkFilterConversion(List *targetList,
							 TupleDesc cleanTupType,
							 TupleTableSlot *slot)
{
	JunkFilter *junkfilter;
	int			cleanLength;
	AttrNumber *cleanMap;
	ListCell   *t;
	int			i;

	/*
	 * Use the given slot, or make a new slot if we weren't given one.
	 */
	if (slot)
		ExecSetSlotDescriptor(slot, cleanTupType);
	else
		slot = MakeSingleTupleTableSlot(cleanTupType, &TTSOpsVirtual);

	/*
	 * Calculate the mapping between the original tuple's attributes and the
	 * "clean" tuple's attributes.
	 *
	 * The "map" is an array of "cleanLength" attribute numbers, i.e. one
	 * entry for every attribute of the "clean" tuple. The value of this entry
	 * is the attribute number of the corresponding attribute of the
	 * "original" tuple.  We store zero for any deleted attributes, marking
	 * that a NULL is needed in the output tuple.
	 */
	cleanLength = cleanTupType->natts;
	if (cleanLength > 0)
	{
		cleanMap = (AttrNumber *) palloc0(cleanLength * sizeof(AttrNumber));
		t = list_head(targetList);
		for (i = 0; i < cleanLength; i++)
		{
			if (TupleDescCompactAttr(cleanTupType, i)->attisdropped)
				continue;		/* map entry is already zero */
			for (;;)
			{
				TargetEntry *tle = lfirst(t);

				t = lnext(targetList, t);
				if (!tle->resjunk)
				{
					cleanMap[i] = tle->resno;
					break;
				}
			}
		}
	}
	else
		cleanMap = NULL;

	/*
	 * Finally create and initialize the JunkFilter struct.
	 */
	junkfilter = makeNode(JunkFilter);

	junkfilter->jf_targetList = targetList;
	junkfilter->jf_cleanTupType = cleanTupType;
	junkfilter->jf_cleanMap = cleanMap;
	junkfilter->jf_resultSlot = slot;

	return junkfilter;
}

/*
 * ============================================================================
 * 【中文注释】ExecFindJunkAttribute / ExecFindJunkAttributeInTlist —— 定位 junk 列
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   按 resname 在 targetlist 里找 junk 列，返回其 resno（供 slot_getattr
 *   使用）；找不到返回 InvalidAttrNumber。命名规范：junk 列的名字由规划器
 *   固定给出（"ctid"、"junk_sort"、"junk_filter" 等）。
 * ExecFindJunkAttribute 走过滤器内的 tlist；InTlist 版本可直接用于任意
 * 子计划的 tlist（无需先建 JunkFilter）。
 * ============================================================================
 */
AttrNumber
ExecFindJunkAttribute(JunkFilter *junkfilter, const char *attrName)
{
	return ExecFindJunkAttributeInTlist(junkfilter->jf_targetList, attrName);
}

/*
 * ExecFindJunkAttributeInTlist
 *
 * Find a junk attribute given a subplan's targetlist (not necessarily
 * part of a JunkFilter).
 */
AttrNumber
ExecFindJunkAttributeInTlist(List *targetlist, const char *attrName)
{
	ListCell   *t;

	foreach(t, targetlist)
	{
		TargetEntry *tle = lfirst(t);

		if (tle->resjunk && tle->resname &&
			(strcmp(tle->resname, attrName) == 0))
		{
			/* We found it ! */
			return tle->resno;
		}
	}

	return InvalidAttrNumber;
}

/*
 * ============================================================================
 * 【中文注释】ExecFilterJunk —— 剥掉 junk 列，产出"干净"槽
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把含 junk 列的原槽按映射表转置到结果槽，返回"干净虚拟元组"。
 *   零拷贝：只做数组级 Datum 搬运（slot_getallattrs 解出全部列后按
 *   cleanMap 拷贝 values/isnull 对），最后 ExecStoreVirtualTuple 定稿。
 * ============================================================================
 */
TupleTableSlot *
ExecFilterJunk(JunkFilter *junkfilter, TupleTableSlot *slot)
{
	TupleTableSlot *resultSlot;
	AttrNumber *cleanMap;
	TupleDesc	cleanTupType;
	int			cleanLength;
	int			i;
	Datum	   *values;
	bool	   *isnull;
	Datum	   *old_values;
	bool	   *old_isnull;

	/*
	 * Extract all the values of the old tuple.
	 */
	slot_getallattrs(slot);
	old_values = slot->tts_values;
	old_isnull = slot->tts_isnull;

	/*
	 * get info from the junk filter
	 */
	cleanTupType = junkfilter->jf_cleanTupType;
	cleanLength = cleanTupType->natts;
	cleanMap = junkfilter->jf_cleanMap;
	resultSlot = junkfilter->jf_resultSlot;

	/*
	 * Prepare to build a virtual result tuple.
	 */
	ExecClearTuple(resultSlot);
	values = resultSlot->tts_values;
	isnull = resultSlot->tts_isnull;

	/*
	 * Transpose data into proper fields of the new tuple.
	 */
	for (i = 0; i < cleanLength; i++)
	{
		int			j = cleanMap[i];

		if (j == 0)
		{
			values[i] = (Datum) 0;
			isnull[i] = true;
		}
		else
		{
			values[i] = old_values[j - 1];
			isnull[i] = old_isnull[j - 1];
		}
	}

	/*
	 * And return the virtual tuple.
	 */
	return ExecStoreVirtualTuple(resultSlot);
}
