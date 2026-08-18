/*-------------------------------------------------------------------------
 *
 * execTuples.c
 *	  Routines dealing with TupleTableSlots.  These are used for resource
 *	  management associated with tuples (eg, releasing buffer pins for
 *	  tuples in disk buffers, or freeing the memory occupied by transient
 *	  tuples).  Slots also provide access abstraction that lets us implement
 *	  "virtual" tuples to reduce data-copying overhead.
 *
 *	  Routines dealing with the type information for tuples. Currently,
 *	  the type information for a tuple is an array of FormData_pg_attribute.
 *	  This information is needed by routines manipulating tuples
 *	  (getattribute, formtuple, etc.).
 *
 *
 *	 EXAMPLE OF HOW TABLE ROUTINES WORK
 *		Suppose we have a query such as SELECT emp.name FROM emp and we have
 *		a single SeqScan node in the query plan.
 *
 *		At ExecutorStart()
 *		----------------
 *
 *		- ExecInitSeqScan() calls ExecInitScanTupleSlot() to construct a
 *		  TupleTableSlots for the tuples returned by the access method, and
 *		  ExecInitResultTypeTL() to define the node's return
 *		  type. ExecAssignScanProjectionInfo() will, if necessary, create
 *		  another TupleTableSlot for the tuples resulting from performing
 *		  target list projections.
 *
 *		During ExecutorRun()
 *		----------------
 *		- SeqNext() calls ExecStoreBufferHeapTuple() to place the tuple
 *		  returned by the access method into the scan tuple slot.
 *
 *		- ExecSeqScan() (via ExecScan), if necessary, calls ExecProject(),
 *		  putting the result of the projection in the result tuple slot. If
 *		  not necessary, it directly returns the slot returned by SeqNext().
 *
 *		- ExecutePlan() calls the output function.
 *
 *		The important thing to watch in the executor code is how pointers
 *		to the slots containing tuples are passed instead of the tuples
 *		themselves.  This facilitates the communication of related information
 *		(such as whether or not a tuple should be pfreed, what buffer contains
 *		this tuple, the tuple's tuple descriptor, etc).  It also allows us
 *		to avoid physically constructing projection tuples in many cases.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execTuples.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * ============================================================================
 * 【中文注释】execTuples.c —— 元组表槽（TupleTableSlot）机制总览
 * ----------------------------------------------------------------------------
 * 文件定位：
 *   执行器的"元组容器"基础设施层。执行器内部从不直接传递裸元组指针，
 *   而是把元组"塞进"一个 TupleTableSlot（元组表槽）再传递槽指针。槽统一
 *   承载三类信息：
 *     1) 元组所属的表（tts_tableOid）、行标识（tts_tid）、元组描述符
 *        （tts_tupleDescriptor，列类型/名字/约束）；
 *     2) 已解（deform）出的列值数组 tts_values[] 与 NULL 标记 tts_isnull[]
 *        （"虚拟元组"视图，避免反复物理解包）；
 *     3) 资源归属（buffer pin、内存该谁释放、何时释放）。
 *
 * 四种槽实现（多态，通过 TupleTableSlotOps 函数指针表分发）：
 *   - TTSOpsVirtual（虚拟槽）        ：只含 Datum/isnull 数组，无物理元组，
 *       投影等中间结果的首选，最大限度避免拷贝；
 *   - TTSOpsHeapTuple（堆元组槽）     ：持有完整的 HeapTuple（含系统列），
 *       元组内存可由槽负责释放（SHOULDFREE 标志）；
 *   - TTSOpsMinimalTuple（最小元组槽）：持有 MinimalTuple（去掉了系统列的
 *       轻量表示，用于排序/物化等中间结果）；
 *   - TTSOpsBufferHeapTuple（缓冲槽） ：指向磁盘缓冲页内的元组并持有该页的
 *       buffer pin，实现"零拷贝"扫描（扫描到哪行就 pin 哪页）。
 *
 * 设计思想：
 *   - 懒解包（deform-on-demand）：槽先只持有物理元组，tts_nvalid 记录已解
 *     出多少列；调用方要哪一列才解到那一列，且增量续解不重算；
 *   - 惰性物化（materialize）：需要元组独立于底层存储时（如离开 buffer、
 *     跨上下文使用）再拷到槽自己的内存上下文并置 SHOULDFREE；
 *   - 不要裸 pfree 元组：用 ExecClearTuple 清槽，从而正确处理 pin 释放、
 *     内存释放与标志复位。
 * ============================================================================
 */
#include "postgres.h"

#include "access/heaptoast.h"
#include "access/htup_details.h"
#include "access/tupdesc_details.h"
#include "access/xact.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "nodes/nodeFuncs.h"
#include "storage/bufmgr.h"
#include "utils/builtins.h"
#include "utils/expandeddatum.h"
#include "utils/lsyscache.h"
#include "utils/typcache.h"

static TupleDesc ExecTypeFromTLInternal(List *targetList,
										bool skipjunk);
static pg_always_inline void slot_deform_heap_tuple(TupleTableSlot *slot, HeapTuple tuple, uint32 *offp,
													int reqnatts, bool support_cstring);
static inline void tts_buffer_heap_store_tuple(TupleTableSlot *slot,
											   HeapTuple tuple,
											   Buffer buffer,
											   bool transfer_pin);
static void tts_heap_store_tuple(TupleTableSlot *slot, HeapTuple tuple, bool shouldFree);


const TupleTableSlotOps TTSOpsVirtual;
const TupleTableSlotOps TTSOpsHeapTuple;
const TupleTableSlotOps TTSOpsMinimalTuple;
const TupleTableSlotOps TTSOpsBufferHeapTuple;


/*
 * ============================================================================
 * 【中文注释】TupleTableSlotOps 实现（四大槽类型）——总体说明
 * ----------------------------------------------------------------------------
 * 每套实现都按"槽协议"提供一组回调：init / release（槽生命周期）、clear
 * （清空槽内元组并释放其持有的资源）、getsomeattrs（按需解出 N 个属性）、
 * getsysattr（系统列，仅堆/缓冲槽支持）、materialize（把内容物化到槽自身
 * 内存上下文）、copyslot（整槽复制）、get/copy_heap_tuple、get/copy_minimal
 * _tuple（物理元组存取，不支持的返回 NULL 或走 copy 路径）。
 *
 * 关键不变量：
 *   - TTS_FLAG_EMPTY：槽为空；TTS_FLAG_SHOULDFREE：槽拥有元组内存，clear
 *     时必须释放；TTS_FLAG_FIXED：槽的元组描述符固定。
 *   - 解包/物化的一致性：tts_values 可能指向"未物化的底层元组"，任何跨越
 *     底层存储生命周期的使用都必须先 materialize。
 * ============================================================================
 */

/*
 * ============================================================================
 * 【中文注释】虚拟槽（VirtualTupleTableSlot）实现
 * ----------------------------------------------------------------------------
 * 特点：槽里只存 Datum/isnull 数组，没有物理元组也没有 buffer pin，因此
 * init/release 都是空操作；clear 仅需释放之前物化时分配的内存。
 *
 * getsomeattrs：永不应被调用——虚拟槽在 ExecStoreVirtualTuple 时已把全部
 * 属性解出（tts_nvalid = natts），调用即编程错误，直接报错。
 * getsysattr / is_current_xact_tuple：虚拟槽不承载系统列与事务信息，走到
 * 就报"不支持"，让错误尽早暴露而不是返回垃圾值。
 *
 * materialize（核心）：把非按值（by-value）的 Datum 拷贝进 slot 自己的
 * 内存上下文，使槽不再依赖外部存储。实现上先两遍扫描：
 *   第一遍只算总需求内存（按对齐规则逐列累加；expanded 对象按展开后的
 *   平坦大小计），一次 MemoryContextAlloc 分配整块，提高缓存命中与分配
 *   效率；第二遍逐列 memcpy/EOH_flatten_into 填入，并把 tts_values 改写
 *   为指向新内存。全部为按值类型时 sz==0，直接返回（无需物化）。
 * ============================================================================
 */
static void
tts_virtual_init(TupleTableSlot *slot)
{
}

static void
tts_virtual_release(TupleTableSlot *slot)
{
}

static void
tts_virtual_clear(TupleTableSlot *slot)
{
	if (unlikely(TTS_SHOULDFREE(slot)))
	{
		VirtualTupleTableSlot *vslot = (VirtualTupleTableSlot *) slot;

		pfree(vslot->data);
		vslot->data = NULL;

		slot->tts_flags &= ~TTS_FLAG_SHOULDFREE;
	}

	slot->tts_nvalid = 0;
	slot->tts_flags |= TTS_FLAG_EMPTY;
	ItemPointerSetInvalid(&slot->tts_tid);
}

/*
 * VirtualTupleTableSlots always have fully populated tts_values and
 * tts_isnull arrays.  So this function should never be called.
 */
static void
tts_virtual_getsomeattrs(TupleTableSlot *slot, int natts)
{
	elog(ERROR, "getsomeattrs is not required to be called on a virtual tuple table slot");
}

/*
 * VirtualTupleTableSlots never provide system attributes (except those
 * handled generically, such as tableoid).  We generally shouldn't get
 * here, but provide a user-friendly message if we do.
 */
static Datum
tts_virtual_getsysattr(TupleTableSlot *slot, int attnum, bool *isnull)
{
	Assert(!TTS_EMPTY(slot));

	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("cannot retrieve a system column in this context")));

	return 0;					/* silence compiler warnings */
}

/*
 * VirtualTupleTableSlots never have storage tuples.  We generally
 * shouldn't get here, but provide a user-friendly message if we do.
 */
static bool
tts_virtual_is_current_xact_tuple(TupleTableSlot *slot)
{
	Assert(!TTS_EMPTY(slot));

	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("don't have transaction information for this type of tuple")));

	return false;				/* silence compiler warnings */
}

/*
 * To materialize a virtual slot all the datums that aren't passed by value
 * have to be copied into the slot's memory context.  To do so, compute the
 * required size, and allocate enough memory to store all attributes.  That's
 * good for cache hit ratio, but more importantly requires only memory
 * allocation/deallocation.
 */
static void
tts_virtual_materialize(TupleTableSlot *slot)
{
	VirtualTupleTableSlot *vslot = (VirtualTupleTableSlot *) slot;
	TupleDesc	desc = slot->tts_tupleDescriptor;
	Size		sz = 0;
	char	   *data;

	/* already materialized */
	if (TTS_SHOULDFREE(slot))
		return;

	/* compute size of memory required */
	for (int natt = 0; natt < desc->natts; natt++)
	{
		CompactAttribute *att = TupleDescCompactAttr(desc, natt);
		Datum		val;

		if (att->attbyval || slot->tts_isnull[natt])
			continue;

		val = slot->tts_values[natt];

		if (att->attlen == -1 &&
			VARATT_IS_EXTERNAL_EXPANDED(DatumGetPointer(val)))
		{
			/*
			 * We want to flatten the expanded value so that the materialized
			 * slot doesn't depend on it.
			 */
			sz = att_nominal_alignby(sz, att->attalignby);
			sz += EOH_get_flat_size(DatumGetEOHP(val));
		}
		else
		{
			sz = att_nominal_alignby(sz, att->attalignby);
			sz = att_addlength_datum(sz, att->attlen, val);
		}
	}

	/* all data is byval */
	if (sz == 0)
		return;

	/* allocate memory */
	vslot->data = data = MemoryContextAlloc(slot->tts_mcxt, sz);
	slot->tts_flags |= TTS_FLAG_SHOULDFREE;

	/* and copy all attributes into the pre-allocated space */
	for (int natt = 0; natt < desc->natts; natt++)
	{
		CompactAttribute *att = TupleDescCompactAttr(desc, natt);
		Datum		val;

		if (att->attbyval || slot->tts_isnull[natt])
			continue;

		val = slot->tts_values[natt];

		if (att->attlen == -1 &&
			VARATT_IS_EXTERNAL_EXPANDED(DatumGetPointer(val)))
		{
			Size		data_length;

			/*
			 * We want to flatten the expanded value so that the materialized
			 * slot doesn't depend on it.
			 */
			ExpandedObjectHeader *eoh = DatumGetEOHP(val);

			data = (char *) att_nominal_alignby(data,
												att->attalignby);
			data_length = EOH_get_flat_size(eoh);
			EOH_flatten_into(eoh, data, data_length);

			slot->tts_values[natt] = PointerGetDatum(data);
			data += data_length;
		}
		else
		{
			Size		data_length = 0;

			data = (char *) att_nominal_alignby(data, att->attalignby);
			data_length = att_addlength_datum(data_length, att->attlen, val);

			memcpy(data, DatumGetPointer(val), data_length);

			slot->tts_values[natt] = PointerGetDatum(data);
			data += data_length;
		}
	}
}

static void
tts_virtual_copyslot(TupleTableSlot *dstslot, TupleTableSlot *srcslot)
{
	TupleDesc	srcdesc = srcslot->tts_tupleDescriptor;

	tts_virtual_clear(dstslot);

	slot_getallattrs(srcslot);

	for (int natt = 0; natt < srcdesc->natts; natt++)
	{
		dstslot->tts_values[natt] = srcslot->tts_values[natt];
		dstslot->tts_isnull[natt] = srcslot->tts_isnull[natt];
	}

	dstslot->tts_nvalid = srcdesc->natts;
	dstslot->tts_flags &= ~TTS_FLAG_EMPTY;

	/* make sure storage doesn't depend on external memory */
	tts_virtual_materialize(dstslot);
}

static HeapTuple
tts_virtual_copy_heap_tuple(TupleTableSlot *slot)
{
	Assert(!TTS_EMPTY(slot));

	return heap_form_tuple(slot->tts_tupleDescriptor,
						   slot->tts_values,
						   slot->tts_isnull);
}

static MinimalTuple
tts_virtual_copy_minimal_tuple(TupleTableSlot *slot, Size extra)
{
	Assert(!TTS_EMPTY(slot));

	return heap_form_minimal_tuple(slot->tts_tupleDescriptor,
								   slot->tts_values,
								   slot->tts_isnull,
								   extra);
}


/*
 * ============================================================================
 * 【中文注释】堆元组槽（HeapTupleTableSlot）实现
 * ----------------------------------------------------------------------------
 * 特点：持有完整 HeapTuple（含事务/系统列信息），用于需要系统列、或元组
 * 独立于缓冲页存在的场合。tuple 指针为 NULL 时表示槽内容是"虚拟形式"
 * （只有数组），此时 getsysattr / is_current_xact_tuple 报错。
 *
 * clear：SHOULDFREE 时 heap_freetuple；并复位 off（解包偏移）、nvalid。
 * getsomeattrs：委托给核心函数 slot_deform_heap_tuple 增量解包。
 * materialize：确保槽自持内存——无 tuple 时按数组 heap_form_tuple 造一个，
 * 有 tuple 但非自有（无 SHOULDFREE）时 heap_copytuple 拷入槽上下文；解包
 * 偏移清零强制从新拷贝重新解包，避免 tts_values 指向旧（可能已消失的）元组。
 * copyslot：在目标槽上下文拷贝一份堆元组后 ExecStoreHeapTuple 存入
 * （shouldFree=true，目标槽获得所有权）。
 * ============================================================================
 */
static void
tts_heap_init(TupleTableSlot *slot)
{
}

static void
tts_heap_release(TupleTableSlot *slot)
{
}

static void
tts_heap_clear(TupleTableSlot *slot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	/* Free the memory for the heap tuple if it's allowed. */
	if (TTS_SHOULDFREE(slot))
	{
		heap_freetuple(hslot->tuple);
		slot->tts_flags &= ~TTS_FLAG_SHOULDFREE;
	}

	slot->tts_nvalid = 0;
	slot->tts_flags |= TTS_FLAG_EMPTY;
	ItemPointerSetInvalid(&slot->tts_tid);
	hslot->off = 0;
	hslot->tuple = NULL;
}

static void
tts_heap_getsomeattrs(TupleTableSlot *slot, int natts)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	slot_deform_heap_tuple(slot, hslot->tuple, &hslot->off, natts, false);
}

static Datum
tts_heap_getsysattr(TupleTableSlot *slot, int attnum, bool *isnull)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	/*
	 * In some code paths it's possible to get here with a non-materialized
	 * slot, in which case we can't retrieve system columns.
	 */
	if (!hslot->tuple)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot retrieve a system column in this context")));

	return heap_getsysattr(hslot->tuple, attnum,
						   slot->tts_tupleDescriptor, isnull);
}

static bool
tts_heap_is_current_xact_tuple(TupleTableSlot *slot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;
	TransactionId xmin;

	Assert(!TTS_EMPTY(slot));

	/*
	 * In some code paths it's possible to get here with a non-materialized
	 * slot, in which case we can't check if tuple is created by the current
	 * transaction.
	 */
	if (!hslot->tuple)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("don't have a storage tuple in this context")));

	xmin = HeapTupleHeaderGetRawXmin(hslot->tuple->t_data);

	return TransactionIdIsCurrentTransactionId(xmin);
}

static void
tts_heap_materialize(TupleTableSlot *slot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;
	MemoryContext oldContext;

	Assert(!TTS_EMPTY(slot));

	/* If slot has its tuple already materialized, nothing to do. */
	if (TTS_SHOULDFREE(slot))
		return;

	oldContext = MemoryContextSwitchTo(slot->tts_mcxt);

	/*
	 * Have to deform from scratch, otherwise tts_values[] entries could point
	 * into the non-materialized tuple (which might be gone when accessed).
	 */
	slot->tts_nvalid = 0;
	hslot->off = 0;

	if (!hslot->tuple)
		hslot->tuple = heap_form_tuple(slot->tts_tupleDescriptor,
									   slot->tts_values,
									   slot->tts_isnull);
	else
	{
		/*
		 * The tuple contained in this slot is not allocated in the memory
		 * context of the given slot (else it would have TTS_FLAG_SHOULDFREE
		 * set).  Copy the tuple into the given slot's memory context.
		 */
		hslot->tuple = heap_copytuple(hslot->tuple);
	}

	slot->tts_flags |= TTS_FLAG_SHOULDFREE;

	MemoryContextSwitchTo(oldContext);
}

static void
tts_heap_copyslot(TupleTableSlot *dstslot, TupleTableSlot *srcslot)
{
	HeapTuple	tuple;
	MemoryContext oldcontext;

	oldcontext = MemoryContextSwitchTo(dstslot->tts_mcxt);
	tuple = ExecCopySlotHeapTuple(srcslot);
	MemoryContextSwitchTo(oldcontext);

	ExecStoreHeapTuple(tuple, dstslot, true);
}

static HeapTuple
tts_heap_get_heap_tuple(TupleTableSlot *slot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));
	if (!hslot->tuple)
		tts_heap_materialize(slot);

	return hslot->tuple;
}

static HeapTuple
tts_heap_copy_heap_tuple(TupleTableSlot *slot)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));
	if (!hslot->tuple)
		tts_heap_materialize(slot);

	return heap_copytuple(hslot->tuple);
}

static MinimalTuple
tts_heap_copy_minimal_tuple(TupleTableSlot *slot, Size extra)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	if (!hslot->tuple)
		tts_heap_materialize(slot);

	return minimal_tuple_from_heap_tuple(hslot->tuple, extra);
}

static void
tts_heap_store_tuple(TupleTableSlot *slot, HeapTuple tuple, bool shouldFree)
{
	HeapTupleTableSlot *hslot = (HeapTupleTableSlot *) slot;

	tts_heap_clear(slot);

	slot->tts_nvalid = 0;
	hslot->tuple = tuple;
	hslot->off = 0;
	slot->tts_flags &= ~(TTS_FLAG_EMPTY | TTS_FLAG_SHOULDFREE);
	slot->tts_tid = tuple->t_self;

	if (shouldFree)
		slot->tts_flags |= TTS_FLAG_SHOULDFREE;
}


/*
 * ============================================================================
 * 【中文注释】最小元组槽（MinimalTupleTableSlot）实现
 * ----------------------------------------------------------------------------
 * 特点：持有 MinimalTuple（MinimalTuple = HeapTupleHeader 去掉系统列
 * 事务信息的紧凑表示）。排序、hash、物化等中间节点用它减少内存占用。
 *
 * 巧妙点：init 时把 mslot->tuple 指向内嵌的 minhdr 伪 HeapTuple——把
 * MinimalTuple 前面"虚构"出 HeapTupleData 头，从而让 slot_deform_heap_tuple
 * 按堆元组的方式统一解包；store/materialize 时同步维护 minhdr.t_len 与
 * t_data（指向 mintuple 偏移 MINIMAL_TUPLE_OFFSET 处）。
 *
 * 限制：不提供系统列（getsysattr 报错）与事务信息（is_current_xact_tuple
 * 报错），与 MinimalTuple 的设计目的一致。
 * ============================================================================
 */
static void
tts_minimal_init(TupleTableSlot *slot)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	/*
	 * Initialize the heap tuple pointer to access attributes of the minimal
	 * tuple contained in the slot as if it's a heap tuple.
	 */
	mslot->tuple = &mslot->minhdr;
}

static void
tts_minimal_release(TupleTableSlot *slot)
{
}

static void
tts_minimal_clear(TupleTableSlot *slot)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	if (TTS_SHOULDFREE(slot))
	{
		heap_free_minimal_tuple(mslot->mintuple);
		slot->tts_flags &= ~TTS_FLAG_SHOULDFREE;
	}

	slot->tts_nvalid = 0;
	slot->tts_flags |= TTS_FLAG_EMPTY;
	ItemPointerSetInvalid(&slot->tts_tid);
	mslot->off = 0;
	mslot->mintuple = NULL;
}

static void
tts_minimal_getsomeattrs(TupleTableSlot *slot, int natts)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	slot_deform_heap_tuple(slot, mslot->tuple, &mslot->off, natts, true);
}

/*
 * MinimalTupleTableSlots never provide system attributes. We generally
 * shouldn't get here, but provide a user-friendly message if we do.
 */
static Datum
tts_minimal_getsysattr(TupleTableSlot *slot, int attnum, bool *isnull)
{
	Assert(!TTS_EMPTY(slot));

	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("cannot retrieve a system column in this context")));

	return 0;					/* silence compiler warnings */
}

/*
 * Within MinimalTuple abstraction transaction information is unavailable.
 * We generally shouldn't get here, but provide a user-friendly message if
 * we do.
 */
static bool
tts_minimal_is_current_xact_tuple(TupleTableSlot *slot)
{
	Assert(!TTS_EMPTY(slot));

	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("don't have transaction information for this type of tuple")));

	return false;				/* silence compiler warnings */
}

static void
tts_minimal_materialize(TupleTableSlot *slot)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;
	MemoryContext oldContext;

	Assert(!TTS_EMPTY(slot));

	/* If slot has its tuple already materialized, nothing to do. */
	if (TTS_SHOULDFREE(slot))
		return;

	oldContext = MemoryContextSwitchTo(slot->tts_mcxt);

	/*
	 * Have to deform from scratch, otherwise tts_values[] entries could point
	 * into the non-materialized tuple (which might be gone when accessed).
	 */
	slot->tts_nvalid = 0;
	mslot->off = 0;

	if (!mslot->mintuple)
	{
		mslot->mintuple = heap_form_minimal_tuple(slot->tts_tupleDescriptor,
												  slot->tts_values,
												  slot->tts_isnull,
												  0);
	}
	else
	{
		/*
		 * The minimal tuple contained in this slot is not allocated in the
		 * memory context of the given slot (else it would have
		 * TTS_FLAG_SHOULDFREE set).  Copy the minimal tuple into the given
		 * slot's memory context.
		 */
		mslot->mintuple = heap_copy_minimal_tuple(mslot->mintuple, 0);
	}

	slot->tts_flags |= TTS_FLAG_SHOULDFREE;

	Assert(mslot->tuple == &mslot->minhdr);

	mslot->minhdr.t_len = mslot->mintuple->t_len + MINIMAL_TUPLE_OFFSET;
	mslot->minhdr.t_data = (HeapTupleHeader) ((char *) mslot->mintuple - MINIMAL_TUPLE_OFFSET);

	MemoryContextSwitchTo(oldContext);
}

static void
tts_minimal_copyslot(TupleTableSlot *dstslot, TupleTableSlot *srcslot)
{
	MemoryContext oldcontext;
	MinimalTuple mintuple;

	oldcontext = MemoryContextSwitchTo(dstslot->tts_mcxt);
	mintuple = ExecCopySlotMinimalTuple(srcslot);
	MemoryContextSwitchTo(oldcontext);

	ExecStoreMinimalTuple(mintuple, dstslot, true);
}

static MinimalTuple
tts_minimal_get_minimal_tuple(TupleTableSlot *slot)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	if (!mslot->mintuple)
		tts_minimal_materialize(slot);

	return mslot->mintuple;
}

static HeapTuple
tts_minimal_copy_heap_tuple(TupleTableSlot *slot)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	if (!mslot->mintuple)
		tts_minimal_materialize(slot);

	return heap_tuple_from_minimal_tuple(mslot->mintuple);
}

static MinimalTuple
tts_minimal_copy_minimal_tuple(TupleTableSlot *slot, Size extra)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	if (!mslot->mintuple)
		tts_minimal_materialize(slot);

	return heap_copy_minimal_tuple(mslot->mintuple, extra);
}

static void
tts_minimal_store_tuple(TupleTableSlot *slot, MinimalTuple mtup, bool shouldFree)
{
	MinimalTupleTableSlot *mslot = (MinimalTupleTableSlot *) slot;

	tts_minimal_clear(slot);

	Assert(!TTS_SHOULDFREE(slot));
	Assert(TTS_EMPTY(slot));

	slot->tts_flags &= ~TTS_FLAG_EMPTY;
	slot->tts_nvalid = 0;
	mslot->off = 0;

	mslot->mintuple = mtup;
	Assert(mslot->tuple == &mslot->minhdr);
	mslot->minhdr.t_len = mtup->t_len + MINIMAL_TUPLE_OFFSET;
	mslot->minhdr.t_data = (HeapTupleHeader) ((char *) mtup - MINIMAL_TUPLE_OFFSET);
	/* no need to set t_self or t_tableOid since we won't allow access */

	if (shouldFree)
		slot->tts_flags |= TTS_FLAG_SHOULDFREE;
}


/*
 * ============================================================================
 * 【中文注释】缓冲堆元组槽（BufferHeapTupleTableSlot）实现
 * ----------------------------------------------------------------------------
 * 特点：扫描节点的"零拷贝"槽——直接指向磁盘缓冲页中的元组，并持有该页的
 * buffer pin（保证元组内存一直有效）。release 槽内资源时释放 pin。
 *
 * clear：先处理 SHOULDFREE（此时必然已物化、无 pin，断言校验），再释放
 * buffer pin，最后复位各字段。
 * materialize：把内容物化进槽内存并解除对 buffer 的依赖（拷贝元组后释放
 * pin，置 InvalidBuffer），随后才置 SHOULDFREE——顺序保证不存在"既持有
 * pin 又带 SHOULDFREE"的非法中间态（有断言校验该不变量）。
 * copyslot 优化：若源槽同类型、未物化且有物理元组，直接引用同一 buffer
 * 内的元组（共享 pin），只把 HeapTupleData 头拷贝进目标槽内嵌的 tupdata
 * 以延长寿命；否则退化为整拷贝。
 *
 * 附加机制（ts_buffer_heap_store_tuple，见下）：同页连续扫描时避免
 * 释放再获取 pin 的来回开销；transfer_pin 模式把调用方 pin 直接转移给槽。
 * ============================================================================
 */
static void
tts_buffer_heap_init(TupleTableSlot *slot)
{
}

static void
tts_buffer_heap_release(TupleTableSlot *slot)
{
}

static void
tts_buffer_heap_clear(TupleTableSlot *slot)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	/*
	 * Free the memory for heap tuple if allowed. A tuple coming from buffer
	 * can never be freed. But we may have materialized a tuple from buffer.
	 * Such a tuple can be freed.
	 */
	if (TTS_SHOULDFREE(slot))
	{
		/* We should have unpinned the buffer while materializing the tuple. */
		Assert(!BufferIsValid(bslot->buffer));

		heap_freetuple(bslot->base.tuple);
		slot->tts_flags &= ~TTS_FLAG_SHOULDFREE;
	}

	if (BufferIsValid(bslot->buffer))
		ReleaseBuffer(bslot->buffer);

	slot->tts_nvalid = 0;
	slot->tts_flags |= TTS_FLAG_EMPTY;
	ItemPointerSetInvalid(&slot->tts_tid);
	bslot->base.tuple = NULL;
	bslot->base.off = 0;
	bslot->buffer = InvalidBuffer;
}

static void
tts_buffer_heap_getsomeattrs(TupleTableSlot *slot, int natts)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	slot_deform_heap_tuple(slot, bslot->base.tuple, &bslot->base.off, natts, false);
}

static Datum
tts_buffer_heap_getsysattr(TupleTableSlot *slot, int attnum, bool *isnull)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	/*
	 * In some code paths it's possible to get here with a non-materialized
	 * slot, in which case we can't retrieve system columns.
	 */
	if (!bslot->base.tuple)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot retrieve a system column in this context")));

	return heap_getsysattr(bslot->base.tuple, attnum,
						   slot->tts_tupleDescriptor, isnull);
}

static bool
tts_buffer_is_current_xact_tuple(TupleTableSlot *slot)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;
	TransactionId xmin;

	Assert(!TTS_EMPTY(slot));

	/*
	 * In some code paths it's possible to get here with a non-materialized
	 * slot, in which case we can't check if tuple is created by the current
	 * transaction.
	 */
	if (!bslot->base.tuple)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("don't have a storage tuple in this context")));

	xmin = HeapTupleHeaderGetRawXmin(bslot->base.tuple->t_data);

	return TransactionIdIsCurrentTransactionId(xmin);
}

static void
tts_buffer_heap_materialize(TupleTableSlot *slot)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;
	MemoryContext oldContext;

	Assert(!TTS_EMPTY(slot));

	/* If slot has its tuple already materialized, nothing to do. */
	if (TTS_SHOULDFREE(slot))
		return;

	oldContext = MemoryContextSwitchTo(slot->tts_mcxt);

	/*
	 * Have to deform from scratch, otherwise tts_values[] entries could point
	 * into the non-materialized tuple (which might be gone when accessed).
	 */
	bslot->base.off = 0;
	slot->tts_nvalid = 0;

	if (!bslot->base.tuple)
	{
		/*
		 * Normally BufferHeapTupleTableSlot should have a tuple + buffer
		 * associated with it, unless it's materialized (which would've
		 * returned above). But when it's useful to allow storing virtual
		 * tuples in a buffer slot, which then also needs to be
		 * materializable.
		 */
		bslot->base.tuple = heap_form_tuple(slot->tts_tupleDescriptor,
											slot->tts_values,
											slot->tts_isnull);
	}
	else
	{
		bslot->base.tuple = heap_copytuple(bslot->base.tuple);

		/*
		 * A heap tuple stored in a BufferHeapTupleTableSlot should have a
		 * buffer associated with it, unless it's materialized or virtual.
		 */
		if (likely(BufferIsValid(bslot->buffer)))
			ReleaseBuffer(bslot->buffer);
		bslot->buffer = InvalidBuffer;
	}

	/*
	 * We don't set TTS_FLAG_SHOULDFREE until after releasing the buffer, if
	 * any.  This avoids having a transient state that would fall foul of our
	 * assertions that a slot with TTS_FLAG_SHOULDFREE doesn't own a buffer.
	 * In the unlikely event that ReleaseBuffer() above errors out, we'd
	 * effectively leak the copied tuple, but that seems fairly harmless.
	 */
	slot->tts_flags |= TTS_FLAG_SHOULDFREE;

	MemoryContextSwitchTo(oldContext);
}

static void
tts_buffer_heap_copyslot(TupleTableSlot *dstslot, TupleTableSlot *srcslot)
{
	BufferHeapTupleTableSlot *bsrcslot = (BufferHeapTupleTableSlot *) srcslot;
	BufferHeapTupleTableSlot *bdstslot = (BufferHeapTupleTableSlot *) dstslot;

	/*
	 * If the source slot is of a different kind, or is a buffer slot that has
	 * been materialized / is virtual, make a new copy of the tuple. Otherwise
	 * make a new reference to the in-buffer tuple.
	 */
	if (dstslot->tts_ops != srcslot->tts_ops ||
		TTS_SHOULDFREE(srcslot) ||
		!bsrcslot->base.tuple)
	{
		MemoryContext oldContext;

		ExecClearTuple(dstslot);
		dstslot->tts_flags &= ~TTS_FLAG_EMPTY;
		oldContext = MemoryContextSwitchTo(dstslot->tts_mcxt);
		bdstslot->base.tuple = ExecCopySlotHeapTuple(srcslot);
		dstslot->tts_flags |= TTS_FLAG_SHOULDFREE;
		MemoryContextSwitchTo(oldContext);
	}
	else
	{
		Assert(BufferIsValid(bsrcslot->buffer));

		tts_buffer_heap_store_tuple(dstslot, bsrcslot->base.tuple,
									bsrcslot->buffer, false);

		/*
		 * The HeapTupleData portion of the source tuple might be shorter
		 * lived than the destination slot. Therefore copy the HeapTuple into
		 * our slot's tupdata, which is guaranteed to live long enough (but
		 * will still point into the buffer).
		 */
		memcpy(&bdstslot->base.tupdata, bdstslot->base.tuple, sizeof(HeapTupleData));
		bdstslot->base.tuple = &bdstslot->base.tupdata;
	}
}

static HeapTuple
tts_buffer_heap_get_heap_tuple(TupleTableSlot *slot)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	if (!bslot->base.tuple)
		tts_buffer_heap_materialize(slot);

	return bslot->base.tuple;
}

static HeapTuple
tts_buffer_heap_copy_heap_tuple(TupleTableSlot *slot)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	if (!bslot->base.tuple)
		tts_buffer_heap_materialize(slot);

	return heap_copytuple(bslot->base.tuple);
}

static MinimalTuple
tts_buffer_heap_copy_minimal_tuple(TupleTableSlot *slot, Size extra)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	Assert(!TTS_EMPTY(slot));

	if (!bslot->base.tuple)
		tts_buffer_heap_materialize(slot);

	return minimal_tuple_from_heap_tuple(bslot->base.tuple, extra);
}

static inline void
tts_buffer_heap_store_tuple(TupleTableSlot *slot, HeapTuple tuple,
							Buffer buffer, bool transfer_pin)
{
	BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

	if (TTS_SHOULDFREE(slot))
	{
		/* materialized slot shouldn't have a buffer to release */
		Assert(!BufferIsValid(bslot->buffer));

		heap_freetuple(bslot->base.tuple);
		slot->tts_flags &= ~TTS_FLAG_SHOULDFREE;
	}

	slot->tts_flags &= ~TTS_FLAG_EMPTY;
	slot->tts_nvalid = 0;
	bslot->base.tuple = tuple;
	bslot->base.off = 0;
	slot->tts_tid = tuple->t_self;

	/*
	 * If tuple is on a disk page, keep the page pinned as long as we hold a
	 * pointer into it.  We assume the caller already has such a pin.  If
	 * transfer_pin is true, we'll transfer that pin to this slot, if not
	 * we'll pin it again ourselves.
	 *
	 * This is coded to optimize the case where the slot previously held a
	 * tuple on the same disk page: in that case releasing and re-acquiring
	 * the pin is a waste of cycles.  This is a common situation during
	 * seqscans, so it's worth troubling over.
	 */
	if (bslot->buffer != buffer)
	{
		if (BufferIsValid(bslot->buffer))
			ReleaseBuffer(bslot->buffer);

		bslot->buffer = buffer;

		if (!transfer_pin && BufferIsValid(buffer))
			IncrBufferRefCount(buffer);
	}
	else if (transfer_pin && BufferIsValid(buffer))
	{
		/*
		 * In transfer_pin mode the caller won't know about the same-page
		 * optimization, so we gotta release its pin.
		 */
		ReleaseBuffer(buffer);
	}
}

/*
 * ============================================================================
 * 【中文注释】slot_deform_heap_tuple —— 增量解包核心（性能关键路径）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把槽内的物理堆元组按需解出到 tts_values/tts_isnull 数组，最多解到
 *   reqnatts 列。是 heap_deform_tuple 的"增量版"：tts_nvalid 记录已解
 *   列数，本次只续解缺失部分，绝不重算已解列。
 *
 * 性能设计（这是执行器最热的路径之一，值得逐条理解）：
 *   1. 分段解包，每段用不同优化策略：
 *      - [0, firstNonGuaranteedAttr)：TupleDescFinalize 保证这些列在元组
 *        里必然存在且为定长按值类型（attcacheoff 有效），循环完全跳过
 *        NULL 位图与 natts 读取；
 *      - [firstNonGuaranteed, firstNullAttr)：利用 attcacheoff 缓存偏移
 *        快速定位定长列，直到第一个 NULL 为止（NULL 之后偏移不再可缓存）；
 *      - [firstNullAttr, natts)：一般路径，逐列做对齐/取长度/取数据；
 *      - 之后：属性数不足时调用 slot_getmissingattrs 补齐（缺失列默认
 *        NULL 或用 TupleDesc 登记的 missing 默认值），reqnatts 超过
 *        描述符列数则报错。
 *   2. off 偏移增量保存到调用方传入的 offp（各种槽各持一份），下次续解
 *      直接接着走；
 *   3. support_cstring 作为常量参数传入，编译器内联时把 cstring 特判
 *      （attlen==-1 的 cstring 类型只出现在 MinimalTuple）整体裁剪掉；
 *   4. first_null_attr / populate_isnull_array 一次性批量处理 NULL 位图，
 *      避免逐位判断；attcacheoff 只失效到第一个 NULL 之前。
 * ============================================================================
 */
static pg_always_inline void
slot_deform_heap_tuple(TupleTableSlot *slot, HeapTuple tuple, uint32 *offp,
					   int reqnatts, bool support_cstring)
{
	CompactAttribute *cattrs;
	CompactAttribute *cattr;
	TupleDesc	tupleDesc = slot->tts_tupleDescriptor;
	HeapTupleHeader tup = tuple->t_data;
	size_t		attnum;
	int			firstNonCacheOffsetAttr;
	int			firstNonGuaranteedAttr;
	int			firstNullAttr;
	int			natts;
	Datum	   *values;
	bool	   *isnull;
	char	   *tp;				/* ptr to tuple data */
	uint32		off;			/* offset in tuple data */

	/* Did someone forget to call TupleDescFinalize()? */
	Assert(tupleDesc->firstNonCachedOffsetAttr >= 0);

	isnull = slot->tts_isnull;

	/*
	 * Some callers may form and deform tuples prior to NOT NULL constraints
	 * being checked.  Here we'd like to optimize the case where we only need
	 * to fetch attributes before or up to the point where the attribute is
	 * guaranteed to exist in the tuple.  We rely on the slot flag being set
	 * correctly to only enable this optimization when it's valid to do so.
	 * This optimization allows us to save fetching the number of attributes
	 * from the tuple and saves the additional cost of handling non-byval
	 * attrs.
	 */
	firstNonGuaranteedAttr = Min(reqnatts, slot->tts_first_nonguaranteed);

	firstNonCacheOffsetAttr = tupleDesc->firstNonCachedOffsetAttr;

	if (HeapTupleHasNulls(tuple))
	{
		natts = HeapTupleHeaderGetNatts(tup);
		tp = (char *) tup + MAXALIGN(offsetof(HeapTupleHeaderData, t_bits) +
									 BITMAPLEN(natts));

		natts = Min(natts, reqnatts);
		if (natts > firstNonGuaranteedAttr)
		{
			uint8	   *bp = tup->t_bits;

			/* Find the first NULL attr */
			firstNullAttr = first_null_attr(bp, natts);

			/*
			 * And populate the isnull array for all attributes being fetched
			 * from the tuple.
			 */
			populate_isnull_array(bp, natts, isnull);
		}
		else
		{
			/* Otherwise all required columns are guaranteed to exist */
			firstNullAttr = natts;

			/*
			 * Check TupleDescFinalize() didn't get confused when setting
			 * firstNonGuaranteedAttr.  There should never be a NULL in a
			 * guaranteed column.
			 */
			Assert(first_null_attr(tup->t_bits, natts) >= firstNullAttr);
		}
	}
	else
	{
		tp = (char *) tup + MAXALIGN(offsetof(HeapTupleHeaderData, t_bits));

		/*
		 * We only need to look at the tuple's natts if we need more than the
		 * guaranteed number of columns
		 */
		if (reqnatts > firstNonGuaranteedAttr)
			natts = Min(HeapTupleHeaderGetNatts(tup), reqnatts);
		else
		{
			/* No need to access the number of attributes in the tuple */
			natts = reqnatts;
		}

		/* All attrs can be fetched without checking for NULLs */
		firstNullAttr = natts;
	}

	attnum = slot->tts_nvalid;
	values = slot->tts_values;
	slot->tts_nvalid = reqnatts;

	/*
	 * We store the tupleDesc's CompactAttribute array in 'cattrs' as gcc
	 * seems to be unwilling to optimize accessing the CompactAttribute
	 * element efficiently when accessing it via TupleDescCompactAttr().
	 */
	cattrs = tupleDesc->compact_attrs;

	/* Ensure we calculated tp correctly */
	Assert(tp == (char *) tup + tup->t_hoff);

	if (attnum < firstNonGuaranteedAttr)
	{
		int			attlen;

		do
		{
			isnull[attnum] = false;
			cattr = &cattrs[attnum];
			attlen = cattr->attlen;

			/* We don't expect any non-byval types */
			pg_assume(attlen > 0);
			Assert(cattr->attbyval == true);

			off = cattr->attcacheoff;
			values[attnum] = fetch_att_noerr(tp + off, true, attlen);
			attnum++;
		} while (attnum < firstNonGuaranteedAttr);

		off += attlen;

		if (attnum == reqnatts)
			goto done;
	}
	else
	{
		/*
		 * We may be incrementally deforming the tuple, so set 'off' to the
		 * previously cached value.  This may be 0, if the slot has just
		 * received a new tuple.
		 */
		off = *offp;

		/* We expect *offp to be set to 0 when attnum == 0 */
		Assert(off == 0 || attnum > 0);
	}

	/* We can use attcacheoff up until the first NULL */
	firstNonCacheOffsetAttr = Min(firstNonCacheOffsetAttr, firstNullAttr);

	/*
	 * Handle the portion of the tuple that we have cached the offset for up
	 * to the first NULL attribute.  The offset is effectively fixed for
	 * these, so we can use the CompactAttribute's attcacheoff.
	 */
	if (attnum < firstNonCacheOffsetAttr)
	{
		int			attlen;

		do
		{
			isnull[attnum] = false;
			cattr = &cattrs[attnum];
			attlen = cattr->attlen;
			off = cattr->attcacheoff;
			values[attnum] = fetch_att_noerr(tp + off,
											 cattr->attbyval,
											 attlen);
			attnum++;
		} while (attnum < firstNonCacheOffsetAttr);

		/*
		 * Point the offset after the end of the last attribute with a cached
		 * offset.  We expect the final cached offset attribute to have a
		 * fixed width, so just add the attlen to the attcacheoff
		 */
		Assert(attlen > 0);
		off += attlen;
	}

	/*
	 * Handle any portion of the tuple that doesn't have a fixed offset up
	 * until the first NULL attribute.  This loop only differs from the one
	 * after it by the NULL checks.
	 */
	for (; attnum < firstNullAttr; attnum++)
	{
		int			attlen;

		isnull[attnum] = false;
		cattr = &cattrs[attnum];
		attlen = cattr->attlen;

		/*
		 * Only emit the cstring-related code in align_fetch_then_add() when
		 * cstring support is needed.  We assume support_cstring will be
		 * passed as a const to allow the compiler to eliminate this branch.
		 */
		if (!support_cstring)
			pg_assume(attlen > 0 || attlen == -1);

		/* align 'off', fetch the datum, and increment off beyond the datum */
		values[attnum] = align_fetch_then_add(tp,
											  &off,
											  cattr->attbyval,
											  attlen,
											  cattr->attalignby);
	}

	/*
	 * Now handle any remaining attributes in the tuple up to the requested
	 * attnum.  This time, include NULL checks as we're now at the first NULL
	 * attribute.
	 */
	for (; attnum < natts; attnum++)
	{
		int			attlen;

		if (isnull[attnum])
		{
			values[attnum] = (Datum) 0;
			continue;
		}

		cattr = &cattrs[attnum];
		attlen = cattr->attlen;

		/* As above, only emit cstring code when needed. */
		if (!support_cstring)
			pg_assume(attlen > 0 || attlen == -1);

		/* align 'off', fetch the datum, and increment off beyond the datum */
		values[attnum] = align_fetch_then_add(tp,
											  &off,
											  cattr->attbyval,
											  attlen,
											  cattr->attalignby);
	}

	/* Fetch any missing attrs and raise an error if reqnatts is invalid */
	if (unlikely(attnum < reqnatts))
	{
		/*
		 * Cache the offset before calling the function to allow the compiler
		 * to implement a tail-call optimization
		 */
		*offp = off;

		Assert(HeapTupleHeaderGetNatts(tup) <= attnum);

		/*
		 * Fetch all missing attributes.  We pass natts rather than attnum as
		 * if we're deforming attributes after having already deformed some
		 * missing attributes, then the call to populate_isnull_array() may
		 * have overwritten the previous tts_isnull values from what was
		 * stored in the previous call to slot_getmissingattrs().
		 */
		slot_getmissingattrs(slot, HeapTupleHeaderGetNatts(tup), reqnatts);
		return;
	}
done:

	/* Save current offset for next execution */
	*offp = off;
}

/*
 * ============================================================================
 * 【中文注释】TTSOps* 全局函数指针表 —— 四种槽类型的多态分发表
 * ----------------------------------------------------------------------------
 * 每个槽结构体第一成员是 tts_ops 指针，指向下列常量表之一；执行器代码
 * 通过 slot->tts_ops->xxx() 调用对应实现，实现"面向接口编程"。
 *
 * 各表差异速查：
 *   - 虚拟槽：get_heap_tuple/get_minimal_tuple 为 NULL（不拥有物理元组），
 *     需要物理元组时走 copy_heap_tuple/copy_minimal_tuple（新造一个）；
 *   - 堆元组槽：get_heap_tuple 可用，get_minimal_tuple 为 NULL；
 *   - 最小元组槽：get_minimal_tuple 可用，get_heap_tuple 为 NULL；
 *   - 缓冲槽：get_heap_tuple 可用（返回指向缓冲页的元组），
 *     copy_minimal_tuple 可用（即时转换）。
 * 执行器上层用 ExecFetchSlotHeapTuple/ExecFetchSlotMinimalTuple 统一取数，
 * 它们根据"表是否提供 get_* 回调"自动决定是直接引用还是拷贝。
 * ============================================================================
 */
const TupleTableSlotOps TTSOpsVirtual = {
	.base_slot_size = sizeof(VirtualTupleTableSlot),
	.init = tts_virtual_init,
	.release = tts_virtual_release,
	.clear = tts_virtual_clear,
	.getsomeattrs = tts_virtual_getsomeattrs,
	.getsysattr = tts_virtual_getsysattr,
	.materialize = tts_virtual_materialize,
	.is_current_xact_tuple = tts_virtual_is_current_xact_tuple,
	.copyslot = tts_virtual_copyslot,

	/*
	 * A virtual tuple table slot can not "own" a heap tuple or a minimal
	 * tuple.
	 */
	.get_heap_tuple = NULL,
	.get_minimal_tuple = NULL,
	.copy_heap_tuple = tts_virtual_copy_heap_tuple,
	.copy_minimal_tuple = tts_virtual_copy_minimal_tuple
};

const TupleTableSlotOps TTSOpsHeapTuple = {
	.base_slot_size = sizeof(HeapTupleTableSlot),
	.init = tts_heap_init,
	.release = tts_heap_release,
	.clear = tts_heap_clear,
	.getsomeattrs = tts_heap_getsomeattrs,
	.getsysattr = tts_heap_getsysattr,
	.is_current_xact_tuple = tts_heap_is_current_xact_tuple,
	.materialize = tts_heap_materialize,
	.copyslot = tts_heap_copyslot,
	.get_heap_tuple = tts_heap_get_heap_tuple,

	/* A heap tuple table slot can not "own" a minimal tuple. */
	.get_minimal_tuple = NULL,
	.copy_heap_tuple = tts_heap_copy_heap_tuple,
	.copy_minimal_tuple = tts_heap_copy_minimal_tuple
};

const TupleTableSlotOps TTSOpsMinimalTuple = {
	.base_slot_size = sizeof(MinimalTupleTableSlot),
	.init = tts_minimal_init,
	.release = tts_minimal_release,
	.clear = tts_minimal_clear,
	.getsomeattrs = tts_minimal_getsomeattrs,
	.getsysattr = tts_minimal_getsysattr,
	.is_current_xact_tuple = tts_minimal_is_current_xact_tuple,
	.materialize = tts_minimal_materialize,
	.copyslot = tts_minimal_copyslot,

	/* A minimal tuple table slot can not "own" a heap tuple. */
	.get_heap_tuple = NULL,
	.get_minimal_tuple = tts_minimal_get_minimal_tuple,
	.copy_heap_tuple = tts_minimal_copy_heap_tuple,
	.copy_minimal_tuple = tts_minimal_copy_minimal_tuple
};

const TupleTableSlotOps TTSOpsBufferHeapTuple = {
	.base_slot_size = sizeof(BufferHeapTupleTableSlot),
	.init = tts_buffer_heap_init,
	.release = tts_buffer_heap_release,
	.clear = tts_buffer_heap_clear,
	.getsomeattrs = tts_buffer_heap_getsomeattrs,
	.getsysattr = tts_buffer_heap_getsysattr,
	.is_current_xact_tuple = tts_buffer_is_current_xact_tuple,
	.materialize = tts_buffer_heap_materialize,
	.copyslot = tts_buffer_heap_copyslot,
	.get_heap_tuple = tts_buffer_heap_get_heap_tuple,

	/* A buffer heap tuple table slot can not "own" a minimal tuple. */
	.get_minimal_tuple = NULL,
	.copy_heap_tuple = tts_buffer_heap_copy_heap_tuple,
	.copy_minimal_tuple = tts_buffer_heap_copy_minimal_tuple
};


/* ----------------------------------------------------------------
 *				  tuple table create/delete functions
 * ----------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】MakeTupleTableSlot —— 槽工厂（核心构造入口）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   创建空 TupleTableSlot。tupleDesc 非 NULL 时槽描述符固定（TTS_FLAG_FIXED）
 *   ——values/isnull 数组与槽结构一次性整体分配（减少内存碎片与指针访问
 *   次数）；tupleDesc 为 NULL 时只分配裸槽，之后用 ExecSetSlotDescriptor
 *   绑定描述符（数组另行分配）。
 *
 * 细节：
 *   - isnull 数组按 8 的倍数取整分配——populate_isnull_array 以 8 元素为
 *     单位批量转换 NULL 位图；
 *   - 传入的 flags 仅允许非瞬时标志（TTS_FLAGS_TRANSIENT 被强制清除）；
 *   - 固定描述符时 PinTupleDesc 增加引用计数（槽持有引用）；
 *   - tts_first_nonguaranteed 决定"哪些列保证在元组中存在"（见
 *     slot_deform_heap_tuple 的快路径），不满足 NOT NULL 约束的场景
 *     （TTS_FLAG_OBEYS_NOT_NULL_CONSTRAINTS 未置位）必须置 0 禁用快路径；
 *   - 最后调用 tts_ops->init 让具体槽类型做初始化（如 minimal 槽构造
 *     minhdr 伪元组头）。
 * ============================================================================
 */
TupleTableSlot *
MakeTupleTableSlot(TupleDesc tupleDesc,
				   const TupleTableSlotOps *tts_ops, uint16 flags)
{
	Size		basesz,
				allocsz;
	TupleTableSlot *slot;

	basesz = tts_ops->base_slot_size;

	/* Ensure callers don't have any way to set transient flags permanently */
	flags &= ~TTS_FLAGS_TRANSIENT;

	/*
	 * When a fixed descriptor is specified, we can reduce overhead by
	 * allocating the entire slot in one go.
	 *
	 * We round the size of tts_isnull up to the next highest multiple of 8.
	 * This is needed as populate_isnull_array() operates on 8 elements at a
	 * time when converting a tuple's NULL bitmap into a boolean array.
	 */
	if (tupleDesc)
		allocsz = MAXALIGN(basesz) +
			MAXALIGN(tupleDesc->natts * sizeof(Datum)) +
			TYPEALIGN(8, tupleDesc->natts * sizeof(bool));
	else
		allocsz = basesz;

	slot = palloc0(allocsz);
	/* const for optimization purposes, OK to modify at allocation time */
	*((const TupleTableSlotOps **) &slot->tts_ops) = tts_ops;
	slot->type = T_TupleTableSlot;
	slot->tts_flags = TTS_FLAG_EMPTY | flags;
	if (tupleDesc != NULL)
		slot->tts_flags |= TTS_FLAG_FIXED;
	slot->tts_tupleDescriptor = tupleDesc;
	slot->tts_mcxt = CurrentMemoryContext;
	slot->tts_nvalid = 0;

	if (tupleDesc != NULL)
	{
		slot->tts_values = (Datum *)
			(((char *) slot)
			 + MAXALIGN(basesz));

		slot->tts_isnull = (bool *)
			(((char *) slot)
			 + MAXALIGN(basesz)
			 + MAXALIGN(tupleDesc->natts * sizeof(Datum)));

		PinTupleDesc(tupleDesc);

		/*
		 * Precalculate the maximum guaranteed attribute that has to exist in
		 * every tuple which gets deformed into this slot.  When the
		 * TTS_FLAG_OBEYS_NOT_NULL_CONSTRAINTS flag is enabled, we simply take
		 * the pre-calculated value from the tupleDesc, otherwise the
		 * optimization is disabled, and we set the value to 0.
		 */
		if ((flags & TTS_FLAG_OBEYS_NOT_NULL_CONSTRAINTS) != 0)
			slot->tts_first_nonguaranteed = tupleDesc->firstNonGuaranteedAttr;
		else
			slot->tts_first_nonguaranteed = 0;
	}

	/*
	 * And allow slot type specific initialization.
	 */
	slot->tts_ops->init(slot);

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】ExecAllocTableSlot —— 把新槽登记进执行器元组表
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   建槽并 append 到 es_tupleTable 链表。凡"属于执行器"的槽都必须走这里
 *   登记，这样 ExecEndPlan → ExecResetTupleTable 能统一释放所有槽资源
 *   （pin、描述符引用计数、内存），各节点无需各自维护清理逻辑。
 * ============================================================================
 */
TupleTableSlot *
ExecAllocTableSlot(List **tupleTable, TupleDesc desc,
				   const TupleTableSlotOps *tts_ops, uint16 flags)
{
	TupleTableSlot *slot = MakeTupleTableSlot(desc, tts_ops, flags);

	*tupleTable = lappend(*tupleTable, slot);

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】ExecResetTupleTable —— 元组表统一资源回收
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   遍历元组表：每个槽先 ExecClearTuple 释放其持有的资源（缓冲 pin、
 *   元组内存），再调用 release 回调，最后释放描述符引用；shouldFree 为
 *   真时连槽结构本身与链表一起 pfree。
 *
 * 业务场景：ExecEndPlan 查询收尾时调用（shouldFree=true）；并行 worker
 * 等场合可先只清资源而保留结构复用。
 * ============================================================================
 */
void
ExecResetTupleTable(List *tupleTable,	/* tuple table */
					bool shouldFree)	/* true if we should free memory */
{
	ListCell   *lc;

	foreach(lc, tupleTable)
	{
		TupleTableSlot *slot = lfirst_node(TupleTableSlot, lc);

		/* Always release resources and reset the slot to empty */
		ExecClearTuple(slot);
		slot->tts_ops->release(slot);
		if (slot->tts_tupleDescriptor)
		{
			ReleaseTupleDesc(slot->tts_tupleDescriptor);
			slot->tts_tupleDescriptor = NULL;
		}

		/* If shouldFree, release memory occupied by the slot itself */
		if (shouldFree)
		{
			if (!TTS_FIXED(slot))
			{
				if (slot->tts_values)
					pfree(slot->tts_values);
				if (slot->tts_isnull)
					pfree(slot->tts_isnull);
			}
			pfree(slot);
		}
	}

	/* If shouldFree, release the list structure */
	if (shouldFree)
		list_free(tupleTable);
}

/*
 * ============================================================================
 * 【中文注释】MakeSingleTupleTableSlot / ExecDropSingleTupleTableSlot —— 独立槽
 * ----------------------------------------------------------------------------
 * 函数作用（成对）：
 *   MakeSingleTupleTableSlot：为"游离于主元组表之外"的临时用途造一个槽
 *   （如触发器、SRF 一次性取数）；ExecDropSingleTupleTableSlot 释放之。
 *
 * 注意：后者绝不用于登记在元组表里的槽（那里由 ExecResetTupleTable 统一
 * 处理）。清理顺序与 ExecResetTupleTable 对单个槽的处理严格一致：
 *   ExecClearTuple → release 回调 → 释放描述符引用 → 释放数组 → pfree 槽。
 * ============================================================================
 */
TupleTableSlot *
MakeSingleTupleTableSlot(TupleDesc tupdesc,
						 const TupleTableSlotOps *tts_ops)
{
	TupleTableSlot *slot = MakeTupleTableSlot(tupdesc, tts_ops, 0);

	return slot;
}

/* --------------------------------
 *		ExecDropSingleTupleTableSlot
 *
 *		Release a TupleTableSlot made with MakeSingleTupleTableSlot.
 *		DON'T use this on a slot that's part of a tuple table list!
 * --------------------------------
 */
void
ExecDropSingleTupleTableSlot(TupleTableSlot *slot)
{
	/* This should match ExecResetTupleTable's processing of one slot */
	Assert(IsA(slot, TupleTableSlot));
	ExecClearTuple(slot);
	slot->tts_ops->release(slot);
	if (slot->tts_tupleDescriptor)
		ReleaseTupleDesc(slot->tts_tupleDescriptor);
	if (!TTS_FIXED(slot))
	{
		if (slot->tts_values)
			pfree(slot->tts_values);
		if (slot->tts_isnull)
			pfree(slot->tts_isnull);
	}
	pfree(slot);
}


/* ----------------------------------------------------------------
 *				  tuple table slot accessor functions
 * ----------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】ExecSetSlotDescriptor —— 运行时绑定元组描述符
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给非固定描述符的槽更换/绑定元组描述符。旧描述符引用、values/isnull
 *   数组一并释放后重建（先 ExecClearTuple 保证槽为空再动结构，避免悬挂
 *   引用）。
 *
 * 适用场景：扫描前才知道返回行类型（如通用节点、临时行类型）的节点；
 * 若类型固定不变应优先用 MakeTupleTableSlot 的固定描述符模式。
 * ============================================================================
 */
void
ExecSetSlotDescriptor(TupleTableSlot *slot, /* slot to change */
					  TupleDesc tupdesc)	/* new tuple descriptor */
{
	Assert(!TTS_FIXED(slot));

	/* For safety, make sure slot is empty before changing it */
	ExecClearTuple(slot);

	/*
	 * Release any old descriptor.  Also release old Datum/isnull arrays if
	 * present (we don't bother to check if they could be re-used).
	 */
	if (slot->tts_tupleDescriptor)
		ReleaseTupleDesc(slot->tts_tupleDescriptor);

	if (slot->tts_values)
		pfree(slot->tts_values);
	if (slot->tts_isnull)
		pfree(slot->tts_isnull);

	/*
	 * Install the new descriptor; if it's refcounted, bump its refcount.
	 */
	slot->tts_tupleDescriptor = tupdesc;
	PinTupleDesc(tupdesc);

	/*
	 * Allocate Datum/isnull arrays of the appropriate size.  These must have
	 * the same lifetime as the slot, so allocate in the slot's own context.
	 */
	slot->tts_values = (Datum *)
		MemoryContextAlloc(slot->tts_mcxt, tupdesc->natts * sizeof(Datum));

	/*
	 * We round the size of tts_isnull up to the next highest multiple of 8.
	 * This is needed as populate_isnull_array() operates on 8 elements at a
	 * time when converting a tuple's NULL bitmap into a boolean array.
	 */
	slot->tts_isnull = (bool *)
		MemoryContextAlloc(slot->tts_mcxt, TYPEALIGN(8, tupdesc->natts * sizeof(bool)));
}

/*
 * ============================================================================
 * 【中文注释】ExecStoreHeapTuple —— 存入堆元组（堆元组槽专用）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把堆元组放进 TTSOpsHeapTuple 槽。shouldFree 指示槽清空时是否代释放
 *   （pfree）元组：
 *   - true：临时构造的元组（投影/触发器结果），槽接管所有权；
 *   - false：元组属于更下层的执行节点（如子计划的槽），本层只借用指针，
 *     且必须保证本层在用完前下层不会释放它——不确定时请 heap_copytuple
 *     拷贝一份再以 true 存入。
 *
 * 注意：仅当目标槽保证是堆元组槽时使用；类型不确定的场合用（更贵的）
 * ExecForceStoreHeapTuple 自动转换。
 * ============================================================================
 */
TupleTableSlot *
ExecStoreHeapTuple(HeapTuple tuple,
				   TupleTableSlot *slot,
				   bool shouldFree)
{
	/*
	 * sanity checks
	 */
	Assert(tuple != NULL);
	Assert(slot != NULL);
	Assert(slot->tts_tupleDescriptor != NULL);

	if (unlikely(!TTS_IS_HEAPTUPLE(slot)))
		elog(ERROR, "trying to store a heap tuple into wrong type of slot");
	tts_heap_store_tuple(slot, tuple, shouldFree);

	slot->tts_tableOid = tuple->t_tableOid;

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】ExecStoreBufferHeapTuple —— 存入缓冲页内元组（零拷贝）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把磁盘缓冲页里的元组放进 TTSOpsBufferHeapTuple 槽。槽会自行为该页
 *   获取 buffer pin（调用方已有 pin 时由 tts_buffer_heap_store_tuple 再
 *   引用一次），pin 一直持有到槽被清空，保证扫描期间页内元组内存有效。
 *
 * 配套 ExecStorePinnedBufferHeapTuple：把调用方已有 pin 直接"转移"给槽
 * （调用方不得再释放），省一次引用计数往返。
 * ============================================================================
 */
TupleTableSlot *
ExecStoreBufferHeapTuple(HeapTuple tuple,
						 TupleTableSlot *slot,
						 Buffer buffer)
{
	/*
	 * sanity checks
	 */
	Assert(tuple != NULL);
	Assert(slot != NULL);
	Assert(slot->tts_tupleDescriptor != NULL);
	Assert(BufferIsValid(buffer));

	if (unlikely(!TTS_IS_BUFFERTUPLE(slot)))
		elog(ERROR, "trying to store an on-disk heap tuple into wrong type of slot");
	tts_buffer_heap_store_tuple(slot, tuple, buffer, false);

	slot->tts_tableOid = tuple->t_tableOid;

	return slot;
}

/*
 * Like ExecStoreBufferHeapTuple, but transfer an existing pin from the caller
 * to the slot, i.e. the caller doesn't need to, and may not, release the pin.
 */
TupleTableSlot *
ExecStorePinnedBufferHeapTuple(HeapTuple tuple,
							   TupleTableSlot *slot,
							   Buffer buffer)
{
	/*
	 * sanity checks
	 */
	Assert(tuple != NULL);
	Assert(slot != NULL);
	Assert(slot->tts_tupleDescriptor != NULL);
	Assert(BufferIsValid(buffer));

	if (unlikely(!TTS_IS_BUFFERTUPLE(slot)))
		elog(ERROR, "trying to store an on-disk heap tuple into wrong type of slot");
	tts_buffer_heap_store_tuple(slot, tuple, buffer, true);

	slot->tts_tableOid = tuple->t_tableOid;

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】ExecStoreMinimalTuple —— 存入最小元组（最小元组槽专用）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 MinimalTuple 放进 TTSOpsMinimalTuple 槽；shouldFree 语义同
 *   ExecStoreHeapTuple（true=槽接管所有权，清槽时释放）。
 * 目标槽类型不确定时用 ExecForceStoreMinimalTuple。
 * ============================================================================
 */
TupleTableSlot *
ExecStoreMinimalTuple(MinimalTuple mtup,
					  TupleTableSlot *slot,
					  bool shouldFree)
{
	/*
	 * sanity checks
	 */
	Assert(mtup != NULL);
	Assert(slot != NULL);
	Assert(slot->tts_tupleDescriptor != NULL);

	if (unlikely(!TTS_IS_MINIMALTUPLE(slot)))
		elog(ERROR, "trying to store a minimal tuple into wrong type of slot");
	tts_minimal_store_tuple(slot, mtup, shouldFree);

	return slot;
}

/*
 * ============================================================================
 * 【中文注释】ExecForceStoreHeapTuple —— 向任意类型槽存入堆元组（自动转换）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   不关心目标槽类型的通用存元组入口，按槽类型三分支处理：
 *   - 堆元组槽：直接存（零拷贝）；
 *   - 缓冲槽：拷贝进槽内存并置 SHOULDFREE（不能破坏"缓冲槽必须持 pin"
 *     的约束，因此宁可拷贝）；
 *   - 其他（虚拟/最小）：解包进 values/isnull 数组后 ExecStoreVirtualTuple
 *     （虚拟形式）；shouldFree 时先物化再释放传入元组，保证槽内容独立。
 *
 * 配套 ExecForceStoreMinimalTuple：同构，只是输入换成 MinimalTuple
 * （最小槽直接存，其他槽走解包→虚拟存储路径）。
 * ============================================================================
 */
void
ExecForceStoreHeapTuple(HeapTuple tuple,
						TupleTableSlot *slot,
						bool shouldFree)
{
	if (TTS_IS_HEAPTUPLE(slot))
	{
		ExecStoreHeapTuple(tuple, slot, shouldFree);
	}
	else if (TTS_IS_BUFFERTUPLE(slot))
	{
		MemoryContext oldContext;
		BufferHeapTupleTableSlot *bslot = (BufferHeapTupleTableSlot *) slot;

		ExecClearTuple(slot);
		slot->tts_flags &= ~TTS_FLAG_EMPTY;
		oldContext = MemoryContextSwitchTo(slot->tts_mcxt);
		bslot->base.tuple = heap_copytuple(tuple);
		slot->tts_flags |= TTS_FLAG_SHOULDFREE;
		MemoryContextSwitchTo(oldContext);

		if (shouldFree)
			pfree(tuple);
	}
	else
	{
		ExecClearTuple(slot);
		heap_deform_tuple(tuple, slot->tts_tupleDescriptor,
						  slot->tts_values, slot->tts_isnull);
		ExecStoreVirtualTuple(slot);

		if (shouldFree)
		{
			ExecMaterializeSlot(slot);
			pfree(tuple);
		}
	}
}

/*
 * Store a MinimalTuple into any kind of slot, performing conversion if
 * necessary.
 */
void
ExecForceStoreMinimalTuple(MinimalTuple mtup,
						   TupleTableSlot *slot,
						   bool shouldFree)
{
	if (TTS_IS_MINIMALTUPLE(slot))
	{
		tts_minimal_store_tuple(slot, mtup, shouldFree);
	}
	else
	{
		HeapTupleData htup;

		ExecClearTuple(slot);

		htup.t_len = mtup->t_len + MINIMAL_TUPLE_OFFSET;
		htup.t_data = (HeapTupleHeader) ((char *) mtup - MINIMAL_TUPLE_OFFSET);
		heap_deform_tuple(&htup, slot->tts_tupleDescriptor,
						  slot->tts_values, slot->tts_isnull);
		ExecStoreVirtualTuple(slot);

		if (shouldFree)
		{
			ExecMaterializeSlot(slot);
			pfree(mtup);
		}
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecStoreVirtualTuple —— 虚拟元组装载协议入口
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   标记槽为"已装载虚拟元组"。使用协议（三板斧，避免一次数据拷贝）：
 *     1) ExecClearTuple 清空槽；
 *     2) 直接向 tts_values/tts_isnull 数组写入各列值；
 *     3) 调用本函数置有效位（清除 EMPTY、tts_nvalid = natts）。
 * 注意本函数只作标记，不拷贝数据；调用方须保证已写全所有列。
 * 配套 ExecStoreAllNullTuple：把全部列置 NULL 的便捷装载
 * （清空→数组清零→标记有效，与 ExecClearTuple 的"空槽"语义相反——
 * 它是"满槽"）。
 * ExecStoreHeapTupleDatum：把复合类型 Datum（HeapTupleHeader）解包进
 * 虚拟槽（依赖 datum 存活，物化前不得释放 datum）。
 * ============================================================================
 */
TupleTableSlot *
ExecStoreVirtualTuple(TupleTableSlot *slot)
{
	/*
	 * sanity checks
	 */
	Assert(slot != NULL);
	Assert(slot->tts_tupleDescriptor != NULL);
	Assert(TTS_EMPTY(slot));

	slot->tts_flags &= ~TTS_FLAG_EMPTY;
	slot->tts_nvalid = slot->tts_tupleDescriptor->natts;

	return slot;
}

/* --------------------------------
 *		ExecStoreAllNullTuple
 *			Set up the slot to contain a null in every column.
 *
 * At first glance this might sound just like ExecClearTuple, but it's
 * entirely different: the slot ends up full, not empty.
 * --------------------------------
 */
TupleTableSlot *
ExecStoreAllNullTuple(TupleTableSlot *slot)
{
	/*
	 * sanity checks
	 */
	Assert(slot != NULL);
	Assert(slot->tts_tupleDescriptor != NULL);

	/* Clear any old contents */
	ExecClearTuple(slot);

	/*
	 * Fill all the columns of the virtual tuple with nulls
	 */
	MemSet(slot->tts_values, 0,
		   slot->tts_tupleDescriptor->natts * sizeof(Datum));
	memset(slot->tts_isnull, true,
		   slot->tts_tupleDescriptor->natts * sizeof(bool));

	return ExecStoreVirtualTuple(slot);
}

/*
 * Store a HeapTuple in datum form, into a slot. That always requires
 * deforming it and storing it in virtual form.
 *
 * Until the slot is materialized, the contents of the slot depend on the
 * datum.
 */
void
ExecStoreHeapTupleDatum(Datum data, TupleTableSlot *slot)
{
	HeapTupleData tuple = {0};
	HeapTupleHeader td;

	td = DatumGetHeapTupleHeader(data);

	tuple.t_len = HeapTupleHeaderGetDatumLength(td);
	tuple.t_self = td->t_ctid;
	tuple.t_data = td;

	ExecClearTuple(slot);

	heap_deform_tuple(&tuple, slot->tts_tupleDescriptor,
					  slot->tts_values, slot->tts_isnull);
	ExecStoreVirtualTuple(slot);
}

/*
 * ============================================================================
 * 【中文注释】ExecFetchSlotHeapTuple —— 统一取堆元组（所有槽类型）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   以 HeapTuple 形式返回槽内容。两条路径：
 *   - 槽实现支持 get_heap_tuple（堆/缓冲槽）：直接返回内部元组指针
 *     （shouldFree=false，只读，仍依赖槽的存储）；
 *   - 不支持（虚拟/最小槽）：调用 copy_heap_tuple 即时构造一个
 *     （shouldFree=true，调用方负责释放）。
 *
 * materialize 参数：为真时先把槽内容物化到槽自身上下文（释放 buffer pin、
 * 元组归槽所有），保证返回元组及槽内容在后续任意使用中安全——代价是
 * 一次拷贝。
 * ============================================================================
 */
HeapTuple
ExecFetchSlotHeapTuple(TupleTableSlot *slot, bool materialize, bool *shouldFree)
{
	/*
	 * sanity checks
	 */
	Assert(slot != NULL);
	Assert(!TTS_EMPTY(slot));

	/* Materialize the tuple so that the slot "owns" it, if requested. */
	if (materialize)
		slot->tts_ops->materialize(slot);

	if (slot->tts_ops->get_heap_tuple == NULL)
	{
		if (shouldFree)
			*shouldFree = true;
		return slot->tts_ops->copy_heap_tuple(slot);
	}
	else
	{
		if (shouldFree)
			*shouldFree = false;
		return slot->tts_ops->get_heap_tuple(slot);
	}
}

/*
 * ============================================================================
 * 【中文注释】ExecFetchSlotMinimalTuple —— 统一取最小元组（所有槽类型）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   以 MinimalTuple 形式返回槽内容。支持 get_minimal_tuple 的槽（最小
 *   槽）直接返回其持有的最小元组（shouldFree=false，只读）；否则调用
 *   copy_minimal_tuple 构造拷贝（shouldFree=true，可写）。
 * 配套 ExecFetchSlotHeapTupleDatum：把槽内容转成复合类型 Datum
 * （heap_copy_tuple_as_datum 会顺带做行类型"福佑"，结果总是全新 palloc
 * 在调用方上下文，使用后需自行释放）。
 * ============================================================================
 */
MinimalTuple
ExecFetchSlotMinimalTuple(TupleTableSlot *slot,
						  bool *shouldFree)
{
	/*
	 * sanity checks
	 */
	Assert(slot != NULL);
	Assert(!TTS_EMPTY(slot));

	if (slot->tts_ops->get_minimal_tuple)
	{
		if (shouldFree)
			*shouldFree = false;
		return slot->tts_ops->get_minimal_tuple(slot);
	}
	else
	{
		if (shouldFree)
			*shouldFree = true;
		return slot->tts_ops->copy_minimal_tuple(slot, 0);
	}
}

/* --------------------------------
 *		ExecFetchSlotHeapTupleDatum
 *			Fetch the slot's tuple as a composite-type Datum.
 *
 *		The result is always freshly palloc'd in the caller's memory context.
 * --------------------------------
 */
Datum
ExecFetchSlotHeapTupleDatum(TupleTableSlot *slot)
{
	HeapTuple	tup;
	TupleDesc	tupdesc;
	bool		shouldFree;
	Datum		ret;

	/* Fetch slot's contents in regular-physical-tuple form */
	tup = ExecFetchSlotHeapTuple(slot, false, &shouldFree);
	tupdesc = slot->tts_tupleDescriptor;

	/* Convert to Datum form */
	ret = heap_copy_tuple_as_datum(tup, tupdesc);

	if (shouldFree)
		pfree(tup);

	return ret;
}

/* ----------------------------------------------------------------
 *				convenience initialization routines
 * ----------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】ExecInitResultTypeTL —— 由 targetlist 推导结果元组描述符
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   用计划节点 targetlist 生成结果元组描述符（ExecTypeFromTL），暂存到
 *   ps_ResultTupleDesc。后续 ExecInitResultSlot 用它创建结果槽。
 * ============================================================================
 */
void
ExecInitResultTypeTL(PlanState *planstate)
{
	TupleDesc	tupDesc = ExecTypeFromTL(planstate->plan->targetlist);

	planstate->ps_ResultTupleDesc = tupDesc;
}

/* --------------------------------
 *		ExecInit{Result,Scan,Extra}TupleSlot[TL]
 *
 *		These are convenience routines to initialize the specified slot
 *		in nodes inheriting the appropriate state.  ExecInitExtraTupleSlot
 *		is used for initializing special-purpose slots.
 * --------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】ExecInitResultSlot / ExecInitResultTupleSlotTL —— 结果槽初始化
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   ExecInitResultSlot：按先前算好的 ps_ResultTupleDesc 在元组表登记一个
 *   结果槽（tts_ops 决定槽类型），并缓存槽类型到 resultops 字段（配合
 *   ExecGetResultSlotOps 供上层查询，如 append 求公共槽类型）；
 *   ExecInitResultTupleSlotTL：一步到位版——先 ExecInitResultTypeTL 再
 *   ExecInitResultSlot。
 *
 * 业务场景：几乎所有执行节点初始化时都要"准备输出槽"，两函数是节点
 * 初始化代码的标准开场白。
 * ============================================================================
 */
void
ExecInitResultSlot(PlanState *planstate, const TupleTableSlotOps *tts_ops)
{
	TupleTableSlot *slot;

	slot = ExecAllocTableSlot(&planstate->state->es_tupleTable,
							  planstate->ps_ResultTupleDesc, tts_ops, 0);
	planstate->ps_ResultTupleSlot = slot;

	planstate->resultopsfixed = planstate->ps_ResultTupleDesc != NULL;
	planstate->resultops = tts_ops;
	planstate->resultopsset = true;
}

/* ----------------
 *		ExecInitResultTupleSlotTL
 *
 *		Initialize result tuple slot, using the plan node's targetlist.
 * ----------------
 */
void
ExecInitResultTupleSlotTL(PlanState *planstate,
						  const TupleTableSlotOps *tts_ops)
{
	ExecInitResultTypeTL(planstate);
	ExecInitResultSlot(planstate, tts_ops);
}

/*
 * ============================================================================
 * 【中文注释】ExecInitScanTupleSlot —— 扫描元组槽初始化
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   为扫描类节点创建 ss_ScanTupleSlot（存放扫描到的原始行）并登记进元组
 *   表；tupledesc 固定槽的行类型，同时记录扫描槽类型到 scanops 字段
 *   （供上层 ExecGetScanSlotOps 等查询）。
 * ============================================================================
 */
void
ExecInitScanTupleSlot(EState *estate, ScanState *scanstate,
					  TupleDesc tupledesc, const TupleTableSlotOps *tts_ops,
					  uint16 flags)
{
	scanstate->ss_ScanTupleSlot = ExecAllocTableSlot(&estate->es_tupleTable,
													 tupledesc, tts_ops, flags);
	scanstate->ps.scandesc = tupledesc;
	scanstate->ps.scanopsfixed = tupledesc != NULL;
	scanstate->ps.scanops = tts_ops;
	scanstate->ps.scanopsset = true;
}

/*
 * ============================================================================
 * 【中文注释】ExecInitExtraTupleSlot —— 特殊用途槽
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   创建登记在元组表里的"杂项"槽（无固定描述符或类型各异的中间槽）。
 *   tupledesc 为 NULL 时调用方须先用 ExecSetSlotDescriptor 绑定。
 * 配套 ExecInitNullTupleSlot：直接造一个"全 NULL 元组"的槽——外连接
 * 补空行时用它充当"缺失一侧"的输入行。
 * ============================================================================
 */
TupleTableSlot *
ExecInitExtraTupleSlot(EState *estate,
					   TupleDesc tupledesc,
					   const TupleTableSlotOps *tts_ops)
{
	return ExecAllocTableSlot(&estate->es_tupleTable, tupledesc, tts_ops, 0);
}

/* ----------------
 *		ExecInitNullTupleSlot
 *
 * Build a slot containing an all-nulls tuple of the given type.
 * This is used as a substitute for an input tuple when performing an
 * outer join.
 * ----------------
 */
TupleTableSlot *
ExecInitNullTupleSlot(EState *estate, TupleDesc tupType,
					  const TupleTableSlotOps *tts_ops)
{
	TupleTableSlot *slot = ExecInitExtraTupleSlot(estate, tupType, tts_ops);

	return ExecStoreAllNullTuple(slot);
}

/* ---------------------------------------------------------------
 *      Routines for setting/accessing attributes in a slot.
 * ---------------------------------------------------------------
 */

/*
 * ============================================================================
 * 【中文注释】slot_getmissingattrs —— 补齐缺失列（默认值或 NULL）
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   物理元组的列数可能少于描述符（表结构变更/旧元组），把
 *   [startAttNum, lastAttNum) 区间的列填上：描述符登记了缺失默认值
 *   （constr->missing，即 ALTER TABLE ... ADD COLUMN ... DEFAULT 的优化）
 *   则用默认值，否则填 NULL。列号越界时报错。
 *
 * 暴露原因：JIT 编译的元组解包需要直接调用它；除此之外只在本文件使用。
 * 配套 slot_getsomeattrs_int：slot_getsomeattrs 的 JIT 导出包装
 * （保持可尾调用优化的形状，除委托外不放任何代码）。
 * ============================================================================
 */
void
slot_getmissingattrs(TupleTableSlot *slot, int startAttNum, int lastAttNum)
{
	AttrMissing *attrmiss = NULL;

	/* Check for invalid attnums */
	if (unlikely(lastAttNum > slot->tts_tupleDescriptor->natts))
		elog(ERROR, "invalid attribute number %d", lastAttNum);

	if (slot->tts_tupleDescriptor->constr)
		attrmiss = slot->tts_tupleDescriptor->constr->missing;

	if (!attrmiss)
	{
		/* no missing values array at all, so just fill everything in as NULL */
		for (int attnum = startAttNum; attnum < lastAttNum; attnum++)
		{
			slot->tts_values[attnum] = (Datum) 0;
			slot->tts_isnull[attnum] = true;
		}
	}
	else
	{
		/* use attrmiss to set the missing values */
		for (int attnum = startAttNum; attnum < lastAttNum; attnum++)
		{
			slot->tts_values[attnum] = attrmiss[attnum].am_value;
			slot->tts_isnull[attnum] = !attrmiss[attnum].am_present;
		}
	}
}

/*
 * slot_getsomeattrs_int
 *		external function to call getsomeattrs() for use in JIT
 */
void
slot_getsomeattrs_int(TupleTableSlot *slot, int attnum)
{
	/* Check for caller errors */
	Assert(slot->tts_nvalid < attnum);	/* checked in slot_getsomeattrs */
	Assert(attnum > 0);

	/* Fetch as many attributes as possible from the underlying tuple. */
	slot->tts_ops->getsomeattrs(slot, attnum);

	/*
	 * Avoid putting new code here as that would prevent the compiler from
	 * using the sibling call optimization for the above function.
	 */
}

/*
 * ============================================================================
 * 【中文注释】ExecTypeFromTL / ExecCleanTypeFromTL —— 由 targetlist 造描述符
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   从（解析/计划阶段的）targetlist 生成结果元组描述符：逐 TargetEntry
 *   取列名/类型/typmod/排序规则填入模板描述符，再 TupleDescFinalize
 *   固化（预计算 attcacheoff 等解包加速数据）。
 *
 * 差异：ExecTypeFromTL 保留 resjunk 列（内部传递用的过滤/排序键列），
 * ExecCleanTypeFromTL 剔除它们（对外可见的结果行）。
 * 共同实现 ExecTypeFromTLInternal 以 skipjunk 区分。
 *
 * 相关：ExecTypeFromExprList 处理"裸表达式列表"（无名字，如 SRF
 * 结果）；ExecTypeSetColNames 给尚未 bless 的 RECORD 描述符补列名
 * （别名列表驱动，跳过空名与已删除列）。
 * ============================================================================
 */
TupleDesc
ExecTypeFromTL(List *targetList)
{
	return ExecTypeFromTLInternal(targetList, false);
}

/* ----------------------------------------------------------------
 *		ExecCleanTypeFromTL
 *
 *		Same as above, but resjunk columns are omitted from the result.
 * ----------------------------------------------------------------
 */
TupleDesc
ExecCleanTypeFromTL(List *targetList)
{
	return ExecTypeFromTLInternal(targetList, true);
}

static TupleDesc
ExecTypeFromTLInternal(List *targetList, bool skipjunk)
{
	TupleDesc	typeInfo;
	ListCell   *l;
	int			len;
	int			cur_resno = 1;

	if (skipjunk)
		len = ExecCleanTargetListLength(targetList);
	else
		len = ExecTargetListLength(targetList);
	typeInfo = CreateTemplateTupleDesc(len);

	foreach(l, targetList)
	{
		TargetEntry *tle = lfirst(l);

		if (skipjunk && tle->resjunk)
			continue;
		TupleDescInitEntry(typeInfo,
						   cur_resno,
						   tle->resname,
						   exprType((Node *) tle->expr),
						   exprTypmod((Node *) tle->expr),
						   0);
		TupleDescInitEntryCollation(typeInfo,
									cur_resno,
									exprCollation((Node *) tle->expr));
		cur_resno++;
	}

	TupleDescFinalize(typeInfo);

	return typeInfo;
}

/*
 * ExecTypeFromExprList - build a tuple descriptor from a list of Exprs
 *
 * This is roughly like ExecTypeFromTL, but we work from bare expressions
 * not TargetEntrys.  No names are attached to the tupledesc's columns.
 */
TupleDesc
ExecTypeFromExprList(List *exprList)
{
	TupleDesc	typeInfo;
	ListCell   *lc;
	int			cur_resno = 1;

	typeInfo = CreateTemplateTupleDesc(list_length(exprList));

	foreach(lc, exprList)
	{
		Node	   *e = lfirst(lc);

		TupleDescInitEntry(typeInfo,
						   cur_resno,
						   NULL,
						   exprType(e),
						   exprTypmod(e),
						   0);
		TupleDescInitEntryCollation(typeInfo,
									cur_resno,
									exprCollation(e));
		cur_resno++;
	}

	TupleDescFinalize(typeInfo);

	return typeInfo;
}

/*
 * ExecTypeSetColNames - set column names in a RECORD TupleDesc
 *
 * Column names must be provided as an alias list (list of String nodes).
 */
void
ExecTypeSetColNames(TupleDesc typeInfo, List *namesList)
{
	int			colno = 0;
	ListCell   *lc;

	/* It's only OK to change col names in a not-yet-blessed RECORD type */
	Assert(typeInfo->tdtypeid == RECORDOID);
	Assert(typeInfo->tdtypmod < 0);

	foreach(lc, namesList)
	{
		char	   *cname = strVal(lfirst(lc));
		Form_pg_attribute attr;

		/* Guard against too-long names list (probably can't happen) */
		if (colno >= typeInfo->natts)
			break;
		attr = TupleDescAttr(typeInfo, colno);
		colno++;

		/*
		 * Do nothing for empty aliases or dropped columns (these cases
		 * probably can't arise in RECORD types, either)
		 */
		if (cname[0] == '\0' || attr->attisdropped)
			continue;

		/* OK, assign the column name */
		namestrcpy(&(attr->attname), cname);
	}
}

/*
 * ============================================================================
 * 【中文注释】BlessTupleDesc —— "福佑"描述符：给 RECORD 类型正式登记
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   保证用该描述符构造的复合类型 Datum 携带合法的类型信息。来自系统表
 *   （relcache）的描述符天然合法；临时制造的 RECORD 描述符（tdtypmod<0）
 *   则调用 assign_record_type_typmod 向 typcache 注册一个正式 typmod，
 *   之后所有用它的复合 Datum 都能被正确解析（SRF 返回记录行必需）。
 * 前置条件：描述符已 TupleDescFinalize。
 *
 * 后续函数（TupleDescGetAttInMetadata / BuildTupleFromCStrings）：为
 * "从 C 字符串批量构造元组"提供支持——前者预取各列的输入函数
 * （"in"函数）、IO 参数与 typmod；后者把字符串数组逐个调用输入函数
 * 转成 Datum（NULL 字符串=该列 NULL，但函数仍被调用以支持域约束），
 * 再 heap_form_tuple 成形。
 * ============================================================================
 */
TupleDesc
BlessTupleDesc(TupleDesc tupdesc)
{
	/* Did someone forget to call TupleDescFinalize()? */
	Assert(tupdesc->firstNonCachedOffsetAttr >= 0);

	if (tupdesc->tdtypeid == RECORDOID &&
		tupdesc->tdtypmod < 0)
		assign_record_type_typmod(tupdesc);

	return tupdesc;				/* just for notational convenience */
}

/*
 * ============================================================================
 * 【中文注释】TupleDescGetAttInMetadata —— 预取列输入信息
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   基于描述符准备 AttInMetadata：福佑描述符 + 为每列预取"输入函数
 *   （text 转类型的 in 函数）"、IO 参数与 typmod，供
 *   BuildTupleFromCStrings 批量建元组复用（SRF 返回多行时避免重复查找）。
 * ============================================================================
 */
AttInMetadata *
TupleDescGetAttInMetadata(TupleDesc tupdesc)
{
	int			natts = tupdesc->natts;
	int			i;
	Oid			atttypeid;
	Oid			attinfuncid;
	FmgrInfo   *attinfuncinfo;
	Oid		   *attioparams;
	int32	   *atttypmods;
	AttInMetadata *attinmeta;

	attinmeta = palloc_object(AttInMetadata);

	/* "Bless" the tupledesc so that we can make rowtype datums with it */
	attinmeta->tupdesc = BlessTupleDesc(tupdesc);

	/*
	 * Gather info needed later to call the "in" function for each attribute
	 */
	attinfuncinfo = (FmgrInfo *) palloc0(natts * sizeof(FmgrInfo));
	attioparams = (Oid *) palloc0(natts * sizeof(Oid));
	atttypmods = (int32 *) palloc0(natts * sizeof(int32));

	for (i = 0; i < natts; i++)
	{
		Form_pg_attribute att = TupleDescAttr(tupdesc, i);

		/* Ignore dropped attributes */
		if (!att->attisdropped)
		{
			atttypeid = att->atttypid;
			getTypeInputInfo(atttypeid, &attinfuncid, &attioparams[i]);
			fmgr_info(attinfuncid, &attinfuncinfo[i]);
			atttypmods[i] = att->atttypmod;
		}
	}
	attinmeta->attinfuncs = attinfuncinfo;
	attinmeta->attioparams = attioparams;
	attinmeta->atttypmods = atttypmods;

	return attinmeta;
}

/*
 * BuildTupleFromCStrings - build a HeapTuple given user data in C string form.
 * values is an array of C strings, one for each attribute of the return tuple.
 * A NULL string pointer indicates we want to create a NULL field.
 */
HeapTuple
BuildTupleFromCStrings(AttInMetadata *attinmeta, char **values)
{
	TupleDesc	tupdesc = attinmeta->tupdesc;
	int			natts = tupdesc->natts;
	Datum	   *dvalues;
	bool	   *nulls;
	int			i;
	HeapTuple	tuple;

	dvalues = (Datum *) palloc(natts * sizeof(Datum));
	nulls = (bool *) palloc(natts * sizeof(bool));

	/*
	 * Call the "in" function for each non-dropped attribute, even for nulls,
	 * to support domains.
	 */
	for (i = 0; i < natts; i++)
	{
		if (!TupleDescCompactAttr(tupdesc, i)->attisdropped)
		{
			/* Non-dropped attributes */
			dvalues[i] = InputFunctionCall(&attinmeta->attinfuncs[i],
										   values[i],
										   attinmeta->attioparams[i],
										   attinmeta->atttypmods[i]);
			if (values[i] != NULL)
				nulls[i] = false;
			else
				nulls[i] = true;
		}
		else
		{
			/* Handle dropped attributes by setting to NULL */
			dvalues[i] = (Datum) 0;
			nulls[i] = true;
		}
	}

	/*
	 * Form a tuple
	 */
	tuple = heap_form_tuple(tupdesc, dvalues, nulls);

	/*
	 * Release locally palloc'd space.  XXX would probably be good to pfree
	 * values of pass-by-reference datums, as well.
	 */
	pfree(dvalues);
	pfree(nulls);

	return tuple;
}

/*
 * ============================================================================
 * 【中文注释】HeapTupleHeaderGetDatum —— HeapTupleHeader 转复合类型 Datum
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   把 heap_form_tuple 刚造好的元组头转成复合类型 Datum（供函数返回
 *  RECORD 行使用）。不允许用于磁盘元组；描述符须已福佑。
 *
 * 实现要点：
 *   复合 Datum 不允许含外部 TOAST 指针（行值序列化时无法解引用），因此
 *   检测到有外部 toast 指针时（HeapTupleHeaderHasExternal），必须查回
 *   行类型描述符并 toast_flatten_tuple_to_datum 把外联大字段内联展开成
 *   新元组再返回。无外部指针则直接指针转 Datum 返回。
 * 注意：新元组分配在调用时的当前内存上下文，调用方不能中途切换上下文。
 * ============================================================================
 */
Datum
HeapTupleHeaderGetDatum(HeapTupleHeader tuple)
{
	Datum		result;
	TupleDesc	tupDesc;

	/* No work if there are no external TOAST pointers in the tuple */
	if (!HeapTupleHeaderHasExternal(tuple))
		return PointerGetDatum(tuple);

	/* Use the type data saved by heap_form_tuple to look up the rowtype */
	tupDesc = lookup_rowtype_tupdesc(HeapTupleHeaderGetTypeId(tuple),
									 HeapTupleHeaderGetTypMod(tuple));

	/* And do the flattening */
	result = toast_flatten_tuple_to_datum(tuple,
										  HeapTupleHeaderGetDatumLength(tuple),
										  tupDesc);

	ReleaseTupleDesc(tupDesc);

	return result;
}


/*
 * ============================================================================
 * 【中文注释】begin_tup_output_tupdesc / do_tup_output / do_text_output_multiline
 * / end_tup_output —— 面向目标接收者的直通输出
 * ----------------------------------------------------------------------------
 * 函数作用：
 *   给不需要完整执行器、只需把行直接投影给 DestReceiver 的命令（EXPLAIN、
 *   SHOW ALL）提供极简输出通道：
 *   - begin_tup_output_tupdesc：建一个临时槽并调用 rStartup 启动接收者；
 *   - do_tup_output：把 Datum/isnull 数组装进临时虚拟槽后
 *     dest->receiveSlot 送出；
 *   - do_text_output_multiline：单 TEXT 列输出，按换行拆段（EXPLAIN 文本
 *     行适配）；
 *   - end_tup_output：rShutdown 关停接收者（接收者自身销毁由调用方负责）
 *     并释放临时槽。
 * ============================================================================
 */
TupOutputState *
begin_tup_output_tupdesc(DestReceiver *dest,
						 TupleDesc tupdesc,
						 const TupleTableSlotOps *tts_ops)
{
	TupOutputState *tstate;

	tstate = palloc_object(TupOutputState);

	tstate->slot = MakeSingleTupleTableSlot(tupdesc, tts_ops);
	tstate->dest = dest;

	tstate->dest->rStartup(tstate->dest, (int) CMD_SELECT, tupdesc);

	return tstate;
}

/*
 * write a single tuple
 */
void
do_tup_output(TupOutputState *tstate, const Datum *values, const bool *isnull)
{
	TupleTableSlot *slot = tstate->slot;
	int			natts = slot->tts_tupleDescriptor->natts;

	/* make sure the slot is clear */
	ExecClearTuple(slot);

	/* insert data */
	memcpy(slot->tts_values, values, natts * sizeof(Datum));
	memcpy(slot->tts_isnull, isnull, natts * sizeof(bool));

	/* mark slot as containing a virtual tuple */
	ExecStoreVirtualTuple(slot);

	/* send the tuple to the receiver */
	(void) tstate->dest->receiveSlot(slot, tstate->dest);

	/* clean up */
	ExecClearTuple(slot);
}

/*
 * write a chunk of text, breaking at newline characters
 *
 * Should only be used with a single-TEXT-attribute tupdesc.
 */
void
do_text_output_multiline(TupOutputState *tstate, const char *txt)
{
	Datum		values[1];
	bool		isnull[1] = {false};

	while (*txt)
	{
		const char *eol;
		int			len;

		eol = strchr(txt, '\n');
		if (eol)
		{
			len = eol - txt;
			eol++;
		}
		else
		{
			len = strlen(txt);
			eol = txt + len;
		}

		values[0] = PointerGetDatum(cstring_to_text_with_len(txt, len));
		do_tup_output(tstate, values, isnull);
		pfree(DatumGetPointer(values[0]));
		txt = eol;
	}
}

void
end_tup_output(TupOutputState *tstate)
{
	tstate->dest->rShutdown(tstate->dest);
	/* note that destroying the dest is not ours to do */
	ExecDropSingleTupleTableSlot(tstate->slot);
	pfree(tstate);
}
