/*-------------------------------------------------------------------------
 *
 * buf_init.c
 *	  buffer manager initialization routines
 *
 * 【模块总览(中文)】
 * 本文件负责共享缓冲池(buffers pool)在共享内存中的"申请"与"初始化",
 * 是 PostgreSQL 启动流程中共享内存子系统回调本模块的入口:
 *
 * 1. request 阶段(BufferManagerShmemRequest):声明四块共享内存区域——
 *    a) BufferDescriptors:缓冲区描述符数组(NBuffers 个,每个按缓存行
 *       cacheline 对齐,防止多核"伪共享"(false sharing)导致性能下降);
 *    b) BufferBlocks:实际存放页数据的内存池(NBuffers * BLCKSZ 字节,
 *       按 I/O 页对齐,满足直接 I/O 要求);
 *    c) BufferIOCVArray:每缓冲区一个条件变量,用于等待 I/O 完成
 *       (AIO 时代替代旧版的每缓冲区 LWLock);
 *    d) CkptBufferIds:检查点排序用的临时数组。特意放进共享内存——
 *       检查点进行中(或检查点进程重启时)临时分配大内存可能失败,
 *       会造成麻烦,不如启动时一次分配好。
 *
 * 2. init 阶段(BufferManagerShmemInit):把描述符数组逐项初始化
 *    (清标签、state 置 0、buf_id 赋值、条件变量与等待队列初始化等),
 *    并初始化本后端进程私有的写回上下文(WritebackContext)。
 *
 * 3. attach 阶段(BufferManagerShmemAttach):非 postmaster 的进程在
 *    挂接共享内存后调用,只做进程私有的初始化。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/buffer/buf_init.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "storage/aio.h"
#include "storage/buf_internals.h"
#include "storage/bufmgr.h"
#include "storage/proclist.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"

BufferDescPadded *BufferDescriptors;
/* 缓冲区描述符数组(共享内存,已按缓存行填充对齐)。
 * 每个元素 = BufferDesc + padding,下标即缓冲区 id。
 * 宏 GetBufferDescriptor(i) 取第 i 个。 */
char	   *BufferBlocks;
/* 缓冲区数据池(共享内存):NBuffers * BLCKSZ 字节的连续内存,
 * 每个缓冲区一块;由宏 BufferGetBlock / BufferDescriptorGetBlock 换算。 */
ConditionVariableMinimallyPadded *BufferIOCVArray;
/* 每缓冲区一个条件变量:等待"某缓冲区的 I/O 完成"信号。
 * (AIO 实现中,BM_IO_IN_PROGRESS 清除时通过它唤醒等待者。) */
WritebackContext BackendWritebackContext;
/* 本后端进程私有的"延迟写回"上下文:把脏页写盘时机聚合成批,
 * 配合 OS 的写回(如 sync_file_range),提升顺序写性能。 */
CkptSortItem *CkptBufferIds;
/* 检查点排序数组(共享内存):检查点进程按"文件位置顺序"对脏缓冲区
 * 排序,使写盘尽量顺序化,减少磁盘寻道。 */

static void BufferManagerShmemRequest(void *arg);
static void BufferManagerShmemInit(void *arg);
static void BufferManagerShmemAttach(void *arg);

/* 注册到共享内存子系统的回调:postmaster 启动时先调 request 汇总内存
 * 需求,分配完成后调 init 做初始化;其他进程 attach 后调 attach。 */
const ShmemCallbacks BufferManagerShmemCallbacks = {
	.request_fn = BufferManagerShmemRequest,
	.init_fn = BufferManagerShmemInit,
	.attach_fn = BufferManagerShmemAttach,
};

/*
 * Data Structures:
 *		buffers live in a freelist and a lookup data structure.
 *
 *
 * Buffer Lookup:
 *		Two important notes.  First, the buffer has to be
 *		available for lookup BEFORE an IO begins.  Otherwise
 *		a second process trying to read the buffer will
 *		allocate its own copy and the buffer pool will
 *		become inconsistent.
 *
 * Buffer Replacement:
 *		see freelist.c.  A buffer cannot be replaced while in
 *		use either by data manager or during IO.
 *
 *
 * Synchronization/Locking:
 *
 * IO_IN_PROGRESS -- this is a flag in the buffer descriptor.
 *		It must be set when an IO is initiated and cleared at
 *		the end of the IO.  It is there to make sure that one
 *		process doesn't start to use a buffer while another is
 *		faulting it in.  see WaitIO and related routines.
 *
 * refcount --	Counts the number of processes holding pins on a buffer.
 *		A buffer is pinned during IO and immediately after a BufferAlloc().
 *		Pins must be released before end of transaction.  For efficiency the
 *		shared refcount isn't increased if an individual backend pins a buffer
 *		multiple times. Check the PrivateRefCount infrastructure in bufmgr.c.
 */


/*
 * Register shared memory area for the buffer pool.
 */
/* (中文)向共享内存子系统申报缓冲池所需的全部共享内存区域
 *
 * 【作用】启动早期被调用:声明四块内存区域(见文件头总览),并把分配
 * 好的指针分别写入对应全局变量。
 *
 * 【对齐设计】PostgreSQL 的共享内存分配器支持按调用方指定对齐:
 * - 描述符按缓存行对齐:相邻缓冲区描述符各占一条 cacheline,避免多个
 *   CPU 核同时读写相邻描述符时互相"踢"缓存行(伪共享),这是多核
 *   数据库性能的关键细节;
 * - 数据池按 I/O 页大小对齐:直接 I/O(direct I/O)/io_uring 要求
 *   缓冲区地址与长度页对齐,否则会失败或产生额外的拷贝;
 * - 条件变量同样按缓存行对齐。
 *
 * 【参数】arg —— 未使用(匹配回调签名)。
 * 【返回值】无(通过全局变量指针输出)。 */
static void
BufferManagerShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "Buffer Descriptors",
					   .size = NBuffers * sizeof(BufferDescPadded),
	/* Align descriptors to a cacheline boundary. */
					   .alignment = PG_CACHE_LINE_SIZE,
					   .ptr = (void **) &BufferDescriptors,
		);

	ShmemRequestStruct(.name = "Buffer Blocks",
					   .size = NBuffers * (Size) BLCKSZ,
	/* Align buffer pool on IO page size boundary. */
					   .alignment = PG_IO_ALIGN_SIZE,
					   .ptr = (void **) &BufferBlocks,
		);

	ShmemRequestStruct(.name = "Buffer IO Condition Variables",
					   .size = NBuffers * sizeof(ConditionVariableMinimallyPadded),
	/* Align descriptors to a cacheline boundary. */
					   .alignment = PG_CACHE_LINE_SIZE,
					   .ptr = (void **) &BufferIOCVArray,
		);

	/*
	 * The array used to sort to-be-checkpointed buffer ids is located in
	 * shared memory, to avoid having to allocate significant amounts of
	 * memory at runtime. As that'd be in the middle of a checkpoint, or when
	 * the checkpointer is restarted, memory allocation failures would be
	 * painful.
	 */
	ShmemRequestStruct(.name = "Checkpoint BufferIds",
					   .size = NBuffers * sizeof(CkptSortItem),
					   .ptr = (void **) &CkptBufferIds,
		);
}

/*
 * Initialize shared buffer pool
 *
 * This is called once during shared-memory initialization (either in the
 * postmaster, or in a standalone backend).
 */
/*
 * BufferManagerShmemInit
 *      (中文)初始化共享缓冲池(仅一次,postmaster 或单机后端启动时)
 *
 * 【作用】对每个缓冲区描述符逐项初始化:
 * - 清空页标签(tag);
 * - state 原子字段置 0(无 pin、无标志、无使用计数);
 * - 等待者进程号置为 INVALID(无人在等待该缓冲区的 cleanup 锁);
 * - buf_id 赋为数组下标(共享缓冲区的 id 从 0 开始,非负);
 * - 清空 AIO 等待引用;初始化"等待该缓冲区内容锁"的进程链表
 *   (lock_waiters,用于 PinCountWaiters 场景);
 * - 初始化该缓冲区专用的条件变量(BufferIOCVArray[i]),
 *   供等待 I/O 完成的进程使用。
 * 最后初始化本进程的延迟写回上下文(与 GUC backend_flush_after 联动)。
 *
 * 【注意】数据块(BufferBlocks)由系统清零(共享内存按需初始化为 0),
 * 这里不需要也不应该触碰它们。
 *
 * 【参数】arg —— 未使用。【返回值】无。 */
static void
BufferManagerShmemInit(void *arg)
{
	/*
	 * Initialize all the buffer headers.
	 */
	for (int i = 0; i < NBuffers; i++)
	{
		BufferDesc *buf = GetBufferDescriptor(i);

		ClearBufferTag(&buf->tag);

		pg_atomic_init_u64(&buf->state, 0);
		buf->wait_backend_pgprocno = INVALID_PROC_NUMBER;

		buf->buf_id = i;

		pgaio_wref_clear(&buf->io_wref);

		proclist_init(&buf->lock_waiters);
		ConditionVariableInit(BufferDescriptorGetIOCV(buf));
	}

	/* Initialize per-backend file flush context */
	WritebackContextInit(&BackendWritebackContext,
						 &backend_flush_after);
}

static void
BufferManagerShmemAttach(void *arg)
/* (中文)共享内存挂接回调:非 postmaster 进程(postmaster fork 出的
 * 子进程)在挂接共享内存后调用。此处只做进程私有状态的初始化
 * (每进程的延迟写回上下文),共享状态已在 postmaster 中初始化完毕。 */
{
	/* Initialize per-backend file flush context */
	WritebackContextInit(&BackendWritebackContext,
						 &backend_flush_after);
}
