/*-------------------------------------------------------------------------
 *
 * read_stream.c
 *	  Mechanism for accessing buffered relation data with look-ahead
 *
 * Code that needs to access relation data typically pins blocks one at a
 * time, often in a predictable order that might be sequential or data-driven.
 * Calling the simple ReadBuffer() function for each block is inefficient,
 * because blocks that are not yet in the buffer pool require I/O operations
 * that are small and might stall waiting for storage.  This mechanism looks
 * into the future and calls StartReadBuffers() and WaitReadBuffers() to read
 * neighboring blocks together and ahead of time, with an adaptive look-ahead
 * distance.
 *
 * A user-provided callback generates a stream of block numbers that is used
 * to form reads of up to io_combine_limit, by attempting to merge them with a
 * pending read.  When that isn't possible, the existing pending read is sent
 * to StartReadBuffers() so that a new one can begin to form.
 *
 * The algorithm for controlling the look-ahead distance is based on recent
 * cache / miss history, as well as whether we need to wait for I/O completion
 * after a miss.  When no I/O is necessary, there is no benefit in looking
 * ahead more than one block.  This is the default initial assumption.  When
 * blocks needing I/O are streamed, the combine distance is increased to
 * benefit from I/O combining and the read-ahead distance is increased
 * whenever we need to wait for I/O to try to benefit from increased I/O
 * concurrency. Both are reduced gradually when cached blocks are streamed.
 *
 * The main data structure is a circular queue of buffers of size
 * max_pinned_buffers plus some extra space for technical reasons, ready to be
 * returned by read_stream_next_buffer().  Each buffer also has an optional
 * variable sized object that is passed from the callback to the consumer of
 * buffers.
 *
 * Parallel to the queue of buffers, there is a circular queue of in-progress
 * I/Os that have been started with StartReadBuffers(), and for which
 * WaitReadBuffers() must be called before returning the buffer.
 *
 * For example, if the callback returns block numbers 10, 42, 43, 44, 60 in
 * successive calls, then these data structures might appear as follows:
 *
 *                          buffers buf/data       ios
 *
 *                          +----+  +-----+       +--------+
 *                          |    |  |     |  +----+ 42..44 | <- oldest_io_index
 *                          +----+  +-----+  |    +--------+
 *   oldest_buffer_index -> | 10 |  |  ?  |  | +--+ 60..60 |
 *                          +----+  +-----+  | |  +--------+
 *                          | 42 |  |  ?  |<-+ |  |        | <- next_io_index
 *                          +----+  +-----+    |  +--------+
 *                          | 43 |  |  ?  |    |  |        |
 *                          +----+  +-----+    |  +--------+
 *                          | 44 |  |  ?  |    |  |        |
 *                          +----+  +-----+    |  +--------+
 *                          | 60 |  |  ?  |<---+
 *                          +----+  +-----+
 *     next_buffer_index -> |    |  |     |
 *                          +----+  +-----+
 *
 * In the example, 5 buffers are pinned, and the next buffer to be streamed to
 * the client is block 10.  Block 10 was a hit and has no associated I/O, but
 * the range 42..44 requires an I/O wait before its buffers are returned, as
 * does block 60.
 *
 * 【模块总览(中文)】
 * 本文件实现"带前瞻(read-ahead)的流式读"(ReadStream):把用户通过
 * 回调给出的块号序列,在真正读取之前先行窥探,合并成最多 io_combine_limit
 * 块的大批量读,并提前交给缓冲管理器(StartReadBuffers / WaitReadBuffers)
 * 异步执行,让存储子系统始终"有事可做",从而用并发 I/O 掩盖磁盘延迟。
 *
 * 核心数据结构是两块并行的循环队列(详见 struct ReadStream):
 * 1) 缓冲区队列:最多 max_pinned_buffers 个缓冲槽,存放"已 pin、等待
 *    消费者取走"的 Buffer;队列尾部预留 io_combine_limit-1 个溢出槽,
 *    保证一次合并读的连续缓冲数组不会因环形绕回而断裂;
 * 2) 在途 I/O 队列:记录已交给 StartReadBuffers() 但尚未调用
 *    WaitReadBuffers() 的 ReadBuffersOperation,它们与缓冲区队列通过
 *    buffer_index 一一对应。
 *
 * 前瞻距离的自适应算法(readahead_distance / combine_distance)是全文
 * 的思想核心:
 * - 初始假设"数据全在缓冲池",两个距离都为 1;
 * - 消费缓冲时若被迫等待 I/O,readahead_distance 立即加倍(上限
 *   max_pinned_buffers),并设置 distance_decay_holdoff 保护期,防止
 *   在"缓存命中为主、偶发 I/O"的工作负载中距离过快衰减;
 * - 只要做过 I/O,combine_distance 就加倍(上限 io_combine_limit):
 *   即使数据全命中内核页缓存,大块读也能摊薄系统调用/提交开销;
 * - 在一段无 I/O 的窗口内,距离按 1 逐步递减,最终退回 1 并进入
 *   fast_path(单缓冲槽直通路径)。
 *
 * 与异步 I/O 的衔接:构建下一次读取时以批处理模式
 * (pgaio_enter_batchmode / pgaio_exit_batchmode)暂存多个 I/O、合并后
 * 一次性提交,摊薄提交开销;调用方也可用 READ_STREAM_USE_BATCHING 主动
 * 启用。
 *
 *
 * Portions Copyright (c) 2024-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/aio/read_stream.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "miscadmin.h"
#include "executor/instrument_node.h"
#include "storage/aio.h"
#include "storage/fd.h"
#include "storage/smgr.h"
#include "storage/read_stream.h"
#include "utils/memdebug.h"
#include "utils/rel.h"
#include "utils/spccache.h"

/* (中文)一个"已发出、但尚未等待完成"的读操作的记账单元:
 * - buffer_index : 该 I/O 完成后,受影响的第一块缓冲在缓冲区队列中的下标
 *                   (read_stream_next_buffer() 据此判断该缓冲是否需要等待);
 * - op           : ReadBuffersOperation 描述符,记录本次读的目标关系、
 *                   起始块号、缓冲数组指针等,由 StartReadBuffers() 填充。 */
typedef struct InProgressIO
{
	int16		buffer_index;
	ReadBuffersOperation op;
} InProgressIO;

/*
 * State for managing a stream of reads.
 */
/* (中文)读流(ReadStream)的主状态对象,一次 palloc 分配、贯穿流的一生。
 *
 * 环形缓冲区队列(下标 0..queue_size-1 为主区):
 * - buffers[]          : 缓冲队列;queue_size 之后的 queue_overflow 个槽
 *                         是溢出区,存放"一次合并读跨过队尾时"的缓冲副本
 *                         (双份副本在消费时都会被清空);
 * - oldest_buffer_index: 下一个要交付给消费者的缓冲槽;
 * - next_buffer_index  : 下一个要 pin 的缓冲槽;
 * - pinned_buffers     : 已被 pin、等待消费的缓冲个数;
 * - initialized_buffers: 已初始化为 InvalidBuffer 的槽数,用于区分
 *                         "从未用过"与"被消费清空"的槽;
 * - forwarded_buffers  : 上一次 StartReadBuffers() 因 pin 限额被截短时为
 *                         本次读"预存"的缓冲个数(这些 pin 已持有,但
 *                         不计入 pinned_buffers,见 read_stream_start_pending_read)。
 *
 * 在途 I/O 环形队列:
 * - ios[] / oldest_io_index / next_io_index / ios_in_progress:见文件头的
 *   图示说明。
 *
 * 前瞻距离状态机:
 * - combine_distance / readahead_distance : 允许合并/前瞻的最大块数,
 *   随"缓存命中/等待 I/O"的历史自适应增减;置 0 表示流已到终点;
 * - distance_decay_holdoff  : 近期做过 I/O 时的距离衰减保护期;
 * - resume_readahead_distance / resume_combine_distance:read_stream_pause()
 *   保存、read_stream_resume() 恢复的距离;
 * - seq_blocknum / seq_until_processed : 识别顺序访问段,配合内核预读
 *   (posix_fadvise)建议的发放与收回;
 * - pending_read_blocknum / pending_read_nblocks : 正在构建、尚未发出的读;
 * - buffered_blocknum : 单块"退回缓存",解决 I/O 拆分时的流控问题。
 *
 * 模式开关:
 * - sync_mode    : io_method=sync,退化为"建议式预读"伪异步;
 * - batch_mode   : 启用 AIO 批处理提交(READ_STREAM_USE_BATCHING);
 * - advice_enabled : 是否给内核发放预读建议;
 * - fast_path    : 全缓存扫描的直通路径(单缓冲槽、无队列管理);
 * - temporary    : 目标为临时表,走本地缓冲区。 */
struct ReadStream
{
	int16		max_ios;
	int16		io_combine_limit;
	int16		ios_in_progress;
	int16		queue_size;
	int16		max_pinned_buffers;
	int16		forwarded_buffers;
	int16		pinned_buffers;

	/*
	 * Limit of how far, in blocks, to look-ahead for IO combining and for
	 * read-ahead.
	 *
	 * The limits for read-ahead and combining are handled separately to allow
	 * for IO combining even in cases where the I/O subsystem can keep up at a
	 * low read-ahead distance, as doing larger IOs is more efficient.
	 *
	 * Set to 0 when the end of the stream is reached.
	 */
	int16		combine_distance;
	int16		readahead_distance;
	uint16		distance_decay_holdoff;
	int16		initialized_buffers;
	int16		resume_readahead_distance;
	int16		resume_combine_distance;
	int			read_buffers_flags;
	bool		sync_mode;		/* using io_method=sync */
	bool		batch_mode;		/* READ_STREAM_USE_BATCHING */
	bool		advice_enabled;
	bool		temporary;

	/* scan stats counters */
	IOStats    *stats;

	/*
	 * One-block buffer to support 'ungetting' a block number, to resolve flow
	 * control problems when I/Os are split.
	 */
	BlockNumber buffered_blocknum;

	/*
	 * The callback that will tell us which block numbers to read, and an
	 * opaque pointer that will be pass to it for its own purposes.
	 */
	ReadStreamBlockNumberCB callback;
	void	   *callback_private_data;

	/* Next expected block, for detecting sequential access. */
	BlockNumber seq_blocknum;
	BlockNumber seq_until_processed;

	/* The read operation we are currently preparing. */
	BlockNumber pending_read_blocknum;
	int16		pending_read_nblocks;

	/* Space for buffers and optional per-buffer private data. */
	size_t		per_buffer_data_size;
	void	   *per_buffer_data;

	/* Read operations that have been started but not waited for yet. */
	InProgressIO *ios;
	int16		oldest_io_index;
	int16		next_io_index;

	bool		fast_path;

	/* Circular queue of buffers. */
	int16		oldest_buffer_index;	/* Next pinned buffer to return */
	int16		next_buffer_index;	/* Index of next buffer to pin */
	Buffer		buffers[FLEXIBLE_ARRAY_MEMBER];
};

/*
 * Return a pointer to the per-buffer data by index.
 */
/*
 * (中文)按下标返回该缓冲槽对应的"每缓冲私有数据"区域指针。
 *
 * 【作用】per-buffer 数据是块号回调与消费者之间传递的每块元数据,在
 * read_stream_begin_impl() 里作为一整块内存分配在流对象末尾,与缓冲区
 * 队列一一对应。
 * 【设计思想】用"基址 + per_buffer_data_size * index"直接计算地址,
 * 省去一张指针数组,也保证各槽数据在内存中彼此相邻(利于缓存局部性)。
 *
 * 【参数】buffer_index:缓冲区队列下标。
 * 【返回值】对应私有数据区域的指针。
 */
static inline void *
get_per_buffer_data(ReadStream *stream, int16 buffer_index)
{
	return (char *) stream->per_buffer_data +
		stream->per_buffer_data_size * buffer_index;
}

/*
 * General-use ReadStreamBlockNumberCB for block range scans.  Loops over the
 * blocks [current_blocknum, last_exclusive).
 */
/*
 * (中文)通用的"块区间扫描"块号回调。
 *
 * 【作用】供顺序扫描等场景直接使用:从 current_blocknum 起依次吐出块号,
 * 到 last_exclusive(不含)为止。
 *
 * 【参数】callback_private_data:BlockRangeReadStreamPrivate 结构,内含
 * current_blocknum(下一次要吐出的块号,调用后自增)与 last_exclusive
 * (终点,不含);per_buffer_data:本块对应的私有数据区(本例未使用)。
 * 【返回值】下一个要读的块号;流结束时返回 InvalidBlockNumber。
 */
BlockNumber
block_range_read_stream_cb(ReadStream *stream,
						   void *callback_private_data,
						   void *per_buffer_data)
{
	BlockRangeReadStreamPrivate *p = callback_private_data;

	if (p->current_blocknum < p->last_exclusive)
		return p->current_blocknum++;

	return InvalidBlockNumber;
}

/*
 * (中文)统计"预读深度":消费者每取出一个缓冲,就记录此刻流中已 pin
 * 的缓冲个数。
 *
 * 【作用】用于计算平均前瞻深度(distance_sum / prefetch_count)与最大
 * 深度(distance_max),供 EXPLAIN ANALYZE 等展示流式扫描的预读效果。
 *
 * 【设计思想】采样点选在"返回一个缓冲给消费者"的时刻,恰好反映消费者
 * 眼中的前瞻余量;每块只采一次样,避免重复计数。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static inline void
read_stream_count_prefetch(ReadStream *stream)
{
	IOStats    *stats = stream->stats;

	if (stats == NULL)
		return;

	stats->prefetch_count++;
	stats->distance_sum += stream->pinned_buffers;
	if (stream->pinned_buffers > stats->distance_max)
		stats->distance_max = stream->pinned_buffers;
}

/*
 * (中文)统计 I/O 请求:请求次数、总块数、此刻的在途 I/O 数。
 *
 * 【作用】io_count / io_nblocks / io_in_progress 三个指标用于评估"合并
 * 读"的效果:平均每次请求的块数(io_nblocks / io_count)越大,合并越成功。
 *
 * 【参数】nblocks:本次发出的 I/O 覆盖的块数;in_progress:发出后的在途
 * I/O 总数(含本次)。
 * 【返回值】无。
 */
static inline void
read_stream_count_io(ReadStream *stream, int nblocks, int in_progress)
{
	IOStats    *stats = stream->stats;

	if (stats == NULL)
		return;

	stats->io_count++;
	stats->io_nblocks += nblocks;
	stats->io_in_progress += in_progress;
}

/*
 * (中文)统计"消费缓冲时被迫等待 I/O"的次数。
 *
 * 【作用】wait_count 是前瞻自适应算法的关键反馈信号:需要等待说明当前
 * 前瞻距离太小,应在 read_stream_next_buffer() 中加倍 readahead_distance。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static inline void
read_stream_count_wait(ReadStream *stream)
{
	IOStats    *stats = stream->stats;

	if (stats == NULL)
		return;

	stats->wait_count++;
}

/*
 * (中文)把流与一个 IOStats 统计结构绑定,开始收集扫描统计。
 *
 * 【作用】EXPLAIN ANALYZE 通过它把流的预读统计上报给执行器;绑定前先把
 * 距离容量(distance_capacity = max_pinned_buffers)记入统计,供上层换算
 * 前瞻深度百分比。
 *
 * 【参数】stats:目标统计结构(通常已由调用方清零);传 NULL 则关闭统计。
 * 【返回值】无。
 */
void
read_stream_enable_stats(ReadStream *stream, IOStats *stats)
{
	stream->stats = stats;
	if (stream->stats)
		stream->stats->distance_capacity = stream->max_pinned_buffers;
}

/*
 * (中文)向块号回调询问"下一个想读的块号",前面设有一个单块缓冲槽,使
 * read_stream_unget_block() 的"退回"成为可能。
 *
 * 【设计思想】当回调返回的块号无法立即处理(缓冲不足、I/O 已到上限)时,
 * 先把该块号暂存到 buffered_blocknum,下次调用优先返回它——在不改变回调
 * 语义(回调仍按顺序被调用)的前提下实现了流控。
 *
 * 【参数】per_buffer_data:准备分配给该块的私有数据区(可为 NULL);交给
 * 回调前先向 Valgrind 声明其内容未定义,以捕捉"回调没写、消费者却读"的
 * 漏初始化 bug。
 * 【返回值】下一个块号;回调报告流结束(InvalidBlockNumber)时返回
 * InvalidBlockNumber。
 */
static inline BlockNumber
read_stream_get_block(ReadStream *stream, void *per_buffer_data)
{
	BlockNumber blocknum;

	blocknum = stream->buffered_blocknum;
	if (blocknum != InvalidBlockNumber)
		stream->buffered_blocknum = InvalidBlockNumber;
	else
	{
		/*
		 * Tell Valgrind that the per-buffer data is undefined.  That replaces
		 * the "noaccess" state that was set when the consumer moved past this
		 * entry last time around the queue, and should also catch callbacks
		 * that fail to initialize data that the buffer consumer later
		 * accesses.  On the first go around, it is undefined already.
		 */
		VALGRIND_MAKE_MEM_UNDEFINED(per_buffer_data,
									stream->per_buffer_data_size);
		blocknum = stream->callback(stream,
									stream->callback_private_data,
									per_buffer_data);
	}

	return blocknum;
}

/*
 * (中文)把已从回调消费的一个块号"退回"到单块缓冲槽,留待稍后处理。
 *
 * 【作用】应对"缓冲区短缺 / 短读后的 I/O 限额"等场景:前瞻算法必须先
 * 把当前 pending read 发出才能继续构建下一个,于是把刚取到的块号退回,
 * 下次 read_stream_get_block() 会优先返回它。
 *
 * 【设计思想】只用单块缓存即可:一次最多只会退回一个块号,且退回的块号
 * 必然紧接着被消费,不存在累积。
 *
 * 【参数】blocknum:要退回的块号(必须有效)。
 * 【返回值】无。
 */
static inline void
read_stream_unget_block(ReadStream *stream, BlockNumber blocknum)
{
	/* We shouldn't ever unget more than one block. */
	Assert(stream->buffered_blocknum == InvalidBlockNumber);
	Assert(blocknum != InvalidBlockNumber);
	stream->buffered_blocknum = blocknum;
}

/*
 * (中文)把当前 pending read 尽量多地发出。若因每后端 pin 限额或缓冲
 * 管理器决定截短,则剩余部分留在 pending read 中,由下一次调用续发。
 *
 * 【作用】读操作的发起者:把 [pending_read_blocknum,
 * pending_read_blocknum + nblocks) 这一连续区间交给 StartReadBuffers(),
 * 并维护 pinned_buffers / ios_in_progress / forwarded_buffers / 距离衰减
 * 等全部记账字段。
 *
 * 【设计思想】
 * - 截短与转发(forward):StartReadBuffers() 返回的 nblocks 是实际
 *   pin 到的块数,可能小于请求(缓冲限额、页已由并发者读入等)。若实际
 *   pin 的缓冲区比请求多,多出的部分已在前一次调用中顺手 pin 好
 *   (forwarded buffers,留在队列原处),本函数把它们当作本次读的"前导
 *   块"计入限额、下次调用继续使用;流提前结束时这些缓冲会被释放;
 * - 循环队列绕回:给 StartReadBuffers() 的缓冲数组必须连续,因此把
 *   "跨过队尾"的缓冲复制一份到溢出区(queue_size 之后),主区那份留给
 *   消费者——两份在消费时都会被清空(见 read_stream_next_buffer());
 * - 距离衰减:若本次不需要等待 I/O 且此刻没有在途 I/O,则距离按 1
 *   递减(distance_decay_holdoff 保护期内不衰减),使全缓存扫描最终
 *   退回 fast_path;combine_distance 的递减也是为了让 fast_path 的
 *   进入条件(combine_distance == 1)可以满足;
 * - 保证进展:即使每后端限额为 0 且流中一个缓冲都没有,也强制发一个
 *   单块读(buffer_limit 至少为 1),确保流不会卡死。
 *
 * 【参数】stream:目标读流。
 * 【返回值】true 表示已尽最大努力发起(可能截短);false 表示因缓冲
 * 不足完全无法发起(此时调用方应暂停前瞻,等消费者释放缓冲)。
 */
static bool
read_stream_start_pending_read(ReadStream *stream)
{
	bool		need_wait;
	int			requested_nblocks;
	int			nblocks;
	int			flags;
	int			forwarded;
	int16		io_index;
	int16		overflow;
	int16		buffer_index;
	int			buffer_limit;

	/* This should only be called with a pending read. */
	Assert(stream->pending_read_nblocks > 0);
	Assert(stream->pending_read_nblocks <= stream->io_combine_limit);

	/* We had better not exceed the per-stream buffer limit with this read. */
	Assert(stream->pinned_buffers + stream->pending_read_nblocks <=
		   stream->max_pinned_buffers);

#ifdef USE_ASSERT_CHECKING
	/* We had better not be overwriting an existing pinned buffer. */
	if (stream->pinned_buffers > 0)
		Assert(stream->next_buffer_index != stream->oldest_buffer_index);
	else
		Assert(stream->next_buffer_index == stream->oldest_buffer_index);

	/*
	 * Pinned buffers forwarded by a preceding StartReadBuffers() call that
	 * had to split the operation should match the leading blocks of this
	 * following StartReadBuffers() call.
	 */
	Assert(stream->forwarded_buffers <= stream->pending_read_nblocks);
	for (int i = 0; i < stream->forwarded_buffers; ++i)
		Assert(BufferGetBlockNumber(stream->buffers[stream->next_buffer_index + i]) ==
			   stream->pending_read_blocknum + i);

	/*
	 * Check that we've cleared the queue/overflow entries corresponding to
	 * the rest of the blocks covered by this read, unless it's the first go
	 * around and we haven't even initialized them yet.
	 */
	for (int i = stream->forwarded_buffers; i < stream->pending_read_nblocks; ++i)
		Assert(stream->next_buffer_index + i >= stream->initialized_buffers ||
			   stream->buffers[stream->next_buffer_index + i] == InvalidBuffer);
#endif

	/* Do we need to issue read-ahead advice? */
	flags = stream->read_buffers_flags;
	if (stream->advice_enabled)
	{
		if (stream->pending_read_blocknum == stream->seq_blocknum)
		{
			/*
			 * Sequential:  Issue advice until the preadv() calls have caught
			 * up with the first advice issued for this sequential region, and
			 * then stay out of the way of the kernel's own read-ahead.
			 */
			if (stream->seq_until_processed != InvalidBlockNumber)
				flags |= READ_BUFFERS_ISSUE_ADVICE;
		}
		else
		{
			/*
			 * Random jump:  Note the starting location of a new potential
			 * sequential region and start issuing advice.  Skip it this time
			 * if the preadv() follows immediately, eg first block in stream.
			 */
			stream->seq_until_processed = stream->pending_read_blocknum;
			if (stream->pinned_buffers > 0)
				flags |= READ_BUFFERS_ISSUE_ADVICE;
		}
	}

	/*
	 * How many more buffers is this backend allowed?
	 *
	 * Forwarded buffers are already pinned and map to the leading blocks of
	 * the pending read (the remaining portion of an earlier short read that
	 * we're about to continue).  They are not counted in pinned_buffers, but
	 * they are counted as pins already held by this backend according to the
	 * buffer manager, so they must be added to the limit it grants us.
	 */
	if (stream->temporary)
		buffer_limit = Min(GetAdditionalLocalPinLimit(), PG_INT16_MAX);
	else
		buffer_limit = Min(GetAdditionalPinLimit(), PG_INT16_MAX);
	Assert(stream->forwarded_buffers <= stream->pending_read_nblocks);

	buffer_limit += stream->forwarded_buffers;
	buffer_limit = Min(buffer_limit, PG_INT16_MAX);

	if (buffer_limit == 0 && stream->pinned_buffers == 0)
		buffer_limit = 1;		/* guarantee progress */

	/* Does the per-backend limit affect this read? */
	nblocks = stream->pending_read_nblocks;
	if (buffer_limit < nblocks)
	{
		int16		new_distance;

		/* Shrink distance: no more look-ahead until buffers are released. */
		new_distance = stream->pinned_buffers + buffer_limit;
		if (stream->readahead_distance > new_distance)
			stream->readahead_distance = new_distance;

		/* Unless we have nothing to give the consumer, stop here. */
		if (stream->pinned_buffers > 0)
			return false;

		/* A short read is required to make progress. */
		nblocks = buffer_limit;
	}

	/*
	 * We say how many blocks we want to read, but it may be smaller on return
	 * if the buffer manager decides to shorten the read.  Initialize buffers
	 * to InvalidBuffer (= not a forwarded buffer) as input on first use only,
	 * and keep the original nblocks number so we can check for forwarded
	 * buffers as output, below.
	 */
	buffer_index = stream->next_buffer_index;
	io_index = stream->next_io_index;
	while (stream->initialized_buffers < buffer_index + nblocks)
		stream->buffers[stream->initialized_buffers++] = InvalidBuffer;
	requested_nblocks = nblocks;
	need_wait = StartReadBuffers(&stream->ios[io_index].op,
								 &stream->buffers[buffer_index],
								 stream->pending_read_blocknum,
								 &nblocks,
								 flags);
	stream->pinned_buffers += nblocks;

	/* Remember whether we need to wait before returning this buffer. */
	if (!need_wait)
	{
		/*
		 * If there currently is no IO in progress, and we have not needed to
		 * issue IO recently, decay the look-ahead distance.  We detect if we
		 * had to issue IO recently by having a decay holdoff that's set to
		 * the max look-ahead distance whenever we need to do IO.  This is
		 * important to ensure we eventually reach a high enough distance to
		 * perform IO asynchronously when starting out with a small look-ahead
		 * distance.
		 */
		if (stream->ios_in_progress == 0)
		{
			if (stream->distance_decay_holdoff > 0)
				stream->distance_decay_holdoff--;
			else
			{
				if (stream->readahead_distance > 1)
					stream->readahead_distance--;

				/*
				 * For now we reduce the IO combine distance after
				 * sufficiently many buffer hits. There is no clear
				 * performance argument for doing so, but at the moment we
				 * need to do so to make the entrance into fast_path work
				 * correctly: We require combine_distance == 1 to enter
				 * fast-path, as without that condition we would wrongly
				 * re-enter fast-path when readahead_distance == 1 and
				 * pinned_buffers == 1, as we would not yet have prepared
				 * another IO in that situation.
				 */
				if (stream->combine_distance > 1)
					stream->combine_distance--;
			}
		}
	}
	else
	{
		/*
		 * Remember to call WaitReadBuffers() before returning head buffer.
		 * Look-ahead distance will be adjusted after waiting.
		 */
		stream->ios[io_index].buffer_index = buffer_index;
		if (++stream->next_io_index == stream->max_ios)
			stream->next_io_index = 0;
		Assert(stream->ios_in_progress < stream->max_ios);
		stream->ios_in_progress++;
		stream->seq_blocknum = stream->pending_read_blocknum + nblocks;

		/* update I/O stats */
		read_stream_count_io(stream, nblocks, stream->ios_in_progress);
	}

	/*
	 * How many pins were acquired but forwarded to the next call?  These need
	 * to be passed to the next StartReadBuffers() call by leaving them
	 * exactly where they are in the queue, or released if the stream ends
	 * early.  We need the number for accounting purposes, since they are not
	 * counted in stream->pinned_buffers but we already hold them.
	 */
	forwarded = 0;
	while (nblocks + forwarded < requested_nblocks &&
		   stream->buffers[buffer_index + nblocks + forwarded] != InvalidBuffer)
		forwarded++;
	stream->forwarded_buffers = forwarded;

	/*
	 * We gave a contiguous range of buffer space to StartReadBuffers(), but
	 * we want it to wrap around at queue_size.  Copy overflowing buffers to
	 * the front of the array where they'll be consumed, but also leave a copy
	 * in the overflow zone which the I/O operation has a pointer to (it needs
	 * a contiguous array).  Both copies will be cleared when the buffers are
	 * handed to the consumer.
	 */
	overflow = (buffer_index + nblocks + forwarded) - stream->queue_size;
	if (overflow > 0)
	{
		Assert(overflow < stream->queue_size);	/* can't overlap */
		memcpy(&stream->buffers[0],
			   &stream->buffers[stream->queue_size],
			   sizeof(stream->buffers[0]) * overflow);
	}

	/* Compute location of start of next read, without using % operator. */
	buffer_index += nblocks;
	if (buffer_index >= stream->queue_size)
		buffer_index -= stream->queue_size;
	Assert(buffer_index >= 0 && buffer_index < stream->queue_size);
	stream->next_buffer_index = buffer_index;

	/* Adjust the pending read to cover the remaining portion, if any. */
	stream->pending_read_blocknum += nblocks;
	stream->pending_read_nblocks -= nblocks;

	return true;
}

/*
 * (中文)判断是否应继续向前窥视:或把 pending read 拼得更大(合并),或
 * 发起更多预读。
 *
 * 【设计思想】决定继续前瞻的三种情形各有讲究:
 * 1) 回调已报告流结束(readahead_distance == 0):无块可看;
 * 2) 在途 I/O 已达 max_ios 上限:再发无益;
 * 3) 正在构建的 pending read 还小于 combine_distance,且流中一个缓冲都
 *    没有(pinned_buffers == 0):继续取块把它拼大——即使 readahead
 *    distance 很小(如 I/O 子系统跟得上),大块读也更省 CPU。这里故意
 *    可以突破 readahead 距离上限,但不会突破 pin 上限,因为
 *    combine_distance 被 max_pinned_buffers 封顶;一旦有读已发出
 *    (pinned_buffers > 0)就不再需要这条路径——等待 I/O 会让距离自动
 *    涨起来;
 * 4) 其余情况:pinned_buffers + pending_read_nblocks 不得超过
 *    readahead_distance(同样被 max_pinned_buffers 封顶),防止前瞻过远
 *    超过 pin 上限。
 *
 * 【参数】stream:目标读流。
 * 【返回值】true:应继续向前取块;false:应把 pending read 发出或停止。
 */
static inline bool
read_stream_should_look_ahead(ReadStream *stream)
{
	/* If the callback has signaled end-of-stream, we're done */
	if (stream->readahead_distance == 0)
		return false;

	/* never start more IOs than our cap */
	if (stream->ios_in_progress >= stream->max_ios)
		return false;

	/*
	 * Allow looking further ahead if we are in the process of building a
	 * larger IO, the IO is not yet big enough, and we don't yet have IO in
	 * flight.
	 *
	 * We do so to allow building larger reads when readahead_distance is
	 * small (e.g. because the I/O subsystem is keeping up or
	 * effective_io_concurrency is small). That's a useful goal because larger
	 * reads are more CPU efficient than smaller reads, even if the system is
	 * not IO bound.
	 *
	 * The reason we do *not* do so when we already have a read prepared (i.e.
	 * why we check for pinned_buffers == 0) is once we are actually reading
	 * ahead, we don't need it:
	 *
	 * - We won't issue unnecessarily small reads as
	 * read_stream_should_issue_now() will return false until the IO is
	 * suitably sized. The issuance of the pending read will be delayed until
	 * enough buffers have been consumed.
	 *
	 * - If we are not reading ahead aggressively enough, future
	 * WaitReadBuffers() calls will return true, leading to readahead_distance
	 * being increased. After that more full-sized IOs can be issued.
	 *
	 * Furthermore, if we did not have the pinned_buffers == 0 condition, we
	 * might end up issuing I/O more aggressively than we need.
	 *
	 * Note that a return of true here can lead to exceeding the read-ahead
	 * limit, but we won't exceed the buffer pin limit (because pinned_buffers
	 * == 0 and combine_distance is capped by max_pinned_buffers).
	 */
	if (stream->pending_read_nblocks > 0 &&
		stream->pinned_buffers == 0 &&
		stream->pending_read_nblocks < stream->combine_distance)
		return true;

	/*
	 * Don't start more read-ahead if that'd put us over the distance limit
	 * for doing read-ahead. As stream->readahead_distance is capped by
	 * max_pinned_buffers, this prevents us from looking ahead so far that it
	 * would put us over the pin limit.
	 */
	if (stream->pinned_buffers + stream->pending_read_nblocks >= stream->readahead_distance)
		return false;

	return true;
}

/*
 * (中文)判断"当前是否应把 pending read 立刻发出"。
 *
 * 【设计思想】默认策略是把 pending read 尽量拼到 combine_distance 再
 * 发出,但下列情形必须立即发出:
 * 1) 没有 pending read(pending_read_nblocks == 0):无事可发;
 * 2) 在途 I/O 已达 max_ios 上限:不允许再多发;
 * 3) 流已结束(readahead_distance == 0):没有继续合并的可能;
 * 4) 已拼满 combine_distance:再等也不会更大;
 * 5) 既没有在途读、也没有已准备的读(pinned_buffers == 0)且前瞻已
 *    到头:此时必须发出,保证消费者任何时候都有缓冲可取(至少有一个
 *    读处于已准备状态)。
 *
 * 【参数】stream:目标读流。
 * 【返回值】true:应立刻调用 read_stream_start_pending_read()。
 */
static inline bool
read_stream_should_issue_now(ReadStream *stream)
{
	int16		pending_read_nblocks = stream->pending_read_nblocks;

	/* there is no pending IO that could be issued */
	if (pending_read_nblocks == 0)
		return false;

	/* never start more IOs than our cap */
	if (stream->ios_in_progress >= stream->max_ios)
		return false;

	/*
	 * If the callback has signaled end-of-stream, start the pending read
	 * immediately. There is no further potential for IO combining.
	 */
	if (stream->readahead_distance == 0)
		return true;

	/*
	 * If we've already reached combine_distance, there's no chance of growing
	 * the read further.
	 */
	if (pending_read_nblocks >= stream->combine_distance)
		return true;

	/*
	 * If we currently have no reads in flight or prepared, issue the IO once
	 * we are not looking ahead further. This ensures there's always at least
	 * one IO prepared.
	 */
	if (stream->pinned_buffers == 0 &&
		!read_stream_should_look_ahead(stream))
		return true;

	return false;
}

/*
 * (中文)前瞻主循环:持续取块、合并、必要时发出 pending read,直到满足
 * 停止条件。
 *
 * 【作用】read_stream_next_buffer() 每次调用后都通过它"为下一次调用做
 * 准备"(补充 pin 缓冲、构建/发出读);也是 AIO 批处理提交的现场——整个
 * 前瞻过程以 pgaio_enter_batchmode() / pgaio_exit_batchmode() 包裹,把
 * 构建期间产生的多个暂存 I/O 合并为一次提交,摊薄提交开销。
 *
 * 【设计思想】循环由 read_stream_should_look_ahead() 与
 * read_stream_should_issue_now() 两个谓词驱动:
 * - 若应立即发出则发出(可能被截短),然后继续下一轮;
 * - 否则向回调取下一个块:与当前 pending read 的块号连续则并入
 *   (合并);不连续则必须先清空 pending read(若因限额无法清空,把该
 *   块号退回、停止前瞻),再以该块开启新的 pending read;
 * - 循环退出后,若 pending read 已满足发出条件再补发一次,保证离开
 *   本函数时流中总有缓冲可交付(流已结束除外)。
 *
 * 【参数】stream:目标读流。
 * 【返回值】无。
 */
static void
read_stream_look_ahead(ReadStream *stream)
{
	/*
	 * Allow amortizing the cost of submitting IO over multiple IOs. This
	 * requires that we don't do any operations that could lead to a deadlock
	 * with staged-but-unsubmitted IO. The callback needs to opt-in to being
	 * careful.
	 */
	if (stream->batch_mode)
		pgaio_enter_batchmode();

	while (read_stream_should_look_ahead(stream))
	{
		BlockNumber blocknum;
		int16		buffer_index;
		void	   *per_buffer_data;

		if (read_stream_should_issue_now(stream))
		{
			read_stream_start_pending_read(stream);
			continue;
		}

		/*
		 * See which block the callback wants next in the stream.  We need to
		 * compute the index of the Nth block of the pending read including
		 * wrap-around, but we don't want to use the expensive % operator.
		 */
		buffer_index = stream->next_buffer_index + stream->pending_read_nblocks;
		if (buffer_index >= stream->queue_size)
			buffer_index -= stream->queue_size;
		Assert(buffer_index >= 0 && buffer_index < stream->queue_size);
		per_buffer_data = get_per_buffer_data(stream, buffer_index);
		blocknum = read_stream_get_block(stream, per_buffer_data);
		if (blocknum == InvalidBlockNumber)
		{
			/* End of stream. */
			stream->readahead_distance = 0;
			stream->combine_distance = 0;
			break;
		}

		/* Can we merge it with the pending read? */
		if (stream->pending_read_nblocks > 0 &&
			stream->pending_read_blocknum + stream->pending_read_nblocks == blocknum)
		{
			stream->pending_read_nblocks++;
			continue;
		}

		/* We have to start the pending read before we can build another. */
		while (stream->pending_read_nblocks > 0)
		{
			if (!read_stream_start_pending_read(stream) ||
				stream->ios_in_progress == stream->max_ios)
			{
				/* We've hit the buffer or I/O limit.  Rewind and stop here. */
				read_stream_unget_block(stream, blocknum);
				if (stream->batch_mode)
					pgaio_exit_batchmode();
				return;
			}
		}

		/* This is the start of a new pending read. */
		stream->pending_read_blocknum = blocknum;
		stream->pending_read_nblocks = 1;
	}

	/*
	 * Check if the pending read should be issued now, or if we should give it
	 * another chance to grow to the full size.
	 *
	 * Note that the pending read can exceed the distance goal, if the latter
	 * was reduced after hitting the per-backend buffer limit.
	 */
	if (read_stream_should_issue_now(stream))
		read_stream_start_pending_read(stream);

	/*
	 * There should always be something pinned when we leave this function,
	 * whether started by this call or not, unless we've hit the end of the
	 * stream.  In the worst case we can always make progress one buffer at a
	 * time.
	 */
	Assert(stream->pinned_buffers > 0 || stream->readahead_distance == 0);

	if (stream->batch_mode)
		pgaio_exit_batchmode();
}

/*
 * (中文)创建读流对象的真正实现(两个公开入口都转到这里)。
 *
 * 【作用】一次性算出并分配"流对象 + 缓冲队列 + 溢出区 + 在途 I/O 数组 +
 * per-buffer 数据"的整块内存,根据 GUC / 表空间配置决定并发度与距离上限,
 * 并完成各字段的初始化。
 *
 * 【设计思想】关键的数量关系:
 * - max_ios:可同时在途的 I/O 数,来自 effective_io_concurrency 或表空间
 *   的 io concurrency 设置;目录表 / 未连接数据库时回退到全局 GUC,避免
 *   在 spccache 就绪前产生循环依赖;
 * - max_pinned_buffers = min((max_ios + 1) * io_combine_limit, 各上限):
 *   多留"一个满 I/O 的缓冲"余量,使上一批 I/O 结束后不必等消费者取走
 *   缓冲就能开新一批;随后还要受"策略环 pin 上限"
 *   (GetAccessStrategyPinLimit)与缓冲管理器的每后端 pin 限额
 *   (GetAdditionalPinLimit / GetAdditionalLocalPinLimit)约束;上限为
 *   0 时(缓冲过少的系统)强制到 1,保证流能推进;
 * - queue_size = max_pinned_buffers + 1:多出的一个空槽作为 head 与
 *   tail 之间的间隙,保证 per-buffer 数据在消费者访问期间不被覆盖;
 * - 缓冲槽额外预留 queue_overflow = io_combine_limit - 1 个溢出槽,使
 *   一次合并读的连续缓冲数组不会因环形队列绕回而断裂;
 * - 初始化时把每个 InProgressIO 中"整个流不变"的字段(rel / smgr /
 *   策略 / 持久性 / fork)预先填好,避免每次读重复赋值;
 * - READ_STREAM_FULL(将读整个关系)时跳过初始爬升,直接以全尺寸距离
 *   起步;否则从 1 开始,等待"命中/未命中"历史来自适应。
 *
 * 【参数】flags:READ_STREAM_* 位标志;strategy:缓冲访问策略(可为 NULL);
 * rel:目标关系(可为 NULL);smgr:存储管理器关系;persistence:关系持久性;
 * forknum:分支号;callback:块号回调;callback_private_data:回调私有数据;
 * per_buffer_data_size:每块私有数据大小(0 表示不需要)。
 * 【返回值】新建的 ReadStream*,随后用 read_stream_next_buffer() 消费。
 */
static ReadStream *
read_stream_begin_impl(int flags,
					   BufferAccessStrategy strategy,
					   Relation rel,
					   SMgrRelation smgr,
					   char persistence,
					   ForkNumber forknum,
					   ReadStreamBlockNumberCB callback,
					   void *callback_private_data,
					   size_t per_buffer_data_size)
{
	ReadStream *stream;
	size_t		size;
	int16		queue_size;
	int16		queue_overflow;
	int			max_ios;
	int			strategy_pin_limit;
	uint32		max_pinned_buffers;
	uint32		max_possible_buffer_limit;
	Oid			tablespace_id;

	/*
	 * Reject attempts to read non-local temporary relations; we would be
	 * likely to get wrong data since we have no visibility into the owning
	 * session's local buffers.
	 */
	if (rel && RELATION_IS_OTHER_TEMP(rel))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot access temporary tables of other sessions")));

	/*
	 * Decide how many I/Os we will allow to run at the same time.  This
	 * number also affects how far we look ahead for opportunities to start
	 * more I/Os.
	 */
	tablespace_id = smgr->smgr_rlocator.locator.spcOid;
	if (!OidIsValid(MyDatabaseId) ||
		(rel && IsCatalogRelation(rel)) ||
		IsCatalogRelationOid(smgr->smgr_rlocator.locator.relNumber))
	{
		/*
		 * Avoid circularity while trying to look up tablespace settings or
		 * before spccache.c is ready.
		 */
		max_ios = effective_io_concurrency;
	}
	else if (flags & READ_STREAM_MAINTENANCE)
		max_ios = get_tablespace_maintenance_io_concurrency(tablespace_id);
	else
		max_ios = get_tablespace_io_concurrency(tablespace_id);

	/* Cap to INT16_MAX to avoid overflowing below */
	max_ios = Min(max_ios, PG_INT16_MAX);

	/*
	 * If starting a multi-block I/O near the end of the queue, we might
	 * temporarily need extra space for overflowing buffers before they are
	 * moved to regular circular position.  This is the maximum extra space we
	 * could need.
	 */
	queue_overflow = io_combine_limit - 1;

	/*
	 * Choose the maximum number of buffers we're prepared to pin.  We try to
	 * pin fewer if we can, though.  We add one so that we can make progress
	 * even if max_ios is set to 0 (see also further down).  For max_ios > 0,
	 * this also allows an extra full I/O's worth of buffers: after an I/O
	 * finishes we don't want to have to wait for its buffers to be consumed
	 * before starting a new one.
	 *
	 * Be careful not to allow int16 to overflow.  That is possible with the
	 * current GUC range limits, so this is an artificial limit of ~32k
	 * buffers and we'd need to adjust the types to exceed that.  We also have
	 * to allow for the spare entry and the overflow space.
	 */
	max_pinned_buffers = (max_ios + 1) * io_combine_limit;
	max_pinned_buffers = Min(max_pinned_buffers,
							 PG_INT16_MAX - queue_overflow - 1);

	/* Give the strategy a chance to limit the number of buffers we pin. */
	strategy_pin_limit = GetAccessStrategyPinLimit(strategy);
	max_pinned_buffers = Min(strategy_pin_limit, max_pinned_buffers);

	/*
	 * Also limit our queue to the maximum number of pins we could ever be
	 * allowed to acquire according to the buffer manager.  We may not really
	 * be able to use them all due to other pins held by this backend, but
	 * we'll check that later in read_stream_start_pending_read().
	 */
	if (SmgrIsTemp(smgr))
		max_possible_buffer_limit = GetLocalPinLimit();
	else
		max_possible_buffer_limit = GetPinLimit();
	max_pinned_buffers = Min(max_pinned_buffers, max_possible_buffer_limit);

	/*
	 * The limit might be zero on a system configured with too few buffers for
	 * the number of connections.  We need at least one to make progress.
	 */
	max_pinned_buffers = Max(1, max_pinned_buffers);

	/*
	 * We need one extra entry for buffers and per-buffer data, because users
	 * of per-buffer data have access to the object until the next call to
	 * read_stream_next_buffer(), so we need a gap between the head and tail
	 * of the queue so that we don't clobber it.
	 */
	queue_size = max_pinned_buffers + 1;

	/*
	 * Allocate the object, the buffers, the ios and per_buffer_data space in
	 * one big chunk.  Though we have queue_size buffers, we want to be able
	 * to assume that all the buffers for a single read are contiguous (i.e.
	 * don't wrap around halfway through), so we allow temporary overflows of
	 * up to the maximum possible overflow size.
	 */
	size = offsetof(ReadStream, buffers);
	size += sizeof(Buffer) * (queue_size + queue_overflow);
	size += sizeof(InProgressIO) * Max(1, max_ios);
	size += per_buffer_data_size * queue_size;
	size += MAXIMUM_ALIGNOF * 2;
	stream = (ReadStream *) palloc(size);
	memset(stream, 0, offsetof(ReadStream, buffers));
	stream->ios = (InProgressIO *)
		MAXALIGN(&stream->buffers[queue_size + queue_overflow]);
	if (per_buffer_data_size > 0)
		stream->per_buffer_data = (void *)
			MAXALIGN(&stream->ios[Max(1, max_ios)]);

	stream->sync_mode = io_method == IOMETHOD_SYNC;
	stream->batch_mode = flags & READ_STREAM_USE_BATCHING;

#ifdef USE_PREFETCH

	/*
	 * Read-ahead advice simulating asynchronous I/O with synchronous calls.
	 * Issue advice only if AIO is not used, direct I/O isn't enabled, the
	 * caller hasn't promised sequential access (overriding our detection
	 * heuristics), and max_ios hasn't been set to zero.
	 */
	if (stream->sync_mode &&
		(io_direct_flags & IO_DIRECT_DATA) == 0 &&
		(flags & READ_STREAM_SEQUENTIAL) == 0 &&
		max_ios > 0)
		stream->advice_enabled = true;
#endif

	/*
	 * Setting max_ios to zero disables AIO and advice-based pseudo AIO, but
	 * we still need to allocate space to combine and run one I/O.  Bump it up
	 * to one, and remember to ask for synchronous I/O only.
	 */
	if (max_ios == 0)
	{
		max_ios = 1;
		stream->read_buffers_flags = READ_BUFFERS_SYNCHRONOUSLY;
	}

	/*
	 * Capture stable values for these two GUC-derived numbers for the
	 * lifetime of this stream, so we don't have to worry about the GUCs
	 * changing underneath us beyond this point.
	 */
	stream->max_ios = max_ios;
	stream->io_combine_limit = io_combine_limit;

	stream->per_buffer_data_size = per_buffer_data_size;
	stream->max_pinned_buffers = max_pinned_buffers;
	stream->queue_size = queue_size;
	stream->callback = callback;
	stream->callback_private_data = callback_private_data;
	stream->buffered_blocknum = InvalidBlockNumber;
	stream->seq_blocknum = InvalidBlockNumber;
	stream->seq_until_processed = InvalidBlockNumber;
	stream->temporary = SmgrIsTemp(smgr);
	stream->distance_decay_holdoff = 0;

	/*
	 * Skip the initial ramp-up phase if the caller says we're going to be
	 * reading the whole relation.  This way we start out assuming we'll be
	 * doing full io_combine_limit sized reads.
	 */
	if (flags & READ_STREAM_FULL)
	{
		stream->readahead_distance = Min(max_pinned_buffers, stream->io_combine_limit);
		stream->combine_distance = Min(max_pinned_buffers, stream->io_combine_limit);
	}
	else
	{
		stream->readahead_distance = 1;
		stream->combine_distance = 1;
	}
	stream->resume_readahead_distance = stream->readahead_distance;
	stream->resume_combine_distance = stream->combine_distance;

	/*
	 * Since we always access the same relation, we can initialize parts of
	 * the ReadBuffersOperation objects and leave them that way, to avoid
	 * wasting CPU cycles writing to them for each read.
	 */
	for (int i = 0; i < max_ios; ++i)
	{
		stream->ios[i].op.rel = rel;
		stream->ios[i].op.smgr = smgr;
		stream->ios[i].op.persistence = persistence;
		stream->ios[i].op.forknum = forknum;
		stream->ios[i].op.strategy = strategy;
	}

	return stream;
}

/*
 * (中文)创建读流的公开入口(基于 Relation 的 relcache 条目)。
 *
 * 【作用】从 relcache 条目取出 smgr 与持久性,再转调 read_stream_begin_impl,
 * 是顺序扫描等场景的主要入口。
 *
 * 【参数】flags / strategy / forknum / callback / callback_private_data /
 * per_buffer_data_size:语义同 read_stream_begin_impl;rel:目标关系。
 * 【返回值】新建的 ReadStream*。
 */
ReadStream *
read_stream_begin_relation(int flags,
						   BufferAccessStrategy strategy,
						   Relation rel,
						   ForkNumber forknum,
						   ReadStreamBlockNumberCB callback,
						   void *callback_private_data,
						   size_t per_buffer_data_size)
{
	return read_stream_begin_impl(flags,
								  strategy,
								  rel,
								  RelationGetSmgr(rel),
								  rel->rd_rel->relpersistence,
								  forknum,
								  callback,
								  callback_private_data,
								  per_buffer_data_size);
}

/*
 * (中文)创建读流的公开入口(基于 SMgrRelation,不要求 relcache 条目)。
 *
 * 【作用】供没有 relcache 条目的场景(如某些扩展算子)使用:rel 传 NULL,
 * 持久性由调用方显式给出(smgr_persistence)。
 *
 * 【参数】flags / strategy / forknum / callback / callback_private_data /
 * per_buffer_data_size:语义同 read_stream_begin_impl;smgr:存储管理器
 * 关系;smgr_persistence:关系持久性。
 * 【返回值】新建的 ReadStream*。
 */
ReadStream *
read_stream_begin_smgr_relation(int flags,
								BufferAccessStrategy strategy,
								SMgrRelation smgr,
								char smgr_persistence,
								ForkNumber forknum,
								ReadStreamBlockNumberCB callback,
								void *callback_private_data,
								size_t per_buffer_data_size)
{
	return read_stream_begin_impl(flags,
								  strategy,
								  NULL,
								  smgr,
								  smgr_persistence,
								  forknum,
								  callback,
								  callback_private_data,
								  per_buffer_data_size);
}

/*
 * (中文)从流中取出一块已 pin 的缓冲交给调用者;每次调用返回一块,顺序
 * 与块号回调给出的顺序一致。
 *
 * 【作用】流的对外核心接口:处理"等待在途 I/O、自适应调整距离、清理
 * 队列槽位、为下次调用前瞻补货"等全部内部状态,并在全缓存扫描时切入
 * fast_path 直通路径。
 *
 * 【设计思想】本函数是自适应算法的反馈回路所在:
 * - 若最老的缓冲对应一个在途 I/O,先 WaitReadBuffers() 等它完成,并把
 *   "是否需要等待"当作反馈:需要等待则 readahead_distance 加倍(上限
 *   max_pinned_buffers)并设置 distance_decay_holdoff(上限
 *   max_pinned_buffers)抑制后续衰减;不需要等待则距离保持不变(现有
 *   距离显然足够)。sync 模式下同步 I/O 一律视为"需要等待",否则
 *   effective_io_concurrency = 0 时距离永远涨不起来、无法合并 I/O;
 * - combine_distance 只要做过 I/O 就加倍(上限 io_combine_limit):即使
 *   数据命中内核页缓存,大块读也能摊薄系统调用 / 提交开销;对 io_uring
 *   尤其重要——它不会因缓存命中而报告需要等待,只能靠此规则涨距离;
 * - 取出缓冲后清空队列槽位(溢出区双份副本一并清理),递减
 *   pinned_buffers 并把 oldest_buffer_index 前移,最后调用
 *   read_stream_look_ahead() 为下次调用补货;
 * - fast_path:当流处于"全缓存、无私有数据、两个距离都为 1"的稳态时,
 *   退化为"单缓冲槽 + StartReadBuffer()"直通路径,跳过全部队列管理;
 *   若该块是缓存未命中(StartReadBuffer 发起 I/O),立即退出 fast_path;
 * - Valgrind / CLOBBER_FREED_MEMORY 下还会把上一个槽的私有数据区擦掉
 *   (置 noaccess),捕捉消费者持有的悬垂指针。
 *
 * 【参数】stream:目标读流;per_buffer_data:可空;若 per_buffer_data_size
 * 非 0,这里收到回调为本次返回的块写入的私有数据指针(该数据有效到下次
 * 调用本函数)。
 * 【返回值】块对应的 Buffer(pin 已转移给调用者,应由调用者释放);流
 * 结束时返回 InvalidBuffer。
 */
Buffer
read_stream_next_buffer(ReadStream *stream, void **per_buffer_data)
{
	Buffer		buffer;
	int16		oldest_buffer_index;

#ifndef READ_STREAM_DISABLE_FAST_PATH

	/*
	 * A fast path for all-cached scans.  This is the same as the usual
	 * algorithm, but it is specialized for no I/O and no per-buffer data, so
	 * we can skip the queue management code, stay in the same buffer slot and
	 * use singular StartReadBuffer().
	 */
	if (likely(stream->fast_path))
	{
		BlockNumber next_blocknum;

		/* Fast path assumptions. */
		Assert(stream->ios_in_progress == 0);
		Assert(stream->forwarded_buffers == 0);
		Assert(stream->pinned_buffers == 1);
		Assert(stream->readahead_distance == 1);
		Assert(stream->combine_distance == 1);
		Assert(stream->pending_read_nblocks == 0);
		Assert(stream->per_buffer_data_size == 0);
		Assert(stream->initialized_buffers > stream->oldest_buffer_index);

		/* We're going to return the buffer we pinned last time. */
		oldest_buffer_index = stream->oldest_buffer_index;
		Assert((oldest_buffer_index + 1) % stream->queue_size ==
			   stream->next_buffer_index);
		buffer = stream->buffers[oldest_buffer_index];
		Assert(buffer != InvalidBuffer);

		/* Choose the next block to pin. */
		next_blocknum = read_stream_get_block(stream, NULL);

		if (likely(next_blocknum != InvalidBlockNumber))
		{
			int			flags = stream->read_buffers_flags;

			if (stream->advice_enabled)
				flags |= READ_BUFFERS_ISSUE_ADVICE;

			/*
			 * While in fast-path, execute any IO that we might encounter
			 * synchronously. Because we are, right now, only looking one
			 * block ahead, dispatching any occasional IO to workers would
			 * have the overhead of dispatching to workers, without any
			 * realistic chance of the IO completing before we need it. We
			 * will switch to non-synchronous IO after this.
			 *
			 * Arguably we should do so only for worker, as there's far less
			 * dispatch overhead with io_uring. However, tests so far have not
			 * shown a clear downside and additional io_method awareness here
			 * seems not great from an abstraction POV.
			 */
			flags |= READ_BUFFERS_SYNCHRONOUSLY;

			/*
			 * Pin a buffer for the next call.  Same buffer entry, and
			 * arbitrary I/O entry (they're all free).  We don't have to
			 * adjust pinned_buffers because we're transferring one to caller
			 * but pinning one more.
			 *
			 * In the fast path we don't need to check the pin limit.  We're
			 * always allowed at least one pin so that progress can be made,
			 * and that's all we need here.  Although two pins are momentarily
			 * held at the same time, the model used here is that the stream
			 * holds only one, and the other now belongs to the caller.
			 */
			if (likely(!StartReadBuffer(&stream->ios[0].op,
										&stream->buffers[oldest_buffer_index],
										next_blocknum,
										flags)))
			{
				/* Fast return. */
				read_stream_count_prefetch(stream);
				return buffer;
			}

			/* Next call must wait for I/O for the newly pinned buffer. */
			stream->oldest_io_index = 0;
			stream->next_io_index = stream->max_ios > 1 ? 1 : 0;
			stream->ios_in_progress = 1;
			stream->ios[0].buffer_index = oldest_buffer_index;
			stream->seq_blocknum = next_blocknum + 1;

			/*
			 * XXX: It might be worth triggering additional read-ahead here,
			 * to avoid having to effectively do another synchronous IO for
			 * the next block (if it were also a miss).
			 */

			/* update I/O stats */
			read_stream_count_io(stream, 1, stream->ios_in_progress);

			/* update prefetch distance */
			read_stream_count_prefetch(stream);
		}
		else
		{
			/* No more blocks, end of stream. */
			stream->readahead_distance = 0;
			stream->combine_distance = 0;
			stream->oldest_buffer_index = stream->next_buffer_index;
			stream->pinned_buffers = 0;
			stream->buffers[oldest_buffer_index] = InvalidBuffer;
		}

		stream->fast_path = false;
		return buffer;
	}
#endif

	if (unlikely(stream->pinned_buffers == 0))
	{
		Assert(stream->oldest_buffer_index == stream->next_buffer_index);

		/* End of stream reached?  */
		if (stream->readahead_distance == 0)
			return InvalidBuffer;

		/*
		 * The usual order of operations is that we look ahead at the bottom
		 * of this function after potentially finishing an I/O and making
		 * space for more, but if we're just starting up we'll need to crank
		 * the handle to get started.
		 */
		read_stream_look_ahead(stream);

		/* End of stream reached? */
		if (stream->pinned_buffers == 0)
		{
			Assert(stream->readahead_distance == 0);
			return InvalidBuffer;
		}
	}

	/* Grab the oldest pinned buffer and associated per-buffer data. */
	Assert(stream->pinned_buffers > 0);
	oldest_buffer_index = stream->oldest_buffer_index;
	Assert(oldest_buffer_index >= 0 &&
		   oldest_buffer_index < stream->queue_size);
	buffer = stream->buffers[oldest_buffer_index];
	if (per_buffer_data)
		*per_buffer_data = get_per_buffer_data(stream, oldest_buffer_index);

	Assert(BufferIsValid(buffer));

	/* Do we have to wait for an associated I/O first? */
	if (stream->ios_in_progress > 0 &&
		stream->ios[stream->oldest_io_index].buffer_index == oldest_buffer_index)
	{
		int16		io_index = stream->oldest_io_index;
		bool		needed_wait;

		/* Sanity check that we still agree on the buffers. */
		Assert(stream->ios[io_index].op.buffers ==
			   &stream->buffers[oldest_buffer_index]);

		needed_wait = WaitReadBuffers(&stream->ios[io_index].op);

		Assert(stream->ios_in_progress > 0);
		stream->ios_in_progress--;
		if (++stream->oldest_io_index == stream->max_ios)
			stream->oldest_io_index = 0;

		/*
		 * If the IO was executed synchronously, we will never see
		 * WaitReadBuffers() block. Treat it as if it did block. This is
		 * particularly crucial when effective_io_concurrency=0 is used, as
		 * all IO will be synchronous.  Without treating synchronous IO as
		 * having waited, we'd never allow the distance to get large enough to
		 * allow for IO combining, resulting in bad performance.
		 */
		if (stream->ios[io_index].op.flags & READ_BUFFERS_SYNCHRONOUSLY)
			needed_wait = true;

		/* Count it as a wait if we need to wait for IO */
		if (needed_wait)
			read_stream_count_wait(stream);

		/*
		 * Have the read-ahead distance ramp up rapidly after we needed to
		 * wait for IO. We only increase the read-ahead-distance when we
		 * needed to wait, to avoid increasing the distance further than
		 * necessary, as looking ahead too far can be costly, both due to the
		 * cost of unnecessarily pinning many buffers and due to doing IOs
		 * that may never be consumed if the stream is ended/reset before
		 * completion.
		 *
		 * If we did not need to wait, the current distance was evidently
		 * sufficient.
		 *
		 * NB: Must not increase the distance if we already reached the end of
		 * the stream, as stream->readahead_distance == 0 is used to keep
		 * track of having reached the end.
		 */
		if (stream->readahead_distance > 0 && needed_wait)
		{
			/* wider temporary value, due to overflow risk */
			int32		readahead_distance;

			readahead_distance = stream->readahead_distance * 2;
			readahead_distance = Min(readahead_distance, stream->max_pinned_buffers);
			stream->readahead_distance = readahead_distance;
		}

		/*
		 * As we needed IO, prevent distances from being reduced within our
		 * maximum look-ahead window. This avoids collapsing distances too
		 * quickly in workloads where most of the required blocks are cached,
		 * but where the remaining IOs are a sufficient enough factor to cause
		 * a substantial slowdown if executed synchronously.
		 *
		 * There are valid arguments for preventing decay for max_ios or for
		 * max_pinned_buffers.  But the argument for max_pinned_buffers seems
		 * clearer - if we can't see any misses within the maximum look-ahead
		 * distance, we can't do any useful read-ahead.
		 */
		stream->distance_decay_holdoff = stream->max_pinned_buffers;

		/*
		 * Whether we needed to wait or not, allow for more IO combining if we
		 * needed to do IO. The reason to do so independent of needing to wait
		 * is that when the data is resident in the kernel page cache, IO
		 * combining reduces the syscall / dispatch overhead, making it
		 * worthwhile regardless of needing to wait.
		 *
		 * It is also important with io_uring as it will never signal the need
		 * to wait for reads if all the data is in the page cache. There are
		 * heuristics to deal with that in method_io_uring.c, but they only
		 * work when the IO gets large enough.
		 */
		if (stream->combine_distance > 0 &&
			stream->combine_distance < stream->io_combine_limit)
		{
			/* wider temporary value, due to overflow risk */
			int32		combine_distance;

			combine_distance = stream->combine_distance * 2;
			combine_distance = Min(combine_distance, stream->io_combine_limit);
			combine_distance = Min(combine_distance, stream->max_pinned_buffers);
			stream->combine_distance = combine_distance;
		}

		/*
		 * If we've reached the first block of a sequential region we're
		 * issuing advice for, cancel that until the next jump.  The kernel
		 * will see the sequential preadv() pattern starting here.
		 */
		if (stream->advice_enabled &&
			stream->ios[io_index].op.blocknum == stream->seq_until_processed)
			stream->seq_until_processed = InvalidBlockNumber;
	}

	/*
	 * We must zap this queue entry, or else it would appear as a forwarded
	 * buffer.  If it's potentially in the overflow zone (ie from a
	 * multi-block I/O that wrapped around the queue), also zap the copy.
	 */
	stream->buffers[oldest_buffer_index] = InvalidBuffer;
	if (oldest_buffer_index < stream->io_combine_limit - 1)
		stream->buffers[stream->queue_size + oldest_buffer_index] =
			InvalidBuffer;

#if defined(CLOBBER_FREED_MEMORY) || defined(USE_VALGRIND)

	/*
	 * The caller will get access to the per-buffer data, until the next call.
	 * We wipe the one before, which is never occupied because queue_size
	 * allowed one extra element.  This will hopefully trip up client code
	 * that is holding a dangling pointer to it.
	 */
	if (stream->per_buffer_data)
	{
		void	   *per_buffer_data;

		per_buffer_data = get_per_buffer_data(stream,
											  oldest_buffer_index == 0 ?
											  stream->queue_size - 1 :
											  oldest_buffer_index - 1);

#if defined(CLOBBER_FREED_MEMORY)
		/* This also tells Valgrind the memory is "noaccess". */
		wipe_mem(per_buffer_data, stream->per_buffer_data_size);
#elif defined(USE_VALGRIND)
		/* Tell it ourselves. */
		VALGRIND_MAKE_MEM_NOACCESS(per_buffer_data,
								   stream->per_buffer_data_size);
#endif
	}
#endif

	read_stream_count_prefetch(stream);

	/* Pin transferred to caller. */
	Assert(stream->pinned_buffers > 0);
	stream->pinned_buffers--;

	/* Advance oldest buffer, with wrap-around. */
	stream->oldest_buffer_index++;
	if (stream->oldest_buffer_index == stream->queue_size)
		stream->oldest_buffer_index = 0;

	/* Prepare for the next call. */
	read_stream_look_ahead(stream);

#ifndef READ_STREAM_DISABLE_FAST_PATH
	/* See if we can take the fast path for all-cached scans next time. */
	if (stream->ios_in_progress == 0 &&
		stream->forwarded_buffers == 0 &&
		stream->pinned_buffers == 1 &&
		stream->readahead_distance == 1 &&
		stream->combine_distance == 1 &&
		stream->pending_read_nblocks == 0 &&
		stream->per_buffer_data_size == 0)
	{
		/*
		 * The fast path spins on one buffer entry repeatedly instead of
		 * rotating through the whole queue and clearing the entries behind
		 * it.  If the buffer it starts with happened to be forwarded between
		 * StartReadBuffers() calls and also wrapped around the circular queue
		 * partway through, then a copy also exists in the overflow zone, and
		 * it won't clear it out as the regular path would.  Do that now, so
		 * it doesn't need code for that.
		 */
		if (stream->oldest_buffer_index < stream->io_combine_limit - 1)
			stream->buffers[stream->queue_size + stream->oldest_buffer_index] =
				InvalidBuffer;

		stream->fast_path = true;
	}
#endif

	return buffer;
}

/*
 * (中文)过渡性支持接口:让调用方绕过流、自己执行(或跳过)读取。
 *
 * 【作用】返回并消费"前瞻算法本要读取的下一块号",同时报告将使用的缓冲
 * 策略;返回 InvalidBlockNumber 表示流已到终点。供"先自读一块、决定是否
 * 改用流"的迁移期代码使用。
 *
 * 【参数】stream:目标读流;strategy:输出参数,收到该块将使用的策略。
 * 【返回值】下一块号;流结束时为 InvalidBlockNumber。
 */
BlockNumber
read_stream_next_block(ReadStream *stream, BufferAccessStrategy *strategy)
{
	*strategy = stream->ios[0].op.strategy;
	return read_stream_get_block(stream, NULL);
}

/*
 * (中文)暂停流式前瞻:保存当前距离,并把两个距离置 0 使前瞻停止。
 *
 * 【作用】用于"自引用块"等场景:回调需要先消费一块缓冲、查看内容才能
 * 给出后续块号。暂停后由 read_stream_resume() 恢复。
 *
 * 【设计思想】用 resume_*_distance 保存当前距离、距离置 0 表示"暂时
 * 没有块可看"。若在块号回调内部调用,回调应把本函数的返回值(恒为
 * InvalidBlockNumber)直接返回,向流宣告暂停。
 *
 * 【参数】stream:目标读流。
 * 【返回值】恒为 InvalidBlockNumber(供回调直接返回)。
 */
BlockNumber
read_stream_pause(ReadStream *stream)
{
	stream->resume_readahead_distance = stream->readahead_distance;
	stream->resume_combine_distance = stream->combine_distance;
	stream->readahead_distance = 0;
	stream->combine_distance = 0;
	return InvalidBlockNumber;
}

/*
 * (中文)恢复前瞻:把 read_stream_pause() 保存的两个距离还原。
 *
 * 【作用】配合 read_stream_pause() 支持"自引用块"流:消费并查看缓冲后
 * 恢复前瞻,继续从回调取得更多块号。
 *
 * 【参数】stream:目标读流。
 * 【返回值】无。
 */
void
read_stream_resume(ReadStream *stream)
{
	stream->readahead_distance = stream->resume_readahead_distance;
	stream->combine_distance = stream->resume_combine_distance;
}

/*
 * (中文)重置读流:释放所有已 pin / 已转发的缓冲,清除终点状态与
 * fast_path,使流可以重新用于不同的块序列。
 *
 * 【作用】两种典型用途:清除"流已结束"状态后重新开始;或丢弃已投机预读
 * 的块、改读别的块。
 *
 * 【设计思想】先停止前瞻并把距离置 0,再反复调用 read_stream_next_buffer()
 * 把队列中剩余缓冲全部取出并 ReleaseBuffer(顺带清空队列槽与溢出区双份
 * 副本);之后单独清扫"转发缓冲"(forwarded_buffers:已 pin、但还没进入
 * 队列、未计入 pinned_buffers 的缓冲);最后把距离重置为 1、清空
 * distance_decay_holdoff,回到"初始假设数据全在缓存"的起点。
 *
 * 【参数】stream:目标读流。
 * 【返回值】无。
 */
void
read_stream_reset(ReadStream *stream)
{
	int16		index;
	Buffer		buffer;

	/* Stop looking ahead. */
	stream->readahead_distance = 0;
	stream->combine_distance = 0;

	/* Forget buffered block number and fast path state. */
	stream->buffered_blocknum = InvalidBlockNumber;
	stream->fast_path = false;

	/* Unpin anything that wasn't consumed. */
	while ((buffer = read_stream_next_buffer(stream, NULL)) != InvalidBuffer)
		ReleaseBuffer(buffer);

	/* Unpin any unused forwarded buffers. */
	index = stream->next_buffer_index;
	while (index < stream->initialized_buffers &&
		   (buffer = stream->buffers[index]) != InvalidBuffer)
	{
		Assert(stream->forwarded_buffers > 0);
		stream->forwarded_buffers--;
		ReleaseBuffer(buffer);

		stream->buffers[index] = InvalidBuffer;
		if (index < stream->io_combine_limit - 1)
			stream->buffers[stream->queue_size + index] = InvalidBuffer;

		if (++index == stream->queue_size)
			index = 0;
	}

	Assert(stream->forwarded_buffers == 0);
	Assert(stream->pinned_buffers == 0);
	Assert(stream->ios_in_progress == 0);

	/* Start off assuming data is cached. */
	stream->readahead_distance = 1;
	stream->combine_distance = 1;
	stream->resume_readahead_distance = stream->readahead_distance;
	stream->resume_combine_distance = stream->combine_distance;
	stream->distance_decay_holdoff = 0;
}

/*
 * (中文)结束并销毁读流。
 *
 * 【作用】先调用 read_stream_reset() 释放全部缓冲 pin 与转发缓冲,再释放
 * 流对象本身(整块 palloc 内存)。
 *
 * 【参数】stream:目标读流。
 * 【返回值】无。
 */
void
read_stream_end(ReadStream *stream)
{
	read_stream_reset(stream);
	pfree(stream);
}
