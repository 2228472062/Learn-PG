/*-------------------------------------------------------------------------
 *
 * xlogreader.c
 *		Generic XLog reading facility
 *
 * Portions Copyright (c) 2013-2026, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *		src/backend/access/transam/xlogreader.c
 *
 * NOTES
 *		See xlogreader.h for more notes on this facility.
 *
 *		This file is compiled as both front-end and backend code, so it
 *		may not use ereport, server-defined static variables, etc.
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的通用 WAL 读取器（generic WAL reader），是 backend
 * （崩溃恢复、物理/逻辑复制、两阶段提交恢复等）与 frontend（pg_waldump、
 * pg_rewind）共用的 WAL 解析基础设施。核心数据结构是 xlogreader.h 中定义的
 * XLogReaderState，它把“从何处读 WAL”（XLogReaderRoutine 回调）、“读到的原始
 * 页面”（readBuf）、“解码后的 record”（decode_buffer 与 decode_queue_*）以及
 * 错误状态分离，使同一套解码代码可以服务于磁盘文件、归档、流复制等不同来源。
 *
 * 主要职责：
 *   1. 定位与读取：XLogBeginRead / XLogFindNextRecord 定位 record；
 *      XLogReadRecord / XLogNextRecord / XLogReadAhead 驱动读取；
 *      ReadPageInternal 通过 page_read 回调按页取数并缓存。
 *   2. 页头校验：XLogReaderValidatePageHeader 检查 xlp_magic、xlp_info、
 *      长页头中的 system identifier / segment size / XLOG_BLCKSZ、
 *      xlp_pageaddr 以及 timeline 单调性，防止读到回收中的旧段、错误
 *      timeline 或损坏数据。
 *   3. 记录重组：一条 record 可能跨越多个 page，后续 page 以 continuation
 *      record（页头 XLP_FIRST_IS_CONTRECORD + xlp_rem_len）标记。本文件负责
 *      跨页拼接、校验 xlp_rem_len，并处理 XLP_FIRST_IS_OVERWRITE_CONTRECORD
 *      （恢复期间被覆盖的 contrecord），把完整 record 暂存到 readRecordBuf。
 *   4. 记录校验与解码：ValidXLogRecordHeader 做长度、rmid、prev-link 检查，
 *      ValidXLogRecord 做 CRC32C 校验，DecodeXLogRecord 把 record 拆分为
 *      main data 和各 block reference（含 full-page image、fork、relfilenode、
 *      block number 等），放入连续的 DecodedXLogRecord 内存布局。
 *   5. 错误处理：本文件同时编译进 frontend 和 backend，不能直接使用 ereport，
 *      因此通过 report_invalid_record() 把诊断信息格式化到
 *      state->errormsg_buf，并置 errormsg_deferred；已经成功解码并排队的
 *      record 会先被消费，错误随后由 XLogNextRecord()/XLogReadRecord() 返回。
 *      XLogReaderResetError() 可清除页头校验错误后重试。
 *   6. 跨 timeline/跨 segment：WALRead 是 page_read 回调的通用辅助函数，按
 *      timeline 和 segment 边界循环 pg_pread；segment_open/segment_close
 *      回调由调用方提供，WALOpenSegmentInit 维护当前打开的段。
 *
 * 回调接口（XLogReaderRoutine）：
 *   - page_read：读取 [targetPagePtr, +reqLen) 的页数据，返回实际字节数或 -1；
 *     非阻塞模式下可返回 XLREAD_WOULDBLOCK。它还必须把实际读取的 timeline
 *     写入 state->seg.ws_tli，供 timeline 校验使用。
 *   - segment_open / segment_close：WALRead 用来跨 segment 打开/关闭文件；
 *     segment_close 必须始终提供，XLogReaderFree 也会调用它。
 *
 * 与其他模块的关系：
 *   - xlogrecovery.c 使用 XLogReader 读取并重放 WAL，是 startup process 的
 *     核心读取路径；
 *   - xlogutils.c 提供 backend 的 XLogPageRead 回调及恢复期间的页读取策略；
 *   - xlogprefetcher.c 通过 XLogReadAhead(nonblocking) 预解码并预取 block；
 *   - 逻辑解码（logical.c）、walsender、walsummarizer、twophase.c 复用同一个
 *     reader；
 *   - frontend 的 pg_waldump / pg_rewind 直接链接本文件，用相同的解码语义
 *     输出 record，因此这里不能依赖 backend 专有设施（ereport、静态变量等）。
 *
 * 关键设计思想：
 *   - 读、校验、解码分层：page_read 只负责取字节，页头、record 头、CRC 各自
 *     独立校验，任何一层失败都不会把不可信数据交给 redo；
 *   - 延迟报错：先返回已解码队列中的 record，再报告错误，避免 readahead/
 *     prefetch 场景下丢失已经成功解析的记录；
 *   - 环形解码缓冲区加超大 record 单独 palloc：普通 record 无需逐条分配，
 *     超大 record 也不会撑爆固定缓冲区；
 *   - 通过 XLogReaderRoutine 回调解耦 WAL 来源，使同一 reader 可用于磁盘、
 *     归档、流式复制和离线工具；
 *   - 对不可信 WAL 输入保持防御式编程：先验证长度再分配/拷贝，所有跨页长度
 *     都与 xlp_rem_len 交叉校验，避免越界读或整数溢出。
 */
#include "postgres.h"

#include <unistd.h>
#ifdef USE_LZ4
#include <lz4.h>
#endif
#ifdef USE_ZSTD
#include <zstd.h>
#endif

#include "access/transam.h"
#include "access/xlog_internal.h"
#include "access/xlogreader.h"
#include "access/xlogrecord.h"
#include "catalog/pg_control.h"
#include "common/pg_lzcompress.h"
#include "replication/origin.h"

#ifndef FRONTEND
#include "pgstat.h"
#include "storage/bufmgr.h"
#include "utils/wait_event.h"
#else
#include "common/logging.h"
#endif

/*
 * 中文注释：
 * 本文件内部函数的前置声明。各函数的完整语义、参数、返回值、副作用和错误
 * 处理见其定义处的注释块；这里保持原有声明顺序，仅用于让编译器在定义之前
 * 看到原型。
 */
static void report_invalid_record(XLogReaderState *state, const char *fmt, ...)
			pg_attribute_printf(2, 3);
static void allocate_recordbuf(XLogReaderState *state, uint32 reclength);
static int	ReadPageInternal(XLogReaderState *state, XLogRecPtr pageptr,
							 int reqLen);
static void XLogReaderInvalReadState(XLogReaderState *state);
static XLogPageReadResult XLogDecodeNextRecord(XLogReaderState *state, bool nonblocking);
static bool ValidXLogRecordHeader(XLogReaderState *state, XLogRecPtr RecPtr,
								  XLogRecPtr PrevRecPtr, XLogRecord *record, bool randAccess);
static bool ValidXLogRecord(XLogReaderState *state, XLogRecord *record,
							XLogRecPtr recptr);
static void ResetDecoder(XLogReaderState *state);
static void WALOpenSegmentInit(WALOpenSegment *seg, WALSegmentContext *segcxt,
							   int segsize, const char *waldir);

/* size of the buffer allocated for error message. */
/*
 * 中文注释：
 * state->errormsg_buf 的容量（不含结尾 NUL）。错误消息会被截断到这个长度，
 * 保证即使格式化结果很长也不会越界；XLogReaderAllocate 实际分配
 * MAX_ERRORMSG_LEN + 1 字节。
 */
#define MAX_ERRORMSG_LEN 1000

/*
 * Default size; large enough that typical users of XLogReader won't often need
 * to use the 'oversized' memory allocation code path.
 */
/*
 * 中文注释：
 * 调用方没有通过 XLogReaderSetDecodeBuffer() 指定缓冲区时，环形 decode
 * buffer 的默认大小（64KB）。该大小足以容纳常见 record，使普通读取路径
 * 不必为每条 record 单独 palloc；超出容量的 record 仍走 oversized 的独立
 * 分配路径。
 */
#define DEFAULT_DECODE_BUFFER_SIZE (64 * 1024)

/*
 * Construct a string in state->errormsg_buf explaining what's wrong with
 * the current record being read.
 */
/*
 * 中文注释：
 * 把“当前 record/page 为什么无效”格式化成人类可读消息，写入
 * state->errormsg_buf（最多 MAX_ERRORMSG_LEN 字节），并置
 * state->errormsg_deferred = true，表示有一个待上报的错误。
 *
 * 为什么不在发现错误时立刻报错：本文件同时被 backend 和 frontend 编译，
 * 不能使用 ereport/elog；而且 XLogReadAhead() 可能已经成功解码了若干条
 * record 排在队列里，调用方应先把这些 record 消费完，再看到错误。真正的错误
 * 文本由 XLogNextRecord()/XLogReadRecord() 通过 *errormsg 返回，由调用方
 * 决定 FATAL/ERROR 或直接打印。
 *
 * 参数：
 *   state：reader 状态，错误缓冲区和 deferred 标志都在其中；
 *   fmt, ...：printf 风格的错误描述，会经过 gettext 翻译。
 *
 * 副作用：覆盖 errormsg_buf 中已有的消息（只保留最后一次错误），设置
 * errormsg_deferred；不分配内存、不抛异常。仅操作调用方私有的 reader，
 * 无并发保护需求。
 */
static void
report_invalid_record(XLogReaderState *state, const char *fmt, ...)
{
	va_list		args;

	fmt = _(fmt);

	va_start(args, fmt);
	vsnprintf(state->errormsg_buf, MAX_ERRORMSG_LEN, fmt, args);
	va_end(args);

	state->errormsg_deferred = true;
}

/*
 * Set the size of the decoding buffer.  A pointer to a caller supplied memory
 * region may also be passed in, in which case non-oversized records will be
 * decoded there.
 */
/*
 * 中文注释：
 * 为 reader 指定解码缓冲区（decode buffer）及其大小。buffer 可以由调用方
 * 提供（例如恢复时按 wal_decode_buffer_size 使用一块大内存），也可以传
 * NULL，表示稍后由 XLogReadRecordAlloc() 按 DEFAULT_DECODE_BUFFER_SIZE
 * 自动 palloc。
 *
 * 调用场景：必须在第一次解码之前调用；xlogrecovery.c 在 XLogReaderAllocate()
 * 之后用它设置恢复用的解码缓冲区大小，以便 readahead/prefetch 能缓存多条
 * 已解码 record。断言 state->decode_buffer == NULL，防止重复设置或覆盖已经
 * 分配的缓冲区。
 *
 * 参数：
 *   state：已分配但尚未开始读取的 reader；
 *   buffer/size：外部缓冲区及其字节数；size 为 0 时使用默认大小。
 *
 * 副作用：只初始化 decode_buffer/head/tail 指针和大小，不触碰 readBuf。
 * 若 buffer 非 NULL，reader 不拥有它，XLogReaderFree 不会释放；
 * free_decode_buffer 保持为零（state 由 MCXT_ALLOC_ZERO 分配）。
 */
void
XLogReaderSetDecodeBuffer(XLogReaderState *state, void *buffer, size_t size)
{
	Assert(state->decode_buffer == NULL);

	state->decode_buffer = buffer;
	state->decode_buffer_size = size;
	state->decode_buffer_tail = buffer;
	state->decode_buffer_head = buffer;
}

/*
 * Allocate and initialize a new XLogReader.
 *
 * Returns NULL if the xlogreader couldn't be allocated.
 */
/*
 * 中文注释：
 * 分配并初始化一个 XLogReaderState，是使用 XLogReader 的入口。调用方随后
 * 通常执行 XLogBeginRead()/XLogFindNextRecord()，再循环调用 XLogReadRecord()
 * 直到返回 NULL。
 *
 * 参数：
 *   wal_segment_size：WAL segment 大小（字节），用于计算 segment 边界；
 *   waldir：WAL 目录，可为 NULL（流复制/归档场景由回调自行决定路径）；
 *   routine：回调集合，至少必须提供 segment_close；要调用 XLogReadRecord
 *     还必须提供 page_read；要使用 WALRead 则还需 segment_open；
 *   private_data：原样保存在 state 中，供回调取用自己的上下文。
 *
 * 返回值：成功返回零初始化的 state；内存不足返回 NULL（使用
 * MCXT_ALLOC_NO_OOM，不抛错），由调用方决定如何报告。
 *
 * 初始化内容：复制 routine；永久分配 XLOG_BLCKSZ 字节的 readBuf（页缓存）；
 * 初始化 seg/segcxt（ws_file = -1 表示尚未打开任何段）；分配 errormsg_buf；
 * 以最小大小初始化 readRecordBuf（跨页重组时再按需增长）。
 * system_identifier 默认为 0，表示不校验 WAL 来源的系统标识；
 * ReadRecPtr/EndRecPtr/readLen 等由 MCXT_ALLOC_ZERO 清零。
 *
 * 副作用：进行多次 palloc；失败路径会释放已分配的部分，不会泄漏。
 * 返回的 state 只能由分配它的进程/线程使用，内部没有加锁。
 */
XLogReaderState *
XLogReaderAllocate(int wal_segment_size, const char *waldir,
				   XLogReaderRoutine *routine, void *private_data)
{
	XLogReaderState *state;

	state = (XLogReaderState *)
		palloc_extended(sizeof(XLogReaderState),
						MCXT_ALLOC_NO_OOM | MCXT_ALLOC_ZERO);
	if (!state)
		return NULL;

	/* initialize caller-provided support functions */
	state->routine = *routine;

	/*
	 * Permanently allocate readBuf.  We do it this way, rather than just
	 * making a static array, for two reasons: (1) no need to waste the
	 * storage in most instantiations of the backend; (2) a static char array
	 * isn't guaranteed to have any particular alignment, whereas
	 * palloc_extended() will provide MAXALIGN'd storage.
	 */
	state->readBuf = (char *) palloc_extended(XLOG_BLCKSZ,
											  MCXT_ALLOC_NO_OOM);
	if (!state->readBuf)
	{
		pfree(state);
		return NULL;
	}

	/* Initialize segment info. */
	WALOpenSegmentInit(&state->seg, &state->segcxt, wal_segment_size,
					   waldir);

	/* system_identifier initialized to zeroes above */
	state->private_data = private_data;
	/* ReadRecPtr, EndRecPtr and readLen initialized to zeroes above */
	state->errormsg_buf = palloc_extended(MAX_ERRORMSG_LEN + 1,
										  MCXT_ALLOC_NO_OOM);
	if (!state->errormsg_buf)
	{
		pfree(state->readBuf);
		pfree(state);
		return NULL;
	}
	state->errormsg_buf[0] = '\0';

	/*
	 * Allocate an initial readRecordBuf of minimal size, which can later be
	 * enlarged if necessary.
	 */
	allocate_recordbuf(state, 0);
	return state;
}

/*
 * 中文注释：
 * 释放 XLogReader 及其拥有的全部资源：关闭仍打开的 WAL segment（通过
 * routine.segment_close），释放 decode_buffer（仅当 free_decode_buffer 为真，
 * 即由 reader 自己 palloc 时）、错误消息缓冲区、跨页重组缓冲区
 * readRecordBuf、页缓存 readBuf，最后释放 state 本身。
 *
 * 调用场景：读取结束、错误清理或 backend 退出前。调用后所有由
 * XLogNextRecord()/XLogReadRecord() 返回的 DecodedXLogRecord 指针，以及
 * XLogRecGetBlockData()/XLogRecGetData() 指向的数据都失效，调用方不得再使用。
 *
 * 注意：state->seg.ws_file == -1 表示没有打开的段，此时不调用 segment_close；
 * 该约定由 WALOpenSegmentInit 和各 segment 回调共同维护。函数不检查 NULL，
 * 调用方需保证 state 非空。
 */
void
XLogReaderFree(XLogReaderState *state)
{
	if (state->seg.ws_file != -1)
		state->routine.segment_close(state);

	if (state->decode_buffer && state->free_decode_buffer)
		pfree(state->decode_buffer);

	pfree(state->errormsg_buf);
	if (state->readRecordBuf)
		pfree(state->readRecordBuf);
	pfree(state->readBuf);
	pfree(state);
}

/*
 * Allocate readRecordBuf to fit a record of at least the given length.
 *
 * readRecordBufSize is set to the new buffer size.
 *
 * To avoid useless small increases, round its size to a multiple of
 * XLOG_BLCKSZ, and make sure it's at least 5*Max(BLCKSZ, XLOG_BLCKSZ) to start
 * with.  (That is enough for all "normal" records, but very large commit or
 * abort records might need more space.)
 *
 * The caller must make sure that "reclength" is valid and within the
 * XLogRecordMaxSize limit.
 *
 * Note: This routine should *never* be called for xl_tot_len until the header
 * of the record has been fully validated.
 */
/*
 * 中文注释：
 * 确保 state->readRecordBuf 至少能容纳 reclength 字节的完整 record，并把
 * readRecordBufSize 更新为新大小。
 *
 * 该缓冲区只用于“跨页 record 的重组”：一条 record 从当前页开始、延续到
 * 后续页时，XLogDecodeNextRecord() 会把所有片段 memcpy 到这里，再做 CRC
 * 校验和解码。不跨页的 record 直接使用 readBuf，不会分配此缓冲区。
 *
 * 大小策略：向上按 XLOG_BLCKSZ 对齐，避免为每条略大的 record 反复 palloc；
 * 最小为 5 * Max(BLCKSZ, XLOG_BLCKSZ)，足以容纳常见的 commit/abort record
 * 以及跨页 record header；超大 record 则按实际长度增长。
 *
 * 参数 reclength 必须已经过合法性检查（<= XLogRecordMaxSize）：在 record
 * header 尚未验证前绝不能拿不可信的 xl_tot_len 调用本函数，否则可能因超大
 * 分配而拒绝服务。函数会释放旧缓冲区，因此此前从 readRecordBuf 取得的指针
 * 全部失效；调用发生在单线程 reader 内，无并发问题。
 */
static void
allocate_recordbuf(XLogReaderState *state, uint32 reclength)
{
	uint32		newSize;

	Assert(reclength <= XLogRecordMaxSize);

	newSize = TYPEALIGN(XLOG_BLCKSZ, reclength);
	newSize = Max(newSize, 5 * Max(BLCKSZ, XLOG_BLCKSZ));

	if (state->readRecordBuf)
		pfree(state->readRecordBuf);
	state->readRecordBuf = (char *) palloc(newSize);
	state->readRecordBufSize = newSize;
}

/*
 * Initialize the passed segment structs.
 */
/*
 * 中文注释：
 * 初始化 WAL 打开段（WALOpenSegment）和段上下文（WALSegmentContext）。
 *
 * WALOpenSegment 记录当前打开的段文件描述符、段号和 timeline；
 * WALSegmentContext 记录 WAL 目录和段大小，供 WALRead/页读取回调计算段内
 * 偏移和段号。ws_file 初始化为 -1，作为“没有打开文件”的哨兵，XLogReaderFree
 * 和 WALRead 都依赖该约定；ws_segno/ws_tli 置 0。
 *
 * waldir 为 NULL 时保留 ws_dir 的零值（由调用方回调自行决定路径）；非 NULL
 * 时截断复制到 MAXPGPATH 大小的缓冲区。
 *
 * 调用场景：XLogReaderAllocate() 中调用一次；之后由 WALRead 的
 * segment_open/segment_close 回调更新 ws_file/ws_segno/ws_tli。
 * 纯初始化，无 I/O、无锁。
 */
static void
WALOpenSegmentInit(WALOpenSegment *seg, WALSegmentContext *segcxt,
				   int segsize, const char *waldir)
{
	seg->ws_file = -1;
	seg->ws_segno = 0;
	seg->ws_tli = 0;

	segcxt->ws_segsize = segsize;
	if (waldir)
		snprintf(segcxt->ws_dir, MAXPGPATH, "%s", waldir);
}

/*
 * Begin reading WAL at 'RecPtr'.
 *
 * 'RecPtr' should point to the beginning of a valid WAL record.  Pointing at
 * the beginning of a page is also OK, if there is a new record right after
 * the page header, i.e. not a continuation.
 *
 * This does not make any attempt to read the WAL yet, and hence cannot fail.
 * If the starting address is not correct, the first call to XLogReadRecord()
 * will error out.
 */
/*
 * 中文注释：
 * 把 reader 定位到 RecPtr，准备读取该位置开始（或该页第一条 record）的 WAL。
 *
 * RecPtr 必须指向一条有效 record 的起始位置，或指向某个 page 的起始位置
 * （此时要求页头之后紧接一条新 record，而不是 continuation record）。本函数
 * 不读取 WAL，因此不会失败；如果地址不合法，要等到第一次 XLogReadRecord()/
 * XLogReadAhead() 才会报错。
 *
 * 行为：
 *   - 调用 ResetDecoder() 丢弃队列中所有已解码 record（释放 oversized 的），
 *     清空环形 decode buffer 和延迟错误；
 *   - EndRecPtr/NextRecPtr 设为 RecPtr，ReadRecPtr/DecodeRecPtr 置为
 *     InvalidXLogRecPtr；
 *   - DecodeRecPtr 无效会让 XLogDecodeNextRecord() 把下次读取当作随机访问
 *     （randAccess = true），从而只要求 prev-link 小于当前 record 地址，
 *     而不是精确等于上一条 record 的结束位置。
 *
 * 调用场景：恢复开始时定位到 checkpoint 的 redo 点、pg_waldump 定位输出起点、
 * XLogFindNextRecord 找到有效地址后重新定位。调用方不能持有此前
 * XLogNextRecord() 返回的指针，因为 ResetDecoder 已使其失效。
 */
void
XLogBeginRead(XLogReaderState *state, XLogRecPtr RecPtr)
{
	Assert(XLogRecPtrIsValid(RecPtr));

	ResetDecoder(state);

	/* Begin at the passed-in record pointer. */
	state->EndRecPtr = RecPtr;
	state->NextRecPtr = RecPtr;
	state->ReadRecPtr = InvalidXLogRecPtr;
	state->DecodeRecPtr = InvalidXLogRecPtr;
}

/*
 * Release the last record that was returned by XLogNextRecord(), if any, to
 * free up space.  Returns the LSN past the end of the record.
 */
/*
 * 中文注释：
 * 释放最近一次由 XLogNextRecord() 返回的 record（state->record），把它从
 * 已解码 record 队列头部移除，并返回该 record 的 next_lsn（即下一条 record
 * 的起始 LSN）。没有待释放 record 时返回 InvalidXLogRecPtr。
 *
 * 释放策略：
 *   - oversized record 是单独 palloc 的，直接 pfree；
 *   - 普通 record 位于环形 decode_buffer 中，只需把 head 前移到下一条仍在
 *     buffer 中的 record（跳过队列里夹在中间的 oversized record）；若队列
 *     已空，把 head/tail 一起重置到缓冲区起点，以便复用整块空间；
 *   - 这里不移动/压缩数据。调用方在 release 后不应继续使用此前返回的指针。
 *
 * 调用场景：XLogNextRecord() 在返回下一条 record 前自动调用；
 * XLogReadRecord() 在开始新一次读取前也会调用，以便准确判断队列是否为空。
 * prefetch 场景下，调用方消费完一条 record 后也通过它释放空间。
 *
 * 注意：state->record 必须是队列中最老的 decode_queue_head，代码用 Assert
 * 约束；误用会导致队列/缓冲区指针错乱。单线程使用，无锁。
 */
XLogRecPtr
XLogReleasePreviousRecord(XLogReaderState *state)
{
	DecodedXLogRecord *record;
	XLogRecPtr	next_lsn;

	if (!state->record)
		return InvalidXLogRecPtr;

	/*
	 * Remove it from the decoded record queue.  It must be the oldest item
	 * decoded, decode_queue_head.
	 */
	record = state->record;
	next_lsn = record->next_lsn;
	Assert(record == state->decode_queue_head);
	state->record = NULL;
	state->decode_queue_head = record->next;

	/* It might also be the newest item decoded, decode_queue_tail. */
	if (state->decode_queue_tail == record)
		state->decode_queue_tail = NULL;

	/* Release the space. */
	if (unlikely(record->oversized))
	{
		/* It's not in the decode buffer, so free it to release space. */
		pfree(record);
	}
	else
	{
		/* It must be the head (oldest) record in the decode buffer. */
		Assert(state->decode_buffer_head == (char *) record);

		/*
		 * We need to update head to point to the next record that is in the
		 * decode buffer, if any, being careful to skip oversized ones
		 * (they're not in the decode buffer).
		 */
		record = record->next;
		while (unlikely(record && record->oversized))
			record = record->next;

		if (record)
		{
			/* Adjust head to release space up to the next record. */
			state->decode_buffer_head = (char *) record;
		}
		else
		{
			/*
			 * Otherwise we might as well just reset head and tail to the
			 * start of the buffer space, because we're empty.  This means
			 * we'll keep overwriting the same piece of memory if we're not
			 * doing any prefetching.
			 */
			state->decode_buffer_head = state->decode_buffer;
			state->decode_buffer_tail = state->decode_buffer;
		}
	}

	return next_lsn;
}

/*
 * Attempt to read an XLOG record.
 *
 * XLogBeginRead() or XLogFindNextRecord() and then XLogReadAhead() must be
 * called before the first call to XLogNextRecord().  This functions returns
 * records and errors that were put into an internal queue by XLogReadAhead().
 *
 * On success, a record is returned.
 *
 * The returned record (or *errormsg) points to an internal buffer that's
 * valid until the next call to XLogNextRecord.
 */
/*
 * 中文注释：
 * 从已解码 record 队列中取出最老的一条，返回其 DecodedXLogRecord；队列为空
 * 时返回 NULL，并在有延迟错误时通过 *errormsg 返回错误文本。
 *
 * 这是“消费端”接口：XLogReadAhead()/XLogDecodeNextRecord() 只负责把 record
 * 解码并挂到 decode_queue_tail，真正的消费由本函数完成。每次调用会先释放
 * 上一次返回的 record（XLogReleasePreviousRecord），因此返回的指针只保证在
 * 下一次调用本函数之前有效。
 *
 * 返回 record 时还会更新 state->record、ReadRecPtr 和 EndRecPtr，以兼容
 * 历史上直接访问 xlogreader 字段的 XLogRecXXX() 宏。
 *
 * *errormsg 的语义：
 *   - 队列非空：置 NULL，正常返回 record；
 *   - 队列为空且 errormsg_deferred：返回错误文本（若错误由 page_read 回调
 *     直接报告，缓冲区可能为空，此时 *errormsg 仍为 NULL）；
 *   - 队列为空且无错误：返回 NULL，*errormsg = NULL，表示已到 WAL 末尾或
 *     暂时没有数据。
 *
 * 调用方应在循环中先处理返回的 record，再调用下一次；record 内存由 reader
 * 管理，不能 pfree。无锁，state 只能单线程访问。
 */
DecodedXLogRecord *
XLogNextRecord(XLogReaderState *state, char **errormsg)
{
	/* Release the last record returned by XLogNextRecord(). */
	XLogReleasePreviousRecord(state);

	if (state->decode_queue_head == NULL)
	{
		*errormsg = NULL;
		if (state->errormsg_deferred)
		{
			if (state->errormsg_buf[0] != '\0')
				*errormsg = state->errormsg_buf;
			state->errormsg_deferred = false;
		}

		/*
		 * state->EndRecPtr is expected to have been set by the last call to
		 * XLogBeginRead() or XLogNextRecord(), and is the location of the
		 * error.
		 */
		Assert(XLogRecPtrIsValid(state->EndRecPtr));

		return NULL;
	}

	/*
	 * Record this as the most recent record returned, so that we'll release
	 * it next time.  This also exposes it to the traditional
	 * XLogRecXXX(xlogreader) macros, which work with the decoder rather than
	 * the record for historical reasons.
	 */
	state->record = state->decode_queue_head;

	/*
	 * Update the pointers to the beginning and one-past-the-end of this
	 * record, again for the benefit of historical code that expected the
	 * decoder to track this rather than accessing these fields of the record
	 * itself.
	 */
	state->ReadRecPtr = state->record->lsn;
	state->EndRecPtr = state->record->next_lsn;

	*errormsg = NULL;

	return state->record;
}

/*
 * Attempt to read an XLOG record.
 *
 * XLogBeginRead() or XLogFindNextRecord() must be called before the first call
 * to XLogReadRecord().
 *
 * If the page_read callback fails to read the requested data, NULL is
 * returned.  The callback is expected to have reported the error; errormsg
 * is set to NULL.
 *
 * If the reading fails for some other reason, NULL is also returned, and
 * *errormsg is set to a string with details of the failure.
 *
 * The returned pointer (or *errormsg) points to an internal buffer that's
 * valid until the next call to XLogReadRecord.
 */
/*
 * 中文注释：
 * 传统（阻塞式）读取接口：读取下一条 WAL record，成功返回其 XLogRecord
 * 头部指针，失败或到达 WAL 末尾返回 NULL。
 *
 * 使用前提：必须先调用 XLogBeginRead() 或 XLogFindNextRecord() 定位。
 * 内部流程：
 *   1. 释放上一次返回的 record，确保能准确判断队列是否为空；
 *   2. 若队列中没有 record 或错误，则以阻塞模式调用 XLogReadAhead()，等待
 *      至少解码出一条 record（或产生错误）；
 *   3. 调用 XLogNextRecord() 消费队首。
 *
 * 返回值只是 record header 的地址，真正的解码结果在 state->record 中；
 * 调用方应通过 XLogRecGetData()/XLogRecGetBlockXXX() 等宏访问，不要直接
 * 解析返回的 XLogRecord。指针在下一次调用 XLogReadRecord/XLogNextRecord 前
 * 有效。
 *
 * *errormsg 的语义：
 *   - page_read 回调自己报告了错误（例如无法打开文件）时返回 NULL，且
 *     *errormsg = NULL；
 *   - 页头/record 校验失败等 reader 内部错误：返回 NULL，*errormsg 指向
 *     state->errormsg_buf 中的说明；
 *   - 正常到达 WAL 末尾：返回 NULL，*errormsg = NULL。
 *
 * 注意：本函数是阻塞的，非阻塞/预取场景应直接使用 XLogReadAhead()。
 * 单线程使用，不能并发调用同一个 reader。
 */
XLogRecord *
XLogReadRecord(XLogReaderState *state, char **errormsg)
{
	DecodedXLogRecord *decoded;

	/*
	 * Release last returned record, if there is one.  We need to do this so
	 * that we can check for empty decode queue accurately.
	 */
	XLogReleasePreviousRecord(state);

	/*
	 * Call XLogReadAhead() in blocking mode to make sure there is something
	 * in the queue, though we don't use the result.
	 */
	if (!XLogReaderHasQueuedRecordOrError(state))
		XLogReadAhead(state, false /* nonblocking */ );

	/* Consume the head record or error. */
	decoded = XLogNextRecord(state, errormsg);
	if (decoded)
	{
		/*
		 * This function returns a pointer to the record's header, not the
		 * actual decoded record.  The caller will access the decoded record
		 * through the XLogRecGetXXX() macros, which reach the decoded
		 * recorded as xlogreader->record.
		 */
		Assert(state->record == decoded);
		return &decoded->header;
	}

	return NULL;
}

/*
 * Allocate space for a decoded record.  The only member of the returned
 * object that is initialized is the 'oversized' flag, indicating that the
 * decoded record wouldn't fit in the decode buffer and must eventually be
 * freed explicitly.
 *
 * The caller is responsible for adjusting decode_buffer_tail with the real
 * size after successfully decoding a record into this space.  This way, if
 * decoding fails, then there is nothing to undo unless the 'oversized' flag
 * was set and pfree() must be called.
 *
 * Return NULL if there is no space in the decode buffer and allow_oversized
 * is false, or if memory allocation fails for an oversized buffer.
 */
/*
 * 中文注释：
 * 为一条待解码 record 分配空间，返回 DecodedXLogRecord 指针；只初始化
 * oversized 标志，其余字段由 DecodeXLogRecord() 填写。
 *
 * 分配策略：
 *   1. 如果还没有 decode buffer，按 DEFAULT_DECODE_BUFFER_SIZE（或调用方通过
 *      XLogReaderSetDecodeBuffer() 指定的大小）palloc 一块环形缓冲区；
 *   2. 计算 DecodeXLogRecordRequiredSpace(xl_tot_len)，在环形缓冲区中寻找
 *      一段连续空间：优先 tail 到缓冲区末尾；不够则从缓冲区开头到 head；
 *      tail 在 head 左边时则使用两者之间的空隙；
 *   3. 空间不足且 allow_oversized 为 true 时，单独 palloc 一整块并标记
 *      oversized；否则返回 NULL，让调用方在非阻塞模式下返回
 *      XLREAD_WOULDBLOCK。
 *
 * allow_oversized 的两种调用时机：
 *   - 读取早期传 false：此时 xl_tot_len 可能来自回收页中的垃圾数据，不能
 *     据此做大块分配，缓冲区不足就等待/让调用方消费；
 *   - 完成页头、长度和跨页一致性校验后传 true：此时长度可信，允许为超大
 *     record 单独分配。
 *
 * 调用方职责：成功解码后用 decoded->size 推进 decode_buffer_tail；若解码
 * 失败且 oversized，需 pfree。环形缓冲区中的空间在成功前保持“未占用”，
 * 失败无需回滚。
 *
 * 返回 NULL 表示缓冲区空间不足（allow_oversized=false）或内存分配失败；
 * 本函数不设置错误消息。无锁。
 */
static DecodedXLogRecord *
XLogReadRecordAlloc(XLogReaderState *state, size_t xl_tot_len, bool allow_oversized)
{
	size_t		required_space = DecodeXLogRecordRequiredSpace(xl_tot_len);
	DecodedXLogRecord *decoded = NULL;

	/* Allocate a circular decode buffer if we don't have one already. */
	if (unlikely(state->decode_buffer == NULL))
	{
		if (state->decode_buffer_size == 0)
			state->decode_buffer_size = DEFAULT_DECODE_BUFFER_SIZE;
		state->decode_buffer = palloc(state->decode_buffer_size);
		state->decode_buffer_head = state->decode_buffer;
		state->decode_buffer_tail = state->decode_buffer;
		state->free_decode_buffer = true;
	}

	/* Try to allocate space in the circular decode buffer. */
	if (state->decode_buffer_tail >= state->decode_buffer_head)
	{
		/* Empty, or tail is to the right of head. */
		if (required_space <=
			state->decode_buffer_size -
			(state->decode_buffer_tail - state->decode_buffer))
		{
			/*-
			 * There is space between tail and end.
			 *
			 * +-----+--------------------+-----+
			 * |     |////////////////////|here!|
			 * +-----+--------------------+-----+
			 *       ^                    ^
			 *       |                    |
			 *       h                    t
			 */
			decoded = (DecodedXLogRecord *) state->decode_buffer_tail;
			decoded->oversized = false;
			return decoded;
		}
		else if (required_space <
				 state->decode_buffer_head - state->decode_buffer)
		{
			/*-
			 * There is space between start and head.
			 *
			 * +-----+--------------------+-----+
			 * |here!|////////////////////|     |
			 * +-----+--------------------+-----+
			 *       ^                    ^
			 *       |                    |
			 *       h                    t
			 */
			decoded = (DecodedXLogRecord *) state->decode_buffer;
			decoded->oversized = false;
			return decoded;
		}
	}
	else
	{
		/* Tail is to the left of head. */
		if (required_space <
			state->decode_buffer_head - state->decode_buffer_tail)
		{
			/*-
			 * There is space between tail and head.
			 *
			 * +-----+--------------------+-----+
			 * |/////|here!               |/////|
			 * +-----+--------------------+-----+
			 *       ^                    ^
			 *       |                    |
			 *       t                    h
			 */
			decoded = (DecodedXLogRecord *) state->decode_buffer_tail;
			decoded->oversized = false;
			return decoded;
		}
	}

	/* Not enough space in the decode buffer.  Are we allowed to allocate? */
	if (allow_oversized)
	{
		decoded = palloc(required_space);
		decoded->oversized = true;
		return decoded;
	}

	return NULL;
}

/*
 * 中文注释：
 * 解码 NextRecPtr 处的下一条 WAL record，并把它挂到已解码队列尾部。这是
 * XLogReader 的核心状态机，负责“定位 → 读页 → 校验页头 → 取长度 →
 * 跨页重组 → CRC 校验 → 解码入队”的全过程。
 *
 * 参数 nonblocking：
 *   - false：正常阻塞读取；page_read 回调会等待数据，decode buffer 满时也会
 *     继续（必要时为超大 record 单独分配）；
 *   - true：仅供 readahead/prefetch 使用；page_read 暂时无数据或 decode
 *     buffer 没有空间时立即返回 XLREAD_WOULDBLOCK，调用方稍后重试。
 *
 * 返回值（XLogPageReadResult）：
 *   - XLREAD_SUCCESS：成功解码并排队一条 record；
 *   - XLREAD_WOULDBLOCK：非阻塞模式下暂时无数据或无缓冲区空间；
 *   - XLREAD_FAIL：读取或校验失败，错误已通过 report_invalid_record() 记录，
 *     并置 errormsg_deferred，等待调用方消费完队列中已有 record 后上报。
 *
 * 关键流程：
 *   1. 清空上次错误（errormsg_buf[0] = '\0'）、abortedRecPtr、
 *      missingContrecPtr；从 NextRecPtr 开始。若 DecodeRecPtr 有效，说明是
 *      顺序读取；否则是 XLogBeginRead() 指定的随机访问（randAccess = true）。
 *   2. ReadPageInternal() 读取包含 record 头的页；XLogPageHeaderSize() 返回
 *      短/长页头长度。若 RecPtr 正好在页首则跳过页头；若偏移落在页头内则
 *      报错；若页头带 XLP_FIRST_IS_CONTRECORD 而目标位置正好是页头之后的
 *      第一条 record，说明调用方要求从 contrecord 中间开始读，报错。
 *   3. 读取 xl_tot_len。若完整 record header 在同一页内，立即调用
 *      ValidXLogRecordHeader() 校验（长度范围、rmid、prev-link）；否则只做
 *      xl_tot_len 的基本范围检查，等跨页重组出完整 header 后再校验。
 *   4. 尝试在 decode buffer 中预留空间（不允许 oversized）；非阻塞且无空间
 *      则返回 XLREAD_WOULDBLOCK。
 *   5. 若 record 不跨页：等待该 record 的数据全部到齐，由 ValidXLogRecord()
 *      做 CRC32C 校验，NextRecPtr = RecPtr + MAXALIGN(total_len)。
 *   6. 若跨页：循环读取后续页，逐页检查 XLP_FIRST_IS_CONTRECORD、
 *      xlp_rem_len 与 total_len 的一致性；遇到 XLP_FIRST_IS_OVERWRITE_
 *      CONTRECORD 时记录 overwrittenRecPtr，并把 RecPtr 重置到该页重新开始
 *      （restart），以兼容恢复期间被覆盖的 contrecord；必要时扩展
 *      readRecordBuf。重组完成后统一做 CRC 校验。
 *   7. 若 record 是 RM_XLOG_ID/XLOG_SWITCH，把 NextRecPtr 直接推到 segment
 *      末尾之后，跳过段尾可能存在的填充/垃圾数据。
 *   8. 调用 DecodeXLogRecord() 拆出 main data 和 block reference；成功后设置
 *      decoded->next_lsn，推进环形缓冲区 tail，并挂入 decode_queue。
 *
 * 错误处理与恢复：
 *   - 跨页重组失败时，设置 abortedRecPtr（正在读的 record 起点）和
 *     missingContrecPtr（缺失 contrecord 的页起点），供 xlogrecovery 在恢复
 *     结束后写入 XLP_FIRST_IS_OVERWRITE_CONTRECORD、标记该 record 作废；
 *   - 即使没有新错误写入 errormsg_buf，也置 errormsg_deferred = true，避免
 *     prefetcher 再次进入并覆盖 aborted/missing 状态；
 *   - 任何失败都会 pfree oversized 临时记录并调用 XLogReaderInvalReadState()
 *     使页缓存失效，因为失败后可能切换 WAL 来源；
 *   - 调用方看到的错误是延迟的：XLogNextRecord() 先把队列中的 record 返回完，
 *     再报告错误。
 *
 * 副作用：读取 WAL（可能阻塞/进行 I/O）、修改 state 的 NextRecPtr/
 * DecodeRecPtr/currRecPtr/readLen/seg 等、分配或释放内存、操作解码队列。
 * 只在单个 reader 上串行调用，无内部锁。
 */
static XLogPageReadResult
XLogDecodeNextRecord(XLogReaderState *state, bool nonblocking)
{
	XLogRecPtr	RecPtr;
	XLogRecord *record;
	XLogRecPtr	targetPagePtr;
	bool		randAccess;
	uint32		len,
				total_len;
	uint32		targetRecOff;
	uint32		pageHeaderSize;
	bool		assembled;
	bool		gotheader;
	int			readOff;
	DecodedXLogRecord *decoded;
	char	   *errormsg;		/* not used */

	/*
	 * randAccess indicates whether to verify the previous-record pointer of
	 * the record we're reading.  We only do this if we're reading
	 * sequentially, which is what we initially assume.
	 */
	randAccess = false;

	/* reset error state */
	state->errormsg_buf[0] = '\0';
	decoded = NULL;

	state->abortedRecPtr = InvalidXLogRecPtr;
	state->missingContrecPtr = InvalidXLogRecPtr;

	RecPtr = state->NextRecPtr;

	if (XLogRecPtrIsValid(state->DecodeRecPtr))
	{
		/* read the record after the one we just read */

		/*
		 * NextRecPtr is pointing to end+1 of the previous WAL record.  If
		 * we're at a page boundary, no more records can fit on the current
		 * page. We must skip over the page header, but we can't do that until
		 * we've read in the page, since the header size is variable.
		 */
	}
	else
	{
		/*
		 * Caller supplied a position to start at.
		 *
		 * In this case, NextRecPtr should already be pointing either to a
		 * valid record starting position or alternatively to the beginning of
		 * a page. See the header comments for XLogBeginRead.
		 */
		Assert(RecPtr % XLOG_BLCKSZ == 0 || XRecOffIsValid(RecPtr));
		randAccess = true;
	}

restart:
	state->nonblocking = nonblocking;
	state->currRecPtr = RecPtr;
	assembled = false;

	targetPagePtr = RecPtr - (RecPtr % XLOG_BLCKSZ);
	targetRecOff = RecPtr % XLOG_BLCKSZ;

	/*
	 * Read the page containing the record into state->readBuf. Request enough
	 * byte to cover the whole record header, or at least the part of it that
	 * fits on the same page.
	 */
	readOff = ReadPageInternal(state, targetPagePtr,
							   Min(targetRecOff + SizeOfXLogRecord, XLOG_BLCKSZ));
	if (readOff == XLREAD_WOULDBLOCK)
		return XLREAD_WOULDBLOCK;
	else if (readOff < 0)
		goto err;

	/*
	 * ReadPageInternal always returns at least the page header, so we can
	 * examine it now.
	 */
	pageHeaderSize = XLogPageHeaderSize((XLogPageHeader) state->readBuf);
	if (targetRecOff == 0)
	{
		/*
		 * At page start, so skip over page header.
		 */
		RecPtr += pageHeaderSize;
		targetRecOff = pageHeaderSize;
	}
	else if (targetRecOff < pageHeaderSize)
	{
		report_invalid_record(state, "invalid record offset at %X/%08X: expected at least %u, got %u",
							  LSN_FORMAT_ARGS(RecPtr),
							  pageHeaderSize, targetRecOff);
		goto err;
	}

	if ((((XLogPageHeader) state->readBuf)->xlp_info & XLP_FIRST_IS_CONTRECORD) &&
		targetRecOff == pageHeaderSize)
	{
		report_invalid_record(state, "contrecord is requested by %X/%08X",
							  LSN_FORMAT_ARGS(RecPtr));
		goto err;
	}

	/* ReadPageInternal has verified the page header */
	Assert(pageHeaderSize <= readOff);

	/*
	 * Read the record length.
	 *
	 * NB: Even though we use an XLogRecord pointer here, the whole record
	 * header might not fit on this page. xl_tot_len is the first field of the
	 * struct, so it must be on this page (the records are MAXALIGNed), but we
	 * cannot access any other fields until we've verified that we got the
	 * whole header.
	 */
	record = (XLogRecord *) (state->readBuf + RecPtr % XLOG_BLCKSZ);
	total_len = record->xl_tot_len;

	/*
	 * If the whole record header is on this page, validate it immediately.
	 * Otherwise do just a basic sanity check on xl_tot_len, and validate the
	 * rest of the header after reading it from the next page.  The xl_tot_len
	 * check is necessary here to ensure that we enter the "Need to reassemble
	 * record" code path below; otherwise we might fail to apply
	 * ValidXLogRecordHeader at all.
	 */
	if (targetRecOff <= XLOG_BLCKSZ - SizeOfXLogRecord)
	{
		if (!ValidXLogRecordHeader(state, RecPtr, state->DecodeRecPtr, record,
								   randAccess))
			goto err;
		gotheader = true;
	}
	else
	{
		/* There may be no next page if it's too small. */
		if (total_len < SizeOfXLogRecord)
		{
			report_invalid_record(state,
								  "invalid record length at %X/%08X: expected at least %u, got %u",
								  LSN_FORMAT_ARGS(RecPtr),
								  (uint32) SizeOfXLogRecord, total_len);
			goto err;
		}

		/*
		 * If the record length exceeds the maximum allowed size, don't try to
		 * reconstruct it.  The backend enforces the same limit in
		 * XLogRecordAssemble().
		 */
		if (total_len > XLogRecordMaxSize)
		{
			report_invalid_record(state,
								  "invalid record length at %X/%08X: expected at most %u, got %u",
								  LSN_FORMAT_ARGS(RecPtr),
								  XLogRecordMaxSize, total_len);
			goto err;
		}

		/* We'll validate the header once we have the next page. */
		gotheader = false;
	}

	/*
	 * Try to find space to decode this record, if we can do so without
	 * calling palloc.  If we can't, we'll try again below after we've
	 * validated that total_len isn't garbage bytes from a recycled WAL page.
	 */
	decoded = XLogReadRecordAlloc(state,
								  total_len,
								  false /* allow_oversized */ );
	if (decoded == NULL && nonblocking)
	{
		/*
		 * There is no space in the circular decode buffer, and the caller is
		 * only reading ahead.  The caller should consume existing records to
		 * make space.
		 */
		return XLREAD_WOULDBLOCK;
	}

	len = XLOG_BLCKSZ - RecPtr % XLOG_BLCKSZ;
	if (total_len > len)
	{
		/* Need to reassemble record */
		char	   *contdata;
		XLogPageHeader pageHeader;
		char	   *buffer;
		uint32		gotlen;

		assembled = true;

		/*
		 * We always have space for a couple of pages, enough to validate a
		 * boundary-spanning record header.
		 */
		Assert(state->readRecordBufSize >= XLOG_BLCKSZ * 2);
		Assert(state->readRecordBufSize >= len);

		/* Copy the first fragment of the record from the first page. */
		memcpy(state->readRecordBuf,
			   state->readBuf + RecPtr % XLOG_BLCKSZ, len);
		buffer = state->readRecordBuf + len;
		gotlen = len;

		do
		{
			/* Calculate pointer to beginning of next page */
			targetPagePtr += XLOG_BLCKSZ;

			/*
			 * Read the page header before processing the record data, so we
			 * can handle the case where the previous record ended as being a
			 * partial one.
			 */
			readOff = ReadPageInternal(state, targetPagePtr, SizeOfXLogShortPHD);
			if (readOff == XLREAD_WOULDBLOCK)
				return XLREAD_WOULDBLOCK;
			else if (readOff < 0)
				goto err;

			Assert(SizeOfXLogShortPHD <= readOff);

			pageHeader = (XLogPageHeader) state->readBuf;

			/*
			 * If we were expecting a continuation record and got an
			 * "overwrite contrecord" flag, that means the continuation record
			 * was overwritten with a different record.  Restart the read by
			 * assuming the address to read is the location where we found
			 * this flag; but keep track of the LSN of the record we were
			 * reading, for later verification.
			 */
			if (pageHeader->xlp_info & XLP_FIRST_IS_OVERWRITE_CONTRECORD)
			{
				state->overwrittenRecPtr = RecPtr;
				RecPtr = targetPagePtr;
				goto restart;
			}

			/* Check that the continuation on next page looks valid */
			if (!(pageHeader->xlp_info & XLP_FIRST_IS_CONTRECORD))
			{
				report_invalid_record(state,
									  "there is no contrecord flag at %X/%08X",
									  LSN_FORMAT_ARGS(RecPtr));
				goto err;
			}

			/*
			 * Cross-check that xlp_rem_len agrees with how much of the record
			 * we expect there to be left.
			 */
			if (pageHeader->xlp_rem_len == 0 ||
				total_len != (pageHeader->xlp_rem_len + gotlen))
			{
				report_invalid_record(state,
									  "invalid contrecord length %u (expected %lld) at %X/%08X",
									  pageHeader->xlp_rem_len,
									  ((long long) total_len) - gotlen,
									  LSN_FORMAT_ARGS(RecPtr));
				goto err;
			}

			/* Wait for the next page to become available */
			readOff = ReadPageInternal(state, targetPagePtr,
									   Min(total_len - gotlen + SizeOfXLogShortPHD,
										   XLOG_BLCKSZ));
			if (readOff == XLREAD_WOULDBLOCK)
				return XLREAD_WOULDBLOCK;
			else if (readOff < 0)
				goto err;

			/* Append the continuation from this page to the buffer */
			pageHeaderSize = XLogPageHeaderSize(pageHeader);

			if (readOff < pageHeaderSize)
				readOff = ReadPageInternal(state, targetPagePtr,
										   pageHeaderSize);

			Assert(pageHeaderSize <= readOff);

			contdata = (char *) state->readBuf + pageHeaderSize;
			len = XLOG_BLCKSZ - pageHeaderSize;
			if (pageHeader->xlp_rem_len < len)
				len = pageHeader->xlp_rem_len;

			if (readOff < pageHeaderSize + len)
				readOff = ReadPageInternal(state, targetPagePtr,
										   pageHeaderSize + len);

			memcpy(buffer, contdata, len);
			buffer += len;
			gotlen += len;

			/* If we just reassembled the record header, validate it. */
			if (!gotheader)
			{
				record = (XLogRecord *) state->readRecordBuf;
				if (!ValidXLogRecordHeader(state, RecPtr, state->DecodeRecPtr,
										   record, randAccess))
					goto err;
				gotheader = true;
			}

			/*
			 * We might need a bigger buffer.  We have validated the record
			 * header, in the case that it split over a page boundary.  We've
			 * also cross-checked total_len against xlp_rem_len on the second
			 * page, and verified xlp_pageaddr on both.
			 */
			if (total_len > state->readRecordBufSize)
			{
				char		save_copy[XLOG_BLCKSZ * 2];

				/*
				 * Save and restore the data we already had.  It can't be more
				 * than two pages.
				 */
				Assert(gotlen <= lengthof(save_copy));
				Assert(gotlen <= state->readRecordBufSize);
				memcpy(save_copy, state->readRecordBuf, gotlen);
				allocate_recordbuf(state, total_len);
				memcpy(state->readRecordBuf, save_copy, gotlen);
				buffer = state->readRecordBuf + gotlen;
			}
		} while (gotlen < total_len);
		Assert(gotheader);

		record = (XLogRecord *) state->readRecordBuf;
		if (!ValidXLogRecord(state, record, RecPtr))
			goto err;

		pageHeaderSize = XLogPageHeaderSize((XLogPageHeader) state->readBuf);
		state->DecodeRecPtr = RecPtr;
		state->NextRecPtr = targetPagePtr + pageHeaderSize
			+ MAXALIGN(pageHeader->xlp_rem_len);
	}
	else
	{
		/* Wait for the record data to become available */
		readOff = ReadPageInternal(state, targetPagePtr,
								   Min(targetRecOff + total_len, XLOG_BLCKSZ));
		if (readOff == XLREAD_WOULDBLOCK)
			return XLREAD_WOULDBLOCK;
		else if (readOff < 0)
			goto err;

		/* Record does not cross a page boundary */
		if (!ValidXLogRecord(state, record, RecPtr))
			goto err;

		state->NextRecPtr = RecPtr + MAXALIGN(total_len);

		state->DecodeRecPtr = RecPtr;
	}

	/*
	 * Special processing if it's an XLOG SWITCH record
	 */
	if (record->xl_rmid == RM_XLOG_ID &&
		(record->xl_info & ~XLR_INFO_MASK) == XLOG_SWITCH)
	{
		/* Pretend it extends to end of segment */
		state->NextRecPtr += state->segcxt.ws_segsize - 1;
		state->NextRecPtr -= XLogSegmentOffset(state->NextRecPtr, state->segcxt.ws_segsize);
	}

	/*
	 * If we got here without a DecodedXLogRecord, it means we needed to
	 * validate total_len before trusting it, but by now we've done that.
	 */
	if (decoded == NULL)
	{
		Assert(!nonblocking);
		decoded = XLogReadRecordAlloc(state,
									  total_len,
									  true /* allow_oversized */ );
		/* allocation should always happen under allow_oversized */
		Assert(decoded != NULL);
	}

	if (DecodeXLogRecord(state, decoded, record, RecPtr, &errormsg))
	{
		/* Record the location of the next record. */
		decoded->next_lsn = state->NextRecPtr;

		/*
		 * If it's in the decode buffer, mark the decode buffer space as
		 * occupied.
		 */
		if (!decoded->oversized)
		{
			/* The new decode buffer head must be MAXALIGNed. */
			Assert(decoded->size == MAXALIGN(decoded->size));
			if ((char *) decoded == state->decode_buffer)
				state->decode_buffer_tail = state->decode_buffer + decoded->size;
			else
				state->decode_buffer_tail += decoded->size;
		}

		/* Insert it into the queue of decoded records. */
		Assert(state->decode_queue_tail != decoded);
		if (state->decode_queue_tail)
			state->decode_queue_tail->next = decoded;
		state->decode_queue_tail = decoded;
		if (!state->decode_queue_head)
			state->decode_queue_head = decoded;
		return XLREAD_SUCCESS;
	}

err:
	if (assembled)
	{
		/*
		 * We get here when a record that spans multiple pages needs to be
		 * assembled, but something went wrong -- perhaps a contrecord piece
		 * was lost.  If caller is WAL replay, it will know where the aborted
		 * record was and where to direct followup WAL to be written, marking
		 * the next piece with XLP_FIRST_IS_OVERWRITE_CONTRECORD, which will
		 * in turn signal downstream WAL consumers that the broken WAL record
		 * is to be ignored.
		 */
		state->abortedRecPtr = RecPtr;
		state->missingContrecPtr = targetPagePtr;

		/*
		 * If we got here without reporting an error, make sure an error is
		 * queued so that XLogPrefetcherReadRecord() doesn't bring us back a
		 * second time and clobber the above state.
		 */
		state->errormsg_deferred = true;
	}

	if (decoded && decoded->oversized)
		pfree(decoded);

	/*
	 * Invalidate the read state. We might read from a different source after
	 * failure.
	 */
	XLogReaderInvalReadState(state);

	/*
	 * If an error was written to errormsg_buf, it'll be returned to the
	 * caller of XLogReadRecord() after all successfully decoded records from
	 * the read queue.
	 */

	return XLREAD_FAIL;
}

/*
 * Try to decode the next available record, and return it.  The record will
 * also be returned to XLogNextRecord(), which must be called to 'consume'
 * each record.
 *
 * If nonblocking is true, may return NULL due to lack of data or WAL decoding
 * space.
 */
/*
 * 中文注释：
 * 尝试解码下一条 record 并放入队列，但不消费它。成功返回新解码的
 * DecodedXLogRecord（即 decode_queue_tail），没有数据/空间或已有延迟错误时
 * 返回 NULL。
 *
 * 调用场景：预取器（xlogprefetcher.c）用 nonblocking=true 提前解码 WAL，
 * 以便在 redo 需要之前发起 block prefetch；恢复主循环和逻辑解码则可用
 * nonblocking=false 主动填充队列。与 XLogReadRecord() 不同，本函数不释放、
 * 不返回队首 record，record 必须由 XLogNextRecord() 消费。
 *
 * nonblocking 语义：true 时若 page_read 暂时没有数据，或环形 decode buffer
 * 没有足够空间，返回 NULL（内部对应 XLREAD_WOULDBLOCK），调用方应先消费已有
 * record 再重试；false 时会等待数据，并允许为超大 record 单独分配。
 *
 * 若 state->errormsg_deferred 已置位，直接返回 NULL，避免在错误未上报前继续
 * 解码、覆盖错误状态。返回 NULL 不一定代表 WAL 结束，调用方应结合
 * XLogReaderHasQueuedRecordOrError() 和错误消息判断。
 */
DecodedXLogRecord *
XLogReadAhead(XLogReaderState *state, bool nonblocking)
{
	XLogPageReadResult result;

	if (state->errormsg_deferred)
		return NULL;

	result = XLogDecodeNextRecord(state, nonblocking);
	if (result == XLREAD_SUCCESS)
	{
		Assert(state->decode_queue_tail != NULL);
		return state->decode_queue_tail;
	}

	return NULL;
}

/*
 * Read a single xlog page including at least [pageptr, reqLen] of valid data
 * via the page_read() callback.
 *
 * Returns XLREAD_FAIL if the required page cannot be read for some
 * reason; errormsg_buf is set in that case (unless the error occurs in the
 * page_read callback).
 *
 * Returns XLREAD_WOULDBLOCK if the requested data can't be read without
 * waiting.  This can be returned only if the installed page_read callback
 * respects the state->nonblocking flag, and cannot read the requested data
 * immediately.
 *
 * We fetch the page from a reader-local cache if we know we have the required
 * data and if there hasn't been any error since caching the data.
 */
/*
 * 中文注释：
 * 读取包含 [pageptr, pageptr + reqLen) 的单个 WAL page，通过
 * state->routine.page_read 回调取数，校验页头后缓存到 state->readBuf。
 *
 * 参数：
 *   pageptr：页起始地址，必须按 XLOG_BLCKSZ 对齐；
 *   reqLen：调用方至少需要的字节数（通常覆盖 record header 或整条 record）；
 *     回调实际可返回更多，最多 XLOG_BLCKSZ。
 *
 * 返回值：
 *   >= 0：readBuf 中有效字节数（至少 reqLen，且不超过 XLOG_BLCKSZ）；
 *   XLREAD_WOULDBLOCK：仅当 page_read 遵守 state->nonblocking 且暂时无数据；
 *   XLREAD_FAIL：读取失败或页头校验失败，errormsg_buf 可能已设置（若错误由
 *     page_read 回调直接报告，则缓冲区可能为空）。
 *
 * 缓存逻辑：若请求的 (segment, offset) 与上次相同且 readLen >= reqLen，直接
 * 返回缓存，避免重复 I/O。缓存未命中时先把 readLen 置 0（保留上次 segno，
 * 以便判断是否需要读段首页），再实际读取。
 *
 * 跨段处理：切换到新 segment 且目标不在段首时，先读该段第一页并校验其长页头
 * （system identifier、segment size、XLOG_BLCKSZ），确保读到的是正确来源的
 * WAL；这是防止误读回收中或其他集群 WAL 的关键检查。
 *
 * 读取分两步：先读 Max(reqLen, SizeOfXLogShortPHD)，至少覆盖短页头；若页头
 * 是长页头则再补读到 XLogPageHeaderSize()；最后调用
 * XLogReaderValidatePageHeader() 校验。任何失败都会
 * XLogReaderInvalReadState() 重置缓存并返回 XLREAD_FAIL。
 *
 * 副作用：修改 readBuf、readLen、seg.ws_segno、segoff；可能触发 I/O。
 * page_read 回调还可能更新 seg.ws_tli。单线程 reader，无锁。
 */
static int
ReadPageInternal(XLogReaderState *state, XLogRecPtr pageptr, int reqLen)
{
	int			readLen;
	uint32		targetPageOff;
	XLogSegNo	targetSegNo;
	XLogPageHeader hdr;

	Assert((pageptr % XLOG_BLCKSZ) == 0);

	XLByteToSeg(pageptr, targetSegNo, state->segcxt.ws_segsize);
	targetPageOff = XLogSegmentOffset(pageptr, state->segcxt.ws_segsize);

	/* check whether we have all the requested data already */
	if (targetSegNo == state->seg.ws_segno &&
		targetPageOff == state->segoff && reqLen <= state->readLen)
		return state->readLen;

	/*
	 * Invalidate contents of internal buffer before read attempt.  Just set
	 * the length to 0, rather than a full XLogReaderInvalReadState(), so we
	 * don't forget the segment we last successfully read.
	 */
	state->readLen = 0;

	/*
	 * Data is not in our buffer.
	 *
	 * Every time we actually read the segment, even if we looked at parts of
	 * it before, we need to do verification as the page_read callback might
	 * now be rereading data from a different source.
	 *
	 * Whenever switching to a new WAL segment, we read the first page of the
	 * file and validate its header, even if that's not where the target
	 * record is.  This is so that we can check the additional identification
	 * info that is present in the first page's "long" header.
	 */
	if (targetSegNo != state->seg.ws_segno && targetPageOff != 0)
	{
		XLogRecPtr	targetSegmentPtr = pageptr - targetPageOff;

		readLen = state->routine.page_read(state, targetSegmentPtr, XLOG_BLCKSZ,
										   state->currRecPtr,
										   state->readBuf);
		if (readLen == XLREAD_WOULDBLOCK)
			return XLREAD_WOULDBLOCK;
		else if (readLen < 0)
			goto err;

		/* we can be sure to have enough WAL available, we scrolled back */
		Assert(readLen == XLOG_BLCKSZ);

		if (!XLogReaderValidatePageHeader(state, targetSegmentPtr,
										  state->readBuf))
			goto err;
	}

	/*
	 * First, read the requested data length, but at least a short page header
	 * so that we can validate it.
	 */
	readLen = state->routine.page_read(state, pageptr, Max(reqLen, SizeOfXLogShortPHD),
									   state->currRecPtr,
									   state->readBuf);
	if (readLen == XLREAD_WOULDBLOCK)
		return XLREAD_WOULDBLOCK;
	else if (readLen < 0)
		goto err;

	Assert(readLen <= XLOG_BLCKSZ);

	/* Do we have enough data to check the header length? */
	if (readLen <= SizeOfXLogShortPHD)
		goto err;

	Assert(readLen >= reqLen);

	hdr = (XLogPageHeader) state->readBuf;

	/* still not enough */
	if (readLen < XLogPageHeaderSize(hdr))
	{
		readLen = state->routine.page_read(state, pageptr, XLogPageHeaderSize(hdr),
										   state->currRecPtr,
										   state->readBuf);
		if (readLen == XLREAD_WOULDBLOCK)
			return XLREAD_WOULDBLOCK;
		else if (readLen < 0)
			goto err;
	}

	/*
	 * Now that we know we have the full header, validate it.
	 */
	if (!XLogReaderValidatePageHeader(state, pageptr, (char *) hdr))
		goto err;

	/* update read state information */
	state->seg.ws_segno = targetSegNo;
	state->segoff = targetPageOff;
	state->readLen = readLen;

	return readLen;

err:
	XLogReaderInvalReadState(state);

	return XLREAD_FAIL;
}

/*
 * Invalidate the xlogreader's read state to force a re-read.
 */
/*
 * 中文注释：
 * 使页缓存失效：把 seg.ws_segno、segoff、readLen 清零，强制下一次
 * ReadPageInternal() 重新读取并重新校验页头。
 *
 * 注意它不关闭当前打开的段文件（ws_file 保持不变），也不改变 timeline；
 * 只是让“readBuf 中缓存的是哪一页”这一信息失效。用于读取/校验失败后，
 * 因为调用方可能切换到其他 WAL 来源（归档、流复制、不同 timeline），
 * 不能再信任之前的缓存。
 *
 * 调用场景：ReadPageInternal() 的错误路径、XLogDecodeNextRecord() 的 err
 * 路径、XLogFindNextRecord() 的失败路径。无返回值、无 I/O、无锁。
 */
static void
XLogReaderInvalReadState(XLogReaderState *state)
{
	state->seg.ws_segno = 0;
	state->segoff = 0;
	state->readLen = 0;
}

/*
 * Validate an XLOG record header.
 *
 * This is just a convenience subroutine to avoid duplicated code in
 * XLogReadRecord.  It's not intended for use from anywhere else.
 */
/*
 * 中文注释：
 * 校验一条 WAL record 的固定头部是否可信，是“在相信 xl_tot_len 之前”必须
 * 通过的第一道检查。只检查头部字段，不校验 CRC，也不检查 record 体。
 *
 * 检查项：
 *   1. xl_tot_len >= SizeOfXLogRecord：header 本身至少完整；
 *   2. xl_tot_len <= XLogRecordMaxSize：防止恶意/垃圾长度导致超大分配；
 *   3. RmgrIdIsValid(xl_rmid)：resource manager ID 必须已注册；
 *   4. prev-link：
 *      - randAccess=true（XLogBeginRead 指定位置）时无法精确比对，只要求
 *        xl_prev < RecPtr，保证指针方向合理；
 *      - 顺序读取时要求 xl_prev 精确等于 PrevRecPtr（上一条 record 的
 *        起点），这可识别“撕裂的 WAL 页”或“回收段中看似合法的旧 record”。
 *
 * 参数：RecPtr 是当前 record 的起始 LSN；PrevRecPtr 是上一条 record 的起始
 * LSN（随机访问时可能为 InvalidXLogRecPtr）；record 指向已读入内存的
 * header；randAccess 表示是否随机定位。
 *
 * 返回值：全部通过返回 true；否则调用 report_invalid_record() 写入错误并
 * 返回 false，由调用方转成 XLREAD_FAIL。
 */
static bool
ValidXLogRecordHeader(XLogReaderState *state, XLogRecPtr RecPtr,
					  XLogRecPtr PrevRecPtr, XLogRecord *record,
					  bool randAccess)
{
	if (record->xl_tot_len < SizeOfXLogRecord)
	{
		report_invalid_record(state,
							  "invalid record length at %X/%08X: expected at least %u, got %u",
							  LSN_FORMAT_ARGS(RecPtr),
							  (uint32) SizeOfXLogRecord, record->xl_tot_len);
		return false;
	}

	if (record->xl_tot_len > XLogRecordMaxSize)
	{
		report_invalid_record(state,
							  "invalid record length at %X/%08X: expected at most %u, got %u",
							  LSN_FORMAT_ARGS(RecPtr),
							  XLogRecordMaxSize, record->xl_tot_len);
		return false;
	}
	if (!RmgrIdIsValid(record->xl_rmid))
	{
		report_invalid_record(state,
							  "invalid resource manager ID %u at %X/%08X",
							  record->xl_rmid, LSN_FORMAT_ARGS(RecPtr));
		return false;
	}
	if (randAccess)
	{
		/*
		 * We can't exactly verify the prev-link, but surely it should be less
		 * than the record's own address.
		 */
		if (!(record->xl_prev < RecPtr))
		{
			report_invalid_record(state,
								  "record with incorrect prev-link %X/%08X at %X/%08X",
								  LSN_FORMAT_ARGS(record->xl_prev),
								  LSN_FORMAT_ARGS(RecPtr));
			return false;
		}
	}
	else
	{
		/*
		 * Record's prev-link should exactly match our previous location. This
		 * check guards against torn WAL pages where a stale but valid-looking
		 * WAL record starts on a sector boundary.
		 */
		if (record->xl_prev != PrevRecPtr)
		{
			report_invalid_record(state,
								  "record with incorrect prev-link %X/%08X at %X/%08X",
								  LSN_FORMAT_ARGS(record->xl_prev),
								  LSN_FORMAT_ARGS(RecPtr));
			return false;
		}
	}

	return true;
}


/*
 * CRC-check an XLOG record.  We do not believe the contents of an XLOG
 * record (other than to the minimal extent of computing the amount of
 * data to read in) until we've checked the CRCs.
 *
 * We assume all of the record (that is, xl_tot_len bytes) has been read
 * into memory at *record.  Also, ValidXLogRecordHeader() has accepted the
 * record's header, which means in particular that xl_tot_len is at least
 * SizeOfXLogRecord.
 */
/*
 * 中文注释：
 * 对已经完整读入内存的一条 WAL record 做 CRC32C 校验，确认 record 内容没有
 * 损坏或被撕裂。
 *
 * 校验范围：从 SizeOfXLogRecord 开始的 record 体（xl_tot_len 减去 header
 * 大小），最后再覆盖 header 中 xl_crc 之前的字段。分两次计算是为了跳过
 * xl_crc 本身，与写入端 XLogRecordAssemble() 的计算顺序保持一致。
 *
 * 前置条件：
 *   - record 指向的缓冲区至少包含 xl_tot_len 字节；
 *   - ValidXLogRecordHeader() 已通过，因此 xl_tot_len 位于合法范围，不会
 *     读越界或计算溢出。
 *
 * 参数：state 用于写错误消息；record 是完整 record；recptr 仅用于错误文本。
 * 返回值：CRC 匹配返回 true；否则 report_invalid_record() 记录
 * "incorrect resource manager data checksum" 并返回 false。
 *
 * 设计思想：WAL 页头有 magic/pageaddr 校验，record 头有 prev-link 校验，
 * 但只有 CRC 能发现任意字节损坏，因此在把 record 交给 redo/解码之前必须完成
 * 本检查。除错误缓冲区外无副作用，无锁。
 */
static bool
ValidXLogRecord(XLogReaderState *state, XLogRecord *record, XLogRecPtr recptr)
{
	pg_crc32c	crc;

	Assert(record->xl_tot_len >= SizeOfXLogRecord);

	/* Calculate the CRC */
	INIT_CRC32C(crc);
	COMP_CRC32C(crc, ((char *) record) + SizeOfXLogRecord, record->xl_tot_len - SizeOfXLogRecord);
	/* include the record header last */
	COMP_CRC32C(crc, (char *) record, offsetof(XLogRecord, xl_crc));
	FIN_CRC32C(crc);

	if (!EQ_CRC32C(record->xl_crc, crc))
	{
		report_invalid_record(state,
							  "incorrect resource manager data checksum in record at %X/%08X",
							  LSN_FORMAT_ARGS(recptr));
		return false;
	}

	return true;
}

/*
 * Validate a page header.
 *
 * Check if 'phdr' is valid as the header of the XLog page at position
 * 'recptr'.
 */
/*
 * 中文注释：
 * 校验 recptr 处页面的 XLogPageHeader（phdr 指向已读入的页数据），确保它是
 * 当前集群、当前 segment 大小/页大小、期望 timeline 上的有效 WAL 页。
 *
 * 检查项：
 *   1. xlp_magic == XLOG_PAGE_MAGIC，否则不是 WAL 页；
 *   2. xlp_info 不含未知标志（~XLP_ALL_FLAGS）；
 *   3. segment 的第一页必须带长页头（XLP_LONG_HEADER），并校验 xlp_sysid
 *      （若 state->system_identifier 非 0）、xlp_seg_size、xlp_xlog_blcksz；
 *   4. xlp_pageaddr 必须等于 recptr，可识别“旧段已被回收但尚未覆盖”的情况；
 *   5. timeline 单调性：只有读取位置比 latestPagePtr 更靠后时才比较 xlp_tli
 *      与 latestPageTLI，防止正常重读旧页时误报；子 timeline 的 TLI 一定
 *      大于父 timeline，因此看到 TLI 回退说明 WAL 序列不一致。
 *
 * 成功后更新 latestPagePtr/latestPageTLI，作为后续页 timeline 检查的基准。
 *
 * 参数：state->seg.ws_tli 用于拼错误信息中的文件名；recptr 必须页对齐；
 * phdr 指向至少一个完整页头（长页头时更多）的缓冲区。
 * 返回值：合法返回 true；否则调用 report_invalid_record() 并返回 false。
 *
 * 调用场景：ReadPageInternal() 每次实际读页后都必须调用；外部（如恢复代码）
 * 也可直接用来验证页头。无 I/O、无锁。
 */
bool
XLogReaderValidatePageHeader(XLogReaderState *state, XLogRecPtr recptr,
							 char *phdr)
{
	XLogSegNo	segno;
	int32		offset;
	XLogPageHeader hdr = (XLogPageHeader) phdr;

	Assert((recptr % XLOG_BLCKSZ) == 0);

	XLByteToSeg(recptr, segno, state->segcxt.ws_segsize);
	offset = XLogSegmentOffset(recptr, state->segcxt.ws_segsize);

	if (hdr->xlp_magic != XLOG_PAGE_MAGIC)
	{
		char		fname[MAXFNAMELEN];

		XLogFileName(fname, state->seg.ws_tli, segno, state->segcxt.ws_segsize);

		report_invalid_record(state,
							  "invalid magic number %04X in WAL segment %s, LSN %X/%08X, offset %u",
							  hdr->xlp_magic,
							  fname,
							  LSN_FORMAT_ARGS(recptr),
							  offset);
		return false;
	}

	if ((hdr->xlp_info & ~XLP_ALL_FLAGS) != 0)
	{
		char		fname[MAXFNAMELEN];

		XLogFileName(fname, state->seg.ws_tli, segno, state->segcxt.ws_segsize);

		report_invalid_record(state,
							  "invalid info bits %04X in WAL segment %s, LSN %X/%08X, offset %u",
							  hdr->xlp_info,
							  fname,
							  LSN_FORMAT_ARGS(recptr),
							  offset);
		return false;
	}

	if (hdr->xlp_info & XLP_LONG_HEADER)
	{
		XLogLongPageHeader longhdr = (XLogLongPageHeader) hdr;

		if (state->system_identifier &&
			longhdr->xlp_sysid != state->system_identifier)
		{
			report_invalid_record(state,
								  "WAL file is from different database system: WAL file database system identifier is %" PRIu64 ", pg_control database system identifier is %" PRIu64,
								  longhdr->xlp_sysid,
								  state->system_identifier);
			return false;
		}
		else if (longhdr->xlp_seg_size != state->segcxt.ws_segsize)
		{
			report_invalid_record(state,
								  "WAL file is from different database system: incorrect segment size in page header");
			return false;
		}
		else if (longhdr->xlp_xlog_blcksz != XLOG_BLCKSZ)
		{
			report_invalid_record(state,
								  "WAL file is from different database system: incorrect XLOG_BLCKSZ in page header");
			return false;
		}
	}
	else if (offset == 0)
	{
		char		fname[MAXFNAMELEN];

		XLogFileName(fname, state->seg.ws_tli, segno, state->segcxt.ws_segsize);

		/* hmm, first page of file doesn't have a long header? */
		report_invalid_record(state,
							  "invalid info bits %04X in WAL segment %s, LSN %X/%08X, offset %u",
							  hdr->xlp_info,
							  fname,
							  LSN_FORMAT_ARGS(recptr),
							  offset);
		return false;
	}

	/*
	 * Check that the address on the page agrees with what we expected. This
	 * check typically fails when an old WAL segment is recycled, and hasn't
	 * yet been overwritten with new data yet.
	 */
	if (hdr->xlp_pageaddr != recptr)
	{
		char		fname[MAXFNAMELEN];

		XLogFileName(fname, state->seg.ws_tli, segno, state->segcxt.ws_segsize);

		report_invalid_record(state,
							  "unexpected pageaddr %X/%08X in WAL segment %s, LSN %X/%08X, offset %u",
							  LSN_FORMAT_ARGS(hdr->xlp_pageaddr),
							  fname,
							  LSN_FORMAT_ARGS(recptr),
							  offset);
		return false;
	}

	/*
	 * Since child timelines are always assigned a TLI greater than their
	 * immediate parent's TLI, we should never see TLI go backwards across
	 * successive pages of a consistent WAL sequence.
	 *
	 * Sometimes we re-read a segment that's already been (partially) read. So
	 * we only verify TLIs for pages that are later than the last remembered
	 * LSN.
	 */
	if (recptr > state->latestPagePtr)
	{
		if (hdr->xlp_tli < state->latestPageTLI)
		{
			char		fname[MAXFNAMELEN];

			XLogFileName(fname, state->seg.ws_tli, segno, state->segcxt.ws_segsize);

			report_invalid_record(state,
								  "out-of-sequence timeline ID %u (after %u) in WAL segment %s, LSN %X/%08X, offset %u",
								  hdr->xlp_tli,
								  state->latestPageTLI,
								  fname,
								  LSN_FORMAT_ARGS(recptr),
								  offset);
			return false;
		}
	}
	state->latestPagePtr = recptr;
	state->latestPageTLI = hdr->xlp_tli;

	return true;
}

/*
 * Forget about an error produced by XLogReaderValidatePageHeader().
 */
/*
 * 中文注释：
 * 清除 XLogReaderValidatePageHeader()/读取过程中记录的错误状态：把
 * errormsg_buf 置空并复位 errormsg_deferred，使 reader 可以继续使用。
 *
 * 调用场景：xlogrecovery.c 在尝试读取某个 timeline/段失败后，可能需要忽略
 * 该页头错误、换一个来源或 timeline 重试；此时必须清掉延迟错误，否则
 * XLogReadAhead() 会因 errormsg_deferred 直接返回 NULL，reader 无法前进。
 *
 * 注意：本函数只清错误文本和标志，不会重置读位置、页缓存或已解码队列；
 * 需要重新定位时应调用 XLogBeginRead()。无 I/O、无锁。
 */
void
XLogReaderResetError(XLogReaderState *state)
{
	state->errormsg_buf[0] = '\0';
	state->errormsg_deferred = false;
}

/*
 * Find the first record with an lsn >= RecPtr.
 *
 * This is different from XLogBeginRead() in that RecPtr doesn't need to point
 * to a valid record boundary.  Useful for checking whether RecPtr is a valid
 * xlog address for reading, and to find the first valid address after some
 * address when dumping records for debugging purposes.
 *
 * This positions the reader, like XLogBeginRead(), so that the next call to
 * XLogReadRecord() will read the next valid record.
 *
 * On failure, InvalidXLogRecPtr is returned, and *errormsg is set to a string
 * with details of the failure.
 *
 * When set, *errormsg points to an internal buffer that's valid until the next
 * call to XLogReadRecord.
 */
/*
 * 中文注释：
 * 从 RecPtr 开始向后查找第一条起始 LSN >= RecPtr 的有效 record，并把 reader
 * 定位到该 record，返回其 LSN；找不到或出错返回 InvalidXLogRecPtr，并通过
 * *errormsg 返回错误说明。
 *
 * 与 XLogBeginRead() 的区别：RecPtr 不必落在 record 边界上，可以指向页中间、
 * contrecord 中间甚至无效位置；本函数会跳过页头和 continuation data，找到
 * 后续第一个合法 record。适用于 pg_waldump 从任意 LSN 开始输出、恢复时校正
 * 起点，以及检查某个 LSN 是否可读。
 *
 * 流程：
 *   1. 强制关闭非阻塞模式（state->nonblocking = false），保证
 *      ReadPageInternal() 可以等待数据；
 *   2. 循环按页读取：若页头带 XLP_FIRST_IS_CONTRECORD，则根据 xlp_rem_len
 *      判断 contrecord 是否在本页结束——结束则跳到续接数据之后，否则跳到
 *      下一页继续；没有 contrecord 则定位到页头之后第一条 record；
 *   3. 用 XLogBeginRead() 定位，循环 XLogReadRecord() 直到
 *      ReadRecPtr >= RecPtr，再 XLogBeginRead(found) 回退到该 record 起点，
 *      保证下一次读取从找到的 record 开始。
 *
 * 错误处理：任何读取/校验失败都调用 XLogReaderInvalReadState()，并把
 * errormsg_deferred 中的消息转交给调用方；*errormsg 指向 reader 内部缓冲区，
 * 在下一次 XLogReadRecord() 前有效。
 *
 * 注意：函数内部会消费 record（改变 ReadRecPtr/EndRecPtr），但最终会重新定位；
 * 返回 InvalidXLogRecPtr 时 reader 位置不确定，调用方应重新 BeginRead。
 */
XLogRecPtr
XLogFindNextRecord(XLogReaderState *state, XLogRecPtr RecPtr, char **errormsg)
{
	XLogRecPtr	tmpRecPtr;
	XLogRecPtr	found = InvalidXLogRecPtr;
	XLogPageHeader header;

	*errormsg = NULL;

	Assert(XLogRecPtrIsValid(RecPtr));

	/* Make sure ReadPageInternal() can't return XLREAD_WOULDBLOCK. */
	state->nonblocking = false;

	/*
	 * skip over potential continuation data, keeping in mind that it may span
	 * multiple pages
	 */
	tmpRecPtr = RecPtr;
	while (true)
	{
		XLogRecPtr	targetPagePtr;
		int			targetRecOff;
		uint32		pageHeaderSize;
		int			readLen;

		/*
		 * Compute targetRecOff. It should typically be equal or greater than
		 * short page-header since a valid record can't start anywhere before
		 * that, except when caller has explicitly specified the offset that
		 * falls somewhere there or when we are skipping multi-page
		 * continuation record. It doesn't matter though because
		 * ReadPageInternal() is prepared to handle that and will read at
		 * least short page-header worth of data
		 */
		targetRecOff = tmpRecPtr % XLOG_BLCKSZ;

		/* scroll back to page boundary */
		targetPagePtr = tmpRecPtr - targetRecOff;

		/* Read the page containing the record */
		readLen = ReadPageInternal(state, targetPagePtr, targetRecOff);
		if (readLen < 0)
			goto err;

		header = (XLogPageHeader) state->readBuf;

		pageHeaderSize = XLogPageHeaderSize(header);

		/* make sure we have enough data for the page header */
		readLen = ReadPageInternal(state, targetPagePtr, pageHeaderSize);
		if (readLen < 0)
			goto err;

		/* skip over potential continuation data */
		if (header->xlp_info & XLP_FIRST_IS_CONTRECORD)
		{
			/*
			 * If the length of the remaining continuation data is more than
			 * what can fit in this page, the continuation record crosses over
			 * this page. Read the next page and try again. xlp_rem_len in the
			 * next page header will contain the remaining length of the
			 * continuation data
			 *
			 * Note that record headers are MAXALIGN'ed
			 */
			if (MAXALIGN(header->xlp_rem_len) >= (XLOG_BLCKSZ - pageHeaderSize))
				tmpRecPtr = targetPagePtr + XLOG_BLCKSZ;
			else
			{
				/*
				 * The previous continuation record ends in this page. Set
				 * tmpRecPtr to point to the first valid record
				 */
				tmpRecPtr = targetPagePtr + pageHeaderSize
					+ MAXALIGN(header->xlp_rem_len);
				break;
			}
		}
		else
		{
			tmpRecPtr = targetPagePtr + pageHeaderSize;
			break;
		}
	}

	/*
	 * we know now that tmpRecPtr is an address pointing to a valid XLogRecord
	 * because either we're at the first record after the beginning of a page
	 * or we just jumped over the remaining data of a continuation.
	 */
	XLogBeginRead(state, tmpRecPtr);
	while (XLogReadRecord(state, errormsg) != NULL)
	{
		/* past the record we've found, break out */
		if (RecPtr <= state->ReadRecPtr)
		{
			/* Rewind the reader to the beginning of the last record. */
			found = state->ReadRecPtr;
			XLogBeginRead(state, found);
			return found;
		}
	}

err:
	XLogReaderInvalReadState(state);

	/*
	 * We may have reported errors due to invalid WAL header, propagate the
	 * error message to the caller.
	 */
	if (state->errormsg_deferred)
	{
		if (state->errormsg_buf[0] != '\0')
			*errormsg = state->errormsg_buf;
		state->errormsg_deferred = false;
	}

	return InvalidXLogRecPtr;
}

/*
 * Helper function to ease writing of XLogReaderRoutine->page_read callbacks.
 * If this function is used, caller must supply a segment_open callback in
 * 'state', as that is used here.
 *
 * Read 'count' bytes into 'buf', starting at location 'startptr', from WAL
 * fetched from timeline 'tli'.
 *
 * Returns true if succeeded, false if an error occurs, in which case
 * 'errinfo' receives error details.
 */
/*
 * 中文注释：
 * 通用的 WAL 读取辅助函数，供 XLogReaderRoutine->page_read 回调使用：从
 * startptr 开始读取 count 字节到 buf，数据来自 timeline tli，允许跨 segment
 * 边界。它把“按段打开文件 + pg_pread + 段切换”这些重复逻辑集中在这里，
 * backend（xlogutils.c 的 XLogPageRead）和 frontend（pg_waldump/pg_rewind）
 * 都可复用。
 *
 * 参数：
 *   state：reader，提供 segcxt（段大小/目录）和 routine 的 segment_open/
 *     segment_close 回调；
 *   buf/startptr/count：目标缓冲区、起始 LSN、字节数；
 *   tli：期望读取的 timeline；segment_open 可以通过 tli_p 返回实际打开的
 *     timeline（例如归档恢复时回退到父 timeline）；
 *   errinfo：失败时填写的 WALReadError，包含 errno、请求/实际读取字节数、
 *     段内偏移和段信息。
 *
 * 返回值：全部读完返回 true；任意一次 pg_pread 返回 <= 0 时填 errinfo 并
 * 返回 false。函数本身不报错，由调用方决定 FATAL/重试/切换来源。
 *
 * 流程：循环直到 nbytes 为 0：
 *   - 计算当前段内偏移；若当前没有打开文件、LSN 已跨段或 timeline 变化，
 *     关闭旧段并调用 segment_open 打开新段；
 *   - 按段边界截断本次读取长度，执行 pg_pread；
 *   - 成功后推进 recptr/nbytes/p；短读也会继续循环，直到读完或出错。
 *
 * 并发/副作用：操作 state->seg（ws_file/ws_segno/ws_tli），可能进行阻塞 I/O；
 * backend 下会统计 WAL I/O 计时和 WAIT_EVENT_WAL_READ。同一个 reader 不能被
 * 并发使用。调用方必须提供 segment_open 和 segment_close 回调。
 */
bool
WALRead(XLogReaderState *state,
		char *buf, XLogRecPtr startptr, Size count, TimeLineID tli,
		WALReadError *errinfo)
{
	char	   *p;
	XLogRecPtr	recptr;
	Size		nbytes;
#ifndef FRONTEND
	instr_time	io_start;
#endif

	p = buf;
	recptr = startptr;
	nbytes = count;

	while (nbytes > 0)
	{
		uint32		startoff;
		size_t		segbytes;
		ssize_t		readbytes;

		startoff = XLogSegmentOffset(recptr, state->segcxt.ws_segsize);

		/*
		 * If the data we want is not in a segment we have open, close what we
		 * have (if anything) and open the next one, using the caller's
		 * provided segment_open callback.
		 */
		if (state->seg.ws_file < 0 ||
			!XLByteInSeg(recptr, state->seg.ws_segno, state->segcxt.ws_segsize) ||
			tli != state->seg.ws_tli)
		{
			XLogSegNo	nextSegNo;

			if (state->seg.ws_file >= 0)
				state->routine.segment_close(state);

			XLByteToSeg(recptr, nextSegNo, state->segcxt.ws_segsize);
			state->routine.segment_open(state, nextSegNo, &tli);

			/* This shouldn't happen -- indicates a bug in segment_open */
			Assert(state->seg.ws_file >= 0);

			/* Update the current segment info. */
			state->seg.ws_tli = tli;
			state->seg.ws_segno = nextSegNo;
		}

		/* How many bytes are within this segment? */
		if (nbytes > (state->segcxt.ws_segsize - startoff))
			segbytes = state->segcxt.ws_segsize - startoff;
		else
			segbytes = nbytes;

#ifndef FRONTEND
		/* Measure I/O timing when reading segment */
		io_start = pgstat_prepare_io_time(track_wal_io_timing);

		pgstat_report_wait_start(WAIT_EVENT_WAL_READ);
#endif

		/* Reset errno first; eases reporting non-errno-affecting errors */
		errno = 0;
		readbytes = pg_pread(state->seg.ws_file, p, segbytes, (pgoff_t) startoff);

#ifndef FRONTEND
		pgstat_report_wait_end();
#endif

		if (readbytes <= 0)
		{
			errinfo->wre_errno = errno;
			errinfo->wre_req = segbytes;
			errinfo->wre_read = readbytes;
			errinfo->wre_off = startoff;
			errinfo->wre_seg = state->seg;
			return false;
		}

#ifndef FRONTEND
		pgstat_count_io_op_time(IOOBJECT_WAL, IOCONTEXT_NORMAL, IOOP_READ,
								io_start, 1, readbytes);
#endif

		/* Update state for read */
		recptr += readbytes;
		nbytes -= readbytes;
		p += readbytes;
	}

	return true;
}

/* ----------------------------------------
 * Functions for decoding the data and block references in a record.
 * ----------------------------------------
 */

/*
 * Private function to reset the state, forgetting all decoded records, if we
 * are asked to move to a new read position.
 */
/*
 * 中文注释：
 * 私有重置函数：丢弃所有已解码但尚未消费的 record，释放其中 oversized 的
 * 记录，把环形 decode buffer 清空，并清除错误状态。
 *
 * 调用场景：XLogBeginRead() 重新定位时调用，确保不会把旧位置的 record 误当
 * 成新位置的记录；XLogFindNextRecord() 内部也会通过 XLogBeginRead() 触发。
 *
 * 注意：
 *   - 只 pfree oversized record；位于 decode_buffer 中的普通 record 不需
 *     单独释放，重置 head/tail 即可；
 *   - 不会释放 decode_buffer 本身，也不改变 readRecordBuf/readBuf；
 *   - 不关闭当前 WAL segment，不改变 seg/segno；
 *   - 调用后此前返回的 DecodedXLogRecord 指针和 block data 指针全部失效。
 *
 * 单线程、无 I/O、无锁。
 */
static void
ResetDecoder(XLogReaderState *state)
{
	DecodedXLogRecord *r;

	/* Reset the decoded record queue, freeing any oversized records. */
	while ((r = state->decode_queue_head) != NULL)
	{
		state->decode_queue_head = r->next;
		if (r->oversized)
			pfree(r);
	}
	state->decode_queue_tail = NULL;
	state->decode_queue_head = NULL;
	state->record = NULL;

	/* Reset the decode buffer to empty. */
	state->decode_buffer_tail = state->decode_buffer;
	state->decode_buffer_head = state->decode_buffer;

	/* Clear error state. */
	state->errormsg_buf[0] = '\0';
	state->errormsg_deferred = false;
}

/*
 * Compute the maximum possible amount of padding that could be required to
 * decode a record, given xl_tot_len from the record's header.  This is the
 * amount of output buffer space that we need to decode a record, though we
 * might not finish up using it all.
 *
 * This computation is pessimistic and assumes the maximum possible number of
 * blocks, due to lack of better information.
 */
/*
 * 中文注释：
 * 计算解码一条 xl_tot_len 字节的 record 所需的保守内存上界，供
 * XLogReadRecordAlloc() 预留空间。
 *
 * 组成（全部按最坏情况估算）：
 *   - DecodedXLogRecord 固定部分（到柔性数组 blocks[0] 之前）；
 *   - 最多 XLR_MAX_BLOCK_ID + 1 个 DecodedBkpBlock；
 *   - record 原始数据 xl_tot_len（main data 加所有 block data/image）；
 *   - main_data 前、每个 block data 前以及末尾可能插入的
 *     MAXIMUM_ALIGNOF - 1 字节对齐填充。
 *
 * 该估算是悲观的：实际解码后的 decoded->size 通常更小，但保证
 * DecodeXLogRecord() 绝不会写越界。xl_tot_len 必须已经过合法性检查
 * （<= XLogRecordMaxSize），否则返回值可能接近 SIZE_MAX。
 *
 * 纯计算，无副作用；被 backend 和 frontend 共用。
 */
size_t
DecodeXLogRecordRequiredSpace(size_t xl_tot_len)
{
	size_t		size = 0;

	/* Account for the fixed size part of the decoded record struct. */
	size += offsetof(DecodedXLogRecord, blocks[0]);
	/* Account for the flexible blocks array of maximum possible size. */
	size += sizeof(DecodedBkpBlock) * (XLR_MAX_BLOCK_ID + 1);
	/* Account for all the raw main and block data. */
	size += xl_tot_len;
	/* We might insert padding before main_data. */
	size += (MAXIMUM_ALIGNOF - 1);
	/* We might insert padding before each block's data. */
	size += (MAXIMUM_ALIGNOF - 1) * (XLR_MAX_BLOCK_ID + 1);
	/* We might insert padding at the end. */
	size += (MAXIMUM_ALIGNOF - 1);

	return size;
}

/*
 * Decode a record.  "decoded" must point to a MAXALIGNed memory area that has
 * space for at least DecodeXLogRecordRequiredSpace(record) bytes.  On
 * success, decoded->size contains the actual space occupied by the decoded
 * record, which may turn out to be less.
 *
 * Only decoded->oversized member must be initialized already, and will not be
 * modified.  Other members will be initialized as required.
 *
 * On error, a human-readable error message is returned in *errormsg, and
 * the return value is false.
 */
/*
 * 中文注释：
 * 把一条已通过头部/CRC 校验的 WAL record 解码成 DecodedXLogRecord：
 * 解析可变头部（main data header、origin、toplevel xid、block header），
 * 并把所有 payload 拷贝到 decoded 指向的连续内存中，供 redo、逻辑解码、
 * pg_waldump 通过 XLogRecGetXXX() 访问。
 *
 * 参数：
 *   state：用于写错误消息和 LSN 诊断；
 *   decoded：调用方预留的、MAXALIGN 对齐的缓冲区，至少
 *     DecodeXLogRecordRequiredSpace(record->xl_tot_len) 字节；其 oversized
 *     字段必须已初始化，函数不会修改它；
 *   record：完整 record（含 header）；
 *   lsn：record 起始 LSN，写入 decoded->lsn；
 *   errormsg：失败时指向 state->errormsg_buf。
 *
 * 解码流程：
 *   1. 复制固定头到 decoded->header，初始化 lsn/next/origin/toplevel_xid/
 *      main_data/max_block_id 等字段；
 *   2. 从 header 之后开始解析片段头：XLR_BLOCK_ID_DATA_SHORT/LONG 表示
 *      main data（按约定总是最后）、XLR_BLOCK_ID_ORIGIN、
 *      XLR_BLOCK_ID_TOPLEVEL_XID，或 0..XLR_MAX_BLOCK_ID 的 block header
 *      （fork flags、data_len、full-page image 元数据、relfilenode、
 *      block number）；
 *   3. 大量交叉校验：HAS_DATA 与 data_len、HAS_IMAGE 与 bimg_len/hole、
 *      压缩标志与 BLCKSZ、block_id 必须递增、SAME_REL 必须有前一个
 *      relation 等；任何不一致都报错并返回 false；
 *   4. 校验所有片段长度之和 remaining == datatotal，防止声明长度与实际
 *      数据不符；
 *   5. 把 block image、block data、main data 依次拷贝到 blocks 数组之后，
 *      每段 data 前做 MAXALIGN 对齐（image 不需要），最后把总占用
 *      MAXALIGN 后写入 decoded->size。
 *
 * 内存布局：DecodedXLogRecord 固定字段 + blocks[0..max_block_id] +
 * 对齐后的 payload；main_data 和 blocks[i].data/bkp_image 都指向这块内存，
 * 因此 decoded 必须整体保持有效，不能单独 pfree 这些内部指针。
 *
 * COPY_HEADER_FIELD 宏在每次读取前检查剩余字节，防止越界读；长度不一致
 * 走 shortdata_err，统一报告 "record with invalid length"。
 *
 * 注意：本函数不校验 CRC（由 ValidXLogRecord() 负责），也不验证 record
 * header 的 prev-link/rmid（由 ValidXLogRecordHeader() 负责）；调用方必须
 * 按顺序先做这些检查。无 I/O、无锁。
 */
bool
DecodeXLogRecord(XLogReaderState *state,
				 DecodedXLogRecord *decoded,
				 XLogRecord *record,
				 XLogRecPtr lsn,
				 char **errormsg)
{
	/*
	 * read next _size bytes from record buffer, but check for overrun first.
	 */
/*
 * 中文注释：
 * 从 record 缓冲区读取一个头部字段到 _dst：读取前先检查 remaining 是否足够，
 * 不足则跳转到 shortdata_err 统一报 "record with invalid length"。宏按使用处
 * 展开，ptr/remaining 是 DecodeXLogRecord() 的局部变量，因此只能在该函数内
 * 使用；它同时推进 ptr 并减少 remaining，避免调用方手写重复的边界检查。
 */
#define COPY_HEADER_FIELD(_dst, _size)			\
	do {										\
		if (remaining < _size)					\
			goto shortdata_err;					\
		memcpy(_dst, ptr, _size);				\
		ptr += _size;							\
		remaining -= _size;						\
	} while(0)

	char	   *ptr;
	char	   *out;
	uint32		remaining;
	uint32		datatotal;
	RelFileLocator *rlocator = NULL;
	uint8		block_id;

	decoded->header = *record;
	decoded->lsn = lsn;
	decoded->next = NULL;
	decoded->record_origin = InvalidReplOriginId;
	decoded->toplevel_xid = InvalidTransactionId;
	decoded->main_data = NULL;
	decoded->main_data_len = 0;
	decoded->max_block_id = -1;
	ptr = (char *) record;
	ptr += SizeOfXLogRecord;
	remaining = record->xl_tot_len - SizeOfXLogRecord;

	/* Decode the headers */
	datatotal = 0;
	while (remaining > datatotal)
	{
		COPY_HEADER_FIELD(&block_id, sizeof(uint8));

		if (block_id == XLR_BLOCK_ID_DATA_SHORT)
		{
			/* XLogRecordDataHeaderShort */
			uint8		main_data_len;

			COPY_HEADER_FIELD(&main_data_len, sizeof(uint8));

			decoded->main_data_len = main_data_len;
			datatotal += main_data_len;
			break;				/* by convention, the main data fragment is
								 * always last */
		}
		else if (block_id == XLR_BLOCK_ID_DATA_LONG)
		{
			/* XLogRecordDataHeaderLong */
			uint32		main_data_len;

			COPY_HEADER_FIELD(&main_data_len, sizeof(uint32));
			decoded->main_data_len = main_data_len;
			datatotal += main_data_len;
			break;				/* by convention, the main data fragment is
								 * always last */
		}
		else if (block_id == XLR_BLOCK_ID_ORIGIN)
		{
			COPY_HEADER_FIELD(&decoded->record_origin, sizeof(ReplOriginId));
		}
		else if (block_id == XLR_BLOCK_ID_TOPLEVEL_XID)
		{
			COPY_HEADER_FIELD(&decoded->toplevel_xid, sizeof(TransactionId));
		}
		else if (block_id <= XLR_MAX_BLOCK_ID)
		{
			/* XLogRecordBlockHeader */
			DecodedBkpBlock *blk;
			uint8		fork_flags;

			/* mark any intervening block IDs as not in use */
			for (int i = decoded->max_block_id + 1; i < block_id; ++i)
				decoded->blocks[i].in_use = false;

			if (block_id <= decoded->max_block_id)
			{
				report_invalid_record(state,
									  "out-of-order block_id %u at %X/%08X",
									  block_id,
									  LSN_FORMAT_ARGS(state->ReadRecPtr));
				goto err;
			}
			decoded->max_block_id = block_id;

			blk = &decoded->blocks[block_id];
			blk->in_use = true;
			blk->apply_image = false;

			COPY_HEADER_FIELD(&fork_flags, sizeof(uint8));
			blk->forknum = fork_flags & BKPBLOCK_FORK_MASK;
			blk->flags = fork_flags;
			blk->has_image = ((fork_flags & BKPBLOCK_HAS_IMAGE) != 0);
			blk->has_data = ((fork_flags & BKPBLOCK_HAS_DATA) != 0);

			blk->prefetch_buffer = InvalidBuffer;

			COPY_HEADER_FIELD(&blk->data_len, sizeof(uint16));
			/* cross-check that the HAS_DATA flag is set iff data_length > 0 */
			if (blk->has_data && blk->data_len == 0)
			{
				report_invalid_record(state,
									  "BKPBLOCK_HAS_DATA set, but no data included at %X/%08X",
									  LSN_FORMAT_ARGS(state->ReadRecPtr));
				goto err;
			}
			if (!blk->has_data && blk->data_len != 0)
			{
				report_invalid_record(state,
									  "BKPBLOCK_HAS_DATA not set, but data length is %d at %X/%08X",
									  blk->data_len,
									  LSN_FORMAT_ARGS(state->ReadRecPtr));
				goto err;
			}
			datatotal += blk->data_len;

			if (blk->has_image)
			{
				COPY_HEADER_FIELD(&blk->bimg_len, sizeof(uint16));
				COPY_HEADER_FIELD(&blk->hole_offset, sizeof(uint16));
				COPY_HEADER_FIELD(&blk->bimg_info, sizeof(uint8));

				blk->apply_image = ((blk->bimg_info & BKPIMAGE_APPLY) != 0);

				if (BKPIMAGE_COMPRESSED(blk->bimg_info))
				{
					if (blk->bimg_info & BKPIMAGE_HAS_HOLE)
						COPY_HEADER_FIELD(&blk->hole_length, sizeof(uint16));
					else
						blk->hole_length = 0;
				}
				else
					blk->hole_length = BLCKSZ - blk->bimg_len;
				datatotal += blk->bimg_len;

				/*
				 * cross-check that hole_offset > 0, hole_length > 0 and
				 * bimg_len < BLCKSZ if the HAS_HOLE flag is set.
				 */
				if ((blk->bimg_info & BKPIMAGE_HAS_HOLE) &&
					(blk->hole_offset == 0 ||
					 blk->hole_length == 0 ||
					 blk->bimg_len == BLCKSZ))
				{
					report_invalid_record(state,
										  "BKPIMAGE_HAS_HOLE set, but hole offset %d length %d block image length %d at %X/%08X",
										  blk->hole_offset,
										  blk->hole_length,
										  blk->bimg_len,
										  LSN_FORMAT_ARGS(state->ReadRecPtr));
					goto err;
				}

				/*
				 * cross-check that hole_offset == 0 and hole_length == 0 if
				 * the HAS_HOLE flag is not set.
				 */
				if (!(blk->bimg_info & BKPIMAGE_HAS_HOLE) &&
					(blk->hole_offset != 0 || blk->hole_length != 0))
				{
					report_invalid_record(state,
										  "BKPIMAGE_HAS_HOLE not set, but hole offset %d length %d at %X/%08X",
										  blk->hole_offset,
										  blk->hole_length,
										  LSN_FORMAT_ARGS(state->ReadRecPtr));
					goto err;
				}

				/*
				 * Cross-check that bimg_len < BLCKSZ if it is compressed.
				 */
				if (BKPIMAGE_COMPRESSED(blk->bimg_info) &&
					blk->bimg_len == BLCKSZ)
				{
					report_invalid_record(state,
										  "BKPIMAGE_COMPRESSED set, but block image length %d at %X/%08X",
										  blk->bimg_len,
										  LSN_FORMAT_ARGS(state->ReadRecPtr));
					goto err;
				}

				/*
				 * cross-check that bimg_len = BLCKSZ if neither HAS_HOLE is
				 * set nor COMPRESSED().
				 */
				if (!(blk->bimg_info & BKPIMAGE_HAS_HOLE) &&
					!BKPIMAGE_COMPRESSED(blk->bimg_info) &&
					blk->bimg_len != BLCKSZ)
				{
					report_invalid_record(state,
										  "neither BKPIMAGE_HAS_HOLE nor BKPIMAGE_COMPRESSED set, but block image length is %d at %X/%08X",
										  blk->data_len,
										  LSN_FORMAT_ARGS(state->ReadRecPtr));
					goto err;
				}
			}
			if (!(fork_flags & BKPBLOCK_SAME_REL))
			{
				COPY_HEADER_FIELD(&blk->rlocator, sizeof(RelFileLocator));
				rlocator = &blk->rlocator;
			}
			else
			{
				if (rlocator == NULL)
				{
					report_invalid_record(state,
										  "BKPBLOCK_SAME_REL set but no previous rel at %X/%08X",
										  LSN_FORMAT_ARGS(state->ReadRecPtr));
					goto err;
				}

				blk->rlocator = *rlocator;
			}
			COPY_HEADER_FIELD(&blk->blkno, sizeof(BlockNumber));
		}
		else
		{
			report_invalid_record(state,
								  "invalid block_id %u at %X/%08X",
								  block_id, LSN_FORMAT_ARGS(state->ReadRecPtr));
			goto err;
		}
	}

	if (remaining != datatotal)
		goto shortdata_err;

	/*
	 * Ok, we've parsed the fragment headers, and verified that the total
	 * length of the payload in the fragments is equal to the amount of data
	 * left.  Copy the data of each fragment to contiguous space after the
	 * blocks array, inserting alignment padding before the data fragments so
	 * they can be cast to struct pointers by REDO routines.
	 */
	out = ((char *) decoded) +
		offsetof(DecodedXLogRecord, blocks) +
		sizeof(decoded->blocks[0]) * (decoded->max_block_id + 1);

	/* block data first */
	for (block_id = 0; block_id <= decoded->max_block_id; block_id++)
	{
		DecodedBkpBlock *blk = &decoded->blocks[block_id];

		if (!blk->in_use)
			continue;

		Assert(blk->has_image || !blk->apply_image);

		if (blk->has_image)
		{
			/* no need to align image */
			blk->bkp_image = out;
			memcpy(out, ptr, blk->bimg_len);
			ptr += blk->bimg_len;
			out += blk->bimg_len;
		}
		if (blk->has_data)
		{
			out = (char *) MAXALIGN(out);
			blk->data = out;
			memcpy(blk->data, ptr, blk->data_len);
			ptr += blk->data_len;
			out += blk->data_len;
		}
	}

	/* and finally, the main data */
	if (decoded->main_data_len > 0)
	{
		out = (char *) MAXALIGN(out);
		decoded->main_data = out;
		memcpy(decoded->main_data, ptr, decoded->main_data_len);
		ptr += decoded->main_data_len;
		out += decoded->main_data_len;
	}

	/* Report the actual size we used. */
	decoded->size = MAXALIGN(out - (char *) decoded);
	Assert(DecodeXLogRecordRequiredSpace(record->xl_tot_len) >=
		   decoded->size);

	return true;

shortdata_err:
	report_invalid_record(state,
						  "record with invalid length at %X/%08X",
						  LSN_FORMAT_ARGS(state->ReadRecPtr));
err:
	*errormsg = state->errormsg_buf;

	return false;
}

/*
 * Returns information about the block that a block reference refers to.
 *
 * This is like XLogRecGetBlockTagExtended, except that the block reference
 * must exist and there's no access to prefetch_buffer.
 */
/*
 * 中文注释：
 * 返回指定 block reference 的 RelFileLocator、fork number 和 block number。
 * 这是给 redo 例程使用的便捷接口：调用者确信该 block_id 存在，缺失视为
 * 编程错误。
 *
 * 内部调用 XLogRecGetBlockTagExtended()；若 block ref 不存在：
 *   - backend 用 elog(ERROR) 抛错；
 *   - frontend 用 pg_fatal() 终止（frontend 没有 elog）。
 *
 * 参数均为输出参数，调用方需提供非 NULL 指针。纯读取，不修改 record；
 * 返回的信息指向 decoded record 内部，record 释放后失效。
 */
void
XLogRecGetBlockTag(XLogReaderState *record, uint8 block_id,
				   RelFileLocator *rlocator, ForkNumber *forknum,
				   BlockNumber *blknum)
{
	if (!XLogRecGetBlockTagExtended(record, block_id, rlocator, forknum,
									blknum, NULL))
	{
#ifndef FRONTEND
		elog(ERROR, "could not locate backup block with ID %d in WAL record",
			 block_id);
#else
		pg_fatal("could not locate backup block with ID %d in WAL record",
				 block_id);
#endif
	}
}

/*
 * Returns information about the block that a block reference refers to,
 * optionally including the buffer that the block may already be in.
 *
 * If the WAL record contains a block reference with the given ID, *rlocator,
 * *forknum, *blknum and *prefetch_buffer are filled in (if not NULL), and
 * returns true.  Otherwise returns false.
 */
/*
 * 中文注释：
 * 查询某个 block reference 的完整定位信息，并可选返回“该块可能已经在哪个
 * prefetch buffer 中”的提示。
 *
 * 参数 block_id 是 WAL 记录内的逻辑块号；输出参数 rlocator/forknum/blknum 和
 * prefetch_buffer 都可以为 NULL，调用者只取自己关心的字段。函数先通过
 * XLogRecHasBlockRef 判断该 block_id 是否真的在记录中：不存在时返回 false，而不是
 * 报错；存在时把解码阶段保存的字段复制出来并返回 true。prefetch_buffer 只是恢复
 * 预取器提供的非 pin 提示，调用者不能把它当作稳定引用，仍需正常读取/校验 buffer。
 */
bool
XLogRecGetBlockTagExtended(XLogReaderState *record, uint8 block_id,
						   RelFileLocator *rlocator, ForkNumber *forknum,
						   BlockNumber *blknum,
						   Buffer *prefetch_buffer)
{
	DecodedBkpBlock *bkpb;

	if (!XLogRecHasBlockRef(record, block_id))
		return false;

	bkpb = &record->record->blocks[block_id];
	if (rlocator)
		*rlocator = bkpb->rlocator;
	if (forknum)
		*forknum = bkpb->forknum;
	if (blknum)
		*blknum = bkpb->blkno;
	if (prefetch_buffer)
		*prefetch_buffer = bkpb->prefetch_buffer;
	return true;
}

/*
 * Returns the data associated with a block reference, or NULL if there is
 * no data (e.g. because a full-page image was taken instead). The returned
 * pointer points to a MAXALIGNed buffer.
 */
/*
 * 中文注释：
 * 取得某个 block reference 关联的 block data（rmgr 私有的 redo 数据）。
 *
 * 如果 block_id 越界、该块未使用，或者记录中因为采用了 full-page image 而没有
 * 保存 block data，则返回 NULL；此时若 len 非 NULL，会把它设为 0。成功时返回指向
 * 解码记录内部 MAXALIGN 缓冲区的指针，并把长度写入 *len。返回的指针只在当前
 * XLogReaderState/记录生命周期内有效，调用者不应释放或长期保存。该接口是 redo
 * 例程读取 XLogRegisterBufData 写入内容的标准方式。
 */
char *
XLogRecGetBlockData(XLogReaderState *record, uint8 block_id, Size *len)
{
	DecodedBkpBlock *bkpb;

	if (block_id > record->record->max_block_id ||
		!record->record->blocks[block_id].in_use)
		return NULL;

	bkpb = &record->record->blocks[block_id];

	if (!bkpb->has_data)
	{
		if (len)
			*len = 0;
		return NULL;
	}
	else
	{
		if (len)
			*len = bkpb->data_len;
		return bkpb->data;
	}
}

/*
 * Restore a full-page image from a backup block attached to an XLOG record.
 *
 * Returns true if a full-page image is restored, and false on failure with
 * an error to be consumed by the caller.
 */
/*
 * 中文注释：
 * 从 WAL 记录的某个 block reference 中还原 full-page image（FPI）到调用者提供的
 * page 缓冲区。
 *
 * 恢复流程：
 *   1. 校验 block_id 存在且该块确实带有镜像，否则通过 report_invalid_record 报错
 *      并返回 false（由调用者决定是否升级为 PANIC/ERROR）；
 *   2. 若镜像使用 PGLZ/LZ4/ZSTD 压缩，先解压到临时对齐缓冲区；如果当前构建不支持
 *      该算法或解压失败，同样报告损坏记录；
 *   3. 根据 hole_offset/hole_length 把镜像复制回页：没有空洞时整页复制；有空洞时
 *      复制前半段、把空洞清零（恢复端必须得到确定的页内容）、再复制后半段。
 * 该函数只负责生成页内容，不负责把页写入磁盘或设置页 LSN；redo 代码通常先调用
 * XLogReadBufferForRedo 取得 buffer，再在需要时调用本函数恢复镜像。
 */
bool
RestoreBlockImage(XLogReaderState *record, uint8 block_id, char *page)
{
	DecodedBkpBlock *bkpb;
	char	   *ptr;
	PGAlignedBlock tmp;

	if (block_id > record->record->max_block_id ||
		!record->record->blocks[block_id].in_use)
	{
		report_invalid_record(record,
							  "could not restore image at %X/%08X with invalid block %d specified",
							  LSN_FORMAT_ARGS(record->ReadRecPtr),
							  block_id);
		return false;
	}
	if (!record->record->blocks[block_id].has_image)
	{
		report_invalid_record(record, "could not restore image at %X/%08X with invalid state, block %d",
							  LSN_FORMAT_ARGS(record->ReadRecPtr),
							  block_id);
		return false;
	}

	bkpb = &record->record->blocks[block_id];
	ptr = bkpb->bkp_image;

	if (BKPIMAGE_COMPRESSED(bkpb->bimg_info))
	{
		/* If a backup block image is compressed, decompress it */
		bool		decomp_success = true;

		if ((bkpb->bimg_info & BKPIMAGE_COMPRESS_PGLZ) != 0)
		{
			if (pglz_decompress(ptr, bkpb->bimg_len, tmp.data,
								BLCKSZ - bkpb->hole_length, true) < 0)
				decomp_success = false;
		}
		else if ((bkpb->bimg_info & BKPIMAGE_COMPRESS_LZ4) != 0)
		{
#ifdef USE_LZ4
			if (LZ4_decompress_safe(ptr, tmp.data,
									bkpb->bimg_len, BLCKSZ - bkpb->hole_length) <= 0)
				decomp_success = false;
#else
			report_invalid_record(record, "could not restore image at %X/%08X compressed with %s not supported by build, block %d",
								  LSN_FORMAT_ARGS(record->ReadRecPtr),
								  "LZ4",
								  block_id);
			return false;
#endif
		}
		else if ((bkpb->bimg_info & BKPIMAGE_COMPRESS_ZSTD) != 0)
		{
#ifdef USE_ZSTD
			size_t		decomp_result = ZSTD_decompress(tmp.data,
														BLCKSZ - bkpb->hole_length,
														ptr, bkpb->bimg_len);

			if (ZSTD_isError(decomp_result))
				decomp_success = false;
#else
			report_invalid_record(record, "could not restore image at %X/%08X compressed with %s not supported by build, block %d",
								  LSN_FORMAT_ARGS(record->ReadRecPtr),
								  "zstd",
								  block_id);
			return false;
#endif
		}
		else
		{
			report_invalid_record(record, "could not restore image at %X/%08X compressed with unknown method, block %d",
								  LSN_FORMAT_ARGS(record->ReadRecPtr),
								  block_id);
			return false;
		}

		if (!decomp_success)
		{
			report_invalid_record(record, "could not decompress image at %X/%08X, block %d",
								  LSN_FORMAT_ARGS(record->ReadRecPtr),
								  block_id);
			return false;
		}

		ptr = tmp.data;
	}

	/* generate page, taking into account hole if necessary */
	if (bkpb->hole_length == 0)
	{
		memcpy(page, ptr, BLCKSZ);
	}
	else
	{
		memcpy(page, ptr, bkpb->hole_offset);
		/* must zero-fill the hole */
		MemSet(page + bkpb->hole_offset, 0, bkpb->hole_length);
		memcpy(page + (bkpb->hole_offset + bkpb->hole_length),
			   ptr + bkpb->hole_offset,
			   BLCKSZ - (bkpb->hole_offset + bkpb->hole_length));
	}

	return true;
}

#ifndef FRONTEND

/*
 * Extract the FullTransactionId from a WAL record.
 */
/*
 * 中文注释：
 * 从 WAL 记录头中的 32 位 xl_xid 还原出 64 位 FullTransactionId。
 *
 * WAL 只保存 32 位 TransactionId，且可能跨越 XID 回绕。恢复时用当前共享的
 * nextXid 作为参照，通过 FullTransactionIdFromAllowableAt() 选择与参照值最接近的
 * epoch，从而得到唯一的 FullTransactionId。该转换依赖恢复状态中的 nextXid，因此
 * 只能在 startup 进程或单用户模式下调用（函数用 Assert 检查）；普通后端不能用它
 * 解释任意历史 WAL 记录，否则可能得到错误的 epoch。
 */
FullTransactionId
XLogRecGetFullXid(XLogReaderState *record)
{
	/*
	 * This function is only safe during replay, because it depends on the
	 * replay state.  See AdvanceNextFullTransactionIdPastXid() for more.
	 */
	Assert(AmStartupProcess() || !IsUnderPostmaster);

	return FullTransactionIdFromAllowableAt(TransamVariables->nextXid,
											XLogRecGetXid(record));
}

#endif
