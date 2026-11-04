/*-------------------------------------------------------------------------
 *
 * xlogprefetcher.c
 *		Prefetching support for recovery.
 *
 * Portions Copyright (c) 2022-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *		src/backend/access/transam/xlogprefetcher.c
 *
 * This module provides a drop-in replacement for an XLogReader that tries to
 * minimize I/O stalls by looking ahead in the WAL.  If blocks that will be
 * accessed in the near future are not already in the buffer pool, it initiates
 * I/Os that might complete before the caller eventually needs the data.  When
 * referenced blocks are found in the buffer pool already, the buffer is
 * recorded in the decoded record so that XLogReadBufferForRedo() can try to
 * avoid a second buffer mapping table lookup.
 *
 * Currently, only the main fork is considered for prefetching.  Currently,
 * prefetching is only effective on systems where PrefetchBuffer() does
 * something useful (mainly Linux).
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 恢复（recovery）期间的预取（prefetch）机制，即
 * recovery prefetch。核心问题是：WAL 重放（redo）必须按 LSN 顺序访问大量数据页，
 * 这些随机读往往无法命中 shared buffer pool，startup process 只能同步等待磁盘
 * I/O；而 WAL 通常已经提前到达并解码，因此可以“向前看”，在真正需要某个 block
 * 之前就让操作系统提前把页读入页缓存，从而把部分 I/O 延迟隐藏在重放计算之后。
 *
 * 主要组件：
 *   1. XLogPrefetcher：包装一个 XLogReaderState，在解码队列（decode queue）中向后
 *      扫描未来的 WAL record，找出其中的 block reference；对满足条件的 block 调用
 *      PrefetchSharedBuffer() 发起预取。
 *   2. XLogPrefetcherNextBlock：回调，逐个检查 record 的 block reference，决定
 *      是发起 I/O、跳过（已缓存、FPI、WILL_INIT、被过滤、重复访问），还是暂时没有
 *      更多 WAL 可读。
 *   3. LsnReadQueue：以 LSN 为完成判据的简单环形队列，用来限制“在途”（inflight）
 *      预取数量和向前看的距离。它并不跟踪真实 I/O 完成事件，而是假定：当重放进度
 *      越过某条 record 的 LSN 时，该 record 之前引用的页已经被重放代码同步读取，
 *      因此更早发起的预取要么已经完成，要么已不再有意义。
 *   4. XLogPrefetcherFilter：临时过滤器，避免在 relation/database 尚未创建、已被
 *      截断或删掉时发起预取，防止 ENOENT 以及 relfilenumber 复用时把不同“代”的
 *      block 混淆。
 *   5. XLogPrefetchStats / pg_stat_recovery_prefetch：共享内存中的原子计数器与
 *      瞬时状态，供 SQL 视图观察预取效果。
 *
 * prefetch buffer 的含义：若预取时发现目标 block 已经在 shared buffer pool 中，
 * PrefetchSharedBuffer() 会返回一个 recent_buffer（未 pin，使用前必须重新校验），
 * 本模块把它记录到 DecodedBkpBlock.prefetch_buffer；随后
 * XLogReadBufferForRedo() 可以据此直接尝试该 buffer，省掉一次 buffer mapping table
 * 查找。若真正发起了 I/O，则把 prefetch_buffer 置为 InvalidBuffer。该字段只是
 * 优化提示，不改变重放语义。
 *
 * LSN 顺序与正确性：整个预取过程严格跟随 WAL 的 LSN 递增顺序。过滤器以“创建/
 * 截断该对象的 record 的 LSN 被重放”为解除条件；LsnReadQueue 以“重放进度越过
 * 某 LSN”为 I/O 完成条件。这样无需等待 I/O、也无需额外锁，就能安全地限制并发，
 * 因为重放本身是单线程的（startup process），预取只是为未来的同步读做准备。
 *
 * 与 storage AIO 的关系：本模块发起的是内核级 read-ahead advice（Linux 上为
 * posix_fadvise(POSIX_FADV_WILLNEED)，macOS 上为 F_RDADVISE），调用链为
 * PrefetchSharedBuffer() -> smgrprefetch() -> mdprefetch() -> FilePrefetch()；
 * 它不是 PostgreSQL 通用异步 I/O（AIO）子系统提交的 AIO handle，没有完成回调，
 * 也不等待 I/O。LsnReadQueue 是对“通用 I/O 深度管理器”的简化替代（代码中保留了
 * 函数指针间接层，便于以后替换）；恢复期间实际读页仍然是同步 ReadBuffer。若启用
 * direct I/O（io_direct_flags & IO_DIRECT_DATA），内核页缓存预读没有意义，
 * PrefetchSharedBuffer() 不会发起 I/O，本模块会安静地跳过。
 *
 * 可调参数：
 *   - recovery_prefetch（off/on/try，默认 try）：是否启用；try 仅在平台支持
 *     read-ahead advice（USE_PREFETCH）时生效。
 *   - maintenance_io_concurrency：允许的在途预取 I/O 上限，为 0 时禁用预取。
 *   - wal_decode_buffer_size：间接限制能向前解码多少 WAL，从而限制预取距离。
 *   - XLOGPREFETCHER_DISTANCE_MULTIPLIER：允许向前看的 block reference 数量是
 *     I/O 并发度的倍数。
 *   - XLOGPREFETCHER_SEQ_WINDOW_SIZE：重复访问去重窗口。
 *   - XLOGPREFETCHER_STATS_DISTANCE：统计信息刷新间隔（按 WAL 字节数）。
 *   - XLOGPREFETCHER_DEBUG_LEVEL：编译期调试日志开关，默认关闭。
 *
 * 设计思想：
 *   - 预取是“尽力而为”的优化，绝不参与正确性判断；即使全部预取失败，重放仍然
 *     通过普通同步读完成。
 *   - 只预取 main fork；不预取带 full page image 的 block（重放会直接恢复镜像，
 *     不会读页），也不预取 BKPBLOCK_WILL_INIT 的 block（页会被零初始化）。
 *   - 用过滤器而不是“先试后错”处理尚未创建/已截断的对象，避免无谓的系统调用和
 *     relfilenumber 复用导致的错误页。
 *   - 用小幅去重窗口避免同一 block 被连续重复预取，减少系统调用。
 *   - 所有计数器用 atomic 存放于共享内存，其他 backend 可无锁读取
 *     pg_stat_recovery_prefetch；动态距离字段允许轻微不一致，它们只用于观测。
 *
 * 调用方：xlogrecovery.c 中的 ReadRecord()/PerformWalRecovery() 等通过
 * XLogPrefetcherAllocate() 创建预取器，用 XLogPrefetcherBeginRead() 重置读取起点，
 * 再用 XLogPrefetcherReadRecord() 代替 XLogReadRecord() 获取记录。
 */

#include "postgres.h"

#include "access/xlogprefetcher.h"
#include "access/xlogreader.h"
#include "catalog/pg_control.h"
#include "catalog/storage_xlog.h"
#include "commands/dbcommands_xlog.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "port/atomics.h"
#include "storage/bufmgr.h"
#include "storage/fd.h"
#include "storage/shmem.h"
#include "storage/smgr.h"
#include "storage/subsystems.h"
#include "utils/fmgrprotos.h"
#include "utils/guc_hooks.h"
#include "utils/hsearch.h"
#include "utils/timestamp.h"
#include "utils/tuplestore.h"

/*
 * Every time we process this much WAL, we'll update the values in
 * pg_stat_recovery_prefetch.
 */
/*
 * 中文注释：
 * 统计信息刷新间隔，单位为 WAL 字节数，取一个 BLCKSZ（通常 8kB）。
 * XLogPrefetcherComputeStats() 会把下一次刷新阈值设为
 * “当前 ReadRecPtr + 本常量”；XLogPrefetcherReadRecord() 每返回一条 record 都
 * 检查是否越过该阈值。因此 pg_stat_recovery_prefetch 中的 wal_distance、
 * block_distance、io_depth 通常每隔约 BLCKSZ WAL 更新一次，而不是实时值；若
 * 相邻 record 的 LSN 跨度较大，实际间隔还会更大。用 WAL 字节数而非 record
 * 条数或时间做间隔，是为了让开销与 WAL 处理量成比例，并且在重放速度差异很大时
 * 仍保持稳定的采样频率。
 */
#define XLOGPREFETCHER_STATS_DISTANCE BLCKSZ

/*
 * To detect repeated access to the same block and skip useless extra system
 * calls, we remember a small window of recently prefetched blocks.
 */
/*
 * 中文注释：
 * 最近预取 block 的去重窗口大小。预取器用两个定长数组分别保存最近
 * XLOGPREFETCHER_SEQ_WINDOW_SIZE 个 RelFileLocator 和 BlockNumber，形成环形
 * 窗口；若待预取的 block 与窗口中任一项完全相同，就认为它刚被处理过并跳过，
 * 避免同一页在相邻 record 中被反复 smgropen()/smgrexists()/PrefetchSharedBuffer()。
 * 窗口故意取得很小（4）：它只针对“短时间重复访问”这种最常见情形；窗口越小，
 * 内存和比较开销越低。窗口被覆盖导致的漏判只会让某个 block 多预取一次，不影响
 * 正确性。
 */
#define XLOGPREFETCHER_SEQ_WINDOW_SIZE 4

/*
 * When maintenance_io_concurrency is not saturated, we're prepared to look
 * ahead up to N times that number of block references.
 */
/*
 * 中文注释：
 * 预取距离相对 I/O 并发度的倍数。当预取启用时：
 *   max_inflight = maintenance_io_concurrency
 *   max_distance = max_inflight * XLOGPREFETCHER_DISTANCE_MULTIPLIER
 * LsnReadQueue 的环形缓冲区容量为 max_distance + 1，因此“已检查的 block
 * reference”总数（无论是否真正发起了 I/O）最多约为 I/O 并发度的 4 倍。这样在
 * 并发度尚未被在途 I/O 占满时，仍能继续向前扫描 WAL、把更多候选 block 放入
 * 队列；一旦队列满，XLogPrefetcherNextBlock() 返回 LRQ_NEXT_AGAIN，预取自然
 * 暂停，等待重放推进后由 lrq_complete_lsn() 释放空间。把“已检查但未发 I/O”的
 * 条目也计入距离，可以限制解码队列和 CPU 扫描的开销。
 */
#define XLOGPREFETCHER_DISTANCE_MULTIPLIER 4

/* Define to log internal debugging messages. */
/* #define XLOGPREFETCHER_DEBUG_LEVEL LOG */
/*
 * 中文注释：
 * 编译期调试日志开关。默认被注释掉；若改成例如 LOG 或 DEBUG1 并重新编译，
 * 本文件内所有 #ifdef XLOGPREFETCHER_DEBUG_LEVEL 块都会用 elog() 输出预取决策
 * 细节，包括：因可能的 TLI 切换而暂停 readahead、因 file-copy 建库/建 relation/
 * 截断/relation 不存在/relation 太小而添加过滤器、以及某个 block 被过滤的原因。
 * 它不是 GUC，运行期不能修改；只在开发、排查预取行为或性能问题时临时启用。
 */

/* GUCs */
/*
 * 中文注释：
 * recovery_prefetch GUC 的存储位置，声明于 access/xlogprefetcher.h（因此其他
 * 模块可以直接读取）。取值为 xlogprefetcher.h 中 RecoveryPrefetchValue 枚举：
 *   - RECOVERY_PREFETCH_OFF：完全关闭；
 *   - RECOVERY_PREFETCH_ON：强制开启，平台不支持 read-ahead advice 时由
 *     check_recovery_prefetch() 拒绝；
 *   - RECOVERY_PREFETCH_TRY（默认）：平台支持时才开启。
 * 该变量由 GUC 机制在启动时及运行期（startup process 中）通过
 * assign_recovery_prefetch() 更新；其他进程中的值不影响 startup process。
 */
int			recovery_prefetch = RECOVERY_PREFETCH_TRY;

#ifdef USE_PREFETCH
#define RecoveryPrefetchEnabled() \
		(recovery_prefetch != RECOVERY_PREFETCH_OFF && \
		 maintenance_io_concurrency > 0)
#else
#define RecoveryPrefetchEnabled() false
#endif
/*
 * 中文注释：
 * 统一的“预取当前是否生效”判断宏，避免各处重复组合两个条件。
 * 语义：
 *   - 编译时未定义 USE_PREFETCH（平台没有实现 read-ahead advice 的手段）时，
 *     恒为 false；此时即使 recovery_prefetch=on 也会被 GUC check hook 拒绝，
 *     而 try 则安静地退化为不预取；
 *   - 定义了 USE_PREFETCH 时，要求 recovery_prefetch 不是 off，并且
 *     maintenance_io_concurrency > 0（0 表示不允许任何在途 I/O，等价于关闭）。
 * 注意：它只是策略判断，不检查 io_direct_flags。direct I/O 下本宏仍可能为 true，
 * 但 PrefetchSharedBuffer() 不会真正发起内核预读，XLogPrefetcherNextBlock() 会
 * 跳过这些 block（见该函数中 io_direct_flags 相关的分支）。
 */

/*
 * 中文注释：
 * GUC 重配置计数器，进程内（非共享内存）的单调递增整数。以下事件会调用
 * XLogPrefetchReconfigure() 把它加一：
 *   - recovery_prefetch 的 assign hook 在 startup process 中执行时；
 *   - maintenance_io_concurrency 的 assign hook 在 startup process 中执行时；
 *   - 恢复过程中发生 timeline switch、需要重置预取器时（xlogrecovery.c）。
 * 每个 XLogPrefetcher 在 Allocate 时把自身 reconfigure_count 设为
 * “当前值 - 1”，使首次 XLogPrefetcherReadRecord() 必定重建 LsnReadQueue；
 * 之后每次 ReadRecord 都比较两者，不相等就丢弃旧队列并按新的并发度重建。
 * XLogPrefetcherBeginRead() 也会自减 prefetcher->reconfigure_count，用来丢弃
 * 旧的在途 I/O 记账。由于只有 startup process（或单进程模式）访问，无需加锁。
 */
static int	XLogPrefetchReconfigureCount = 0;

/*
 * Enum used to report whether an IO should be started.
 */
/*
 * 中文注释：
 * LsnReadQueue 的回调返回值，用来告诉队列管理逻辑本次“取一个 LSN”的结果：
 *   - LRQ_NEXT_NO_IO：已经检查了下一个 block reference，但决定不发起 I/O
 *     （已在 buffer pool、FPI、WILL_INIT、被过滤、重复访问、只读非 main fork
 *     等）。队列仍然占用一个“已检查”条目（completed++），以便把向前扫描的
 *     距离计入 max_distance；等重放越过该 LSN 后条目被回收。
 *   - LRQ_NEXT_IO：已经（至少请求内核）发起一次预取 I/O。队列条目标记为
 *     io=true，计入 inflight，直到重放越过对应 LSN 才释放并发额度。
 *   - LRQ_NEXT_AGAIN：当前没有更多可读 WAL，或预取被有意暂停；本次不占用队列
 *     条目，lrq_prefetch() 立即返回，等以后有进展时再重试。
 * 这三种状态把“是否真正产生 I/O”和“是否消耗预取距离”区分开：NO_IO 消耗距离但
 * 不占 I/O 并发度，IO 两者都占，AGAIN 两者都不占。
 */
typedef enum
{
	LRQ_NEXT_NO_IO,
	LRQ_NEXT_IO,
	LRQ_NEXT_AGAIN,
} LsnReadQueueNextStatus;

/*
 * Type of callback that can decide which block to prefetch next.  For now
 * there is only one.
 */
/*
 * 中文注释：
 * LsnReadQueue 的“取下一条候选”回调类型。参数：
 *   - lrq_private：调用方私有的不透明值；本文件传入 XLogPrefetcher *；
 *   - lsn：输出参数，回调必须写入“当该 LSN 被重放后，本次 I/O 可视为完成”的
 *     LSN（对于 NO_IO，通常写当前 record 的 LSN；关闭预取的特殊路径写
 *     InvalidXLogRecPtr）。
 * 返回值见 LsnReadQueueNextStatus。目前唯一的实现是 XLogPrefetcherNextBlock()。
 * 这里使用函数指针而不是直接调用，是为了把 LsnReadQueue 设计成可替换的通用
 * I/O 深度管理器：将来若改用真正的异步 I/O 完成事件，只需替换回调/队列实现，
 * 不必改动 XLogPrefetcher 的其余逻辑。
 */
typedef LsnReadQueueNextStatus (*LsnReadQueueNextFun) (uintptr_t lrq_private,
													   XLogRecPtr *lsn);

/*
 * A simple circular queue of LSNs, using to control the number of
 * (potentially) inflight IOs.  This stands in for a later more general IO
 * control mechanism, which is why it has the apparently unnecessary
 * indirection through a function pointer.
 */
/*
 * 中文注释：
 * 以 LSN 为完成判据的环形队列，用于限制“可能仍在途”的预取 I/O 数量以及向前
 * 扫描的距离。它不是真正的 I/O 完成队列：不持有 AIO handle，也不等待事件；
 * 只是把每次预取决策与一个 LSN 关联起来，等重放进度越过该 LSN 时，就认为对应
 * I/O 已经完成（或已无意义），从而释放额度。
 *
 * 字段：
 *   - next / lrq_private：候选生成回调及其私有上下文（这里指向 XLogPrefetcher）；
 *   - max_inflight：允许同时“在途”的 I/O 数，来自 maintenance_io_concurrency；
 *   - inflight：当前 io=true 且尚未被重放越过的条目数；
 *   - completed：当前 io=false（已检查但未发 I/O）且尚未被重放越过的条目数；
 *   - head：下一个写入位置；tail：最老的未完成条目位置；
 *   - size：环形缓冲区槽位数，等于 max_distance + 1；
 *   - queue[]：每个槽位记录“是否发起了 I/O”和完成判据 LSN。
 *
 * 不变量与设计要点：
 *   - 始终保留一个空槽（size = max_distance + 1），用 head == tail 表示空、
 *     (head + 1) % size == tail 表示满，因此最多容纳 size - 1 = max_distance 个
 *     有效条目；lrq_prefetch() 中的 Assert 正是检查这一点。
 *   - 有效条目数 = inflight + completed；lrq_prefetch() 仅在
 *     inflight < max_inflight 且 inflight + completed < size - 1 时继续取候选，
 *     从而同时限制 I/O 并发度和扫描距离。
 *   - lrq_complete_lsn() 用严格小于比较 queue[tail].lsn < replaying_lsn：
 *     当 replaying_lsn 是“已重放 record 的下一条 LSN”时，所有 lsn 小于它的
 *     条目都对应已经重放完的 record。
 *   - 队列及其中所有状态只由 startup process 单线程访问，因此无需加锁；它不是
 *     共享内存结构，而是 palloc 在启动进程的当前内存上下文中。
 */
typedef struct LsnReadQueue
{
	LsnReadQueueNextFun next;
	uintptr_t	lrq_private;
	uint32		max_inflight;
	uint32		inflight;
	uint32		completed;
	uint32		head;
	uint32		tail;
	uint32		size;
	struct
	{
		bool		io;
		XLogRecPtr	lsn;
	}			queue[FLEXIBLE_ARRAY_MEMBER];
} LsnReadQueue;

/*
 * A prefetcher.  This is a mechanism that wraps an XLogReader, prefetching
 * blocks that will be soon be referenced, to try to avoid IO stalls.
 */
/*
 * 中文注释：
 * 预取器对象。它“包装”一个由调用方拥有的 XLogReaderState：对上层提供与
 * XLogReadRecord() 类似的接口（XLogPrefetcherReadRecord），但在返回当前 record
 * 之前，会利用 reader 的解码队列向前查看后续 record，并尽力提前发起数据页预取。
 *
 * 字段说明：
 *   - reader：底层 WAL reader，不归本对象所有，由 xlogrecovery.c 分配和释放；
 *   - record：当前正在向后扫描的“未来” DecodedXLogRecord；NULL 表示需要解码
 *     下一条。它指向 reader 解码队列中的内存，在对应 record 被重放并释放前保持
 *     有效；预取器绝不释放它，只借用；
 *   - next_block_id：record 内下一个待检查的 block 下标。当 I/O 并发度或扫描
 *     距离用尽时，本对象保留该游标，下一次回调从断点继续，而不是重新扫描；
 *   - next_stats_shm_lsn：下一次刷新 pg_stat_recovery_prefetch 的 WAL LSN 阈值；
 *   - filter_table / filter_queue：私有 hash 表与按“解除过滤 LSN”排序的双向链表，
 *     记录暂时不应预取的 relation/database；详见 XLogPrefetcherFilter；
 *   - recent_rlocator / recent_block / recent_idx：固定大小的重复访问去重窗口，
 *     保存最近处理过的 block 标识；
 *   - no_readahead_until：在此 LSN 被重放之前暂停继续解码/预取。用于可能的
 *     timeline switch，以及非阻塞读取暂时无数据/遇到延迟错误时避免忙等；
 *   - streaming_read：LsnReadQueue，延迟分配并在 GUC 变化或 BeginRead 后重建；
 *   - begin_ptr：最近一次 XLogPrefetcherBeginRead() 指定的起点，用来禁止在
 *     第一条 record 被消费前进行 readahead（保证“只读一条 record”的语义）；
 *   - reconfigure_count：创建/重建时记录的 XLogPrefetchReconfigureCount 快照，
 *     两者不等说明需要重建 streaming_read。
 *
 * 并发与生命周期：整个对象、filter 表和 LsnReadQueue 都只由 startup process
 * （或单进程恢复时的唯一进程）访问，没有锁；它不持有 buffer pin，也不拥有
 * reader。XLogPrefetcherAllocate()/Free() 成对使用。
 */
struct XLogPrefetcher
{
	/* WAL reader and current reading state. */
	XLogReaderState *reader;
	DecodedXLogRecord *record;
	int			next_block_id;

	/* When to publish stats. */
	XLogRecPtr	next_stats_shm_lsn;

	/* Book-keeping to avoid accessing blocks that don't exist yet. */
	HTAB	   *filter_table;
	dlist_head	filter_queue;

	/* Book-keeping to avoid repeat prefetches. */
	RelFileLocator recent_rlocator[XLOGPREFETCHER_SEQ_WINDOW_SIZE];
	BlockNumber recent_block[XLOGPREFETCHER_SEQ_WINDOW_SIZE];
	int			recent_idx;

	/* Book-keeping to disable prefetching temporarily. */
	XLogRecPtr	no_readahead_until;

	/* IO depth manager. */
	LsnReadQueue *streaming_read;

	XLogRecPtr	begin_ptr;

	int			reconfigure_count;
};

/*
 * A temporary filter used to track block ranges that haven't been created
 * yet, whole relations that haven't been created yet, and whole relations
 * that (we assume) have already been dropped, or will be created by bulk WAL
 * operators.
 */
/*
 * 中文注释：
 * 临时过滤器条目，用来表示“在某个 LSN 被重放之前，不要预取该对象（或其某个
 * block 区间）”。它解决三类问题：
 *   1. relation/database 尚未创建：例如 crash recovery 中文件会在未来由 WAL
 *      创建，或 file-copy 建库没有任何逐 relation 的 WAL；提前预取只会得到
 *      ENOENT，甚至在 relfilenumber 复用时读到上一“代”的旧页；
 *   2. relation 尚未扩展到目标 block：block 号超出当前 smgrnblocks()，未来才会
 *      由 WAL 扩展；
 *   3. relation 即将被截断：截断范围内的 block 即将消失，不应预取。
 *
 * 字段：
 *   - rlocator：被过滤对象的定位符。relation 级过滤使用完整的
 *     (spcOid, dbOid, relNumber)；database 级过滤使用
 *     (InvalidOid, dbOid, InvalidRelFileNumber)，见 XLogPrefetcherIsFiltered()；
 *   - filter_until_replayed：解除过滤的判据 LSN。创建/扩展/截断该对象的 WAL
 *     record 被重放后（严格地说，重放进度越过该 LSN 后），过滤即可删除；
 *   - filter_from_block：只过滤大于等于该 block 号的块。0 表示整个 relation；
 *     同一 relation 多次被过滤时取所有下界的最小值，宁可多跳过一些预取，也不
 *     维护复杂的离散区间；
 *   - link：filter_queue 的链表节点。队列按 filter_until_replayed 从旧到新排列，
 *     最新添加/延长的过滤在队头，因此队尾总是最早到期的过滤，便于 O(1) 清理。
 *
 * 生命周期：由 XLogPrefetcherAddFilter() 在 hash 表中创建或更新，由
 * XLogPrefetcherCompleteFilters() 在重放进度足够后删除。所有访问都在
 * startup process 单线程内，无需加锁；hash 表是预取器私有的，不占共享内存。
 */
typedef struct XLogPrefetcherFilter
{
	RelFileLocator rlocator;
	XLogRecPtr	filter_until_replayed;
	BlockNumber filter_from_block;
	dlist_node	link;
} XLogPrefetcherFilter;

/*
 * Counters exposed in shared memory for pg_stat_recovery_prefetch.
 */
/*
 * 中文注释：
 * 放在共享内存中的预取统计结构，由 pg_stat_recovery_prefetch 视图读取。
 * 只有 startup process（或单进程恢复时的唯一进程）写；任意 backend 都可以读，
 * 因此计数字段使用 pg_atomic_uint64，避免 32 位平台上读到撕裂的 64 位值。
 *
 * 字段：
 *   - reset_time：上次重置统计的时间戳（TimestampTz 存在 u64 中）；
 *   - prefetch：真正发起预取 I/O 的 block 数（cache miss 且 initiated_io）；
 *   - hit：预取时发现已在 shared buffer pool 中的 block 数；这些 block 会把
 *     buffer 号记录到 prefetch_buffer 供重放复用；
 *   - skip_init：因 BKPBLOCK_WILL_INIT（页将被零初始化）而跳过的 block 数；
 *   - skip_new：因过滤器、relation 不存在或 block 超出当前文件大小而跳过的数；
 *   - skip_fpw：因附带 full page image（重放直接恢复镜像，不读页）而跳过的数；
 *   - skip_rep：因落在近期去重窗口内而跳过的重复访问数；
 *   - wal_distance：解码队列中最新与最老 record 的 LSN 差值，近似表示预取
 *     领先重放多少 WAL 字节；
 *   - block_distance：当前预取窗口内的 block reference 数（inflight + completed）；
 *   - io_depth：当前在途预取 I/O 数。
 *
 * 后三个是“动态值”，由 XLogPrefetcherComputeStats() 周期性地非原子写入；读者
 * 可能看到略微过时或彼此不完全一致的组合，这对监控来说可以接受。计数字段由
 * XLogPrefetchIncrement() 以“读-加一-写”的方式更新；因为只有一个写者，不会丢
 * 更新，但若与 XLogPrefetchResetStats() 并发，可能短暂出现重置前后的混合值。
 */
typedef struct XLogPrefetchStats
{
	pg_atomic_uint64 reset_time;	/* Time of last reset. */
	pg_atomic_uint64 prefetch;	/* Prefetches initiated. */
	pg_atomic_uint64 hit;		/* Blocks already in cache. */
	pg_atomic_uint64 skip_init; /* Zero-inited blocks skipped. */
	pg_atomic_uint64 skip_new;	/* New/missing blocks filtered. */
	pg_atomic_uint64 skip_fpw;	/* FPWs skipped. */
	pg_atomic_uint64 skip_rep;	/* Repeat accesses skipped. */

	/* Dynamic values */
	int			wal_distance;	/* Number of WAL bytes ahead. */
	int			block_distance; /* Number of block references ahead. */
	int			io_depth;		/* Number of I/Os in progress. */
} XLogPrefetchStats;

/*
 * 中文注释：
 * 本文件内部函数的前置声明。之所以集中声明，是因为这些函数在定义处之前就被
 * 其他函数引用（例如 XLogPrefetcherNextBlock() 调用过滤相关函数，而过滤函数的
 * 定义在文件后半部分）。具体语义见各函数定义前的中文注释。
 */
static inline void XLogPrefetcherAddFilter(XLogPrefetcher *prefetcher,
										   RelFileLocator rlocator,
										   BlockNumber blockno,
										   XLogRecPtr lsn);
static inline bool XLogPrefetcherIsFiltered(XLogPrefetcher *prefetcher,
											RelFileLocator rlocator,
											BlockNumber blockno);
static inline void XLogPrefetcherCompleteFilters(XLogPrefetcher *prefetcher,
												 XLogRecPtr replaying_lsn);
static LsnReadQueueNextStatus XLogPrefetcherNextBlock(uintptr_t pgsr_private,
													  XLogRecPtr *lsn);

/*
 * 中文注释：
 * 指向共享内存中 XLogPrefetchStats 的全局指针。由 shmem 框架在
 * XLogPrefetchShmemRequest() 登记、在分配/挂接共享内存时回填；之后所有 backend
 * 都通过同一地址（传统共享内存映射到相同地址）访问同一份统计。正常 backend
 * 只读，startup process 写。pg_stat_recovery_prefetch 的 SQL 函数也通过它读数。
 */
static XLogPrefetchStats *SharedStats;

/*
 * 中文注释：
 * 这两个函数是 shmem 子系统的 request/init 回调，供下面的
 * XLogPrefetchShmemCallbacks 引用；定义处的注释会详细说明。
 */
static void XLogPrefetchShmemRequest(void *arg);
static void XLogPrefetchShmemInit(void *arg);

/*
 * 中文注释：
 * 注册给 shmem 子系统的回调集合。该常量通过
 * src/include/storage/subsystemlist.h 中的
 * PG_SHMEM_SUBSYSTEM(XLogPrefetchShmemCallbacks) 被纳入全局子系统列表。
 * postmaster 启动时先调用 request_fn 登记共享内存需求，分配完成后调用 init_fn
 * 初始化；EXEC_BACKEND 平台的子进程会重新执行 request_fn 以恢复指针，但没有
 * attach_fn，因此不会重复初始化计数器。
 */
const ShmemCallbacks XLogPrefetchShmemCallbacks = {
	.request_fn = XLogPrefetchShmemRequest,
	.init_fn = XLogPrefetchShmemInit,
};

/*
 * 中文注释：
 * 分配并初始化一个 LsnReadQueue 环形队列。
 *
 * 参数：
 *   - max_distance：允许同时“存在”的条目上限，即向前扫描的 block reference
 *     最大数量；调用方传入 max_inflight * XLOGPREFETCHER_DISTANCE_MULTIPLIER，
 *     关闭预取时传入 1；
 *   - max_inflight：允许同时发起的预取 I/O 数，即 maintenance_io_concurrency；
 *     必须不大于 max_distance（函数内 Assert）；
 *   - lrq_private：回调私有上下文，本文件传入 XLogPrefetcher *；
 *   - next：候选生成回调 XLogPrefetcherNextBlock。
 *
 * 返回值：在 CurrentMemoryContext 中 palloc 得到的新队列，容量字段 size 被设为
 * max_distance + 1。多出的一个槽位用于区分“空”和“满”（环形缓冲区惯用法），
 * 因此实际有效条目最多 max_distance 个。head/tail/inflight/completed 全部清零。
 *
 * 调用场景：XLogPrefetcherReadRecord() 在首次使用或检测到相关 GUC 变化时调用，
 * 用来替换旧队列；旧队列中的在途 I/O 不会被取消，只是不再被记账。
 * 并发/副作用：只在 startup process 单线程中调用，无锁；分配失败会 ereport(ERROR)。
 */
static inline LsnReadQueue *
lrq_alloc(uint32 max_distance,
		  uint32 max_inflight,
		  uintptr_t lrq_private,
		  LsnReadQueueNextFun next)
{
	LsnReadQueue *lrq;
	uint32		size;

	Assert(max_distance >= max_inflight);

	size = max_distance + 1;	/* full ring buffer has a gap */
	lrq = palloc(offsetof(LsnReadQueue, queue) + sizeof(lrq->queue[0]) * size);
	lrq->lrq_private = lrq_private;
	lrq->max_inflight = max_inflight;
	lrq->size = size;
	lrq->next = next;
	lrq->head = 0;
	lrq->tail = 0;
	lrq->inflight = 0;
	lrq->completed = 0;

	return lrq;
}

/*
 * 中文注释：
 * 释放 LsnReadQueue 占用的内存。只做 pfree()，不会取消或等待任何已经发给内核的
 * 预取 I/O（内核 readahead 本身也无法取消）；这些 I/O 之后即使完成，也不会再被
 * 本模块跟踪。参数 lrq 必须非 NULL；调用方（XLogPrefetcherReadRecord 在重建前、
 * XLogPrefetcherFree 在销毁时）负责保证这一点。
 * 只在 startup process 单线程中调用，无锁、无返回值。
 */
static inline void
lrq_free(LsnReadQueue *lrq)
{
	pfree(lrq);
}

/*
 * 中文注释：
 * 返回当前被记为“在途”的预取 I/O 数量，即 io=true 且尚未被重放越过的条目数。
 * 用于 pg_stat_recovery_prefetch 的 io_depth，以及 XLogPrefetcherReadRecord()
 * 中“解码队列为空时应无在途 I/O”的断言。
 * 纯读取，无副作用；只在 startup process 中调用，无锁。
 */
static inline uint32
lrq_inflight(LsnReadQueue *lrq)
{
	return lrq->inflight;
}

/*
 * 中文注释：
 * 返回当前被记为“已检查但未发起 I/O、且尚未被重放越过”的条目数（io=false）。
 * 它与 inflight 之和就是预取窗口内已经扫描过的 block reference 总数，用于
 * pg_stat_recovery_prefetch 的 block_distance，并参与 lrq_prefetch() 的
 * max_distance 限制。
 * 纯读取，无副作用；只在 startup process 中调用，无锁。
 */
static inline uint32
lrq_completed(LsnReadQueue *lrq)
{
	return lrq->completed;
}

/*
 * 中文注释：
 * 在队列容量和 I/O 并发度允许的范围内，反复调用回调取出下一个候选 block，
 * 尽可能填满预取窗口。
 *
 * 循环条件同时约束两件事：
 *   1. inflight < max_inflight：真正在途的预取 I/O 不超过
 *      maintenance_io_concurrency；
 *   2. inflight + completed < size - 1：预取窗口内的总条目数不超过
 *      max_distance（size 多留了一个空槽，用于区分空/满）。
 * 每次迭代只处理一个 block reference：
 *   - 回调返回 LRQ_NEXT_AGAIN：当前没有更多 WAL 可读或预取被暂停。直接 return，
 *     head 不前进，也不占用槽位，以后可重试；
 *   - LRQ_NEXT_IO：把该槽标记 io=true，inflight++；
 *   - LRQ_NEXT_NO_IO：标记 io=false，completed++（仍然占用窗口距离）。
 * 后两种情况下 head 前进并回绕。回调在返回前已经把完成判据 LSN 写入
 * queue[head].lsn，因此这里无需再次处理 LSN。
 *
 * 调用场景：lrq_complete_lsn() 在重放推进、释放额度后调用；以及
 * XLogPrefetcherReadRecord() 在解码队列为空时调用，以保证至少解码并排队一条
 * record（即使预取被关闭，也会用 1/1 的队列解码一条）。
 * 副作用：回调可能解码更多 WAL（XLogReadAhead），可能阻塞等待 WAL（仅当调用方
 * 判断当前没有可重放记录时），并可能向内核发起预取 I/O。只在 startup process
 * 单线程中执行，无锁。
 */
static inline void
lrq_prefetch(LsnReadQueue *lrq)
{
	/* Try to start as many IOs as we can within our limits. */
	while (lrq->inflight < lrq->max_inflight &&
		   lrq->inflight + lrq->completed < lrq->size - 1)
	{
		Assert(((lrq->head + 1) % lrq->size) != lrq->tail);
		switch (lrq->next(lrq->lrq_private, &lrq->queue[lrq->head].lsn))
		{
			case LRQ_NEXT_AGAIN:
				return;
			case LRQ_NEXT_IO:
				lrq->queue[lrq->head].io = true;
				lrq->inflight++;
				break;
			case LRQ_NEXT_NO_IO:
				lrq->queue[lrq->head].io = false;
				lrq->completed++;
				break;
		}
		lrq->head++;
		if (lrq->head == lrq->size)
			lrq->head = 0;
	}
}

/*
 * 中文注释：
 * 通知队列：重放进度已经到达 lsn（通常是 XLogReleasePreviousRecord() 返回的
 * “已重放 record 之后的下一条 LSN”），可以回收所有完成判据 LSN 严格小于它的
 * 条目。
 *
 * 参数 lsn 的双重含义：
 *   - lsn == InvalidXLogRecPtr（即 0）：表示没有上一条 record 可释放（例如首次
 *     调用），此时通常不会回收任何条目；
 *   - 正常 LSN：所有 queue[tail].lsn < lsn 的条目对应的 record 都已经重放完，
 *     因此其数据页已经被重放代码同步读取；早期预取的 I/O 要么已完成，要么即使
 *     尚未完成也不再需要等待。于是：
 *       * io=true 的条目：inflight--；
 *       * io=false 的条目：completed--。
 *     然后 tail 前进并回绕，直到遇到第一个 lsn 不小于参数 lsn 的条目。
 * 这里使用严格小于而不是小于等于：lsn 恰好等于某条 record 的 LSN 时，该 record
 * 可能仍是“当前”尚未释放的 record，不能提前认为它已重放。
 *
 * 回收完成后，仅当 RecoveryPrefetchEnabled() 为真才调用 lrq_prefetch() 继续
 * 预取。这样在 recovery_prefetch 被关闭或 maintenance_io_concurrency 变为 0 后，
 * 已有条目仍能正常排出，但不会发起新的 I/O。若关闭预取，ReadRecord 在队列为空时
 * 仍会直接调用 lrq_prefetch()，用 1/1 的窗口解码一条 record，保证恢复前进。
 *
 * 重要：本函数不等待、也不查询真实 I/O 是否完成，纯粹按重放进度做近似记账；这
 * 是 LsnReadQueue 能够无锁、无回调的全部原因。只在 startup process 单线程中调用。
 */
static inline void
lrq_complete_lsn(LsnReadQueue *lrq, XLogRecPtr lsn)
{
	/*
	 * We know that LSNs before 'lsn' have been replayed, so we can now assume
	 * that any IOs that were started before then have finished.
	 */
	while (lrq->tail != lrq->head &&
		   lrq->queue[lrq->tail].lsn < lsn)
	{
		if (lrq->queue[lrq->tail].io)
			lrq->inflight--;
		else
			lrq->completed--;
		lrq->tail++;
		if (lrq->tail == lrq->size)
			lrq->tail = 0;
	}
	if (RecoveryPrefetchEnabled())
		lrq_prefetch(lrq);
}

/*
 * 中文注释：
 * shmem request 回调：向共享内存框架登记一块名为 "XLogPrefetchStats"、大小为
 * sizeof(XLogPrefetchStats) 的区域，并让框架在分配/挂接后把地址写入全局指针
 * SharedStats。
 *
 * 调用场景：postmaster 启动早期，所有 request_fn 被调用完才计算总需求并创建
 * 共享内存段；此时还没有并发进程。EXEC_BACKEND 平台的子进程也会重新执行本
 * 回调以恢复 SharedStats 指针。
 * 参数 arg：框架传入的 opaque 参数，本模块未使用。
 * 副作用：只登记需求，不初始化内容；真正的计数器初始化在
 * XLogPrefetchShmemInit() 中完成。
 */
static void
XLogPrefetchShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "XLogPrefetchStats",
					   .size = sizeof(XLogPrefetchStats),
					   .ptr = (void **) &SharedStats,
		);
}

/*
 * 中文注释：
 * shmem init 回调：初始化共享统计结构中的原子计数器。
 *
 * 调用场景：postmaster 在共享内存段分配完成之后、任何子进程启动之前调用一次
 * （单进程模式同样如此），此时没有并发访问者，因此可以安全地直接初始化原子量。
 * EXEC_BACKEND 子进程只 attach，不会再次执行 init_fn。
 *
 * 初始化内容：reset_time 设为当前时间；prefetch、hit、skip_init、skip_new、
 * skip_fpw、skip_rep 全部置 0。动态字段 wal_distance、block_distance、
 * io_depth 不在这里设置，而由 XLogPrefetcherAllocate() 在每次恢复开始时清零，
 * 它们只是瞬时观测量。
 *
 * 参数 arg：框架传入的 opaque 参数，本模块未使用。
 * 副作用：写入共享内存；此后其他 backend 即可通过 pg_stat_recovery_prefetch
 * 读取（在 startup process 开始写之前，计数值为 0）。
 */
static void
XLogPrefetchShmemInit(void *arg)
{
	pg_atomic_init_u64(&SharedStats->reset_time, GetCurrentTimestamp());
	pg_atomic_init_u64(&SharedStats->prefetch, 0);
	pg_atomic_init_u64(&SharedStats->hit, 0);
	pg_atomic_init_u64(&SharedStats->skip_init, 0);
	pg_atomic_init_u64(&SharedStats->skip_new, 0);
	pg_atomic_init_u64(&SharedStats->skip_fpw, 0);
	pg_atomic_init_u64(&SharedStats->skip_rep, 0);
}

/*
 * Reset all counters to zero.
 */
/*
 * 中文注释：
 * 把 pg_stat_recovery_prefetch 的累计计数器全部清零，并把 reset_time 更新为
 * 当前时间。
 *
 * 调用场景：由 pgstatfuncs.c 中的 pg_stat_reset_shared('recovery_prefetch')
 * 等路径调用，属于任意 backend 都可触发的管理操作，不是 startup process 专属。
 * 因此这里必须使用 pg_atomic_write_u64() 写共享内存；同时 startup process 可能
 * 正在用 XLogPrefetchIncrement() 更新计数，二者并发时某一次增量可能丢失，或读者
 * 短暂看到重置前后的混合值，这是统计信息可以接受的语义。
 *
 * 副作用：只修改共享统计，不影响预取逻辑、LsnReadQueue 或恢复进度；动态字段
 * （wal_distance/block_distance/io_depth）不在本函数中重置，它们会在下次
 * XLogPrefetcherComputeStats() 时被覆盖。无返回值。
 */
void
XLogPrefetchResetStats(void)
{
	pg_atomic_write_u64(&SharedStats->reset_time, GetCurrentTimestamp());
	pg_atomic_write_u64(&SharedStats->prefetch, 0);
	pg_atomic_write_u64(&SharedStats->hit, 0);
	pg_atomic_write_u64(&SharedStats->skip_init, 0);
	pg_atomic_write_u64(&SharedStats->skip_new, 0);
	pg_atomic_write_u64(&SharedStats->skip_fpw, 0);
	pg_atomic_write_u64(&SharedStats->skip_rep, 0);
}


/*
 * Called when any GUC is changed that affects prefetching.
 */
/*
 * 中文注释：
 * 标记“预取相关配置已变化”，使当前及后续 XLogPrefetcherReadRecord() 重建
 * LsnReadQueue。实现只是把进程内计数器 XLogPrefetchReconfigureCount 加一；真正
 * 的重建发生在下一次 ReadRecord 发现 prefetcher->reconfigure_count 与之不等时。
 *
 * 调用场景：
 *   - recovery_prefetch / maintenance_io_concurrency 的 assign hook 在
 *     startup process 中执行时（assign_recovery_prefetch()、
 *     assign_maintenance_io_concurrency()）；
 *   - 恢复过程中 timeline switch 后，xlogrecovery.c 需要丢弃旧预取状态时。
 * 之所以延迟到 ReadRecord 才重建，是因为 assign hook 可能在任何时刻被调用，而
 * 队列的释放/分配应发生在确定为单线程的恢复上下文中。该函数不分配内存、不加锁，
 * 也不立即取消已有 I/O。无返回值。
 */
void
XLogPrefetchReconfigure(void)
{
	XLogPrefetchReconfigureCount++;
}

/*
 * Increment a counter in shared memory.  This is equivalent to *counter++ on a
 * plain uint64 without any memory barrier or locking, except on platforms
 * where readers can't read uint64 without possibly observing a torn value.
 */
/*
 * 中文注释：
 * 把共享内存中的 64 位统计计数器加一。
 *
 * 实现方式是 pg_atomic_read_u64() + 1 再 pg_atomic_write_u64()，不是原子的
 * read-modify-write；它之所以安全，是因为唯一的写者是 startup process（或单进程
 * 模式下的唯一进程），函数内的 Assert 正是在约束这一点。读方（任意 backend 的
 * pg_stat_recovery_prefetch）只关心单个 64 位值会不会被撕裂，pg_atomic 的读/写
 * 保证了这一点；但本函数没有内存屏障，也不保证读者能看到严格实时的值。
 *
 * 若将来出现多个写者，这种写法会丢增量；若与 XLogPrefetchResetStats() 并发，
 * 也可能出现一次增量被重置覆盖。两种情况都只影响统计精度。
 *
 * 参数 counter：指向 SharedStats 中的某个计数器（prefetch/hit/skip_*）。
 * 副作用：写共享内存，无返回值。
 */
static inline void
XLogPrefetchIncrement(pg_atomic_uint64 *counter)
{
	Assert(AmStartupProcess() || !IsUnderPostmaster);
	pg_atomic_write_u64(counter, pg_atomic_read_u64(counter) + 1);
}

/*
 * Create a prefetcher that is ready to begin prefetching blocks referenced by
 * WAL records.
 */
/*
 * 中文注释：
 * 创建预取器对象，为后续 XLogPrefetcherBeginRead()/XLogPrefetcherReadRecord()
 * 调用做好准备。
 *
 * 参数 reader：调用方已经分配好的 XLogReaderState；预取器只借用、不拥有它，
 * 因此 XLogPrefetcherFree() 不会释放 reader。
 *
 * 完成的工作：
 *   1. palloc0_object() 分配并清零 XLogPrefetcher（因此 begin_ptr、
 *      no_readahead_until、streaming_read、record 等初值都是 0/NULL）；
 *   2. 创建私有 hash 表 XLogPrefetcherFilterTable，键为 RelFileLocator，
 *      表项为 XLogPrefetcherFilter，初始 1024 项，使用 HASH_ELEM | HASH_BLOBS；
 *      这是后端本地内存，不带锁，也不进共享内存；
 *   3. 初始化 filter_queue 双向链表；
 *   4. 把共享统计中的动态字段 wal_distance/block_distance/io_depth 清零，
 *      避免显示上一次恢复的残留值；
 *   5. 把 reconfigure_count 设为“全局计数 - 1”，使第一次 ReadRecord 必定检测到
 *      不一致并分配 LsnReadQueue（延迟分配，见 XLogPrefetcherReadRecord）。
 *
 * 返回值：新预取器指针，由调用方用 XLogPrefetcherFree() 释放。
 * 调用场景：xlogrecovery.c 在分配 xlogreader 之后、开始读取 WAL 之前调用一次。
 * 并发/副作用：只在 startup process 中调用，无锁；会写共享统计的动态字段。
 * 分配失败时 palloc/hash_create 会 ereport(ERROR)。
 */
XLogPrefetcher *
XLogPrefetcherAllocate(XLogReaderState *reader)
{
	XLogPrefetcher *prefetcher;
	HASHCTL		ctl;

	prefetcher = palloc0_object(XLogPrefetcher);
	prefetcher->reader = reader;

	ctl.keysize = sizeof(RelFileLocator);
	ctl.entrysize = sizeof(XLogPrefetcherFilter);
	prefetcher->filter_table = hash_create("XLogPrefetcherFilterTable", 1024,
										   &ctl, HASH_ELEM | HASH_BLOBS);
	dlist_init(&prefetcher->filter_queue);

	SharedStats->wal_distance = 0;
	SharedStats->block_distance = 0;
	SharedStats->io_depth = 0;

	/* First usage will cause streaming_read to be allocated. */
	prefetcher->reconfigure_count = XLogPrefetchReconfigureCount - 1;

	return prefetcher;
}

/*
 * Destroy a prefetcher and release all resources.
 */
/*
 * 中文注释：
 * 销毁预取器，释放它拥有的全部资源：LsnReadQueue、过滤 hash 表以及
 * XLogPrefetcher 本身。
 *
 * 注意：
 *   - 不释放 prefetcher->reader，它由 xlogrecovery.c 单独管理；
 *   - 不释放、也不 pin/unpin 任何数据页 buffer；预取阶段记录的
 *     prefetch_buffer 只是未 pin 的提示，随解码 record 一起消失；
 *   - 不取消已经发给内核的预取 I/O（无法取消，也不会等待）；
 *   - 调用前 streaming_read 必须已经分配（正常情况下至少调用过一次
 *     XLogPrefetcherReadRecord()），因为 lrq_free() 不接受 NULL。
 * 调用场景：恢复结束或出错清理路径。只在 startup process 中执行，无锁。
 */
void
XLogPrefetcherFree(XLogPrefetcher *prefetcher)
{
	lrq_free(prefetcher->streaming_read);
	hash_destroy(prefetcher->filter_table);
	pfree(prefetcher);
}

/*
 * Provide access to the reader.
 */
/*
 * 中文注释：
 * 返回预取器内部使用的 XLogReaderState。
 *
 * 用途：调用方（xlogrecovery.c 的 ReadRecord() 等）需要用 reader 访问当前
 * record 的内容，例如 XLogRecGetData()/XLogRecGetBlockTag() 等宏；这些宏直接
 * 操作 XLogReaderState，而预取器包装后只暴露 XLogRecord *，所以需要提供这个
 * 访问器。返回的指针不转移所有权，调用方不得释放。
 * 纯读取，无副作用；只在 startup process 中使用。
 */
XLogReaderState *
XLogPrefetcherGetReader(XLogPrefetcher *prefetcher)
{
	return prefetcher->reader;
}

/*
 * Update the statistics visible in the pg_stat_recovery_prefetch view.
 */
/*
 * 中文注释：
 * 计算并发布当前这一刻的预取状态到共享内存，供 pg_stat_recovery_prefetch 读取。
 *
 * 计算内容：
 *   - wal_distance：若解码队列非空，等于 decode_queue_tail->lsn -
 *     decode_queue_head->lsn，即最新已解码 record 与最老未释放 record 之间的
 *     WAL 跨度，近似表示预取领先重放的距离；队列为空时为 0。局部变量用 int64
 *     计算，写入 int 字段时依赖 wal_decode_buffer_size 限制其范围（默认 512kB，
 *     通常远小于 INT_MAX）。
 *   - io_depth：LsnReadQueue 中 inflight 条目数；
 *   - block_distance：inflight + completed，即预取窗口内已检查的 block
 *     reference 总数（包括未真正发起 I/O 的条目）。
 * 随后把 next_stats_shm_lsn 设为 reader->ReadRecPtr + XLOGPREFETCHER_STATS_DISTANCE，
 * 作为下一次刷新的阈值。
 *
 * 调用场景：XLogPrefetcherReadRecord() 发现 record->lsn 越过阈值时；恢复即将
 * 进入等待（例如等待 WAL 到达）之前；恢复结束时做最后一次更新。
 * 并发/副作用：startup process 写共享内存中的普通 int 字段，其他 backend 可能
 * 同时读取，看到的值可能来自不同瞬间（非原子、无锁），作为监控数据可以接受。
 * 无返回值。
 */
void
XLogPrefetcherComputeStats(XLogPrefetcher *prefetcher)
{
	uint32		io_depth;
	uint32		completed;
	int64		wal_distance;


	/* How far ahead of replay are we now? */
	if (prefetcher->reader->decode_queue_tail)
	{
		wal_distance =
			prefetcher->reader->decode_queue_tail->lsn -
			prefetcher->reader->decode_queue_head->lsn;
	}
	else
	{
		wal_distance = 0;
	}

	/* How many IOs are currently in flight and completed? */
	io_depth = lrq_inflight(prefetcher->streaming_read);
	completed = lrq_completed(prefetcher->streaming_read);

	/* Update the instantaneous stats visible in pg_stat_recovery_prefetch. */
	SharedStats->io_depth = io_depth;
	SharedStats->block_distance = io_depth + completed;
	SharedStats->wal_distance = wal_distance;

	prefetcher->next_stats_shm_lsn =
		prefetcher->reader->ReadRecPtr + XLOGPREFETCHER_STATS_DISTANCE;
}

/*
 * A callback that examines the next block reference in the WAL, and possibly
 * starts an IO so that a later read will be fast.
 *
 * Returns LRQ_NEXT_AGAIN if no more WAL data is available yet.
 *
 * Returns LRQ_NEXT_IO if the next block reference is for a main fork block
 * that isn't in the buffer pool, and the kernel has been asked to start
 * reading it to make a future read system call faster. An LSN is written to
 * *lsn, and the I/O will be considered to have completed once that LSN is
 * replayed.
 *
 * Returns LRQ_NEXT_NO_IO if we examined the next block reference and found
 * that it was already in the buffer pool, or we decided for various reasons
 * not to prefetch.
 */
/*
 * 中文注释：
 * LsnReadQueue 的候选生成回调：检查 WAL 中“下一个” block reference，决定是否
 * 发起预取，并返回队列所需的状态。
 *
 * 参数：
 *   - pgsr_private：实际是 XLogPrefetcher *（通过 uintptr_t 传递以避免头文件
 *     依赖）；
 *   - lsn：输出参数。只要本次检查的是一个具体 block reference（无论是否发起
 *     I/O），就写入该 block 所属 record 的 LSN；重放越过这个 LSN 后，队列即认为
 *     对应 I/O 完成。关闭预取而仅解码 record 时写 InvalidXLogRecPtr。
 *
 * 返回：
 *   - LRQ_NEXT_IO：main fork 的 block 不在 buffer pool，且已请求内核开始读取；
 *     lsn 已写入；
 *   - LRQ_NEXT_NO_IO：检查了一个 block，但无需/不便预取（已在 buffer pool、
 *     full page image、WILL_INIT、被过滤器拦截、重复访问、非 main fork，或在
 *     direct I/O 下无法预读）；lsn 已写入；
 *   - LRQ_NEXT_AGAIN：暂时无法继续（没有更多 WAL、遇到延迟错误、因 TLI 变化
 *     暂停、或在 BeginRead 后第一条 record 尚未消费完），不占用队列槽位。
 *
 * 状态机/跨调用续扫：
 *   预取器用 prefetcher->record 指向正在扫描的“未来” record，用 next_block_id
 *   指向下个待检查的 block。队列满或 I/O 并发度用尽时，回调直接返回，下次从
 *   断点继续，不会重复检查已处理过的 block。record 扫描完后置 NULL，进入下一条。
 *
 * 主循环流程：
 *   1. 没有当前 record 时，决定是否非阻塞读取：若 reader 已有排队 record 或
 *      延迟错误（XLogReaderHasQueuedRecordOrError），说明调用方还有事可做，不能
 *      阻塞；否则可以阻塞等待 WAL。若非阻塞模式下处于暂停期（replaying_lsn
 *      尚未越过 no_readahead_until）则直接 AGAIN。调用 XLogReadAhead() 解码下一条；
 *      返回 NULL 表示无数据或错误：非阻塞模式下记下当前解码队列末尾 LSN 作为
 *      暂停点，避免在旧队列消费完之前反复空转。
 *   2. 若预取被关闭（平台不支持、GUC=off 或 io_concurrency=0），仍需解码一条
 *      record 以推动恢复（调用方在队列空时会依赖本回调），因此返回 NO_IO，
 *      lsn 置 Invalid，不分析 block。
 *   3. 对新取到的 record 初始化 record/next_block_id 游标。
 *   4. 若该 record 仍在重放点之后（replaying_lsn < record->lsn），根据 rmgr/类型
 *      添加过滤器或暂停：
 *        - RM_XLOG_ID 的 XLOG_CHECKPOINT_SHUTDOWN / XLOG_END_OF_RECOVERY 可能
 *          切换 timeline。为避免“读取 TLI”和“重放 TLI”不一致引发错误，设置
 *          no_readahead_until = record->lsn，在它被重放前不再继续向前解码；
 *        - RM_DBASE_ID 的 XLOG_DBASE_CREATE_FILE_COPY：file-copy 建库不会为每个
 *          relation 产生 WAL，故按 database 级过滤（InvalidOid/db_id/
 *          InvalidRelFileNumber），直到该 record 重放完成，避免 ENOENT 和 OID/
 *          relfilenumber 复用导致的跨代混淆；
 *        - RM_SMGR_ID 的 XLOG_SMGR_CREATE（仅 main fork）：按 relation 级过滤，
 *          从 block 0 开始，原因同上；
 *        - RM_SMGR_ID 的 XLOG_SMGR_TRUNCATE：从 blkno 起过滤，直到截断被重放，
 *          避免预取即将消失的页。
 *      已经到达/早于重放点的 record 不需要这些过滤。
 *   5. 扫描 record 的 block 引用。每个 block 消耗一个队列条目：
 *        - !in_use 的槽位跳过（不占条目）；
 *        - 先把 *lsn 设为 record->lsn，作为该条目的完成判据；
 *        - 只处理 MAIN_FORKNUM；
 *        - has_image（FPI）：重放会直接拷贝镜像，不读页，skip_fpw；
 *        - BKPBLOCK_WILL_INIT：页会被零初始化，不读，skip_init；
 *        - 过滤器命中：skip_new；
 *        - 与最近窗口重复：skip_rep，避免重复系统调用；
 *        - 否则更新去重窗口，smgropen() 打开 relation；若文件不存在，添加
 *          relation 级过滤器（从 block 0 到该 record 重放），skip_new；
 *        - 若 block 号 >= smgrnblocks()，说明 relation 尚未扩展到该块，添加
 *          从该 block 起的过滤器，skip_new；
 *        - 调用 PrefetchSharedBuffer()：
 *            * recent_buffer 有效：命中 buffer pool，记录到
 *              block->prefetch_buffer 供重放复用，hit++，NO_IO；
 *            * initiated_io：已请求内核预读，prefetch_buffer 置
 *              InvalidBuffer，prefetch++，IO；
 *            * 两者都不是：正常（非 direct I/O）情况下不应发生，因为前面已确认
 *              文件存在且足够大；若发生则 elog(ERROR)，提示缓存失效或文件被并发
 *              删除/截断。direct I/O 下这是预期情况（不会预读），于是安静地继续
 *              扫描下一个 block。
 *   6. 一条 record 的所有 block 处理完后，若解码队列末尾恰好是 begin_ptr 对应的
 *      第一条 record，则返回 AGAIN，禁止在它被消费前预读后续 record。原因是
 *      某些调用点要求“只读一条 record、不做内部 readahead”：例如
 *      PerformWalRecovery() 以 PANIC 模式读取 checkpoint 后的第一条 record，
 *      若提前读未来页可能在 XLogPageRead() 中 PANIC；FinishWalRecovery() 需要
 *      依据读完一条 record 后 reader 内部缓冲的内容决定 WAL 写入起点。
 *   7. 否则把 prefetcher->record 置 NULL，循环处理下一条已解码/可解码的 record。
 *
 * 设计思想：把“扫描/决策”和“I/O 深度控制”分离；回调每次只推进一个 block，
 * 队列据此精确限制并发和距离。所有操作都在 startup process 单线程中，无锁；
 * 回调可能触发 WAL 解码甚至阻塞等待 WAL，也可能发起内核预取 I/O。
 */
static LsnReadQueueNextStatus
XLogPrefetcherNextBlock(uintptr_t pgsr_private, XLogRecPtr *lsn)
{
	XLogPrefetcher *prefetcher = (XLogPrefetcher *) pgsr_private;
	XLogReaderState *reader = prefetcher->reader;
	XLogRecPtr	replaying_lsn = reader->ReadRecPtr;

	/*
	 * We keep track of the record and block we're up to between calls with
	 * prefetcher->record and prefetcher->next_block_id.
	 */
	for (;;)
	{
		DecodedXLogRecord *record;

		/* Try to read a new future record, if we don't already have one. */
		if (prefetcher->record == NULL)
		{
			bool		nonblocking;

			/*
			 * If there are already records or an error queued up that could
			 * be replayed, we don't want to block here.  Otherwise, it's OK
			 * to block waiting for more data: presumably the caller has
			 * nothing else to do.
			 */
			nonblocking = XLogReaderHasQueuedRecordOrError(reader);

			/* Readahead is disabled until we replay past a certain point. */
			if (nonblocking && replaying_lsn <= prefetcher->no_readahead_until)
				return LRQ_NEXT_AGAIN;

			record = XLogReadAhead(prefetcher->reader, nonblocking);
			if (record == NULL)
			{
				/*
				 * We can't read any more, due to an error or lack of data in
				 * nonblocking mode.  Don't try to read ahead again until
				 * we've replayed everything already decoded.
				 */
				if (nonblocking && prefetcher->reader->decode_queue_tail)
					prefetcher->no_readahead_until =
						prefetcher->reader->decode_queue_tail->lsn;

				return LRQ_NEXT_AGAIN;
			}

			/*
			 * If prefetching is disabled, we don't need to analyze the record
			 * or issue any prefetches.  We just need to cause one record to
			 * be decoded.
			 */
			if (!RecoveryPrefetchEnabled())
			{
				*lsn = InvalidXLogRecPtr;
				return LRQ_NEXT_NO_IO;
			}

			/* We have a new record to process. */
			prefetcher->record = record;
			prefetcher->next_block_id = 0;
		}
		else
		{
			/* Continue to process from last call, or last loop. */
			record = prefetcher->record;
		}

		/*
		 * Check for operations that require us to filter out block ranges, or
		 * pause readahead completely.
		 */
		if (replaying_lsn < record->lsn)
		{
			uint8		rmid = record->header.xl_rmid;
			uint8		record_type = record->header.xl_info & ~XLR_INFO_MASK;

			if (rmid == RM_XLOG_ID)
			{
				if (record_type == XLOG_CHECKPOINT_SHUTDOWN ||
					record_type == XLOG_END_OF_RECOVERY)
				{
					/*
					 * These records might change the TLI.  Avoid potential
					 * bugs if we were to allow "read TLI" and "replay TLI" to
					 * differ without more analysis.
					 */
					prefetcher->no_readahead_until = record->lsn;

#ifdef XLOGPREFETCHER_DEBUG_LEVEL
					elog(XLOGPREFETCHER_DEBUG_LEVEL,
						 "suppressing all readahead until %X/%08X is replayed due to possible TLI change",
						 LSN_FORMAT_ARGS(record->lsn));
#endif

					/* Fall through so we move past this record. */
				}
			}
			else if (rmid == RM_DBASE_ID)
			{
				/*
				 * When databases are created with the file-copy strategy,
				 * there are no WAL records to tell us about the creation of
				 * individual relations.
				 */
				if (record_type == XLOG_DBASE_CREATE_FILE_COPY)
				{
					xl_dbase_create_file_copy_rec *xlrec =
						(xl_dbase_create_file_copy_rec *) record->main_data;
					RelFileLocator rlocator =
					{InvalidOid, xlrec->db_id, InvalidRelFileNumber};

					/*
					 * Don't try to prefetch anything in this database until
					 * it has been created, or we might confuse the blocks of
					 * different generations, if a database OID or
					 * relfilenumber is reused.  It's also more efficient than
					 * discovering that relations don't exist on disk yet with
					 * ENOENT errors.
					 */
					XLogPrefetcherAddFilter(prefetcher, rlocator, 0, record->lsn);

#ifdef XLOGPREFETCHER_DEBUG_LEVEL
					elog(XLOGPREFETCHER_DEBUG_LEVEL,
						 "suppressing prefetch in database %u until %X/%08X is replayed due to raw file copy",
						 rlocator.dbOid,
						 LSN_FORMAT_ARGS(record->lsn));
#endif
				}
			}
			else if (rmid == RM_SMGR_ID)
			{
				if (record_type == XLOG_SMGR_CREATE)
				{
					xl_smgr_create *xlrec = (xl_smgr_create *)
						record->main_data;

					if (xlrec->forkNum == MAIN_FORKNUM)
					{
						/*
						 * Don't prefetch anything for this whole relation
						 * until it has been created.  Otherwise we might
						 * confuse the blocks of different generations, if a
						 * relfilenumber is reused.  This also avoids the need
						 * to discover the problem via extra syscalls that
						 * report ENOENT.
						 */
						XLogPrefetcherAddFilter(prefetcher, xlrec->rlocator, 0,
												record->lsn);

#ifdef XLOGPREFETCHER_DEBUG_LEVEL
						elog(XLOGPREFETCHER_DEBUG_LEVEL,
							 "suppressing prefetch in relation %u/%u/%u until %X/%08X is replayed, which creates the relation",
							 xlrec->rlocator.spcOid,
							 xlrec->rlocator.dbOid,
							 xlrec->rlocator.relNumber,
							 LSN_FORMAT_ARGS(record->lsn));
#endif
					}
				}
				else if (record_type == XLOG_SMGR_TRUNCATE)
				{
					xl_smgr_truncate *xlrec = (xl_smgr_truncate *)
						record->main_data;

					/*
					 * Don't consider prefetching anything in the truncated
					 * range until the truncation has been performed.
					 */
					XLogPrefetcherAddFilter(prefetcher, xlrec->rlocator,
											xlrec->blkno,
											record->lsn);

#ifdef XLOGPREFETCHER_DEBUG_LEVEL
					elog(XLOGPREFETCHER_DEBUG_LEVEL,
						 "suppressing prefetch in relation %u/%u/%u from block %u until %X/%08X is replayed, which truncates the relation",
						 xlrec->rlocator.spcOid,
						 xlrec->rlocator.dbOid,
						 xlrec->rlocator.relNumber,
						 xlrec->blkno,
						 LSN_FORMAT_ARGS(record->lsn));
#endif
				}
			}
		}

		/* Scan the block references, starting where we left off last time. */
		while (prefetcher->next_block_id <= record->max_block_id)
		{
			int			block_id = prefetcher->next_block_id++;
			DecodedBkpBlock *block = &record->blocks[block_id];
			SMgrRelation reln;
			PrefetchBufferResult result;

			if (!block->in_use)
				continue;

			Assert(!BufferIsValid(block->prefetch_buffer));

			/*
			 * Record the LSN of this record.  When it's replayed,
			 * LsnReadQueue will consider any IOs submitted for earlier LSNs
			 * to be finished.
			 */
			*lsn = record->lsn;

			/* We don't try to prefetch anything but the main fork for now. */
			if (block->forknum != MAIN_FORKNUM)
			{
				return LRQ_NEXT_NO_IO;
			}

			/*
			 * If there is a full page image attached, we won't be reading the
			 * page, so don't bother trying to prefetch.
			 */
			if (block->has_image)
			{
				XLogPrefetchIncrement(&SharedStats->skip_fpw);
				return LRQ_NEXT_NO_IO;
			}

			/* There is no point in reading a page that will be zeroed. */
			if (block->flags & BKPBLOCK_WILL_INIT)
			{
				XLogPrefetchIncrement(&SharedStats->skip_init);
				return LRQ_NEXT_NO_IO;
			}

			/* Should we skip prefetching this block due to a filter? */
			if (XLogPrefetcherIsFiltered(prefetcher, block->rlocator, block->blkno))
			{
				XLogPrefetchIncrement(&SharedStats->skip_new);
				return LRQ_NEXT_NO_IO;
			}

			/* There is no point in repeatedly prefetching the same block. */
			for (int i = 0; i < XLOGPREFETCHER_SEQ_WINDOW_SIZE; ++i)
			{
				if (block->blkno == prefetcher->recent_block[i] &&
					RelFileLocatorEquals(block->rlocator, prefetcher->recent_rlocator[i]))
				{
					/*
					 * XXX If we also remembered where it was, we could set
					 * recent_buffer so that recovery could skip smgropen()
					 * and a buffer table lookup.
					 */
					XLogPrefetchIncrement(&SharedStats->skip_rep);
					return LRQ_NEXT_NO_IO;
				}
			}
			prefetcher->recent_rlocator[prefetcher->recent_idx] = block->rlocator;
			prefetcher->recent_block[prefetcher->recent_idx] = block->blkno;
			prefetcher->recent_idx =
				(prefetcher->recent_idx + 1) % XLOGPREFETCHER_SEQ_WINDOW_SIZE;

			/*
			 * We could try to have a fast path for repeated references to the
			 * same relation (with some scheme to handle invalidations
			 * safely), but for now we'll call smgropen() every time.
			 */
			reln = smgropen(block->rlocator, INVALID_PROC_NUMBER);

			/*
			 * If the relation file doesn't exist on disk, for example because
			 * we're replaying after a crash and the file will be created and
			 * then unlinked by WAL that hasn't been replayed yet, suppress
			 * further prefetching in the relation until this record is
			 * replayed.
			 */
			if (!smgrexists(reln, MAIN_FORKNUM))
			{
#ifdef XLOGPREFETCHER_DEBUG_LEVEL
				elog(XLOGPREFETCHER_DEBUG_LEVEL,
					 "suppressing all prefetch in relation %u/%u/%u until %X/%08X is replayed, because the relation does not exist on disk",
					 reln->smgr_rlocator.locator.spcOid,
					 reln->smgr_rlocator.locator.dbOid,
					 reln->smgr_rlocator.locator.relNumber,
					 LSN_FORMAT_ARGS(record->lsn));
#endif
				XLogPrefetcherAddFilter(prefetcher, block->rlocator, 0,
										record->lsn);
				XLogPrefetchIncrement(&SharedStats->skip_new);
				return LRQ_NEXT_NO_IO;
			}

			/*
			 * If the relation isn't big enough to contain the referenced
			 * block yet, suppress prefetching of this block and higher until
			 * this record is replayed.
			 */
			if (block->blkno >= smgrnblocks(reln, block->forknum))
			{
#ifdef XLOGPREFETCHER_DEBUG_LEVEL
				elog(XLOGPREFETCHER_DEBUG_LEVEL,
					 "suppressing prefetch in relation %u/%u/%u from block %u until %X/%08X is replayed, because the relation is too small",
					 reln->smgr_rlocator.locator.spcOid,
					 reln->smgr_rlocator.locator.dbOid,
					 reln->smgr_rlocator.locator.relNumber,
					 block->blkno,
					 LSN_FORMAT_ARGS(record->lsn));
#endif
				XLogPrefetcherAddFilter(prefetcher, block->rlocator, block->blkno,
										record->lsn);
				XLogPrefetchIncrement(&SharedStats->skip_new);
				return LRQ_NEXT_NO_IO;
			}

			/* Try to initiate prefetching. */
			result = PrefetchSharedBuffer(reln, block->forknum, block->blkno);
			if (BufferIsValid(result.recent_buffer))
			{
				/* Cache hit, nothing to do. */
				XLogPrefetchIncrement(&SharedStats->hit);
				block->prefetch_buffer = result.recent_buffer;
				return LRQ_NEXT_NO_IO;
			}
			else if (result.initiated_io)
			{
				/* Cache miss, I/O (presumably) started. */
				XLogPrefetchIncrement(&SharedStats->prefetch);
				block->prefetch_buffer = InvalidBuffer;
				return LRQ_NEXT_IO;
			}
			else if ((io_direct_flags & IO_DIRECT_DATA) == 0)
			{
				/*
				 * This shouldn't be possible, because we already determined
				 * that the relation exists on disk and is big enough.
				 * Something is wrong with the cache invalidation for
				 * smgrexists(), smgrnblocks(), or the file was unlinked or
				 * truncated beneath our feet?
				 */
				elog(ERROR,
					 "could not prefetch relation %u/%u/%u block %u",
					 reln->smgr_rlocator.locator.spcOid,
					 reln->smgr_rlocator.locator.dbOid,
					 reln->smgr_rlocator.locator.relNumber,
					 block->blkno);
			}
		}

		/*
		 * Several callsites need to be able to read exactly one record
		 * without any internal readahead.  Examples: PerformWalRecovery()
		 * trying to read the first record that follows a checkpoint has emode
		 * set to PANIC, which might otherwise cause XLogPageRead() to panic
		 * on some future page, and FinishWalRecovery() determining where to
		 * start writing WAL next, which depends on the contents of the
		 * reader's internal buffer after reading one record. Therefore, don't
		 * even think about prefetching until the first record after
		 * XLogPrefetcherBeginRead() has been consumed.
		 */
		if (prefetcher->reader->decode_queue_tail &&
			prefetcher->reader->decode_queue_tail->lsn == prefetcher->begin_ptr)
			return LRQ_NEXT_AGAIN;

		/* Advance to the next record. */
		prefetcher->record = NULL;
	}
	pg_unreachable();
}

/*
 * Expose statistics about recovery prefetching.
 */
/*
 * 中文注释：
 * pg_stat_recovery_prefetch 视图底层的集合返回函数（SRF）。
 *
 * 调用场景：任意 backend 在查询 pg_stat_recovery_prefetch 时通过 pg_proc.dat
 * 中的声明调用；不要求处于恢复中，也不要求是 startup process。恢复结束后计数器
 * 保留最后的值，直到下一次恢复或显式重置。
 *
 * 返回：单行、10 列，顺序必须与系统视图定义一致：
 *   0 stats_reset      —— 上次重置时间（共享的 u64 时间戳转 TimestampTz）；
 *   1 prefetch         —— 已发起预取 I/O 的 block 数；
 *   2 hit              —— 预取时已在 buffer pool 的 block 数；
 *   3 skip_init        —— 因 WILL_INIT 跳过的 block 数；
 *   4 skip_new         —— 因过滤器/对象不存在/未扩展而跳过的 block 数；
 *   5 skip_fpw         —— 因 full page image 跳过的 block 数；
 *   6 skip_rep         —— 因重复访问跳过的 block 数；
 *   7 wal_distance     —— 预取领先重放的 WAL 字节数；
 *   8 block_distance   —— 预取窗口内 block reference 数；
 *   9 io_depth         —— 当前在途预取 I/O 数。
 *
 * 实现要点：InitMaterializedSRF() 建立 tuplestore；所有 nulls 置 false。
 * 累计计数器逐个用 pg_atomic_read_u64() 读取，因此多个列不保证来自同一瞬间，
 * 与并发增量/重置之间也没有全局快照；动态字段直接普通读取。对监控用途而言，
 * 这种“近似快照”是刻意接受的。最后 tuplestore_putvalues() 放入唯一一行，返回
 * (Datum) 0（SRF 的结果通过 rsinfo 返回）。
 */
Datum
pg_stat_get_recovery_prefetch(PG_FUNCTION_ARGS)
{
#define PG_STAT_GET_RECOVERY_PREFETCH_COLS 10
	/*
	 * 中文注释：
	 * 本 SRF 返回的列数（stats_reset、prefetch、hit、skip_init、skip_new、
	 * skip_fpw、skip_rep、wal_distance、block_distance、io_depth）。它必须与
	 * pg_proc.dat 中 pg_stat_get_recovery_prefetch 的返回类型以及
	 * pg_stat_recovery_prefetch 视图定义保持一致；下面的 values/nulls 数组
	 * 都用它确定大小，增删列时要同步修改此处和视图定义。
	 */
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	Datum		values[PG_STAT_GET_RECOVERY_PREFETCH_COLS];
	bool		nulls[PG_STAT_GET_RECOVERY_PREFETCH_COLS];

	InitMaterializedSRF(fcinfo, 0);

	for (int i = 0; i < PG_STAT_GET_RECOVERY_PREFETCH_COLS; ++i)
		nulls[i] = false;

	values[0] = TimestampTzGetDatum(pg_atomic_read_u64(&SharedStats->reset_time));
	values[1] = Int64GetDatum(pg_atomic_read_u64(&SharedStats->prefetch));
	values[2] = Int64GetDatum(pg_atomic_read_u64(&SharedStats->hit));
	values[3] = Int64GetDatum(pg_atomic_read_u64(&SharedStats->skip_init));
	values[4] = Int64GetDatum(pg_atomic_read_u64(&SharedStats->skip_new));
	values[5] = Int64GetDatum(pg_atomic_read_u64(&SharedStats->skip_fpw));
	values[6] = Int64GetDatum(pg_atomic_read_u64(&SharedStats->skip_rep));
	values[7] = Int32GetDatum(SharedStats->wal_distance);
	values[8] = Int32GetDatum(SharedStats->block_distance);
	values[9] = Int32GetDatum(SharedStats->io_depth);
	tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc, values, nulls);

	return (Datum) 0;
}

/*
 * Don't prefetch any blocks >= 'blockno' from a given 'rlocator', until 'lsn'
 * has been replayed.
 */
/*
 * 中文注释：
 * 添加或延长一条预取过滤器：在 lsn 被重放之前，不要预取 rlocator 中 block 号
 * 大于等于 blockno 的块。
 *
 * 参数：
 *   - rlocator：过滤对象。完整 locator 表示 relation 级过滤；对于 database 级
 *     过滤，调用方传入 (InvalidOid, db_id, InvalidRelFileNumber)；
 *   - blockno：过滤下界，0 表示整个对象；
 *   - lsn：创建/扩展/截断该对象的 WAL record 的 LSN；该 record 被重放后过滤器
 *     即可解除。
 *
 * 行为：
 *   - 首次为该 rlocator 添加过滤：设置 until/from_block，并把条目压入
 *     filter_queue 队头；
 *   - 已存在过滤：把 until 延长到本次 lsn，把条目移到队头，并把 from_block 取
 *     为旧值与新值的较小者。正常的前向扫描中，XLogPrefetcherNextBlock() 按 LSN
 *     递增顺序处理 record，新 lsn 通常不小于旧值；代码直接赋值（而不是取 Max）
 *     并移动队头，依赖这一顺序来维持“队尾最早到期”的排序。取 Min 是一种保守
 *     策略：一旦某次截断/创建从较低 block 开始过滤，在过滤解除前就继续过滤所有
 *     >= 该下界的块，宁可漏掉一些可预取的块，也不维护离散区间。
 *
 * 调用场景：XLogPrefetcherNextBlock() 在处理未来 record 时，遇到 file-copy
 * 建库、smgr create、smgr truncate，或发现 relation 文件不存在/尚未扩展到目标
 * block 时调用。
 * 并发/副作用：hash_search(HASH_ENTER) 可能分配内存；过滤表和链表都是预取器
 * 私有、仅 startup process 单线程访问，无锁。无返回值。
 */
static inline void
XLogPrefetcherAddFilter(XLogPrefetcher *prefetcher, RelFileLocator rlocator,
						BlockNumber blockno, XLogRecPtr lsn)
{
	XLogPrefetcherFilter *filter;
	bool		found;

	filter = hash_search(prefetcher->filter_table, &rlocator, HASH_ENTER, &found);
	if (!found)
	{
		/*
		 * Don't allow any prefetching of this block or higher until replayed.
		 */
		filter->filter_until_replayed = lsn;
		filter->filter_from_block = blockno;
		dlist_push_head(&prefetcher->filter_queue, &filter->link);
	}
	else
	{
		/*
		 * We were already filtering this rlocator.  Extend the filter's
		 * lifetime to cover this WAL record, but leave the lower of the block
		 * numbers there because we don't want to have to track individual
		 * blocks.
		 */
		filter->filter_until_replayed = lsn;
		dlist_delete(&filter->link);
		dlist_push_head(&prefetcher->filter_queue, &filter->link);
		filter->filter_from_block = Min(filter->filter_from_block, blockno);
	}
}

/*
 * Have we replayed any records that caused us to begin filtering a block
 * range?  That means that relations should have been created, extended or
 * dropped as required, so we can stop filtering out accesses to a given
 * relfilenumber.
 */
/*
 * 中文注释：
 * 在重放推进到 replaying_lsn 后，清理那些“到期”的过滤器：即创建/扩展/截断
 * 对应对象的 record 已经完成重放，继续过滤已无必要。
 *
 * 参数 replaying_lsn：通常是 XLogReleasePreviousRecord() 返回的、刚被重放 record
 * 之后的下一条 LSN，表示所有小于它的 record 都已重放。
 *
 * 清理规则：只检查队尾（最早到期）条目，若其 filter_until_replayed 仍大于等于
 * replaying_lsn，说明队尾尚未到期；由于队列按到期 LSN 从旧到新排序，后面的条目
 * 更晚到期，可以立即停止。否则从链表和 hash 表中删除该条目，继续检查新的队尾。
 * 使用严格比较：filter_until_replayed == replaying_lsn 时，对应 record 可能仍是
 * 当前尚未释放的 record，不能提前解除过滤。
 *
 * 队列排序的维护见 XLogPrefetcherAddFilter()：每次延长过滤都会把条目移到队头，
 * 因此队尾始终是最早的解除点。
 *
 * 调用场景：XLogPrefetcherReadRecord() 在释放上一条已重放 record 之后、回收
 * LsnReadQueue 额度之前调用。这样下一次预取扫描就能看到已经可以安全访问的
 * relation/block 范围。
 * 并发/副作用：修改私有 hash 表和双向链表，无锁；无返回值。`unlikely` 表明
 * 过滤队列大多数时候为空，快速路径只需判断链表头。
 */
static inline void
XLogPrefetcherCompleteFilters(XLogPrefetcher *prefetcher, XLogRecPtr replaying_lsn)
{
	while (unlikely(!dlist_is_empty(&prefetcher->filter_queue)))
	{
		XLogPrefetcherFilter *filter = dlist_tail_element(XLogPrefetcherFilter,
														  link,
														  &prefetcher->filter_queue);

		if (filter->filter_until_replayed >= replaying_lsn)
			break;

		dlist_delete(&filter->link);
		hash_search(prefetcher->filter_table, filter, HASH_REMOVE, NULL);
	}
}

/*
 * Check if a given block should be skipped due to a filter.
 */
/*
 * 中文注释：
 * 判断指定 block 是否落在当前生效的过滤器内，若是则本次预取应跳过。
 *
 * 查找两级键：
 *   1. 完整 RelFileLocator（relation 级）：若存在过滤且
 *      filter_from_block <= blockno，则命中；
 *   2. database 级键：把 relNumber 置 InvalidRelFileNumber、spcOid 置
 *      InvalidOid（保留 dbOid），若存在过滤则整个数据库中所有 relation 都命中，
 *      不再比较 blockno（database 级过滤总是从 block 0 开始）。
 *
 * 快速路径：先检查 filter_queue 是否为空。绝大多数恢复场景没有过滤器，这样
 * 可以完全避免 hash 查找；只有链表非空时才可能命中。`unlikely` 提示编译器把
 * “无过滤”作为常见分支。
 *
 * 参数：
 *   - prefetcher：预取器；
 *   - rlocator：待检查 block 所属 relation 的定位符（按值传入，函数内会修改
 *     本地副本以构造 database 级键，不影响调用方）；
 *   - blockno：待检查的 block 号。
 * 返回值：true 表示应跳过该 block 的预取；false 表示未被过滤。
 *
 * 调用场景：XLogPrefetcherNextBlock() 在检查每个 block reference 时调用，
 * 位于 FPI/WILL_INIT 检查之后、重复访问检查之前。
 * 并发/副作用：只读私有 hash 表和链表，无锁；若编译时启用了
 * XLOGPREFETCHER_DEBUG_LEVEL，会输出一条调试日志。
 */
static inline bool
XLogPrefetcherIsFiltered(XLogPrefetcher *prefetcher, RelFileLocator rlocator,
						 BlockNumber blockno)
{
	/*
	 * Test for empty queue first, because we expect it to be empty most of
	 * the time and we can avoid the hash table lookup in that case.
	 */
	if (unlikely(!dlist_is_empty(&prefetcher->filter_queue)))
	{
		XLogPrefetcherFilter *filter;

		/* See if the block range is filtered. */
		filter = hash_search(prefetcher->filter_table, &rlocator, HASH_FIND, NULL);
		if (filter && filter->filter_from_block <= blockno)
		{
#ifdef XLOGPREFETCHER_DEBUG_LEVEL
			elog(XLOGPREFETCHER_DEBUG_LEVEL,
				 "prefetch of %u/%u/%u block %u suppressed; filtering until LSN %X/%08X is replayed (blocks >= %u filtered)",
				 rlocator.spcOid, rlocator.dbOid, rlocator.relNumber, blockno,
				 LSN_FORMAT_ARGS(filter->filter_until_replayed),
				 filter->filter_from_block);
#endif
			return true;
		}

		/* See if the whole database is filtered. */
		rlocator.relNumber = InvalidRelFileNumber;
		rlocator.spcOid = InvalidOid;
		filter = hash_search(prefetcher->filter_table, &rlocator, HASH_FIND, NULL);
		if (filter)
		{
#ifdef XLOGPREFETCHER_DEBUG_LEVEL
			elog(XLOGPREFETCHER_DEBUG_LEVEL,
				 "prefetch of %u/%u/%u block %u suppressed; filtering until LSN %X/%08X is replayed (whole database)",
				 rlocator.spcOid, rlocator.dbOid, rlocator.relNumber, blockno,
				 LSN_FORMAT_ARGS(filter->filter_until_replayed));
#endif
			return true;
		}
	}

	return false;
}

/*
 * A wrapper for XLogBeginRead() that also resets the prefetcher.
 */
/*
 * 中文注释：
 * 包装 XLogBeginRead()：把底层 reader 的读取位置重置到 recPtr，并重置预取器中
 * 与读取起点和 I/O 记账相关的状态。调用场景包括：从 checkpoint 的 redo 点开始
 * 重放、重读 checkpoint record、结束恢复时定位最后一条 record、timeline switch
 * 后重新定位等。
 *
 * 具体动作：
 *   1. prefetcher->reconfigure_count--：故意制造与全局计数不一致，使下一次
 *      XLogPrefetcherReadRecord() 释放旧 LsnReadQueue 并重新分配，从而“忘记”
 *      旧的在途 I/O 记账（I/O 本身无法取消）。自减而不是置某个固定值，是为了
 *      无论全局计数如何变化都能触发一次重建；
 *   2. begin_ptr = recPtr：记录本次读取起点。XLogPrefetcherNextBlock() 在
 *      decode_queue_tail->lsn == begin_ptr 时暂停预读，确保调用方可以“只读一条
 *      record”而不触发内部 readahead；
 *   3. no_readahead_until = InvalidXLogRecPtr：清除之前因 TLI 或数据不足而设置
 *      的暂停点；
 *   4. XLogBeginRead() 重置 reader：清空解码队列（释放 oversized record 占用的
 *      内存）、清空解码缓冲区、清除延迟错误，并把 EndRecPtr/NextRecPtr 设为
 *      recPtr。
 *
 * 注意：本函数不解析 recPtr 是否有效；XLogBeginRead() 内部只 Assert 其有效，
 * 真正的读取错误会在下一次 XLogPrefetcherReadRecord() 中暴露。
 * 并发/副作用：只在 startup process 单线程中调用；可能释放解码队列内存，但不
 * 取消内核预取、不释放 buffer pin（本模块从未持有 pin）。
 */
void
XLogPrefetcherBeginRead(XLogPrefetcher *prefetcher, XLogRecPtr recPtr)
{
	/* This will forget about any in-flight IO. */
	prefetcher->reconfigure_count--;

	/* Book-keeping to avoid readahead on first read. */
	prefetcher->begin_ptr = recPtr;

	prefetcher->no_readahead_until = InvalidXLogRecPtr;

	/* This will forget about any queued up records in the decoder. */
	XLogBeginRead(prefetcher->reader, recPtr);
}

/*
 * A wrapper for XLogReadRecord() that provides the same interface, but also
 * tries to initiate I/O for blocks referenced in future WAL records.
 */
/*
 * 中文注释：
 * 预取器的核心读取入口，接口与 XLogReadRecord() 类似：返回下一条已解码 record
 * 的 XLogRecord *，失败时返回 NULL（并通过 errmsg 给出错误信息）。区别在于，
 * 在返回当前 record 之前，它会借助解码队列向前查看后续 record，尽力为其中的
 * block 发起预取 I/O。
 *
 * 执行步骤：
 *   1. GUC 重配置检查：若全局 XLogPrefetchReconfigureCount 与本地快照不一致
 *      （recovery_prefetch 或 maintenance_io_concurrency 变化、timeline switch
 *      等），释放旧 LsnReadQueue，并根据当前配置重建：
 *        - 启用预取：max_inflight = maintenance_io_concurrency，
 *          max_distance = max_inflight * XLOGPREFETCHER_DISTANCE_MULTIPLIER；
 *        - 关闭预取：max_inflight = 1，max_distance = 1，仅用于每次解码一条
 *          record、保证恢复能前进。
 *      然后更新本地快照。
 *   2. XLogReleasePreviousRecord()：上一条返回的 record 已经被调用方重放完毕，
 *      释放它在解码队列中的空间，返回“已重放到”的 LSN（下一条 record 的起始）。
 *   3. XLogPrefetcherCompleteFilters()：按该 LSN 清理已到期的过滤器。
 *   4. lrq_complete_lsn()：按该 LSN 回收 LsnReadQueue 中已完成（或已无意义）的
 *      条目，并在预取启用时补充新的预取。
 *   5. 若解码队列仍为空，调用 lrq_prefetch() 至少解码并排队一条 record。此时
 *      断言队列无 inflight/completed 条目：没有排队 record 意味着所有已解码内容
 *      都已重放完，旧的预取窗口应已被清空。
 *   6. XLogNextRecord() 取出（或触发解码）下一条 record；NULL 表示到 WAL 末尾、
 *      遇到错误等，直接返回 NULL，由调用方处理。
 *   7. 断言返回的 record 就是 reader->record（XLogRecXXX() 宏依赖该“当前
 *      record”状态）。
 *   8. 若返回的 record 恰好是预取器正在扫描的那一条，说明预取器为它启动的 I/O
 *      可能只覆盖了部分 block（maintenance_io_concurrency 很低时），现在它要被
 *      交给调用方重放、随后可能被释放，因此把 prefetcher->record 置 NULL，放弃
 *      本 record 剩余的 block；否则预取器仍指向更晚的 record，可继续使用。
 *   9. 若该 record 的 LSN 达到 next_stats_shm_lsn，调用
 *      XLogPrefetcherComputeStats() 刷新 pg_stat_recovery_prefetch。
 *   10. 返回 &record->header。
 *
 * 语义保证：除了“提前发起 I/O”和“记录 prefetch_buffer 提示”之外，本函数与
 * XLogReadRecord() 的可见行为一致；返回的 record 在下次调用前有效，调用方必须
 * 在下一次调用前完成重放。所有操作都在 startup process 单线程中，无锁。
 */
XLogRecord *
XLogPrefetcherReadRecord(XLogPrefetcher *prefetcher, char **errmsg)
{
	DecodedXLogRecord *record;
	XLogRecPtr	replayed_up_to;

	/*
	 * See if it's time to reset the prefetching machinery, because a relevant
	 * GUC was changed.
	 */
	if (unlikely(XLogPrefetchReconfigureCount != prefetcher->reconfigure_count))
	{
		uint32		max_distance;
		uint32		max_inflight;

		if (prefetcher->streaming_read)
			lrq_free(prefetcher->streaming_read);

		if (RecoveryPrefetchEnabled())
		{
			Assert(maintenance_io_concurrency > 0);
			max_inflight = maintenance_io_concurrency;
			max_distance = max_inflight * XLOGPREFETCHER_DISTANCE_MULTIPLIER;
		}
		else
		{
			max_inflight = 1;
			max_distance = 1;
		}

		prefetcher->streaming_read = lrq_alloc(max_distance,
											   max_inflight,
											   (uintptr_t) prefetcher,
											   XLogPrefetcherNextBlock);

		prefetcher->reconfigure_count = XLogPrefetchReconfigureCount;
	}

	/*
	 * Release last returned record, if there is one, as it's now been
	 * replayed.
	 */
	replayed_up_to = XLogReleasePreviousRecord(prefetcher->reader);

	/*
	 * Can we drop any filters yet?  If we were waiting for a relation to be
	 * created or extended, it is now OK to access blocks in the covered
	 * range.
	 */
	XLogPrefetcherCompleteFilters(prefetcher, replayed_up_to);

	/*
	 * All IO initiated by earlier WAL is now completed.  This might trigger
	 * further prefetching.
	 */
	lrq_complete_lsn(prefetcher->streaming_read, replayed_up_to);

	/*
	 * If there's nothing queued yet, then start prefetching to cause at least
	 * one record to be queued.
	 */
	if (!XLogReaderHasQueuedRecordOrError(prefetcher->reader))
	{
		Assert(lrq_inflight(prefetcher->streaming_read) == 0);
		Assert(lrq_completed(prefetcher->streaming_read) == 0);
		lrq_prefetch(prefetcher->streaming_read);
	}

	/* Read the next record. */
	record = XLogNextRecord(prefetcher->reader, errmsg);
	if (!record)
		return NULL;

	/*
	 * The record we just got is the "current" one, for the benefit of the
	 * XLogRecXXX() macros.
	 */
	Assert(record == prefetcher->reader->record);

	/*
	 * If maintenance_io_concurrency is set very low, we might have started
	 * prefetching some but not all of the blocks referenced in the record
	 * we're about to return.  Forget about the rest of the blocks in this
	 * record by dropping the prefetcher's reference to it.
	 */
	if (record == prefetcher->record)
		prefetcher->record = NULL;

	/*
	 * See if it's time to compute some statistics, because enough WAL has
	 * been processed.
	 */
	if (unlikely(record->lsn >= prefetcher->next_stats_shm_lsn))
		XLogPrefetcherComputeStats(prefetcher);

	Assert(record == prefetcher->reader->record);

	return &record->header;
}

/*
 * 中文注释：
 * recovery_prefetch 的 GUC check hook，在参数生效前校验取值。
 *
 * 当前只做一件事：在编译时未定义 USE_PREFETCH 的平台上，拒绝显式的
 * RECOVERY_PREFETCH_ON。原因是该平台没有可用的 read-ahead advice 实现，强制
 * 开启只会给用户“已启用”的错觉；而默认的 RECOVERY_PREFETCH_TRY 允许通过，
 * 由 RecoveryPrefetchEnabled() 安静地返回 false，实现“尽力而为”的语义。
 * 被拒绝时会通过 GUC_check_errdetail() 给出用户可见的详细原因。
 *
 * 参数按 GUC check hook 约定：new_value 指向待校验值，extra 用于返回额外数据
 * （未使用），source 表示配置来源（未使用）。返回 true 表示接受，false 表示拒绝。
 * 该函数不修改全局变量；真正的赋值在 assign_recovery_prefetch() 中完成。
 */
bool
check_recovery_prefetch(int *new_value, void **extra, GucSource source)
{
#ifndef USE_PREFETCH
	if (*new_value == RECOVERY_PREFETCH_ON)
	{
		GUC_check_errdetail("\"recovery_prefetch\" is not supported on platforms that lack support for issuing read-ahead advice.");
		return false;
	}
#endif

	return true;
}

/*
 * 中文注释：
 * recovery_prefetch 的 GUC assign hook：把通过校验的新值写入全局变量，并在
 * startup process 中触发预取器重配置。
 *
 * 行为：
 *   1. recovery_prefetch = new_value：所有进程都会执行（GUC 变量是每进程私有的
 *      副本），但只有 startup process 的值会影响恢复期间的预取；
 *   2. 仅当 AmStartupProcess() 为真时调用 XLogPrefetchReconfigure()，把
 *      XLogPrefetchReconfigureCount 加一，让实际的 LsnReadQueue 重建延迟到下一次
 *      XLogPrefetcherReadRecord()。其他 backend 虽然也会改变自己的
 *      recovery_prefetch 副本，但它们不执行恢复，也无需触碰预取器状态。
 *
 * 参数按 GUC assign hook 约定：new_value 为已校验的新值，extra 为 check hook
 * 可能返回的额外数据（本模块未使用）。无返回值。
 * 副作用：修改全局变量；在 startup process 中递增进程内重配置计数。不加锁，因为
 * 这些变量只由当前进程访问。
 */
void
assign_recovery_prefetch(int new_value, void *extra)
{
	/* Reconfigure prefetching, because a setting it depends on changed. */
	recovery_prefetch = new_value;
	if (AmStartupProcess())
		XLogPrefetchReconfigure();
}
