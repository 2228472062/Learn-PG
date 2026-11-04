/*-------------------------------------------------------------------------
 *
 * generic_xlog.c
 *	 Implementation of generic xlog records.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/generic_xlog.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的通用 WAL 记录（Generic WAL record，资源管理器
 * RM_GENERIC_ID），为扩展和索引访问方法提供一种无需自定义 rmgr 就能把页修改写入
 * WAL 的机制。
 *
 * 主要内容：
 *   1. GenericXLog 生命周期接口：GenericXLogStart/RegisterBuffer/Finish/Abort；
 *   2. 页镜像（page image）管理：调用者在副本上修改，Finish 时统一写回 buffer；
 *   3. delta 编码：逐字节比较修改前后的页，只记录发生变化的片段（fragment）；
 *   4. 恢复重放：generic_redo 按 delta 把修改应用到目标页；
 *   5. 一致性检查辅助：generic_mask 屏蔽 LSN、校验和与页内空闲空间。
 *
 * 核心数据结构：
 *   GenericXLogState 保存一次 generic WAL 记录涉及的所有页。结构体开头是与 I/O
 *   对齐的 PGIOAlignedBlock images[]，随后是描述每页的 GenericXLogPageData
 *   pages[]；最多可注册 MAX_GENERIC_XLOG_PAGES 个页（即
 *   XLR_NORMAL_MAX_BLOCK_ID，当前为 4）。GenericXLogPageData 保存 buffer、flags、
 *   image 副本以及编码后的 delta。
 *
 * delta 格式是若干 fragment 的顺序拼接，每个 fragment 为：
 *   OffsetNumber offset（页内偏移）、OffsetNumber length（长度）、length 字节数据。
 * 未变化的区域不会出现在 delta 中；若两个 fragment 之间未变化的空隙不超过
 * MATCH_THRESHOLD，则把它们合并，避免 fragment 头本身的开销。页的 "lower" 与
 * "upper" 两部分分别计算，中间的 pd_lower..pd_upper 空洞不参与比较。
 *
 * 与其他模块的关系：
 *   xloginsert.c 提供 XLogBeginInsert/XLogRegisterBuffer/XLogRegisterBufData/
 *   XLogInsert；xlogutils.c 的 XLogReadBufferForRedo 在恢复时定位并加锁目标
 *   buffer；bufmask.c 提供 generic_mask 使用的掩码函数；rmgrlist.h 把
 *   RM_GENERIC_ID 绑定到 generic_redo/generic_desc/generic_identify/generic_mask。
 *   generic WAL 记录不参与逻辑解码（未注册 rm_decode）。
 *
 * 关键设计思想：
 *   - delta 编码以 CPU 换 WAL 体积：逐字节比较，适合小改动，页内搬移数据时压缩
 *     效果一般；
 *   - 调用者始终修改页副本，因此 GenericXLogStart 之后、Finish 之前可以安全地
 *     分配内存或报错，真正的 critical section 只存在于 GenericXLogFinish 内部；
 *   - 页必须采用标准布局（pd_lower 与 pd_upper 之间无有用数据），WAL 路径在写回
 *     与重放时都会把该空洞清零，以保证主库页状态与恢复结果一致；
 *   - 并发方面，调用者需在 RegisterBuffer 之前取得每个目标 buffer 的排他锁并保持
 *     到 Finish 之后；重放按 block_id 升序加锁，因此注册顺序应与恢复时的加锁顺序
 *     一致；
 *   - 对于不需要 WAL 的关系（临时表、unlogged 表等），接口行为相同，只是不产生
 *     WAL 记录、不返回有效 LSN。
 */
#include "postgres.h"

#include "access/bufmask.h"
#include "access/generic_xlog.h"
#include "access/xlogutils.h"
#include "miscadmin.h"

/*-------------------------------------------------------------------------
 * Internally, a delta between pages consists of a set of fragments.  Each
 * fragment represents changes made in a given region of a page.  A fragment
 * is made up as follows:
 *
 * - offset of page region (OffsetNumber)
 * - length of page region (OffsetNumber)
 * - data - the data to place into the region ('length' number of bytes)
 *
 * Unchanged regions of a page are not represented in its delta.  As a result,
 * a delta can be more compact than the full page image.  But having an
 * unchanged region between two fragments that is smaller than the fragment
 * header (offset+length) does not pay off in terms of the overall size of
 * the delta.  For this reason, we merge adjacent fragments if the unchanged
 * region between them is <= MATCH_THRESHOLD bytes.
 *
 * We do not bother to merge fragments across the "lower" and "upper" parts
 * of a page; it's very seldom the case that pd_lower and pd_upper are within
 * MATCH_THRESHOLD bytes of each other, and handling that infrequent case
 * would complicate and slow down the delta-computation code unduly.
 * Therefore, the worst-case delta size includes two fragment headers plus
 * a full page's worth of data.
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * FRAGMENT_HEADER_SIZE 是一个 fragment 头的固定开销：offset 与 length 各占一个
 * OffsetNumber。MATCH_THRESHOLD 取 fragment 头大小，含义是：当两个变化片段之间的
 * 未变化空隙不超过该值时，直接把这几个字节一并写进 delta 更划算，因此合并片段。
 * MAX_DELTA_SIZE 是 delta 的最坏情况大小：整页数据加上 lower/upper 两个片段的头。
 * 这些常量共同决定了 GenericXLogPageData.delta 的静态数组大小。
 */
#define FRAGMENT_HEADER_SIZE	(2 * sizeof(OffsetNumber))
#define MATCH_THRESHOLD			FRAGMENT_HEADER_SIZE
#define MAX_DELTA_SIZE			(BLCKSZ + 2 * FRAGMENT_HEADER_SIZE)

/*
 * 中文注释：
 * GenericXLogPageData 描述一次 generic WAL 记录中单个页的构造状态：
 *   buffer   —— 调用者注册的 buffer（pin 与排他锁由调用者负责）；
 *   flags    —— 注册时传入的标志，目前只有 GENERIC_XLOG_FULL_IMAGE；
 *   deltaLen —— delta 数组中已使用的字节数；
 *   image    —— 页的可修改副本，指向 GenericXLogState.images[] 中对应槽位；
 *   delta    —— 编码后的 fragment 序列，最坏情况为 MAX_DELTA_SIZE 字节。
 * image 单独分配而不是原地修改 buffer，既保证内存对齐，也保证在 Finish 前出错时
 * 实际页内容不受影响。
 */
/* Struct of generic xlog data for single page */
typedef struct
{
	Buffer		buffer;			/* registered buffer */
	int			flags;			/* flags for this buffer */
	int			deltaLen;		/* space consumed in delta field */
	char	   *image;			/* copy of page image for modification, do not
								 * do it in-place to have aligned memory chunk */
	char		delta[MAX_DELTA_SIZE];	/* delta between page images */
} GenericXLogPageData;

/*
 * State of generic xlog record construction.  Must be allocated at an I/O
 * aligned address.
 */
/*
 * 中文注释：
 * GenericXLogState 表示一条 generic WAL 记录的构造状态。
 *
 * images[] 必须放在结构体最前面：palloc_aligned 返回的整块内存按 PG_IO_ALIGN_SIZE
 * 对齐，把页镜像放在偏移 0 处可以保证每个镜像都满足直接 I/O 的对齐要求。
 * pages[i].image 指向 images[i].data，两者一一对应，因此 images 只作为存储，
 * 实际元数据与 delta 都在 pages[] 中。
 *
 * isLogged 在 GenericXLogStart 时由 RelationNeedsWAL(relation) 决定：为真时
 * Finish 会计算 delta 并写 WAL；为假时只把镜像写回 buffer。
 */
struct GenericXLogState
{
	/* Page images (properly aligned, must be first) */
	PGIOAlignedBlock images[MAX_GENERIC_XLOG_PAGES];
	/* Info about each page, see above */
	GenericXLogPageData pages[MAX_GENERIC_XLOG_PAGES];
	bool		isLogged;
};

/*
 * 中文注释：
 * 下面四个 static 函数构成 delta 的“编码—应用”核心：
 *   writeFragment       把一个 fragment 追加到 delta；
 *   computeRegionDelta  在指定区域内逐字节比较并产生 fragment；
 *   computeDelta        按页的 lower/upper 布局分别调用 computeRegionDelta；
 *   applyPageRedo       解析 delta 并覆盖到页上（重放与 WAL_DEBUG 自检共用）。
 */
static void writeFragment(GenericXLogPageData *pageData, OffsetNumber offset,
						  OffsetNumber length, const char *data);
static void computeRegionDelta(GenericXLogPageData *pageData,
							   const char *curpage, const char *targetpage,
							   int targetStart, int targetEnd,
							   int validStart, int validEnd);
static void computeDelta(GenericXLogPageData *pageData, Page curpage, Page targetpage);
static void applyPageRedo(Page page, const char *delta, Size deltaSize);


/*
 * Write next fragment into pageData's delta.
 *
 * The fragment has the given offset and length, and data points to the
 * actual data (of length length).
 */
/*
 * 中文注释：
 * 把一个 fragment 追加写入 pageData->delta。
 *
 * 参数：
 *   pageData —— 目标页的构造状态，deltaLen 指示当前写入位置；
 *   offset   —— fragment 在页内的起始偏移；
 *   length   —— fragment 的字节长度；
 *   data     —— 要写入的 length 字节数据（通常指向 targetpage + offset）。
 * 返回值：无。
 *
 * fragment 采用主机字节序直接 memcpy，因此 WAL 只能在同架构、同字节序的实例间
 * 重放，这与 PostgreSQL 其他 WAL 记录的约定一致。函数只操作内存中的 delta
 * 缓冲区，不访问共享缓冲区，也不加锁；调用者必须保证空间足够
 * （computeRegionDelta 的合并策略保证最坏情况不超过 MAX_DELTA_SIZE）。Assert
 * 仅在启用断言的构建中检查边界。
 */
static void
writeFragment(GenericXLogPageData *pageData, OffsetNumber offset, OffsetNumber length,
			  const char *data)
{
	char	   *ptr = pageData->delta + pageData->deltaLen;

	/* Verify we have enough space */
	Assert(pageData->deltaLen + sizeof(offset) +
		   sizeof(length) + length <= sizeof(pageData->delta));

	/* Write fragment data */
	memcpy(ptr, &offset, sizeof(offset));
	ptr += sizeof(offset);
	memcpy(ptr, &length, sizeof(length));
	ptr += sizeof(length);
	memcpy(ptr, data, length);
	ptr += length;

	pageData->deltaLen = ptr - pageData->delta;
}

/*
 * Compute the XLOG fragments needed to transform a region of curpage into the
 * corresponding region of targetpage, and append them to pageData's delta
 * field.  The region to transform runs from targetStart to targetEnd-1.
 * Bytes in curpage outside the range validStart to validEnd-1 should be
 * considered invalid, and always overwritten with target data.
 *
 * This function is a hot spot, so it's worth being as tense as possible
 * about the data-matching loops.
 */
/*
 * 中文注释：
 * 计算把 curpage 的某个区域改造成 targetpage 对应区域所需的 fragments，并追加到
 * pageData->delta。
 *
 * 区域定义为 [targetStart, targetEnd)；只有 [validStart, validEnd) 内的字节被认为
 * 在 curpage 中有效。区间外（例如旧页 pd_lower 之后的空洞或 pd_upper 之前尚未
 * 使用的空间）即使字节碰巧相同也必须覆盖，因此会被并入相邻 fragment 一起写出。
 *
 * 算法：
 *   1. 若 validStart > targetStart，把开头无效区并入第一个 fragment；
 *   2. 主循环同时推进“未匹配片段”和“已匹配区段”：
 *      - 遇到不同字节时开启或延续 fragment；
 *      - 连续相同字节超过 MATCH_THRESHOLD 时，认为保留这段空隙不划算，
 *        把此前累积的 fragment 写出并结束它；
 *      - 相同字节一直延续到 loopEnd 时暂不写出，留给循环结束统一处理；
 *   3. 若 loopEnd < targetEnd，把结尾无效区并入最后一个 fragment；
 *   4. 写出尚未落盘的最后一个 fragment。
 *
 * fragmentBegin/fragmentEnd 的约定：fragmentBegin < 0 表示当前没有待写片段；
 * fragmentEnd 记录最后一个已确认不同的字节之后的位置，仅在匹配一直延伸到
 * loopEnd 的情况下才有意义。内层 while 循环是性能热点，作者刻意保持紧凑。
 *
 * 副作用：通过 writeFragment 追加数据并更新 pageData->deltaLen。只处理本地页
 * 副本，不涉及并发或锁。
 */
static void
computeRegionDelta(GenericXLogPageData *pageData,
				   const char *curpage, const char *targetpage,
				   int targetStart, int targetEnd,
				   int validStart, int validEnd)
{
	int			i,
				loopEnd,
				fragmentBegin = -1,
				fragmentEnd = -1;

	/* Deal with any invalid start region by including it in first fragment */
	if (validStart > targetStart)
	{
		fragmentBegin = targetStart;
		targetStart = validStart;
	}

	/* We'll deal with any invalid end region after the main loop */
	loopEnd = Min(targetEnd, validEnd);

	/* Examine all the potentially matchable bytes */
	i = targetStart;
	while (i < loopEnd)
	{
		if (curpage[i] != targetpage[i])
		{
			/* On unmatched byte, start new fragment if not already in one */
			if (fragmentBegin < 0)
				fragmentBegin = i;
			/* Mark unmatched-data endpoint as uncertain */
			fragmentEnd = -1;
			/* Extend the fragment as far as possible in a tight loop */
			i++;
			while (i < loopEnd && curpage[i] != targetpage[i])
				i++;
			if (i >= loopEnd)
				break;
		}

		/* Found a matched byte, so remember end of unmatched fragment */
		fragmentEnd = i;

		/*
		 * Extend the match as far as possible in a tight loop.  (On typical
		 * workloads, this inner loop is the bulk of this function's runtime.)
		 */
		i++;
		while (i < loopEnd && curpage[i] == targetpage[i])
			i++;

		/*
		 * There are several possible cases at this point:
		 *
		 * 1. We have no unwritten fragment (fragmentBegin < 0).  There's
		 * nothing to write; and it doesn't matter what fragmentEnd is.
		 *
		 * 2. We found more than MATCH_THRESHOLD consecutive matching bytes.
		 * Dump out the unwritten fragment, stopping at fragmentEnd.
		 *
		 * 3. The match extends to loopEnd.  We'll do nothing here, exit the
		 * loop, and then dump the unwritten fragment, after merging it with
		 * the invalid end region if any.  If we don't so merge, fragmentEnd
		 * establishes how much the final writeFragment call needs to write.
		 *
		 * 4. We found an unmatched byte before loopEnd.  The loop will repeat
		 * and will enter the unmatched-byte stanza above.  So in this case
		 * also, it doesn't matter what fragmentEnd is.  The matched bytes
		 * will get merged into the continuing unmatched fragment.
		 *
		 * Only in case 3 do we reach the bottom of the loop with a meaningful
		 * fragmentEnd value, which is why it's OK that we unconditionally
		 * assign "fragmentEnd = i" above.
		 */
		if (fragmentBegin >= 0 && i - fragmentEnd > MATCH_THRESHOLD)
		{
			writeFragment(pageData, fragmentBegin,
						  fragmentEnd - fragmentBegin,
						  targetpage + fragmentBegin);
			fragmentBegin = -1;
			fragmentEnd = -1;	/* not really necessary */
		}
	}

	/* Deal with any invalid end region by including it in final fragment */
	if (loopEnd < targetEnd)
	{
		if (fragmentBegin < 0)
			fragmentBegin = loopEnd;
		fragmentEnd = targetEnd;
	}

	/* Write final fragment if any */
	if (fragmentBegin >= 0)
	{
		if (fragmentEnd < 0)
			fragmentEnd = targetEnd;
		writeFragment(pageData, fragmentBegin,
					  fragmentEnd - fragmentBegin,
					  targetpage + fragmentBegin);
	}
}

/*
 * Compute the XLOG delta record needed to transform curpage into targetpage,
 * and store it in pageData's delta field.
 */
/*
 * 中文注释：
 * 计算从 curpage 到 targetpage 的完整 delta，写入 pageData->delta 并重置
 * deltaLen。
 *
 * 以 targetpage 的 pd_lower/pd_upper 为界，把页分成两个独立区域分别比较：
 *   - lower 部分 [0, targetLower)，旧页的有效范围是 [0, curLower)；
 *   - upper 部分 [targetUpper, BLCKSZ)，旧页的有效范围是 [curUpper, BLCKSZ)。
 * 中间 pd_lower..pd_upper 是空闲空洞，不生成任何 delta；logged 路径的 Finish 与
 * redo 会显式清零，因此无需记录。两部分不跨空洞合并，所以最坏情况 delta 为整页
 * 数据加两个 fragment 头。
 *
 * 该函数只在 GenericXLogFinish 的 logged 分支、且未指定
 * GENERIC_XLOG_FULL_IMAGE 时调用；此时原始页与新镜像都还在，可以逐字节比较。
 *
 * 在启用 WAL_DEBUG 且 XLOG_DEBUG 为真的构建中，会把 delta 应用到一个临时页副本，
 * 并与 targetpage 的 lower/upper 区域比较（空洞不比较），用于自检 delta 编码的
 * 正确性。
 */
static void
computeDelta(GenericXLogPageData *pageData, Page curpage, Page targetpage)
{
	int			targetLower = ((PageHeader) targetpage)->pd_lower,
				targetUpper = ((PageHeader) targetpage)->pd_upper,
				curLower = ((PageHeader) curpage)->pd_lower,
				curUpper = ((PageHeader) curpage)->pd_upper;

	pageData->deltaLen = 0;

	/* Compute delta records for lower part of page ... */
	computeRegionDelta(pageData, curpage, targetpage,
					   0, targetLower,
					   0, curLower);
	/* ... and for upper part, ignoring what's between */
	computeRegionDelta(pageData, curpage, targetpage,
					   targetUpper, BLCKSZ,
					   curUpper, BLCKSZ);

	/*
	 * If xlog debug is enabled, then check produced delta.  Result of delta
	 * application to curpage should be equivalent to targetpage.
	 */
#ifdef WAL_DEBUG
	if (XLOG_DEBUG)
	{
		PGAlignedBlock tmp;

		memcpy(tmp.data, curpage, BLCKSZ);
		applyPageRedo(tmp.data, pageData->delta, pageData->deltaLen);
		if (memcmp(tmp.data, targetpage, targetLower) != 0 ||
			memcmp(tmp.data + targetUpper, targetpage + targetUpper,
				   BLCKSZ - targetUpper) != 0)
			elog(ERROR, "result of generic xlog apply does not match");
	}
#endif
}

/*
 * Start new generic xlog record for modifications to specified relation.
 */
/*
 * 中文注释：
 * 开始构造一条 generic WAL 记录，返回后续 RegisterBuffer/Finish/Abort 使用的
 * 状态。
 *
 * relation 用于判断是否需要 WAL：RelationNeedsWAL() 为假（临时表、unlogged 表
 * 等）时，Finish 只把镜像写回 buffer，不调用 XLogInsert。
 *
 * 分配要点：
 *   - GenericXLogState 通过 palloc_aligned 按 PG_IO_ALIGN_SIZE 对齐，满足直接
 *     I/O 及页镜像对齐要求；结构体把 images[] 放在最前面（见其定义处说明）；
 *   - pages[i].image 指向 images[i].data，buffer 初始化为 InvalidBuffer；
 *   - deltaLen 由后续 computeDelta 重置，这里无需初始化。
 *
 * 本函数不获取任何 buffer 锁或 pin，也不进入 critical section；调用者可以在
 * Start 与 Finish 之间自由分配内存或报错。返回的状态位于当前内存上下文，
 * Finish/Abort 会负责 pfree。
 */
GenericXLogState *
GenericXLogStart(Relation relation)
{
	GenericXLogState *state;
	int			i;

	state = (GenericXLogState *) palloc_aligned(sizeof(GenericXLogState),
												PG_IO_ALIGN_SIZE,
												0);
	state->isLogged = RelationNeedsWAL(relation);

	for (i = 0; i < MAX_GENERIC_XLOG_PAGES; i++)
	{
		state->pages[i].image = state->images[i].data;
		state->pages[i].buffer = InvalidBuffer;
	}

	return state;
}

/*
 * Register new buffer for generic xlog record.
 *
 * Returns pointer to the page's image in the GenericXLogState, which
 * is what the caller should modify.
 *
 * If the buffer is already registered, just return its existing entry.
 * (It's not very clear what to do with the flags in such a case, but
 * for now we stay with the original flags.)
 */
/*
 * 中文注释：
 * 把一个 buffer 注册到当前 generic WAL 记录，并返回可修改的页镜像指针。
 *
 * 行为：
 *   - 在 pages[] 中查找该 buffer：已注册则直接返回已有镜像（flags 保持首次注册的
 *     值，重复注册不会更新 flags，也不会重复拷贝页）；
 *   - 否则占用第一个空闲槽位，记录 buffer 与 flags，并用 memcpy 把
 *     BufferGetPage() 的 BLCKSZ 字节复制到对齐的 image 缓冲区，返回该副本。
 *
 * 调用者约定：必须已经持有该 buffer 的 pin 与排他锁，并保持到
 * GenericXLogFinish() 返回之后；绝不能直接修改 BufferGetPage() 的内容，所有
 * 修改都应在返回的副本上进行。注册顺序就是恢复时 generic_redo 获取 buffer 锁的
 * 顺序，因此多页操作应按一致的顺序注册以避免死锁。
 *
 * 超过 MAX_GENERIC_XLOG_PAGES（当前为 4，等于 XLR_NORMAL_MAX_BLOCK_ID）时
 * elog(ERROR)。返回 NULL 只是为了让编译器满意，正常路径不会到达。
 */
Page
GenericXLogRegisterBuffer(GenericXLogState *state, Buffer buffer, int flags)
{
	int			block_id;

	/* Search array for existing entry or first unused slot */
	for (block_id = 0; block_id < MAX_GENERIC_XLOG_PAGES; block_id++)
	{
		GenericXLogPageData *page = &state->pages[block_id];

		if (BufferIsInvalid(page->buffer))
		{
			/* Empty slot, so use it (there cannot be a match later) */
			page->buffer = buffer;
			page->flags = flags;
			memcpy(page->image, BufferGetPage(buffer), BLCKSZ);
			return (Page) page->image;
		}
		else if (page->buffer == buffer)
		{
			/*
			 * Buffer is already registered.  Just return the image, which is
			 * already prepared.
			 */
			return (Page) page->image;
		}
	}

	elog(ERROR, "maximum number %d of generic xlog buffers is exceeded",
		 MAX_GENERIC_XLOG_PAGES);
	/* keep compiler quiet */
	return NULL;
}

/*
 * Apply changes represented by GenericXLogState to the actual buffers,
 * and emit a generic xlog record.
 */
/*
 * 中文注释：
 * 结束构造：把页镜像的修改应用到真实 buffer，并在需要时写出 generic WAL 记录。
 *
 * 两条路径：
 *   1. state->isLogged 为真：
 *      - 先调用 XLogBeginInsert()。它必须在 critical section 之外执行，因为它可能
 *        报错（例如恢复期间不允许产生新 WAL），而 critical section 内不能报错；
 *      - 进入 critical section，逐页处理：未指定 FULL_IMAGE 时先用原始页与新
 *        镜像计算 delta；然后分三段写回页（[0,pd_lower)、清零空洞、
 *        [pd_upper,BLCKSZ)），使空洞内容与重放结果一致；MarkBufferDirty()；
 *        注册 buffer 时，FULL_IMAGE 使用 REGBUF_FORCE_IMAGE|REGBUF_STANDARD，
 *        否则使用 REGBUF_STANDARD 并通过 XLogRegisterBufData 附加 delta；
 *      - 调用 XLogInsert(RM_GENERIC_ID, 0) 写入记录，再把返回的 LSN 设置到所有
 *        页上；
 *      - 退出 critical section。
 *   2. isLogged 为假（不需要 WAL 的关系）：
 *      - 进入 critical section，直接把整个 image 拷回 buffer 并
 *        MarkBufferDirty()；空洞无需清零；
 *      - 不产生 WAL，返回 InvalidXLogRecPtr。
 * 最后 pfree(state)。
 *
 * 并发/副作用：调用者必须仍持有所有已注册 buffer 的排他锁；critical section 内
 * 不能有会报错的操作。页 LSN 在 XLogInsert 之后才设置，重放时以记录中的 LSN
 * 为准。返回值为 WAL 记录的 LSN；unlogged 路径返回 InvalidXLogRecPtr。
 */
XLogRecPtr
GenericXLogFinish(GenericXLogState *state)
{
	XLogRecPtr	lsn;
	int			i;

	if (state->isLogged)
	{
		/* Logged relation: make xlog record in critical section. */
		XLogBeginInsert();

		START_CRIT_SECTION();

		/*
		 * Compute deltas if necessary, write changes to buffers, mark buffers
		 * dirty, and register changes.
		 */
		for (i = 0; i < MAX_GENERIC_XLOG_PAGES; i++)
		{
			GenericXLogPageData *pageData = &state->pages[i];
			Page		page;
			PageHeader	pageHeader;

			if (BufferIsInvalid(pageData->buffer))
				continue;

			page = BufferGetPage(pageData->buffer);
			pageHeader = (PageHeader) pageData->image;

			/*
			 * Compute delta while we still have both the unmodified page and
			 * the new image. Not needed if we are logging the full image.
			 */
			if (!(pageData->flags & GENERIC_XLOG_FULL_IMAGE))
				computeDelta(pageData, page, (Page) pageData->image);

			/*
			 * Apply the image, being careful to zero the "hole" between
			 * pd_lower and pd_upper in order to avoid divergence between
			 * actual page state and what replay would produce.
			 */
			memcpy(page, pageData->image, pageHeader->pd_lower);
			memset(page + pageHeader->pd_lower, 0,
				   pageHeader->pd_upper - pageHeader->pd_lower);
			memcpy(page + pageHeader->pd_upper,
				   pageData->image + pageHeader->pd_upper,
				   BLCKSZ - pageHeader->pd_upper);

			MarkBufferDirty(pageData->buffer);

			if (pageData->flags & GENERIC_XLOG_FULL_IMAGE)
			{
				XLogRegisterBuffer(i, pageData->buffer,
								   REGBUF_FORCE_IMAGE | REGBUF_STANDARD);
			}
			else
			{
				XLogRegisterBuffer(i, pageData->buffer, REGBUF_STANDARD);
				XLogRegisterBufData(i, pageData->delta, pageData->deltaLen);
			}
		}

		/* Insert xlog record */
		lsn = XLogInsert(RM_GENERIC_ID, 0);

		/* Set LSN */
		for (i = 0; i < MAX_GENERIC_XLOG_PAGES; i++)
		{
			GenericXLogPageData *pageData = &state->pages[i];

			if (BufferIsInvalid(pageData->buffer))
				continue;
			PageSetLSN(BufferGetPage(pageData->buffer), lsn);
		}
		END_CRIT_SECTION();
	}
	else
	{
		/* Unlogged relation: skip xlog-related stuff */
		START_CRIT_SECTION();
		for (i = 0; i < MAX_GENERIC_XLOG_PAGES; i++)
		{
			GenericXLogPageData *pageData = &state->pages[i];

			if (BufferIsInvalid(pageData->buffer))
				continue;
			memcpy(BufferGetPage(pageData->buffer),
				   pageData->image,
				   BLCKSZ);
			/* We don't worry about zeroing the "hole" in this case */
			MarkBufferDirty(pageData->buffer);
		}
		END_CRIT_SECTION();
		/* We don't have a LSN to return, in this case */
		lsn = InvalidXLogRecPtr;
	}

	pfree(state);

	return lsn;
}

/*
 * Abort generic xlog record construction.  No changes are applied to buffers.
 *
 * Note: caller is responsible for releasing locks/pins on buffers, if needed.
 */
/*
 * 中文注释：
 * 放弃构造：释放 GenericXLogState，不对任何真实 buffer 应用修改。
 *
 * 因为所有修改都发生在页镜像副本上，Abort 只需 pfree(state) 即可；它不进入
 * critical section，也不会清理 buffer 的 pin/锁——按约定这些由调用者负责释放。
 * 错误退出路径可以直接调用本函数，无需担心留下半完成的页修改。
 */
void
GenericXLogAbort(GenericXLogState *state)
{
	pfree(state);
}

/*
 * Apply delta to given page image.
 */
/*
 * 中文注释：
 * 把一段编码好的 delta 应用到给定页镜像上。
 *
 * delta 是若干 fragment 的顺序拼接，每个 fragment 为：
 *   OffsetNumber offset; OffsetNumber length; char data[length];
 * 函数从头到尾解析，逐个 memcpy 到 page + offset，直到消费完 deltaSize 字节。
 * deltaSize 为 0 时是空操作（例如 FULL_IMAGE 记录没有附加 delta）。
 *
 * 该函数被 generic_redo（恢复）和 computeDelta 的 WAL_DEBUG 自检共用。它信任
 * WAL 内容的合法性，不做边界检查；调用者必须保证 page 至少有 BLCKSZ 字节、
 * delta 格式正确。函数只访问传入的内存，不涉及共享缓冲区或锁。
 */
static void
applyPageRedo(Page page, const char *delta, Size deltaSize)
{
	const char *ptr = delta;
	const char *end = delta + deltaSize;

	while (ptr < end)
	{
		OffsetNumber offset,
					length;

		memcpy(&offset, ptr, sizeof(offset));
		ptr += sizeof(offset);
		memcpy(&length, ptr, sizeof(length));
		ptr += sizeof(length);

		memcpy(page + offset, ptr, length);

		ptr += length;
	}
}

/*
 * Redo function for generic xlog record.
 */
/*
 * 中文注释：
 * RM_GENERIC_ID 的 redo 回调，重放一条 generic WAL 记录。
 *
 * 记录中的每个 block reference 对应一个被修改的页，block_id 从 0 开始连续编号
 * （GenericXLogFinish 直接用 pages[] 的下标注册）。处理流程：
 *   1. Assert 最大 block_id < MAX_GENERIC_XLOG_PAGES，防止 buffers[] 越界；
 *   2. 对每个 block_id：没有 block reference 则记为 InvalidBuffer；否则调用
 *      XLogReadBufferForRedo 读取并以排他模式锁定目标页，返回动作可能是
 *      BLK_NEEDS_REDO（需要应用 delta）、BLK_DONE（页已是最新）或 BLK_RESTORED
 *      （已从 full-page image 恢复）；
 *   3. 仅在 BLK_NEEDS_REDO 时取 block data 作为 delta，调用 applyPageRedo
 *      应用；随后把 pd_lower..pd_upper 的空洞清零，保证与主库 Finish 时的页
 *      状态一致；再设置页 LSN 并 MarkBufferDirty；
 *   4. 最后按 block_id 升序 UnlockReleaseBuffer，释放所有仍持有的 buffer。
 *
 * 并发注意：XLogReadBufferForRedo 会按 block_id 顺序获取排他锁，因此主库注册
 * buffer 的顺序必须与恢复时的加锁顺序一致，避免死锁。恢复过程逐条重放记录，
 * 不同记录之间不会并发执行；本函数不写 WAL。
 */
void
generic_redo(XLogReaderState *record)
{
	XLogRecPtr	lsn = record->EndRecPtr;
	Buffer		buffers[MAX_GENERIC_XLOG_PAGES];
	uint8		block_id;

	/* Protect limited size of buffers[] array */
	Assert(XLogRecMaxBlockId(record) < MAX_GENERIC_XLOG_PAGES);

	/* Iterate over blocks */
	for (block_id = 0; block_id <= XLogRecMaxBlockId(record); block_id++)
	{
		XLogRedoAction action;

		if (!XLogRecHasBlockRef(record, block_id))
		{
			buffers[block_id] = InvalidBuffer;
			continue;
		}

		action = XLogReadBufferForRedo(record, block_id, &buffers[block_id]);

		/* Apply redo to given block if needed */
		if (action == BLK_NEEDS_REDO)
		{
			Page		page;
			PageHeader	pageHeader;
			char	   *blockDelta;
			Size		blockDeltaSize;

			page = BufferGetPage(buffers[block_id]);
			blockDelta = XLogRecGetBlockData(record, block_id, &blockDeltaSize);
			applyPageRedo(page, blockDelta, blockDeltaSize);

			/*
			 * Since the delta contains no information about what's in the
			 * "hole" between pd_lower and pd_upper, set that to zero to
			 * ensure we produce the same page state that application of the
			 * logged action by GenericXLogFinish did.
			 */
			pageHeader = (PageHeader) page;
			memset(page + pageHeader->pd_lower, 0,
				   pageHeader->pd_upper - pageHeader->pd_lower);

			PageSetLSN(page, lsn);
			MarkBufferDirty(buffers[block_id]);
		}
	}

	/* Changes are done: unlock and release all buffers */
	for (block_id = 0; block_id <= XLogRecMaxBlockId(record); block_id++)
	{
		if (BufferIsValid(buffers[block_id]))
			UnlockReleaseBuffer(buffers[block_id]);
	}
}

/*
 * Mask a generic page before performing consistency checks on it.
 */
/*
 * 中文注释：
 * 一致性检查用的页掩码函数，注册在 RmgrTable 的 rm_mask 槽位。
 *
 * 当 wal_consistency_checking 启用时，恢复会在应用每条记录前后比较页状态。
 * 由于 LSN、校验和以及 pd_lower..pd_upper 之间的空闲空间可能因并发或实现细节
 * 不同，必须先统一屏蔽：
 *   - mask_page_lsn_and_checksum：把 pd_lsn 和 pd_checksum 替换为掩码标记；
 *   - mask_unused_space：用掩码标记填充 pd_lower 到 pd_upper 的空洞。
 * 这样比较只关注真正的数据内容。page 是本地页副本，blkno 当前未使用；函数不加
 * 锁、不写 WAL，仅修改传入的内存。
 */
void
generic_mask(char *page, BlockNumber blkno)
{
	mask_page_lsn_and_checksum(page);

	mask_unused_space(page);
}
