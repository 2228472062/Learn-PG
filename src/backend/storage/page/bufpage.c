/*-------------------------------------------------------------------------
 *
 * bufpage.c
 *	  POSTGRES standard buffer page code.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 标准的"磁盘页(Page)"结构操作,是存储系统最
 * 底层的页格式代码。堆表(heap)、各类索引(btree/hash/gist 等)以及
 * 空闲空间映射(FSM)都复用同一套页布局与操作。
 *
 * 页布局(相关宏与字段定义见 src/include/storage/bufpage.h):
 * - 页头 PageHeaderData:含 pd_lsn(最近 WAL 记录位点)、pd_checksum、
 *   pd_flags(提示位与状态位)、pd_lower(行指针数组上界)、pd_upper
 *   (项数据区下界)、pd_special(特殊空间起点)、pd_pagesize_version、
 *   pd_prune_xid(可见性修剪相关的 xid);
 * - 行指针数组(ItemIdData,pd_linp):从页头之后(pd_lower)向上增长,
 *   每个行指针描述一项数据(偏移 lp_off、长度 lp_len、状态标志
 *   lp_flags),是访问页内数据的"索引项";
 * - 项数据区:位于 pd_upper 与 pd_special 之间,由 pd_upper 向页头
 *   方向增长,实际存放元组/索引项的数据;
 * - 特殊空间(special space):页尾,供索引 AM(如 btree 的页尾元数据)
 *   自由使用,pd_special 标记其起点。
 *
 * 本文件主要职责:
 * 1) 页的初始化(PageInit)与读盘后的完整性校验(PageIsVerified);
 * 2) 项的插入(PageAddItemExtended)、删除(PageIndexTupleDelete 系列)、
 *    覆盖(PageIndexTupleOverwrite);
 * 3) 碎片整理与压缩(PageRepairFragmentation、compactify_tuples、
 *    PageTruncateLinePointerArray);
 * 4) 空闲空间查询(PageGetFreeSpace 系列;注意堆表有 MaxHeapTuplesPerPage
 *    行指针上限的特殊约束,见 PageGetHeapFreeSpace);
 * 5) 临时页的创建与回写(PageGetTempPage 系列,供"在内存中改造一页后
 *    整页写回"的算法使用,如 btree 页分裂);
 * 6) 写盘前计算页校验和(PageSetChecksum),与 checksum.c 配合。
 *
 * 与相邻模块的关系:本文件不涉及缓冲池管理与加锁(调用者负责持有合适
 * 的缓冲锁);不直接写 WAL(调用者在修改页后自行记录);提示位(hint
 * bits)与可见性修剪(pruning)相关的页级操作通过 pd_flags / pd_prune_xid
 * 完成,相关宏同样在 bufpage.h。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/page/bufpage.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "access/itup.h"
#include "access/xlog.h"
#include "pgstat.h"
#include "storage/checksum.h"
#include "utils/memdebug.h"
#include "utils/memutils.h"


/* GUC 变量:ignore_checksum_failure(与 data_checksums 配套使用)。
 * 为 true 时,页校验和不匹配不再视为致命错误:读到的页仍会被接受,只
 * 记录告警(见 PageIsVerified 的 PIV_IGNORE_CHECKSUM_FAILURE 标志)。
 * 这是仅供紧急抢救数据用的危险开关,默认 false。 */
bool		ignore_checksum_failure = false;


/* ----------------------------------------------------------------
 *						Page support functions
 * ----------------------------------------------------------------
 */

/*
 * PageInit
 *      (中文)初始化一个空页(页头 + 空行指针数组 + 空项区)
 *
 * 【作用】把一片 pageSize 大小的内存初始化为可用的空页:整页清零,行
 * 指针数组下界 pd_lower 指向页头之后(即"零个行指针"),项数据上界
 * pd_upper 与特殊空间起点 pd_special 都指向页尾扣除 specialSize 的
 * 位置,页大小与布局版本号写入页头。凡是从零创建一页的地方都会调用它:
 * 新建文件页、FSM 页、索引页、临时页等。
 *
 * 【设计思想】
 * - 整页 MemSet 清零是刻意为之:使"未初始化字段"必然为零,而零值恰好
 *   是各字段的安全默认(pd_prune_xid = InvalidTransactionId、行指针均为
 *   未使用、pd_flags = 0 等),同时 PageIsNew(整页全零判定)对新页成立;
 * - 故意不在这里计算校验和:内存中的页会被频繁修改,写盘时由
 *   PageSetChecksum 统一计算,避免校验和反复失效;
 * - specialSize 按 MAXALIGN 对齐,保证特殊空间与项数据区的边界满足
 *   平台对齐要求,也保证 pd_special 本身对齐(多处代码依赖该不变量)。
 *
 * 【参数】
 *   page        —— 目标内存(通常是缓冲池中的一块 BLCKSZ 内存);
 *   pageSize    —— 页大小(当前必须等于 BLCKSZ);
 *   specialSize —— 页尾特殊空间的大小(索引 AM 用;堆页为 0)。
 * 【返回值】无。
 *
 * PageInit
 *		Initializes the contents of a page.
 *		Note that we don't calculate an initial checksum here; that's not done
 *		until it's time to write.
 */
void
PageInit(Page page, Size pageSize, Size specialSize)
{
	PageHeader	p = (PageHeader) page;

	specialSize = MAXALIGN(specialSize);

	Assert(pageSize == BLCKSZ);
	Assert(pageSize > specialSize + SizeOfPageHeaderData);

	/* Make sure all fields of page are zero, as well as unused space */
	MemSet(p, 0, pageSize);

	p->pd_flags = 0;
	p->pd_lower = SizeOfPageHeaderData;
	p->pd_upper = pageSize - specialSize;
	p->pd_special = pageSize - specialSize;
	PageSetPageSizeAndVersion(page, pageSize, PG_PAGE_LAYOUT_VERSION);
	/* p->pd_prune_xid = InvalidTransactionId;		done by above MemSet */
}


/*
 * PageIsVerified
 *      (中文)校验页头与校验和(页读入后的第一道完整性检查)
 *
 * 【作用】页从磁盘读入缓冲池时调用,以低代价检测"烂页":验证页头字段
 * 是否自洽(行指针数组上下界、特殊空间边界、标志位合法性),并在启用
 * data_checksums 时核验 CRC32C 校验和。目的是在"拿着错误行指针或错误
 * xid 继续操作、造成连锁破坏"之前拦住损坏页。
 *
 * 【设计思想】
 * 1. 全零页必须放行:虽然"故意扩展关系"的路径不会调用本函数,但存在
 *    扩展后崩溃、WAL 未落盘的场景——内核已把零页留在文件中,重启后
 *    零页就在那里。因此这里允许全零页通过,并约定各页访问宏把全零页
 *    视为"空页、无空闲空间",由后续 VACUUM 清理;若把零页当损坏,恢复
 *    后数据库可能连启动都困难;
 * 2. 校验和只对"非新页"计算,且计算期间 HOLD_INTERRUPTS,防止中断处理
 *    修改页内容造成误报(页内容在 I/O 期间不再被改,但保持防御性习惯);
 * 3. "页头自洽"与"校验和正确"是两套独立证据:页头自洽只是允许进缓冲池
 *    的门槛,后续使用仍可能暴露问题——这正是启用校验和的意义;
 * 4. flags 控制失败时的行为:PIV_LOG_WARNING/PIV_LOG_LOG 决定记录级别,
 *   PIV_IGNORE_CHECKSUM_FAILURE 允许校验失败但仍接受页(配合 GUC
 *   ignore_checksum_failure,供紧急恢复),PIV_ZERO_BUFFERS_ON_ERROR
 *   通知调用方出错缓冲区将被清零(防止带病页被写回);
 * 5. 输出参数 checksum_failure_p 让调用方在"整体判定通过"时也能统计
 *   校验失败次数(IGNORE 模式下函数可返回 true 但校验实际失败)。
 *
 * 【参数】
 *   page               —— 待检查的页;
 *   blkno              —— 该页的块号(参与校验和计算);
 *   flags              —— PIV_* 标志(见 bufpage.h,记录日志/忽略失败等);
 *   checksum_failure_p —— 输出参数(可空):是否发生了校验和不匹配。
 * 【返回值】页可安全放入缓冲池返回 true,否则返回 false。
 *
 * PageIsVerified
 *		Check that the page header and checksum (if any) appear valid.
 *
 * This is called when a page has just been read in from disk.  The idea is
 * to cheaply detect trashed pages before we go nuts following bogus line
 * pointers, testing invalid transaction identifiers, etc.
 *
 * It turns out to be necessary to allow zeroed pages here too.  Even though
 * this routine is *not* called when deliberately adding a page to a relation,
 * there are scenarios in which a zeroed page might be found in a table.
 * (Example: a backend extends a relation, then crashes before it can write
 * any WAL entry about the new page.  The kernel will already have the
 * zeroed page in the file, and it will stay that way after restart.)  So we
 * allow zeroed pages here, and are careful that the page access macros
 * treat such a page as empty and without free space.  Eventually, VACUUM
 * will clean up such a page and make it usable.
 *
 * If flag PIV_LOG_WARNING/PIV_LOG_LOG is set, a WARNING/LOG message is logged
 * in the event of a checksum failure.
 *
 * If flag PIV_IGNORE_CHECKSUM_FAILURE is set, checksum failures will cause a
 * message about the failure to be emitted, but will not cause
 * PageIsVerified() to return false.
 *
 * To allow the caller to report statistics about checksum failures,
 * *checksum_failure_p can be passed in. Note that there may be checksum
 * failures even if this function returns true, due to
 * PIV_IGNORE_CHECKSUM_FAILURE.
 */
bool
PageIsVerified(PageData *page, BlockNumber blkno, int flags, bool *checksum_failure_p)
{
	const PageHeaderData *p = (const PageHeaderData *) page;
	size_t	   *pagebytes;
	bool		checksum_failure = false;
	bool		header_sane = false;
	uint16		checksum = 0;

	if (checksum_failure_p)
		*checksum_failure_p = false;

	/*
	 * Don't verify page data unless the page passes basic non-zero test
	 */
	if (!PageIsNew(page))
	{
		/*
		 * There shouldn't be any check for interrupt calls happening in this
		 * codepath, but just to be on the safe side we hold interrupts since
		 * if they did happen the data checksum state could change during
		 * verifying checksums, which could lead to incorrect verification
		 * results.
		 */
		HOLD_INTERRUPTS();
		if (DataChecksumsNeedVerify())
		{
			checksum = pg_checksum_page(page, blkno);

			if (checksum != p->pd_checksum)
			{
				checksum_failure = true;
				if (checksum_failure_p)
					*checksum_failure_p = true;
			}
		}
		RESUME_INTERRUPTS();

		/*
		 * The following checks don't prove the header is correct, only that
		 * it looks sane enough to allow into the buffer pool. Later usage of
		 * the block can still reveal problems, which is why we offer the
		 * checksum option.
		 */
		if ((p->pd_flags & ~PD_VALID_FLAG_BITS) == 0 &&
			p->pd_lower <= p->pd_upper &&
			p->pd_upper <= p->pd_special &&
			p->pd_special <= BLCKSZ &&
			p->pd_special == MAXALIGN(p->pd_special))
			header_sane = true;

		if (header_sane && !checksum_failure)
			return true;
	}

	/* Check all-zeroes case */
	pagebytes = (size_t *) page;

	if (pg_memory_is_all_zeros(pagebytes, BLCKSZ))
		return true;

	/*
	 * Throw a WARNING/LOG, as instructed by PIV_LOG_*, if the checksum fails,
	 * but only after we've checked for the all-zeroes case.
	 */
	if (checksum_failure)
	{
		if ((flags & (PIV_LOG_WARNING | PIV_LOG_LOG)) != 0)
			ereport(flags & PIV_LOG_WARNING ? WARNING : LOG,
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("page verification failed, calculated checksum %u but expected %u%s",
							checksum, p->pd_checksum,
							(flags & PIV_ZERO_BUFFERS_ON_ERROR ? ", buffer will be zeroed" : ""))));

		if (header_sane && (flags & PIV_IGNORE_CHECKSUM_FAILURE))
			return true;
	}

	return false;
}


/*
 * PageAddItemExtended
 *      (中文)向页中添加一个数据项(通用插入函数,PageAddItem 的底层实现)
 *
 * 【作用】把 item 指向的 size 字节数据作为新项插入页中:选定一个行指针
 * 槽位(显式指定或自动查找空闲槽)、在项数据区从 pd_upper 处向下分配
 * 空间、写入行指针并更新页头边界。堆表与所有索引 AM 的"插入一行"最终
 * 都汇聚到这里。
 *
 * 【设计思想】
 * - offsetNumber 的语义分三种:InvalidOffsetNumber 表示"自动找第一个
 *   空闲行指针";指定槽 + PAI_OVERWRITE 表示覆盖写入指定槽(必须当前
 *   未使用,供索引 AM 原地重用行指针);指定槽但无 OVERWRITE 表示在数组
 *   中间插入、把后续行指针后移一位(needshuffle);
 * - 自动找槽时总是从数组头部扫起、优先最早的空闲槽:因为
 *   PageTruncateLinePointerArray 只能截掉"数组尾部连续的空闲行指针",
 *   若新项总往尾部放,行指针数组就永远缩不回去;
 * - PAI_IS_HEAP 强制行指针总数不超过 MaxHeapTuplesPerPage(堆表硬上限,
 *   见 PageGetHeapFreeSpace 的说明);
 * - 所有失败路径只发 WARNING 并返回 InvalidOffsetNumber,绝不抛 ERROR:
 *   空间不足等失败对调用者(插入路径)是可预期的,应当换页重试而不是
 *   中断事务;只有真正不可能的内部错误才允许 elog(见 !!! 注释);
 * - 计算新 lower/upper 用带符号 int,防止 alignedSize 大于 pd_upper 时
 *   无符号回绕导致"空间够"的误判。
 *
 * 【参数】
 *   page         —— 目标页;
 *   item         —— 要插入的数据;
 *   size         —— 数据长度;
 *   offsetNumber —— 指定行指针槽位(1 基)或 InvalidOffsetNumber;
 *   flags        —— PAI_OVERWRITE(覆盖指定槽)/ PAI_IS_HEAP(堆表约束)。
 * 【返回值】插入位置的行号(offsetNumber);失败返回 InvalidOffsetNumber。
 * 注意:页被修改后是否标脏、是否写 WAL 由调用者负责。
 *
 *	PageAddItemExtended
 *
 *	Add an item to a page.  Return value is the offset at which it was
 *	inserted, or InvalidOffsetNumber if the item is not inserted for any
 *	reason.  A WARNING is issued indicating the reason for the refusal.
 *
 *	offsetNumber must be either InvalidOffsetNumber to specify finding a
 *	free line pointer, or a value between FirstOffsetNumber and one past
 *	the last existing item, to specify using that particular line pointer.
 *
 *	If offsetNumber is valid and flag PAI_OVERWRITE is set, we just store
 *	the item at the specified offsetNumber, which must be either a
 *	currently-unused line pointer, or one past the last existing item.
 *
 *	If offsetNumber is valid and flag PAI_OVERWRITE is not set, insert
 *	the item at the specified offsetNumber, moving existing items later
 *	in the array to make room.
 *
 *	If offsetNumber is not valid, then assign a slot by finding the first
 *	one that is both unused and deallocated.
 *
 *	If flag PAI_IS_HEAP is set, we enforce that there can't be more than
 *	MaxHeapTuplesPerPage line pointers on the page.
 *
 *	!!! EREPORT(ERROR) IS DISALLOWED HERE !!!
 */
OffsetNumber
PageAddItemExtended(Page page,
					const void *item,
					Size size,
					OffsetNumber offsetNumber,
					int flags)
{
	PageHeader	phdr = (PageHeader) page;
	Size		alignedSize;
	int			lower;
	int			upper;
	ItemId		itemId;
	OffsetNumber limit;
	bool		needshuffle = false;

	/*
	 * Be wary about corrupted page pointers
	 */
	if (phdr->pd_lower < SizeOfPageHeaderData ||
		phdr->pd_lower > phdr->pd_upper ||
		phdr->pd_upper > phdr->pd_special ||
		phdr->pd_special > BLCKSZ)
		ereport(PANIC,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted page pointers: lower = %u, upper = %u, special = %u",
						phdr->pd_lower, phdr->pd_upper, phdr->pd_special)));

	/*
	 * Select offsetNumber to place the new item at
	 */
	limit = OffsetNumberNext(PageGetMaxOffsetNumber(page));

	/* was offsetNumber passed in? */
	if (OffsetNumberIsValid(offsetNumber))
	{
		/* yes, check it */
		if ((flags & PAI_OVERWRITE) != 0)
		{
			if (offsetNumber < limit)
			{
				itemId = PageGetItemId(page, offsetNumber);
				if (ItemIdIsUsed(itemId) || ItemIdHasStorage(itemId))
				{
					elog(WARNING, "will not overwrite a used ItemId");
					return InvalidOffsetNumber;
				}
			}
		}
		else
		{
			if (offsetNumber < limit)
				needshuffle = true; /* need to move existing linp's */
		}
	}
	else
	{
		/* offsetNumber was not passed in, so find a free slot */
		/* if no free slot, we'll put it at limit (1st open slot) */
		if (PageHasFreeLinePointers(page))
		{
			/*
			 * Scan line pointer array to locate a "recyclable" (unused)
			 * ItemId.
			 *
			 * Always use earlier items first.  PageTruncateLinePointerArray
			 * can only truncate unused items when they appear as a contiguous
			 * group at the end of the line pointer array.
			 */
			for (offsetNumber = FirstOffsetNumber;
				 offsetNumber < limit;	/* limit is maxoff+1 */
				 offsetNumber++)
			{
				itemId = PageGetItemId(page, offsetNumber);

				/*
				 * We check for no storage as well, just to be paranoid;
				 * unused items should never have storage.  Assert() that the
				 * invariant is respected too.
				 */
				Assert(ItemIdIsUsed(itemId) || !ItemIdHasStorage(itemId));

				if (!ItemIdIsUsed(itemId) && !ItemIdHasStorage(itemId))
					break;
			}
			if (offsetNumber >= limit)
			{
				/* the hint is wrong, so reset it */
				PageClearHasFreeLinePointers(page);
			}
		}
		else
		{
			/* don't bother searching if hint says there's no free slot */
			offsetNumber = limit;
		}
	}

	/* Reject placing items beyond the first unused line pointer */
	if (offsetNumber > limit)
	{
		elog(WARNING, "specified item offset is too large");
		return InvalidOffsetNumber;
	}

	/* Reject placing items beyond heap boundary, if heap */
	if ((flags & PAI_IS_HEAP) != 0 && offsetNumber > MaxHeapTuplesPerPage)
	{
		elog(WARNING, "can't put more than MaxHeapTuplesPerPage items in a heap page");
		return InvalidOffsetNumber;
	}

	/*
	 * Compute new lower and upper pointers for page, see if it'll fit.
	 *
	 * Note: do arithmetic as signed ints, to avoid mistakes if, say,
	 * alignedSize > pd_upper.
	 */
	if (offsetNumber == limit || needshuffle)
		lower = phdr->pd_lower + sizeof(ItemIdData);
	else
		lower = phdr->pd_lower;

	alignedSize = MAXALIGN(size);

	upper = (int) phdr->pd_upper - (int) alignedSize;

	if (lower > upper)
		return InvalidOffsetNumber;

	/*
	 * OK to insert the item.  First, shuffle the existing pointers if needed.
	 */
	itemId = PageGetItemId(page, offsetNumber);

	if (needshuffle)
		memmove(itemId + 1, itemId,
				(limit - offsetNumber) * sizeof(ItemIdData));

	/* set the line pointer */
	ItemIdSetNormal(itemId, upper, size);

	/*
	 * Items normally contain no uninitialized bytes.  Core bufpage consumers
	 * conform, but this is not a necessary coding rule; a new index AM could
	 * opt to depart from it.  However, data type input functions and other
	 * C-language functions that synthesize datums should initialize all
	 * bytes; datumIsEqual() relies on this.  Testing here, along with the
	 * similar check in printtup(), helps to catch such mistakes.
	 *
	 * Values of the "name" type retrieved via index-only scans may contain
	 * uninitialized bytes; see comment in btrescan().  Valgrind will report
	 * this as an error, but it is safe to ignore.
	 */
	VALGRIND_CHECK_MEM_IS_DEFINED(item, size);

	/* copy the item's data onto the page */
	memcpy((char *) page + upper, item, size);

	/* adjust page header */
	phdr->pd_lower = (LocationIndex) lower;
	phdr->pd_upper = (LocationIndex) upper;

	return offsetNumber;
}


/*
 * PageGetTempPage
 *      (中文)申请一块"临时页"内存(内容未初始化)
 *
 * 【作用】按给定页的页大小在内存中分配一块页内存,供"离线改造一页"
 * 的算法使用。返回的页内容未定义,调用者必须自行初始化(通常接着调用
 * PageInit 或整页复制)。
 *
 * 【设计思想】某些操作(如 btree 页分裂、堆 HOT 链处理)不便在原页上
 * 就地修改——尤其是需要同时看到"改造前、改造后两版"时。经典做法:
 * 先用本函数(或 Copy / CopySpecial 变体)建一份内存副本,在副本上改,
 * 最后用 PageRestoreTempPage 整页拷回并释放临时页。注意页大小可能
 * 不是标准 BLCKSZ(特殊构造的页),因此用 PageGetPageSize 读取。
 *
 * 【参数】page —— 参考页(只取它的页大小)。
 * 【返回值】palloc 分配的内存页;内容未初始化。
 *
 * PageGetTempPage
 *		Get a temporary page in local memory for special processing.
 *		The returned page is not initialized at all; caller must do that.
 */
Page
PageGetTempPage(const PageData *page)
{
	Size		pageSize;
	Page		temp;

	pageSize = PageGetPageSize(page);
	temp = (Page) palloc(pageSize);

	return temp;
}

/*
 * PageGetTempPageCopy
 *      (中文)创建给定页的内存副本(内容逐字节相同)
 *
 * 【作用】分配一块与给定页同大小的内存并完整拷贝其内容,得到一份
 * "改造用的工作副本"。与 PageGetTempPage 的区别仅在于初始化方式:
 * 前者留给调用者初始化,本函数直接复制原页。
 *
 * 【参数】page —— 被复制的源页。
 * 【返回值】内容与源页一致的内存副本。
 *
 * PageGetTempPageCopy
 *		Get a temporary page in local memory for special processing.
 *		The page is initialized by copying the contents of the given page.
 */
Page
PageGetTempPageCopy(const PageData *page)
{
	Size		pageSize;
	Page		temp;

	pageSize = PageGetPageSize(page);
	temp = (Page) palloc(pageSize);

	memcpy(temp, page, pageSize);

	return temp;
}

/*
 * PageGetTempPageCopySpecial
 *      (中文)创建给定页的"特殊空间副本"
 *
 * 【作用】分配临时页:先用与源页相同的特殊空间大小 PageInit 成空页,
 * 再把源页特殊空间的内容整段拷贝过来,得到"结构与特殊空间完整、但行
 * 指针与数据区全空"的页。
 *
 * 【设计思想】某些索引 AM(如 btree)的页尾特殊空间保存本页的布局元
 * 信息(如右兄弟指针、页级空闲汇总等),复制页时这些元信息必须保留,
 * 而行指针/项数据通常要重建。本函数正好提供"保留特殊空间、清空主体"
 * 的模板页,比 PageGetTempPageCopy 省去"先拷全部、再删主体"的冗余。
 *
 * 【参数】page —— 源页。
 * 【返回值】初始化完成的临时页。
 *
 * PageGetTempPageCopySpecial
 *		Get a temporary page in local memory for special processing.
 *		The page is PageInit'd with the same special-space size as the
 *		given page, and the special space is copied from the given page.
 */
Page
PageGetTempPageCopySpecial(const PageData *page)
{
	Size		pageSize;
	Page		temp;

	pageSize = PageGetPageSize(page);
	temp = (Page) palloc(pageSize);

	PageInit(temp, pageSize, PageGetSpecialSize(page));
	memcpy(PageGetSpecialPointer(temp),
		   PageGetSpecialPointer(page),
		   PageGetSpecialSize(page));

	return temp;
}

/*
 * PageRestoreTempPage
 *      (中文)把临时页拷回原页并释放临时页
 *
 * 【作用】PageGetTempPage 系列函数的收尾:把改造完成的 tempPage 的
 * 全部内容拷回 oldPage(目标缓冲区的页),然后 pfree 释放临时页。
 *
 * 【设计思想】"临时页工作流"的完整闭环:GetTempPage(建副本)→ 修改
 * → RestoreTempPage(提交回原页)。调用者应已持有原页缓冲区的排他锁,
 * 拷贝完成后整页内容一次性可见、WAL 与脏标记由调用者处理。页大小以
 * tempPage 为准,保证与拷贝源一致(拷贝方向固定,避免调用者传错顺序
 * 造成越界)。
 *
 * 【参数】
 *   tempPage —— 临时页(被拷贝且随后释放);
 *   oldPage  —— 目标页(内容被覆盖)。
 * 【返回值】无。
 *
 * PageRestoreTempPage
 *		Copy temporary page back to permanent page after special processing
 *		and release the temporary page.
 */
void
PageRestoreTempPage(Page tempPage, Page oldPage)
{
	Size		pageSize;

	pageSize = PageGetPageSize(tempPage);
	memcpy(oldPage, tempPage, pageSize);

	pfree(tempPage);
}

/*
 * itemIdCompactData
 *      (中文)碎片整理的工作记录结构(供 PageRepairFragmentation /
 *      PageIndexMultiDelete / compactify_tuples 使用)
 *
 * 【作用】把"页上需要保留的项"的摘要信息压缩成定长记录数组:每项一条,
 * 描述其行指针在数组中的下标(offsetindex)、项数据在页内的起始偏移
 * (itemoff)和对齐后的长度(alignedlen)。整理时只操作这个轻量数组,
 * 最后统一搬运数据。
 *
 * 【设计思想】页整理需要"重新排列"页内所有项:先扫描行指针数组收集
 * 存活项,再按新布局搬移数据。为避免搬移过程中反复解析行指针(取偏移、
 * 取长度、反复对齐),先压缩成定长记录;alignedlen 预先存 MAXALIGN 后
 * 的长度,使搬移与目标位置计算无需重复对齐。itemoff 同时被用于
 * "是否已有序(presorted)"的判定与搬移源地址计算。
 */
typedef struct itemIdCompactData
{
	uint16		offsetindex;	/* linp array index */
	int16		itemoff;		/* page offset of item data */
	uint16		alignedlen;		/* MAXALIGN(item data len) */
} itemIdCompactData;
typedef itemIdCompactData *itemIdCompact;

/*
 * compactify_tuples
 *      (中文)把存活元组向页尾搬移,消除被删项留下的空洞(碎片整理核心)
 *
 * 【作用】在删除/标记若干项之后,按 itemidbase 数组(由调用者构造,只
 * 含存活项)把元组数据搬到页尾,并按"行号小的项更靠页尾"的规范重新排列,
 * 最后更新 pd_upper。这是 PageRepairFragmentation 与 PageIndexMultiDelete
 * 共同的核心,也是页面上最热门的代码路径之一(频繁更新的大表每次修剪
 * 都会走到)。
 *
 * 【设计思想】
 * 1. presorted 快速路径(itemidbase 已按 itemoff 降序——元组首次插入
 *    页时的天然顺序,更新型负载下也很常见):
 *    - 先用 memmove 只搬"需要搬的"部分:跳过页尾已经位于正确位置的
 *      连续元组,对剩余部分只在出现空洞(相邻元组之间有间隙)时做一次
 *      合并 memmove,memmove 调用次数降到最少;
 *    - 之所以可以放心 memmove:按 itemoff 降序处理,目标区(upper 之上)
 *      永远不与未搬的源区重叠。
 * 2. 非 presorted 路径(乱序):直接 memmove 可能覆盖尚未搬走的元组,
 *    必须先把要搬的元组复制进临时缓冲(PGAlignedBlock 栈上缓冲,8KB),
 *    再从缓冲按目标顺序 memcpy 回页:
 *    - 存活项很少(< 最大行号/4,即 75% 以上被删)时逐项拷入临时缓冲
 *      (此时页尾大概率没有可跳过的元组);
 *    - 否则只把"需要移动的那段"(phdr->pd_upper 到当前 upper 之间)
 *      一次性 memcpy 进临时缓冲。
 * 3. 无论哪个分支,搬完后元组都恢复成规范排列,下一次整理大概率命中
 *    presorted 快速路径——这个"自愈有序"的效果对频繁更新的表很重要;
 * 4. 行指针(ItemId)只改 lp_off 指向新位置,数组本身不动——数组的收缩
 *    由调用者另行处理(PageRepairFragmentation 截断、PageIndexMultiDelete
 *    用新数组覆盖)。
 *
 * 【参数】
 *   itemidbase —— 存活项摘要数组;
 *   nitems     —— 存活项个数(调用者必须保证 > 0);
 *   page       —— 目标页;
 *   presorted  —— 数组是否已按 itemoff 降序。
 * 【返回值】无(更新页内 pd_upper 与各 lp_off)。
 *
 * After removing or marking some line pointers unused, move the tuples to
 * remove the gaps caused by the removed items and reorder them back into
 * reverse line pointer order in the page.
 *
 * This function can often be fairly hot, so it pays to take some measures to
 * make it as optimal as possible.
 *
 * Callers may pass 'presorted' as true if the 'itemidbase' array is sorted in
 * descending order of itemoff.  When this is true we can just memmove()
 * tuples towards the end of the page.  This is quite a common case as it's
 * the order that tuples are initially inserted into pages.  When we call this
 * function to defragment the tuples in the page then any new line pointers
 * added to the page will keep that presorted order, so hitting this case is
 * still very common for tables that are commonly updated.
 *
 * When the 'itemidbase' array is not presorted then we're unable to just
 * memmove() tuples around freely.  Doing so could cause us to overwrite the
 * memory belonging to a tuple we've not moved yet.  In this case, we copy all
 * the tuples that need to be moved into a temporary buffer.  We can then
 * simply memcpy() out of that temp buffer back into the page at the correct
 * location.  Tuples are copied back into the page in the same order as the
 * 'itemidbase' array, so we end up reordering the tuples back into reverse
 * line pointer order.  This will increase the chances of hitting the
 * presorted case the next time around.
 *
 * Callers must ensure that nitems is > 0
 */
static void
compactify_tuples(itemIdCompact itemidbase, int nitems, Page page, bool presorted)
{
	PageHeader	phdr = (PageHeader) page;
	Offset		upper;
	Offset		copy_tail;
	Offset		copy_head;
	itemIdCompact itemidptr;
	int			i;

	/* Code within will not work correctly if nitems == 0 */
	Assert(nitems > 0);

	if (presorted)
	{

#ifdef USE_ASSERT_CHECKING
		{
			/*
			 * Verify we've not gotten any new callers that are incorrectly
			 * passing a true presorted value.
			 */
			Offset		lastoff = phdr->pd_special;

			for (i = 0; i < nitems; i++)
			{
				itemidptr = &itemidbase[i];

				Assert(lastoff > itemidptr->itemoff);

				lastoff = itemidptr->itemoff;
			}
		}
#endif							/* USE_ASSERT_CHECKING */

		/*
		 * 'itemidbase' is already in the optimal order, i.e, lower item
		 * pointers have a higher offset.  This allows us to memmove() the
		 * tuples up to the end of the page without having to worry about
		 * overwriting other tuples that have not been moved yet.
		 *
		 * There's a good chance that there are tuples already right at the
		 * end of the page that we can simply skip over because they're
		 * already in the correct location within the page.  We'll do that
		 * first...
		 */
		upper = phdr->pd_special;
		i = 0;
		do
		{
			itemidptr = &itemidbase[i];
			if (upper != itemidptr->itemoff + itemidptr->alignedlen)
				break;
			upper -= itemidptr->alignedlen;

			i++;
		} while (i < nitems);

		/*
		 * Now that we've found the first tuple that needs to be moved, we can
		 * do the tuple compactification.  We try and make the least number of
		 * memmove() calls and only call memmove() when there's a gap.  When
		 * we see a gap we just move all tuples after the gap up until the
		 * point of the last move operation.
		 */
		copy_tail = copy_head = itemidptr->itemoff + itemidptr->alignedlen;
		for (; i < nitems; i++)
		{
			ItemId		lp;

			itemidptr = &itemidbase[i];
			lp = PageGetItemId(page, itemidptr->offsetindex + 1);

			if (copy_head != itemidptr->itemoff + itemidptr->alignedlen)
			{
				memmove((char *) page + upper,
						page + copy_head,
						copy_tail - copy_head);

				/*
				 * We've now moved all tuples already seen, but not the
				 * current tuple, so we set the copy_tail to the end of this
				 * tuple so it can be moved in another iteration of the loop.
				 */
				copy_tail = itemidptr->itemoff + itemidptr->alignedlen;
			}
			/* shift the target offset down by the length of this tuple */
			upper -= itemidptr->alignedlen;
			/* point the copy_head to the start of this tuple */
			copy_head = itemidptr->itemoff;

			/* update the line pointer to reference the new offset */
			lp->lp_off = upper;
		}

		/* move the remaining tuples. */
		memmove((char *) page + upper,
				page + copy_head,
				copy_tail - copy_head);
	}
	else
	{
		PGAlignedBlock scratch;
		char	   *scratchptr = scratch.data;

		/*
		 * Non-presorted case:  The tuples in the itemidbase array may be in
		 * any order.  So, in order to move these to the end of the page we
		 * must make a temp copy of each tuple that needs to be moved before
		 * we copy them back into the page at the new offset.
		 *
		 * If a large percentage of tuples have been pruned (>75%) then we'll
		 * copy these into the temp buffer tuple-by-tuple, otherwise, we'll
		 * just do a single memcpy() for all tuples that need to be moved.
		 * When so many tuples have been removed there's likely to be a lot of
		 * gaps and it's unlikely that many non-movable tuples remain at the
		 * end of the page.
		 */
		if (nitems < PageGetMaxOffsetNumber(page) / 4)
		{
			i = 0;
			do
			{
				itemidptr = &itemidbase[i];
				memcpy(scratchptr + itemidptr->itemoff, page + itemidptr->itemoff,
					   itemidptr->alignedlen);
				i++;
			} while (i < nitems);

			/* Set things up for the compactification code below */
			i = 0;
			itemidptr = &itemidbase[0];
			upper = phdr->pd_special;
		}
		else
		{
			upper = phdr->pd_special;

			/*
			 * Many tuples are likely to already be in the correct location.
			 * There's no need to copy these into the temp buffer.  Instead
			 * we'll just skip forward in the itemidbase array to the position
			 * that we do need to move tuples from so that the code below just
			 * leaves these ones alone.
			 */
			i = 0;
			do
			{
				itemidptr = &itemidbase[i];
				if (upper != itemidptr->itemoff + itemidptr->alignedlen)
					break;
				upper -= itemidptr->alignedlen;

				i++;
			} while (i < nitems);

			/* Copy all tuples that need to be moved into the temp buffer */
			memcpy(scratchptr + phdr->pd_upper,
				   page + phdr->pd_upper,
				   upper - phdr->pd_upper);
		}

		/*
		 * Do the tuple compactification.  itemidptr is already pointing to
		 * the first tuple that we're going to move.  Here we collapse the
		 * memcpy calls for adjacent tuples into a single call.  This is done
		 * by delaying the memcpy call until we find a gap that needs to be
		 * closed.
		 */
		copy_tail = copy_head = itemidptr->itemoff + itemidptr->alignedlen;
		for (; i < nitems; i++)
		{
			ItemId		lp;

			itemidptr = &itemidbase[i];
			lp = PageGetItemId(page, itemidptr->offsetindex + 1);

			/* copy pending tuples when we detect a gap */
			if (copy_head != itemidptr->itemoff + itemidptr->alignedlen)
			{
				memcpy((char *) page + upper,
					   scratchptr + copy_head,
					   copy_tail - copy_head);

				/*
				 * We've now copied all tuples already seen, but not the
				 * current tuple, so we set the copy_tail to the end of this
				 * tuple.
				 */
				copy_tail = itemidptr->itemoff + itemidptr->alignedlen;
			}
			/* shift the target offset down by the length of this tuple */
			upper -= itemidptr->alignedlen;
			/* point the copy_head to the start of this tuple */
			copy_head = itemidptr->itemoff;

			/* update the line pointer to reference the new offset */
			lp->lp_off = upper;
		}

		/* Copy the remaining chunk */
		memcpy((char *) page + upper,
			   scratchptr + copy_head,
			   copy_tail - copy_head);
	}

	phdr->pd_upper = upper;
}

/*
 * PageRepairFragmentation
 *      (中文)整理堆页碎片:把项压缩到页尾并截断行指针数组(修剪之后)
 *
 * 【作用】在堆页的可见性修剪(pruning)删除一批死元组(尤其是 HOT 链
 * 中多个死元组)之后调用:把存活元组压缩到页尾消除空洞,并截掉行指针
 * 数组尾部的连续未使用项,把空间归还给后续插入。
 *
 * 【设计思想】
 * - 只适用于堆页(索引页用 PageIndexMultiDelete);调用者必须持有页缓冲
 *   的 cleanup lock——本函数允许在持该锁期间清除 LP_DEAD 等位;
 * - 因为要重新摆布(通常是共享缓冲池中的)页内数据,这里比别处更偏执
 *   地校验页头与每个行指针(偏移/长度/对齐),防止损坏指针把破坏扩散
 *   到相邻缓冲区;
 * - 扫描时顺带完成三件事:统计未使用行指针数、记录"最后一个被使用的
 *   行指针"(finalusedlp,决定数组截断点)、判断项是否天然有序
 *   (presorted,决定 compactify_tuples 是否走快速路径);
 * - 截断后调整 pd_lower,并把 PD_HAS_FREE_LINES 提示位设置/清除:
 *   PageAddItemExtended 依赖该位跳过"扫描找空闲行指针"的昂贵步骤;
 * - 页完全为空时直接重置 pd_upper = pd_special,免去搬移。
 *
 * 【参数】page —— 目标堆页。
 * 【返回值】无。副作用:pd_upper、pd_lower、提示位变化;调用者需要
 * 处理"行指针数组变短"带来的影响(如 HOT 链根指针编号)。
 *
 * PageRepairFragmentation
 *
 * Frees fragmented space on a heap page following pruning.
 *
 * This routine is usable for heap pages only, but see PageIndexMultiDelete.
 *
 * This routine removes unused line pointers from the end of the line pointer
 * array.  This is possible when dead heap-only tuples get removed by pruning,
 * especially when there were HOT chains with several tuples each beforehand.
 *
 * Caller had better have a full cleanup lock on page's buffer.  As a side
 * effect the page's PD_HAS_FREE_LINES hint bit will be set or unset as
 * needed.  Caller might also need to account for a reduction in the length of
 * the line pointer array following array truncation.
 */
void
PageRepairFragmentation(Page page)
{
	Offset		pd_lower = ((PageHeader) page)->pd_lower;
	Offset		pd_upper = ((PageHeader) page)->pd_upper;
	Offset		pd_special = ((PageHeader) page)->pd_special;
	Offset		last_offset;
	itemIdCompactData itemidbase[MaxHeapTuplesPerPage];
	itemIdCompact itemidptr;
	ItemId		lp;
	int			nline,
				nstorage,
				nunused;
	OffsetNumber finalusedlp = InvalidOffsetNumber;
	int			i;
	Size		totallen;
	bool		presorted = true;	/* For now */

	/*
	 * It's worth the trouble to be more paranoid here than in most places,
	 * because we are about to reshuffle data in (what is usually) a shared
	 * disk buffer.  If we aren't careful then corrupted pointers, lengths,
	 * etc could cause us to clobber adjacent disk buffers, spreading the data
	 * loss further.  So, check everything.
	 */
	if (pd_lower < SizeOfPageHeaderData ||
		pd_lower > pd_upper ||
		pd_upper > pd_special ||
		pd_special > BLCKSZ ||
		pd_special != MAXALIGN(pd_special))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted page pointers: lower = %u, upper = %u, special = %u",
						pd_lower, pd_upper, pd_special)));

	/*
	 * Run through the line pointer array and collect data about live items.
	 */
	nline = PageGetMaxOffsetNumber(page);
	itemidptr = itemidbase;
	nunused = totallen = 0;
	last_offset = pd_special;
	for (i = FirstOffsetNumber; i <= nline; i++)
	{
		lp = PageGetItemId(page, i);
		if (ItemIdIsUsed(lp))
		{
			if (ItemIdHasStorage(lp))
			{
				itemidptr->offsetindex = i - 1;
				itemidptr->itemoff = ItemIdGetOffset(lp);

				if (last_offset > itemidptr->itemoff)
					last_offset = itemidptr->itemoff;
				else
					presorted = false;

				if (unlikely(itemidptr->itemoff < (int) pd_upper ||
							 itemidptr->itemoff >= (int) pd_special))
					ereport(ERROR,
							(errcode(ERRCODE_DATA_CORRUPTED),
							 errmsg("corrupted line pointer: %u",
									itemidptr->itemoff)));
				itemidptr->alignedlen = MAXALIGN(ItemIdGetLength(lp));
				totallen += itemidptr->alignedlen;
				itemidptr++;
			}

			finalusedlp = i;	/* Could be the final non-LP_UNUSED item */
		}
		else
		{
			/* Unused entries should have lp_len = 0, but make sure */
			Assert(!ItemIdHasStorage(lp));
			ItemIdSetUnused(lp);
			nunused++;
		}
	}

	nstorage = itemidptr - itemidbase;
	if (nstorage == 0)
	{
		/* Page is completely empty, so just reset it quickly */
		((PageHeader) page)->pd_upper = pd_special;
	}
	else
	{
		/* Need to compact the page the hard way */
		if (totallen > (Size) (pd_special - pd_lower))
			ereport(ERROR,
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("corrupted item lengths: total %zu, available space %u",
							totallen, pd_special - pd_lower)));

		compactify_tuples(itemidbase, nstorage, page, presorted);
	}

	if (finalusedlp != nline)
	{
		/* The last line pointer is not the last used line pointer */
		int			nunusedend = nline - finalusedlp;

		Assert(nunused >= nunusedend && nunusedend > 0);

		/* remove trailing unused line pointers from the count */
		nunused -= nunusedend;
		/* truncate the line pointer array */
		((PageHeader) page)->pd_lower -= (sizeof(ItemIdData) * nunusedend);
	}

	/* Set hint bit for PageAddItemExtended */
	if (nunused > 0)
		PageSetHasFreeLinePointers(page);
	else
		PageClearHasFreeLinePointers(page);
}

/*
 * PageTruncateLinePointerArray
 *      (中文)仅截断行指针数组尾部的连续未使用项(VACUUM 第二趟专用)
 *
 * 【作用】VACUUM 第二趟扫描堆时调用:从数组尾部向前扫描,把连续的
 * LP_UNUSED 行指针从数组中删掉(pd_lower 下移),回收行指针占用的空间;
 * 若截断后数组前端仍残留未使用行指针,则设置 PD_HAS_FREE_LINES 提示位。
 *
 * 【设计思想】
 * - 与 PageRepairFragmentation 不同:本函数不搬移任何元组数据,只删
 *   行指针,因此调用者只需排他锁或 cleanup lock(不需要最高级锁);
 *   预期页上至少有一个刚被 VACUUM 置为 LP_UNUSED 的项,否则不应调用;
 * - 特意避免把行指针数组截到 0 个(必要时留下 1 个 LP_UNUSED):防止
 *   留下 PageIsEmpty() 的页——PageIsEmpty 是许多代码"页为空"的判据,
 *   空行指针数组会让"是否为空"的判断产生歧义;
 * - 扫描逻辑分两段:先(尾部)计数可截断的连续未使用项,遇到第一个
 *   使用中的项后停止计数,但继续向前找"前端是否还有未使用项",据此
 *   决定提示位的设置。
 *
 * 【参数】page —— 目标堆页。
 * 【返回值】无。
 *
 * PageTruncateLinePointerArray
 *
 * Removes unused line pointers at the end of the line pointer array.
 *
 * This routine is usable for heap pages only.  It is called by VACUUM during
 * its second pass over the heap.  We expect at least one LP_UNUSED line
 * pointer on the page (if VACUUM didn't have an LP_DEAD item on the page that
 * it just set to LP_UNUSED then it should not call here).
 *
 * We avoid truncating the line pointer array to 0 items, if necessary by
 * leaving behind a single remaining LP_UNUSED item.  This is a little
 * arbitrary, but it seems like a good idea to avoid leaving a PageIsEmpty()
 * page behind.
 *
 * Caller can have either an exclusive lock or a full cleanup lock on page's
 * buffer.  The page's PD_HAS_FREE_LINES hint bit will be set or unset based
 * on whether or not we leave behind any remaining LP_UNUSED items.
 */
void
PageTruncateLinePointerArray(Page page)
{
	PageHeader	phdr = (PageHeader) page;
	bool		countdone = false,
				sethint = false;
	int			nunusedend = 0;

	/* Scan line pointer array back-to-front */
	for (int i = PageGetMaxOffsetNumber(page); i >= FirstOffsetNumber; i--)
	{
		ItemId		lp = PageGetItemId(page, i);

		if (!countdone && i > FirstOffsetNumber)
		{
			/*
			 * Still determining which line pointers from the end of the array
			 * will be truncated away.  Either count another line pointer as
			 * safe to truncate, or notice that it's not safe to truncate
			 * additional line pointers (stop counting line pointers).
			 */
			if (!ItemIdIsUsed(lp))
				nunusedend++;
			else
				countdone = true;
		}
		else
		{
			/*
			 * Once we've stopped counting we still need to figure out if
			 * there are any remaining LP_UNUSED line pointers somewhere more
			 * towards the front of the array.
			 */
			if (!ItemIdIsUsed(lp))
			{
				/*
				 * This is an unused line pointer that we won't be truncating
				 * away -- so there is at least one.  Set hint on page.
				 */
				sethint = true;
				break;
			}
		}
	}

	if (nunusedend > 0)
	{
		phdr->pd_lower -= sizeof(ItemIdData) * nunusedend;

#ifdef CLOBBER_FREED_MEMORY
		memset((char *) page + phdr->pd_lower, 0x7F,
			   sizeof(ItemIdData) * nunusedend);
#endif
	}
	else
		Assert(sethint);

	/* Set hint bit for PageAddItemExtended */
	if (sethint)
		PageSetHasFreeLinePointers(page);
	else
		PageClearHasFreeLinePointers(page);
}

/*
 * PageGetFreeSpace
 *      (中文)返回页上可分配的空闲空间(已扣除一个新行指针的占用)
 *
 * 【作用】计算"还能容纳多少字节的新数据":pd_upper - pd_lower 再减去
 * 一个 ItemIdData 的大小——放新项必然还要新增一个行指针。通常用于
 * 索引页(堆页请用 PageGetHeapFreeSpace,它额外检查行指针上限)。
 *
 * 【设计思想】用带符号算术,使"页已满甚至 lower > upper(损坏/未初始
 * 化)"时得到负值并归一化为 0,而不是无符号回绕出巨大数值;减去的行
 * 指针大小正是 PageAddItemExtended 插入新项时的真实消耗,因此返回值
 * 与"能否成功插入一个 size 字节项"的判定严格一致。
 *
 * 【参数】page —— 目标页。
 * 【返回值】可分配字节数(不含行指针空间)。
 *
 * PageGetFreeSpace
 *		Returns the size of the free (allocatable) space on a page,
 *		reduced by the space needed for a new line pointer.
 *
 * Note: this should usually only be used on index pages.  Use
 * PageGetHeapFreeSpace on heap pages.
 */
Size
PageGetFreeSpace(const PageData *page)
{
	const PageHeaderData *phdr = (const PageHeaderData *) page;
	int			space;

	/*
	 * Use signed arithmetic here so that we behave sensibly if pd_lower >
	 * pd_upper.
	 */
	space = (int) phdr->pd_upper - (int) phdr->pd_lower;

	if (space < (int) sizeof(ItemIdData))
		return 0;
	space -= sizeof(ItemIdData);

	return (Size) space;
}

/*
 * PageGetFreeSpaceForMultipleTuples
 *      (中文)返回页上可分配的空闲空间(已扣除 ntups 个新行指针的占用)
 *
 * 【作用】PageGetFreeSpace 的批量版本:计算"一次性插入 ntups 个新项
 * 时总共还能容纳多少字节的数据",即 pd_upper - pd_lower 再减去
 * ntups 个 ItemIdData 的大小。索引 AM 预分配一批槽位(如 btree 批量
 * 分裂)时用它判断批量插入是否可行。
 *
 * 【设计思想】与 PageGetFreeSpace 相同的带符号算术与"不足则 0"策略,
 * 只是把行指针的占用按数量放大;调用方需保证 ntups >= 0。
 *
 * 【参数】
 *   page  —— 目标页;
 *   ntups —— 计划新增的行指针数量。
 * 【返回值】可分配字节数(不含行指针空间)。
 *
 * PageGetFreeSpaceForMultipleTuples
 *		Returns the size of the free (allocatable) space on a page,
 *		reduced by the space needed for multiple new line pointers.
 *
 * Note: this should usually only be used on index pages.  Use
 * PageGetHeapFreeSpace on heap pages.
 */
Size
PageGetFreeSpaceForMultipleTuples(const PageData *page, int ntups)
{
	const PageHeaderData *phdr = (const PageHeaderData *) page;
	int			space;

	/*
	 * Use signed arithmetic here so that we behave sensibly if pd_lower >
	 * pd_upper.
	 */
	space = (int) phdr->pd_upper - (int) phdr->pd_lower;

	if (space < (int) (ntups * sizeof(ItemIdData)))
		return 0;
	space -= ntups * sizeof(ItemIdData);

	return (Size) space;
}

/*
 * PageGetExactFreeSpace
 *      (中文)返回页上"原始"的空闲字节数(不考虑行指针)
 *
 * 【作用】直接返回 pd_upper - pd_lower 这一真实空白区间的大小,不
 * 扣除新增行指针的消耗。用于需要精确知道页上空隙的场景(如索引 AM
 * 判断现有空隙是否足够容纳一整块数据、评估压缩收益等)。
 *
 * 【设计思想】与 PageGetFreeSpace 的关系:后者是"实际可用的"、本函数
 * 是"几何上的"。负值(页已满或异常)同样归一化为 0,保证调用方拿到的
 * 一定是合法字节数。
 *
 * 【参数】page —— 目标页。
 * 【返回值】空闲字节数(>= 0)。
 *
 * PageGetExactFreeSpace
 *		Returns the size of the free (allocatable) space on a page,
 *		without any consideration for adding/removing line pointers.
 */
Size
PageGetExactFreeSpace(const PageData *page)
{
	const PageHeaderData *phdr = (const PageHeaderData *) page;
	int			space;

	/*
	 * Use signed arithmetic here so that we behave sensibly if pd_lower >
	 * pd_upper.
	 */
	space = (int) phdr->pd_upper - (int) phdr->pd_lower;

	if (space < 0)
		return 0;

	return (Size) space;
}


/*
 * PageGetHeapFreeSpace
 *      (中文)堆页专用空闲空间查询(额外强制 MaxHeapTuplesPerPage 行指针上限)
 *
 * 【作用】与 PageGetFreeSpace 同语义,但增加一条规则:若页上已有
 * MaxHeapTuplesPerPage 个行指针且没有空闲的,则返回 0——即使物理空间
 * 还够。这保证堆页的行指针数量永远不会突破该硬上限。
 *
 * 【设计思想】为什么需要这道额外检查:理论上页里放不下超过上限的元组,
 * 但在存在 LP_REDIRECT(重定向)或 LP_DEAD 行指针时,行指针数可能超过
 * 元组数;而大量代码假定 MaxHeapTuplesPerPage 是行指针数的绝对上限
 * (例如 PageRepairFragmentation 用固定大小数组 itemidbase 收集存活
 * 项)。因此这里宁可"报告空间不足",也绝不放行超限的行指针。
 *
 * 实现细节:"是否还有空闲行指针"用 PD_HAS_FREE_LINES 提示位判断,但
 * 该位可能过期:提示位为真时实地扫描确认;发现提示位失真时也只能保守
 * 返回 0——本函数不持锁、无权把页标脏,不能就地修正提示位。提示位为
 * 假时同样返回 0(PageAddItem 会相信该位,这里必须保持一致)。
 *
 * 【参数】page —— 目标堆页。
 * 【返回值】可分配字节数(受行指针上限约束)。
 *
 * PageGetHeapFreeSpace
 *		Returns the size of the free (allocatable) space on a page,
 *		reduced by the space needed for a new line pointer.
 *
 * The difference between this and PageGetFreeSpace is that this will return
 * zero if there are already MaxHeapTuplesPerPage line pointers in the page
 * and none are free.  We use this to enforce that no more than
 * MaxHeapTuplesPerPage line pointers are created on a heap page.  (Although
 * no more tuples than that could fit anyway, in the presence of redirected
 * or dead line pointers it'd be possible to have too many line pointers.
 * To avoid breaking code that assumes MaxHeapTuplesPerPage is a hard limit
 * on the number of line pointers, we make this extra check.)
 */
Size
PageGetHeapFreeSpace(const PageData *page)
{
	Size		space;

	space = PageGetFreeSpace(page);
	if (space > 0)
	{
		OffsetNumber offnum,
					nline;

		/*
		 * Are there already MaxHeapTuplesPerPage line pointers in the page?
		 */
		nline = PageGetMaxOffsetNumber(page);
		if (nline >= MaxHeapTuplesPerPage)
		{
			if (PageHasFreeLinePointers(page))
			{
				/*
				 * Since this is just a hint, we must confirm that there is
				 * indeed a free line pointer
				 */
				for (offnum = FirstOffsetNumber; offnum <= nline; offnum = OffsetNumberNext(offnum))
				{
					ItemId		lp = PageGetItemId(unconstify(PageData *, page), offnum);

					if (!ItemIdIsUsed(lp))
						break;
				}

				if (offnum > nline)
				{
					/*
					 * The hint is wrong, but we can't clear it here since we
					 * don't have the ability to mark the page dirty.
					 */
					space = 0;
				}
			}
			else
			{
				/*
				 * Although the hint might be wrong, PageAddItem will believe
				 * it anyway, so we must believe it too.
				 */
				space = 0;
			}
		}
	}
	return space;
}


/*
 * PageIndexTupleDelete
 *      (中文)从索引页删除一个元组(行指针与数据一起压缩掉)
 *
 * 【作用】删除索引页中 offnum 指定的元组:把行指针数组从该位置起整体
 * 前移一位(被删项的行指针被移除)、把被删元组"之后"的数据向前搬 size
 * 字节补齐空洞,最后更新 pd_lower / pd_upper,并修正所有受影响行指针
 * 的偏移。
 *
 * 【设计思想】
 * - 与堆页不同,索引页删除时"彻底移除行指针"而不是置 LP_UNUSED:
 *   索引不需要保持 TID 不变(需要时用 PageIndexTupleDeleteNoCompact),
 *   压缩掉行指针能及时回收空间;
 * - 两个 memmove 各司其职、互不重叠:一个把行指针数组后段前移一格,
 *   另一个把"被删元组与页头之间的数据"(即元组数据区前段)向页头方向
 *   搬 size 字节。若被删元组恰好就是数据区第一项,后者跳过;
 * - 搬移后,所有"起始偏移 <= 被删元组偏移"的行指针都要加上 size,
 *   重新指向正确的数据(注意循环从 1 基行号开始,保证索引项本身也
 *   被修正或已消失);
 * - 入口处像 PageRepairFragmentation 一样做"偏执式"的页头/行指针
 *   校验,防止损坏页造成更大破坏。
 *
 * 【参数】
 *   page   —— 索引页;
 *   offnum —— 要删除的元组行号(1 基,须在 1..页内最大行号之间)。
 * 【返回值】无。
 *
 * PageIndexTupleDelete
 *
 * This routine does the work of removing a tuple from an index page.
 *
 * Unlike heap pages, we compact out the line pointer for the removed tuple.
 */
void
PageIndexTupleDelete(Page page, OffsetNumber offnum)
{
	PageHeader	phdr = (PageHeader) page;
	char	   *addr;
	ItemId		tup;
	Size		size;
	unsigned	offset;
	int			nbytes;
	int			offidx;
	int			nline;

	/*
	 * As with PageRepairFragmentation, paranoia seems justified.
	 */
	if (phdr->pd_lower < SizeOfPageHeaderData ||
		phdr->pd_lower > phdr->pd_upper ||
		phdr->pd_upper > phdr->pd_special ||
		phdr->pd_special > BLCKSZ ||
		phdr->pd_special != MAXALIGN(phdr->pd_special))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted page pointers: lower = %u, upper = %u, special = %u",
						phdr->pd_lower, phdr->pd_upper, phdr->pd_special)));

	nline = PageGetMaxOffsetNumber(page);
	if ((int) offnum <= 0 || (int) offnum > nline)
		elog(ERROR, "invalid index offnum: %u", offnum);

	/* change offset number to offset index */
	offidx = offnum - 1;

	tup = PageGetItemId(page, offnum);
	Assert(ItemIdHasStorage(tup));
	size = ItemIdGetLength(tup);
	offset = ItemIdGetOffset(tup);

	if (offset < phdr->pd_upper || (offset + size) > phdr->pd_special ||
		offset != MAXALIGN(offset))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted line pointer: offset = %u, size = %zu",
						offset, size)));

	/* Amount of space to actually be deleted */
	size = MAXALIGN(size);

	/*
	 * First, we want to get rid of the pd_linp entry for the index tuple. We
	 * copy all subsequent linp's back one slot in the array. We don't use
	 * PageGetItemId, because we are manipulating the _array_, not individual
	 * linp's.
	 */
	nbytes = phdr->pd_lower -
		((char *) &phdr->pd_linp[offidx + 1] - (char *) phdr);

	if (nbytes > 0)
		memmove(&(phdr->pd_linp[offidx]),
				&(phdr->pd_linp[offidx + 1]),
				nbytes);

	/*
	 * Now move everything between the old upper bound (beginning of tuple
	 * space) and the beginning of the deleted tuple forward, so that space in
	 * the middle of the page is left free.  If we've just deleted the tuple
	 * at the beginning of tuple space, then there's no need to do the copy.
	 */

	/* beginning of tuple space */
	addr = (char *) page + phdr->pd_upper;

	if (offset > phdr->pd_upper)
		memmove(addr + size, addr, offset - phdr->pd_upper);

	/* adjust free space boundary pointers */
	phdr->pd_upper += size;
	phdr->pd_lower -= sizeof(ItemIdData);

	/*
	 * Finally, we need to adjust the linp entries that remain.
	 *
	 * Anything that used to be before the deleted tuple's data was moved
	 * forward by the size of the deleted tuple.
	 */
	if (!PageIsEmpty(page))
	{
		int			i;

		nline--;				/* there's one less than when we started */
		for (i = 1; i <= nline; i++)
		{
			ItemId		ii = PageGetItemId(page, i);

			Assert(ItemIdHasStorage(ii));
			if (ItemIdGetOffset(ii) <= offset)
				ii->lp_off += size;
		}
	}
}


/*
 * PageIndexMultiDelete
 *      (中文)从索引页一次性删除多个元组
 *
 * 【作用】按 itemnos 数组(必须升序!)删除页上多个元组,把剩余元组
 * 一次性"重排 + 压缩"完成,比循环调用 PageIndexTupleDelete 快得多
 * (b-tree 的 page cleanup 使用)。
 *
 * 【设计思想】
 * - 数量少(<= 2)时退回 PageIndexTupleDelete 循环(反向删除,避免行号
 *   漂移),不为小删除付出构建摘要数组的开销;
 * - 主路径分两遍:第一遍只读不改,把"要保留的元组"收集进 itemidbase
 *   摘要数组与全新的行指针数组 newitemids,同时完成全部合法性检查
 *   (行指针越界、itemnos 乱序/越界都会在此暴露);第二遍才真正动手:
 *   整段 memcpy 回行指针数组(自然消去被删项),再用 compactify_tuples
 *   压缩数据。这种"先验证、后提交"的两遍法保证检查失败时页保持原样,
 *   不会留下半改的脏状态;
 * - 一次性 memcpy + 一次压缩,总代价与元组数成正比,而逐个删除每次
 *   都要搬移后面全部数据,是 O(n^2) 的差别。
 *
 * 【参数】
 *   page    —— 索引页;
 *   itemnos —— 待删行号数组(必须按升序,调用者保证);
 *   nitems  —— 数组长度。
 * 【返回值】无。
 *
 * PageIndexMultiDelete
 *
 * This routine handles the case of deleting multiple tuples from an
 * index page at once.  It is considerably faster than a loop around
 * PageIndexTupleDelete ... however, the caller *must* supply the array
 * of item numbers to be deleted in item number order!
 */
void
PageIndexMultiDelete(Page page, OffsetNumber *itemnos, int nitems)
{
	PageHeader	phdr = (PageHeader) page;
	Offset		pd_lower = phdr->pd_lower;
	Offset		pd_upper = phdr->pd_upper;
	Offset		pd_special = phdr->pd_special;
	Offset		last_offset;
	itemIdCompactData itemidbase[MaxIndexTuplesPerPage];
	ItemIdData	newitemids[MaxIndexTuplesPerPage];
	itemIdCompact itemidptr;
	ItemId		lp;
	int			nline,
				nused;
	Size		totallen;
	Size		size;
	unsigned	offset;
	int			nextitm;
	OffsetNumber offnum;
	bool		presorted = true;	/* For now */

	Assert(nitems <= MaxIndexTuplesPerPage);

	/*
	 * If there aren't very many items to delete, then retail
	 * PageIndexTupleDelete is the best way.  Delete the items in reverse
	 * order so we don't have to think about adjusting item numbers for
	 * previous deletions.
	 *
	 * TODO: tune the magic number here
	 */
	if (nitems <= 2)
	{
		while (--nitems >= 0)
			PageIndexTupleDelete(page, itemnos[nitems]);
		return;
	}

	/*
	 * As with PageRepairFragmentation, paranoia seems justified.
	 */
	if (pd_lower < SizeOfPageHeaderData ||
		pd_lower > pd_upper ||
		pd_upper > pd_special ||
		pd_special > BLCKSZ ||
		pd_special != MAXALIGN(pd_special))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted page pointers: lower = %u, upper = %u, special = %u",
						pd_lower, pd_upper, pd_special)));

	/*
	 * Scan the line pointer array and build a list of just the ones we are
	 * going to keep.  Notice we do not modify the page yet, since we are
	 * still validity-checking.
	 */
	nline = PageGetMaxOffsetNumber(page);
	itemidptr = itemidbase;
	totallen = 0;
	nused = 0;
	nextitm = 0;
	last_offset = pd_special;
	for (offnum = FirstOffsetNumber; offnum <= nline; offnum = OffsetNumberNext(offnum))
	{
		lp = PageGetItemId(page, offnum);
		Assert(ItemIdHasStorage(lp));
		size = ItemIdGetLength(lp);
		offset = ItemIdGetOffset(lp);
		if (offset < pd_upper ||
			(offset + size) > pd_special ||
			offset != MAXALIGN(offset))
			ereport(ERROR,
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("corrupted line pointer: offset = %u, size = %zu",
							offset, size)));

		if (nextitm < nitems && offnum == itemnos[nextitm])
		{
			/* skip item to be deleted */
			nextitm++;
		}
		else
		{
			itemidptr->offsetindex = nused; /* where it will go */
			itemidptr->itemoff = offset;

			if (last_offset > itemidptr->itemoff)
				last_offset = itemidptr->itemoff;
			else
				presorted = false;

			itemidptr->alignedlen = MAXALIGN(size);
			totallen += itemidptr->alignedlen;
			newitemids[nused] = *lp;
			itemidptr++;
			nused++;
		}
	}

	/* this will catch invalid or out-of-order itemnos[] */
	if (nextitm != nitems)
		elog(ERROR, "incorrect index offsets supplied");

	if (totallen > (Size) (pd_special - pd_lower))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted item lengths: total %zu, available space %u",
						totallen, pd_special - pd_lower)));

	/*
	 * Looks good. Overwrite the line pointers with the copy, from which we've
	 * removed all the unused items.
	 */
	memcpy(phdr->pd_linp, newitemids, nused * sizeof(ItemIdData));
	phdr->pd_lower = SizeOfPageHeaderData + nused * sizeof(ItemIdData);

	/* and compactify the tuple data */
	if (nused > 0)
		compactify_tuples(itemidbase, nused, page, presorted);
	else
		phdr->pd_upper = pd_special;
}


/*
 * PageIndexTupleDeleteNoCompact
 *      (中文)删除索引元组但不压缩行指针(仅置 LP_UNUSED)
 *
 * 【作用】删除 offnum 指定的索引元组:数据区照常搬移回收,但行指针
 * 只在"它是数组最后一个"时才被删掉,否则只是标记为未使用,保留其在
 * 数组中的位置。
 *
 * 【设计思想】这是为"要求存活元组的 TID 永不变化"的索引 AM 准备的
 * (如某些允许 LP_DEAD 位存在的 AM):若删除时压缩行指针,后面所有项
 * 的行号都会变,可能破坏以 TID 为键的引用(如逻辑复制、索引扫描中的
 * 定位)。代价是未使用行指针可能累积,需靠后续整理回收;注意保留的
 * 行指针 lp_off 仍会被修正(数据已被搬走)。倒数第二个及以前的行指针
 * 即使本来已未使用,也不顺手压缩——刻意保持简单。
 *
 * 【参数】
 *   page   —— 索引页;
 *   offnum —— 要删除的元组行号。
 * 【返回值】无。
 *
 * PageIndexTupleDeleteNoCompact
 *
 * Remove the specified tuple from an index page, but set its line pointer
 * to "unused" instead of compacting it out, except that it can be removed
 * if it's the last line pointer on the page.
 *
 * This is used for index AMs that require that existing TIDs of live tuples
 * remain unchanged, and are willing to allow unused line pointers instead.
 */
void
PageIndexTupleDeleteNoCompact(Page page, OffsetNumber offnum)
{
	PageHeader	phdr = (PageHeader) page;
	char	   *addr;
	ItemId		tup;
	Size		size;
	unsigned	offset;
	int			nline;

	/*
	 * As with PageRepairFragmentation, paranoia seems justified.
	 */
	if (phdr->pd_lower < SizeOfPageHeaderData ||
		phdr->pd_lower > phdr->pd_upper ||
		phdr->pd_upper > phdr->pd_special ||
		phdr->pd_special > BLCKSZ ||
		phdr->pd_special != MAXALIGN(phdr->pd_special))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted page pointers: lower = %u, upper = %u, special = %u",
						phdr->pd_lower, phdr->pd_upper, phdr->pd_special)));

	nline = PageGetMaxOffsetNumber(page);
	if ((int) offnum <= 0 || (int) offnum > nline)
		elog(ERROR, "invalid index offnum: %u", offnum);

	tup = PageGetItemId(page, offnum);
	Assert(ItemIdHasStorage(tup));
	size = ItemIdGetLength(tup);
	offset = ItemIdGetOffset(tup);

	if (offset < phdr->pd_upper || (offset + size) > phdr->pd_special ||
		offset != MAXALIGN(offset))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted line pointer: offset = %u, size = %zu",
						offset, size)));

	/* Amount of space to actually be deleted */
	size = MAXALIGN(size);

	/*
	 * Either set the line pointer to "unused", or zap it if it's the last
	 * one.  (Note: it's possible that the next-to-last one(s) are already
	 * unused, but we do not trouble to try to compact them out if so.)
	 */
	if ((int) offnum < nline)
		ItemIdSetUnused(tup);
	else
	{
		phdr->pd_lower -= sizeof(ItemIdData);
		nline--;				/* there's one less than when we started */
	}

	/*
	 * Now move everything between the old upper bound (beginning of tuple
	 * space) and the beginning of the deleted tuple forward, so that space in
	 * the middle of the page is left free.  If we've just deleted the tuple
	 * at the beginning of tuple space, then there's no need to do the copy.
	 */

	/* beginning of tuple space */
	addr = (char *) page + phdr->pd_upper;

	if (offset > phdr->pd_upper)
		memmove(addr + size, addr, offset - phdr->pd_upper);

	/* adjust free space boundary pointer */
	phdr->pd_upper += size;

	/*
	 * Finally, we need to adjust the linp entries that remain.
	 *
	 * Anything that used to be before the deleted tuple's data was moved
	 * forward by the size of the deleted tuple.
	 */
	if (!PageIsEmpty(page))
	{
		int			i;

		for (i = 1; i <= nline; i++)
		{
			ItemId		ii = PageGetItemId(page, i);

			if (ItemIdHasStorage(ii) && ItemIdGetOffset(ii) <= offset)
				ii->lp_off += size;
		}
	}
}


/*
 * PageIndexTupleOverwrite
 *      (中文)原地替换索引页上的一个元组
 *
 * 【作用】用新元组 newtup 替换 offnum 处的旧元组:空间不够时返回 false,
 * 否则把旧元组"前面"的数据整体搬移(新元组更大则向前推、更小则向后
 * 让),把新元组写到旧元组的位置,同步更新行指针与 pd_upper。
 *
 * 【设计思想】
 * - 相比"先删后插",本函数:① 元组对齐尺寸不变时零搬移;② 即使尺寸
 *   变了也不动行指针数组——适合不希望触碰 LP_DEAD 位、或在乎元组
 *   物理顺序的索引 AM(如 BRIN 依赖无存储行指针的元数据);
 * - 搬移方向是"旧元组起点之前的整段数据"(页头与旧元组之间),size_diff
 *   定义为"旧对齐尺寸 - 新对齐尺寸",于是 pd_upper 与受影响行指针的
 *   修正统一为"加 size_diff",代码简洁;
 * - 行指针的 lp_off 更新为 offset + size_diff,lp_len 直接写新的未
 *   对齐长度 newsize,而 lp_flags 保持不变(这正是"不动 LP_DEAD"的
 *   诉求);
 * - 空间不足返回 false 而非报错,由调用者决定换页或抛错;其余异常
 *   (页损坏等)直接 ERROR。
 *
 * 【参数】
 *   page    —— 索引页;
 *   offnum  —— 被替换元组的行号;
 *   newtup  —— 新元组数据;
 *   newsize —— 新元组长度。
 * 【返回值】替换成功返回 true;空间不足返回 false;页损坏直接 ERROR。
 *
 * PageIndexTupleOverwrite
 *
 * Replace a specified tuple on an index page.
 *
 * The new tuple is placed exactly where the old one had been, shifting
 * other tuples' data up or down as needed to keep the page compacted.
 * This is better than deleting and reinserting the tuple, because it
 * avoids any data shifting when the tuple size doesn't change; and
 * even when it does, we avoid moving the line pointers around.
 * This could be used by an index AM that doesn't want to unset the
 * LP_DEAD bit when it happens to be set.  It could conceivably also be
 * used by an index AM that cares about the physical order of tuples as
 * well as their logical/ItemId order.
 *
 * If there's insufficient space for the new tuple, return false.  Other
 * errors represent data-corruption problems, so we just elog.
 */
bool
PageIndexTupleOverwrite(Page page, OffsetNumber offnum,
						const void *newtup, Size newsize)
{
	PageHeader	phdr = (PageHeader) page;
	ItemId		tupid;
	int			oldsize;
	unsigned	offset;
	Size		alignednewsize;
	int			size_diff;
	int			itemcount;

	/*
	 * As with PageRepairFragmentation, paranoia seems justified.
	 */
	if (phdr->pd_lower < SizeOfPageHeaderData ||
		phdr->pd_lower > phdr->pd_upper ||
		phdr->pd_upper > phdr->pd_special ||
		phdr->pd_special > BLCKSZ ||
		phdr->pd_special != MAXALIGN(phdr->pd_special))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted page pointers: lower = %u, upper = %u, special = %u",
						phdr->pd_lower, phdr->pd_upper, phdr->pd_special)));

	itemcount = PageGetMaxOffsetNumber(page);
	if ((int) offnum <= 0 || (int) offnum > itemcount)
		elog(ERROR, "invalid index offnum: %u", offnum);

	tupid = PageGetItemId(page, offnum);
	Assert(ItemIdHasStorage(tupid));
	oldsize = ItemIdGetLength(tupid);
	offset = ItemIdGetOffset(tupid);

	if (offset < phdr->pd_upper || (offset + oldsize) > phdr->pd_special ||
		offset != MAXALIGN(offset))
		ereport(ERROR,
				(errcode(ERRCODE_DATA_CORRUPTED),
				 errmsg("corrupted line pointer: offset = %u, size = %d",
						offset, oldsize)));

	/*
	 * Determine actual change in space requirement, check for page overflow.
	 */
	oldsize = MAXALIGN(oldsize);
	alignednewsize = MAXALIGN(newsize);
	if (alignednewsize > oldsize + (phdr->pd_upper - phdr->pd_lower))
		return false;

	/*
	 * Relocate existing data and update line pointers, unless the new tuple
	 * is the same size as the old (after alignment), in which case there's
	 * nothing to do.  Notice that what we have to relocate is data before the
	 * target tuple, not data after, so it's convenient to express size_diff
	 * as the amount by which the tuple's size is decreasing, making it the
	 * delta to add to pd_upper and affected line pointers.
	 */
	size_diff = oldsize - (int) alignednewsize;
	if (size_diff != 0)
	{
		char	   *addr = (char *) page + phdr->pd_upper;
		int			i;

		/* relocate all tuple data before the target tuple */
		memmove(addr + size_diff, addr, offset - phdr->pd_upper);

		/* adjust free space boundary pointer */
		phdr->pd_upper += size_diff;

		/* adjust affected line pointers too */
		for (i = FirstOffsetNumber; i <= itemcount; i++)
		{
			ItemId		ii = PageGetItemId(page, i);

			/* Allow items without storage; currently only BRIN needs that */
			if (ItemIdHasStorage(ii) && ItemIdGetOffset(ii) <= offset)
				ii->lp_off += size_diff;
		}
	}

	/* Update the item's tuple length without changing its lp_flags field */
	tupid->lp_off = offset + size_diff;
	tupid->lp_len = newsize;

	/* Copy new tuple data onto page */
	memcpy(PageGetItem(page, tupid), newtup, newsize);

	return true;
}


/*
 * PageSetChecksum
 *      (中文)为写盘前的页计算并写入校验和
 *
 * 【作用】页落盘前调用:若启用了 data_checksums 且页不是全零新页,
 * 计算 CRC32C 校验和并写入页头 pd_checksum 字段(读盘时由
 * PageIsVerified 用同一算法核验)。
 *
 * 【设计思想】
 * - 全零页(PageIsNew)不需要校验和:读盘路径对全零页本就跳过校验
 *   (见 PageIsVerified),写入端保持一致,避免对"还没初始化内容的页"
 *   算出一个可能误导的校验和;
 * - 历史上这里要求在页副本上计算,因为提示位(hint bits)可能被并发
 *   修改;如今 I/O 进行期间提示位不再被设置(数据一致性协议保证),因此
 *   可以放心就地计算;
 * - HOLD_INTERRUPTS 防止计算期间被中断打断,写出半算好的值。
 *
 * 【参数】
 *   page —— 要写入的页(若位于共享缓冲池,调用者需持有至少 SHARE 级
 *           缓冲锁,通常持有排他锁);
 *   blkno —— 块号(参与校验和计算)。
 * 【返回值】无。
 *
 * Set checksum on a page.
 *
 * If the page is in shared buffers, it needs to be locked in at least
 * share-exclusive mode.
 *
 * If checksums are disabled, or if the page is not initialized, just
 * return. Otherwise compute and set the checksum.
 *
 * In the past this needed to be done on a copy of the page, due to the
 * possibility of e.g., hint bits being set concurrently. However, this is not
 * necessary anymore as hint bits won't be set while IO is going on.
 */
void
PageSetChecksum(Page page, BlockNumber blkno)
{
	HOLD_INTERRUPTS();
	/* If we don't need a checksum, just return */
	if (PageIsNew(page) || !DataChecksumsNeedWrite())
	{
		RESUME_INTERRUPTS();
		return;
	}

	((PageHeader) page)->pd_checksum = pg_checksum_page(page, blkno);
	RESUME_INTERRUPTS();
}
