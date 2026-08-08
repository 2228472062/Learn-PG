/*-------------------------------------------------------------------------
 *
 * freespace.c
 *	  POSTGRES free space map for quickly finding free space in relations
 *
 *
 * 【模块总览(中文)】
 * 本文件实现堆表(以及需要它的索引 AM)的"空闲空间映射"Free Space Map
 * (FSM)顶层逻辑。FSM 是一棵"树套树"结构:
 * - 单个 FSM 页(8KB)内部是一棵按数组存放的完全二叉树(fsmpage.c 负责),
 *   每个叶子节点对应堆表的一个块,存一个字节(0-255)表示该块的空闲
 *   空间类别(类别划分见 FSM_CATEGORIES / MaxFSMRequestSize 的注释);
 * - FSM 页之间又构成一棵 3~4 层的树(FSM_TREE_DEPTH):底层页的叶子槽
 *   直接对应当堆块,上层页的槽对应下一层页;根页是唯一入口。FSM 页在
 *   磁盘上按"深度优先"顺序物理排列(fsm_logical_to_physical),因此对
 *   整棵树的递归遍历天然是顺序 I/O。
 *
 * 本文件职责:
 * 1) 地址换算:逻辑地址(层 + 层内页号)与物理块号、与堆块号的互转
 *    (fsm_logical_to_physical、fsm_get_location、fsm_get_heap_blk、
 *    fsm_get_parent、fsm_get_child);
 * 2) FSM fork 文件的读取/扩展(fsm_readbuf、fsm_extend);
 * 3) 公开 API:找空闲页(GetPageWithFreeSpace)、记录页空闲度
 *    (RecordPageWithFreeSpace、XLogRecordPageWithFreeSpace)、"记录 +
 *    就近再找"组合(RecordAndGetPageWithFreeSpace)、VACUUM 后的上层
 *    重建(FreeSpaceMapVacuum / FreeSpaceMapVacuumRange)与截断准备
 *    (FreeSpaceMapPrepareTruncateRel);
 * 4) 树搜索与一致性修复(fsm_search、fsm_vacuum_page、fsm_does_block_exist)。
 *
 * 设计要点:
 * - FSM 只是"提示":内容允许暂时不准确。记录空闲度上涨时,新值只传播
 *   到所在 FSM 页的页内祖先,跨页祖先要等 FreeSpaceMapVacuum 才更新;
 *   搜索遇到"上层值过期"会现场修正上层再重试;
 * - FSM 的修改不写 WAL(允许丢失),读取用 RBM_ZERO_ON_ERROR:崩溃造成
 *   torn page 时直接清零重建,与堆页的严格处理形成鲜明对比;
 * - 并发策略:搜索只用共享锁 + 页内轮转指针(fp_next_slot)分散热点,
 *   修正路径才升级排他锁。
 *
 * 相关的页内算法见 fsmpage.c(本文件把每个 FSM 页当作 SlotsPerFSMPage
 * 个槽的黑盒使用),索引 AM 的封装见 indexfsm.c。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/freespace/freespace.c
 *
 *
 * NOTES:
 *
 *	Free Space Map keeps track of the amount of free space on pages, and
 *	allows quickly searching for a page with enough free space. The FSM is
 *	stored in a dedicated relation fork of all heap relations, and those
 *	index access methods that need it (see also indexfsm.c). See README for
 *	more information.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/htup_details.h"
#include "access/xloginsert.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "storage/freespace.h"
#include "storage/fsm_internals.h"
#include "storage/smgr.h"
#include "utils/rel.h"


/* 空闲空间类别划分:用一个字节(0-255)表示页的空闲量。
 * - 共 256 档,每档宽度 FSM_CAT_STEP = BLCKSZ / 256 字节;
 * - 类别 255 表示"至少有 MaxFSMRequestSize(即 MaxHeapTupleSize)字节
 *   空闲",类别 254 表示 [254*FSM_CAT_STEP, MaxFSMRequestSize) 区间,
 *   其余类别 cat 表示 [cat*FSM_CAT_STEP, (cat+1)*FSM_CAT_STEP) 区间;
 * - MaxFSMRequestSize 之所以特殊:如果它不在档位边界上,一个恰好有
 *   MaxFSMRequestSize 字节空闲的页将不能满足同尺寸的请求;而全空页的
 *   空闲量通常不超过 MaxFSMRequestSize(要扣除页头),若没有 255 档,
 *   恰好请求 MaxFSMRequestSize 字节就永远无法被满足。
 */
#define FSM_CATEGORIES	256
#define FSM_CAT_STEP	(BLCKSZ / FSM_CATEGORIES)
#define MaxFSMRequestSize	MaxHeapTupleSize

/*
 * 磁盘上 FSM 树的层数:需要能够寻址 2^32-1 个堆块(堆的最大块数)。
 * 1626 是最小的满足 X^3 >= 2^32-1 的数,256 是满足 X^4 >= 2^32-1 的数;
 * 因此当每个 FSM 页有 >= 1626 个槽(即 BLCKSZ >= 4096)时用 3 层树,
 * 否则用 4 层;512 是支持的最小 BLCKSZ。
 * FSM_ROOT_LEVEL 是最顶层(根页所在层,编号 FSM_TREE_DEPTH-1),
 * FSM_BOTTOM_LEVEL = 0 是最底层(叶子槽直接对应当堆块)。
 */
#define FSM_TREE_DEPTH	((SlotsPerFSMPage >= 1626) ? 3 : 4)

#define FSM_ROOT_LEVEL	(FSM_TREE_DEPTH - 1)
#define FSM_BOTTOM_LEVEL 0

/*
 * FSM 树节点(FSM 页)的逻辑地址:树的每一层可以想象成"一个独立的
 * 文件",每个 FSM 页用 (level, logpageno) 唯一标识;堆块与底层页的
 * 对应关系见 fsm_get_location,真实磁盘块号由 fsm_logical_to_physical
 * 换算(整个树按深度优先顺序铺在 FSM fork 中)。
 */
typedef struct
{
	int			level;			/* level */
	int			logpageno;		/* page number within the level */
} FSMAddress;

/* 根页的逻辑地址:永远在最顶层、页号 0。所有 FSM 搜索与整理的起点。 */
static const FSMAddress FSM_ROOT_ADDRESS = {FSM_ROOT_LEVEL, 0};

/* 以下为本文件内部函数的前置声明,按职责分组:
 * - 树导航:fsm_get_parent(子页 -> 父页及槽号)、fsm_get_child(父页+槽
 *   -> 子页)、fsm_get_location(堆块 -> 底层页+槽)、fsm_get_heap_blk
 *   (逆运算)、fsm_logical_to_physical(逻辑地址 -> 物理块号);
 * - 页读写:fsm_readbuf(读 FSM 页,可扩展)、fsm_extend(扩展 FSM fork);
 * - 类别换算:fsm_space_avail_to_cat(空闲量 -> 类别,向下取整)、
 *   fsm_space_needed_to_cat(需求量 -> 类别,向上取整)、
 *   fsm_space_cat_to_avail(类别 -> 空闲量下界);
 * - 工作函数:fsm_set_and_search(写槽并可就地搜索)、fsm_search(全局
 *   搜索)、fsm_vacuum_page(递归重建上层)、fsm_does_block_exist(堆块
 *   是否越过关系末尾)。 */
static FSMAddress fsm_get_child(FSMAddress parent, uint16 slot);
static FSMAddress fsm_get_parent(FSMAddress child, uint16 *slot);
static FSMAddress fsm_get_location(BlockNumber heapblk, uint16 *slot);
static BlockNumber fsm_get_heap_blk(FSMAddress addr, uint16 slot);
static BlockNumber fsm_logical_to_physical(FSMAddress addr);

static Buffer fsm_readbuf(Relation rel, FSMAddress addr, bool extend);
static Buffer fsm_extend(Relation rel, BlockNumber fsm_nblocks);

/* functions to convert amount of free space to a FSM category */
static uint8 fsm_space_avail_to_cat(Size avail);
static uint8 fsm_space_needed_to_cat(Size needed);
static Size fsm_space_cat_to_avail(uint8 cat);

/* workhorse functions for various operations */
static int	fsm_set_and_search(Relation rel, FSMAddress addr, uint16 slot,
							   uint8 newValue, uint8 minValue);
static BlockNumber fsm_search(Relation rel, uint8 min_cat);
static uint8 fsm_vacuum_page(Relation rel, FSMAddress addr,
							 BlockNumber start, BlockNumber end,
							 bool *eof_p);
static bool fsm_does_block_exist(Relation rel, BlockNumber blknumber);


/******** Public API ********/

/*
 * GetPageWithFreeSpace
 *      (中文)在关系中找到一块至少有指定空闲空间的页
 *
 * 【作用】FSM 的"取页"入口:把需要的字节数换算成类别,然后在 FSM 树
 * 中搜索一个"记录空闲量 >= 该类别"的底层槽,返回对应的堆块号。
 *
 * 【设计思想】
 * - FSM 只是提示:返回的块在调用者真正加锁后可能已放不下(并发插入),
 *   调用者应把实际剩余空间上报(见 RecordAndGetPageWithFreeSpace)后
 *   重试;返回 InvalidBlockNumber 表示整棵树都找不到,调用者应扩展
 *   关系;
 * - 搜索过程中若发现某槽指向的块已越过关系末尾(如 WAL 重放后 FSM
 *   超前),会顺手把该槽清零并重试(见 fsm_search)。
 *
 * 【参数】
 *   rel         —— 关系(取其 FSM fork);
 *   spaceNeeded —— 需要的空闲字节数(<= MaxFSMRequestSize)。
 * 【返回值】满足条件的堆块号;找不到返回 InvalidBlockNumber。
 *
 * GetPageWithFreeSpace - try to find a page in the given relation with
 *		at least the specified amount of free space.
 *
 * If successful, return the block number; if not, return InvalidBlockNumber.
 *
 * The caller must be prepared for the possibility that the returned page
 * will turn out to have too little space available by the time the caller
 * gets a lock on it.  In that case, the caller should report the actual
 * amount of free space available on that page and then try again (see
 * RecordAndGetPageWithFreeSpace).  If InvalidBlockNumber is returned,
 * extend the relation.
 *
 * This can trigger FSM updates if any FSM entry is found to point to a block
 * past the end of the relation.
 */
BlockNumber
GetPageWithFreeSpace(Relation rel, Size spaceNeeded)
{
	uint8		min_cat = fsm_space_needed_to_cat(spaceNeeded);

	return fsm_search(rel, min_cat);
}

/*
 * RecordAndGetPageWithFreeSpace
 *      (中文)上报旧页的实际空闲量,并尝试就近再找一个可用页(组合操作)
 *
 * 【作用】插入一行时的"一体化"流程:先更新"旧页(刚用过、实际只剩余
 * oldSpaceAvail 空闲)"的 FSM 记录,再尝试寻找下一个可插入页。合并成
 * 一次调用,省去分别调用 RecordPageWithFreeSpace + GetPageWithFreeSpace
 * 的重复锁开销,是"插一行找下一页"的高频路径。
 *
 * 【设计思想】
 * - fsm_set_and_search 在写槽的同时、仍持有该 FSM 页排他锁时就地搜索
 *   同页的其他槽:若旧页所在的 FSM 页里恰好有满足新需求的页,直接返回
 *   它——这种"就近"命中通常缓存友好,且能避免一次全树搜索;
 * - 就地找到的候选块在返回前要经过 fsm_does_block_exist 检查(FSM
 *   可能记录了越过关系尾的块),失效则退回常规 fsm_search。
 *
 * 【参数】
 *   rel           —— 关系;
 *   oldPage       —— 刚用完的堆块(其 FSM 记录将被更新);
 *   oldSpaceAvail —— 该块当前的实际空闲量;
 *   spaceNeeded   —— 本次新请求需要的空间。
 * 【返回值】找到的堆块号;找不到返回 InvalidBlockNumber。
 *
 * RecordAndGetPageWithFreeSpace - update info about a page and try again.
 *
 * We provide this combo form to save some locking overhead, compared to
 * separate RecordPageWithFreeSpace + GetPageWithFreeSpace calls. There's
 * also some effort to return a page close to the old page; if there's a
 * page with enough free space on the same FSM page where the old one page
 * is located, it is preferred.
 */
BlockNumber
RecordAndGetPageWithFreeSpace(Relation rel, BlockNumber oldPage,
							  Size oldSpaceAvail, Size spaceNeeded)
{
	int			old_cat = fsm_space_avail_to_cat(oldSpaceAvail);
	int			search_cat = fsm_space_needed_to_cat(spaceNeeded);
	FSMAddress	addr;
	uint16		slot;
	int			search_slot;

	/* Get the location of the FSM byte representing the heap block */
	addr = fsm_get_location(oldPage, &slot);

	search_slot = fsm_set_and_search(rel, addr, slot, old_cat, search_cat);

	/*
	 * If fsm_set_and_search found a suitable new block, return that.
	 * Otherwise, search as usual.
	 */
	if (search_slot != -1)
	{
		BlockNumber blknum = fsm_get_heap_blk(addr, search_slot);

		/*
		 * Check that the blknum is actually in the relation. Don't try to
		 * update the FSM in that case, just fall back to the other case
		 */
		if (fsm_does_block_exist(rel, blknum))
			return blknum;
	}
	return fsm_search(rel, search_cat);
}

/*
 * RecordPageWithFreeSpace
 *      (中文)更新某堆块在 FSM 中的空闲量记录
 *
 * 【作用】把堆块 heapBlk 的空闲量更新为 spaceAvail:换算成类别后写进
 * 底层 FSM 页的对应叶子槽,并向上传播到本页内的祖先节点。
 *
 * 【设计思想】注意:如果新值比旧值大,这个"上涨"在本次只传播到本 FSM
 * 页的页内祖先为止——跨页的更高层祖先要等下一次 FreeSpaceMapVacuum
 * 才会更新,因此新空闲可能暂时对"从根搜索"的请求者不可见。这是刻意
 * 的取舍:每次记录都向根传播需要递归读写多页、加多把锁,代价太高;而
 * 空闲度下跌(页刚被写满)时则必须立即传播,否则会把满页发给别人——
 * fsm_set_avail 的"向上传播直到祖先无变化"逻辑正好保证下跌一路到根。
 *
 * 【参数】
 *   rel        —— 关系;
 *   heapBlk    —— 堆块号;
 *   spaceAvail —— 该块当前的空闲字节数。
 * 【返回值】无。
 *
 * RecordPageWithFreeSpace - update info about a page.
 *
 * Note that if the new spaceAvail value is higher than the old value stored
 * in the FSM, the space might not become visible to searchers until the next
 * FreeSpaceMapVacuum call, which updates the upper level pages.
 */
void
RecordPageWithFreeSpace(Relation rel, BlockNumber heapBlk, Size spaceAvail)
{
	int			new_cat = fsm_space_avail_to_cat(spaceAvail);
	FSMAddress	addr;
	uint16		slot;

	/* Get the location of the FSM byte representing the heap block */
	addr = fsm_get_location(heapBlk, &slot);

	fsm_set_and_search(rel, addr, slot, new_cat, 0);
}

/*
 * XLogRecordPageWithFreeSpace
 *      (中文)WAL 重放版本的 RecordPageWithFreeSpace
 *
 * 【作用】在崩溃恢复(WAL redo)期间更新 FSM 记录。与正常路径的区别:
 * 恢复期没有 Relation 句柄,改用 rlocator 定位文件;FSM 页不存在时
 * 扩展读取(RBM_ZERO_ON_ERROR + PageInit);用完整 MarkBufferDirty
 * 而非 MarkBufferDirtyHint 标记脏。
 *
 * 【设计思想】恢复期不能用 MarkBufferDirtyHint:它在启用校验和时对
 * "只改提示位"的页不做脏标记(为避免 torn page 必须携带完整页镜像,
 * 而恢复期已无法生成新 WAL 数据)。FSM 页的零化处理使校验和错误不会
 * 导致崩溃,可以安全地整页标脏——否则重放对 FSM 的修改可能丢失。
 *
 * 【参数】
 *   rlocator   —— 关系文件定位符(恢复期代替 Relation);
 *   heapBlk    —— 堆块号;
 *   spaceAvail —— 空闲字节数。
 * 【返回值】无。
 *
 * XLogRecordPageWithFreeSpace - like RecordPageWithFreeSpace, for use in
 *		WAL replay
 */
void
XLogRecordPageWithFreeSpace(RelFileLocator rlocator, BlockNumber heapBlk,
							Size spaceAvail)
{
	int			new_cat = fsm_space_avail_to_cat(spaceAvail);
	FSMAddress	addr;
	uint16		slot;
	BlockNumber blkno;
	Buffer		buf;
	Page		page;

	/* Get the location of the FSM byte representing the heap block */
	addr = fsm_get_location(heapBlk, &slot);
	blkno = fsm_logical_to_physical(addr);

	/* If the page doesn't exist already, extend */
	buf = XLogReadBufferExtended(rlocator, FSM_FORKNUM, blkno,
								 RBM_ZERO_ON_ERROR, InvalidBuffer);
	LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

	page = BufferGetPage(buf);
	if (PageIsNew(page))
		PageInit(page, BLCKSZ, 0);

	/*
	 * Changes to FSM are usually marked as changed using MarkBufferDirtyHint;
	 * however, during recovery, it does nothing if checksums are enabled. It
	 * is assumed that the page should not be dirtied during recovery while
	 * modifying hints to prevent torn pages, since no new WAL data can be
	 * generated at this point to store FPI. This is not relevant to the FSM
	 * case, as its blocks are zeroed when a checksum mismatch occurs. So, we
	 * need to use regular MarkBufferDirty here to mark the FSM block as
	 * modified during recovery, otherwise changes to the FSM may be lost.
	 */
	if (fsm_set_avail(page, slot, new_cat))
		MarkBufferDirty(buf);
	UnlockReleaseBuffer(buf);
}

/*
 * GetRecordedFreeSpace
 *      (中文)读取 FSM 中记录的某堆块空闲量
 *
 * 【作用】只读查询:读出堆块 heapBlk 在 FSM 中的记录,换算成字节数
 * 返回。用于统计/决策(如评估页的剩余容量),不修改任何内容。
 *
 * 【设计思想】读不到 FSM 页(关系还没有 FSM,或 FSM 不够长)时返回 0
 * ——表示"没有任何可用空间"这一保守默认;返回的是"类别下限"(见
 * fsm_space_cat_to_avail),即记录值对应的最小字节数,不会高估。
 *
 * 【参数】
 *   rel     —— 关系;
 *   heapBlk —— 堆块号。
 * 【返回值】FSM 记录的(下限)空闲字节数;无记录时返回 0。
 *
 * GetRecordedFreeSpace - return the amount of free space on a particular page,
 *		according to the FSM.
 */
Size
GetRecordedFreeSpace(Relation rel, BlockNumber heapBlk)
{
	FSMAddress	addr;
	uint16		slot;
	Buffer		buf;
	uint8		cat;

	/* Get the location of the FSM byte representing the heap block */
	addr = fsm_get_location(heapBlk, &slot);

	buf = fsm_readbuf(rel, addr, false);
	if (!BufferIsValid(buf))
		return 0;
	cat = fsm_get_avail(BufferGetPage(buf), slot);
	ReleaseBuffer(buf);

	return fsm_space_cat_to_avail(cat);
}

/*
 * FreeSpaceMapPrepareTruncateRel
 *      (中文)为关系截断准备 FSM(计算新 FSM 长度并清理尾部槽)
 *
 * 【作用】堆表被 TRUNCATE / VACUUM 收缩时调用。给定新的堆长度
 * nblocks,计算 FSM 应截到多长:把"第一个被移除的堆块"所在 FSM 页里
 * 该块之后的槽清零(使搜索不会返回已被截掉的块),返回新的 FSM 页数。
 * 调用者随后负责:① 用 smgrtruncate 实际截断 FSM 文件;② 调用
 * FreeSpaceMapVacuumRange 更新上层节点。
 *
 * 【设计思想】
 * - 若第一个被移除的块恰好是新 FSM 页的首槽,整页直接截掉即可,连
 *   清零都省了(走 else 分支);
 * - 尾部清零用完整 MarkBufferDirty 而非 Hint:严格说这不是正确性要求
 *   (fsm_does_block_exist 会兜底挡住越界块),但能避免搜索时反复撞上
 *   这些废弃槽、每次都要做一次 fsm_does_block_exist 检查;
 * - 崩溃时序分析:若在 XLOG_SMGR_TRUNCATE 落盘前崩溃,主 fork 未变短,
 *   本页记录仍然有效;落盘后崩溃,重放会重新走到这里,因此这段修改
 *   属于"可选 WAL"范畴(与 hint bit 同级别,见英文注释);
 * - 若 FSM 已经比目标短(此前已截过),返回 InvalidBlockNumber 表示
 *   "无需截断"。
 *
 * 【参数】
 *   rel     —— 关系;
 *   nblocks —— 截断后堆的块数(即第一个被移除的堆块号)。
 * 【返回值】新的 FSM 块数;无需截断时返回 InvalidBlockNumber。
 *
 * FreeSpaceMapPrepareTruncateRel - prepare for truncation of a relation.
 *
 * nblocks is the new size of the heap.
 *
 * Return the number of blocks of new FSM.
 * If it's InvalidBlockNumber, there is nothing to truncate;
 * otherwise the caller is responsible for calling smgrtruncate()
 * to truncate the FSM pages, and FreeSpaceMapVacuumRange()
 * to update upper-level pages in the FSM.
 */
BlockNumber
FreeSpaceMapPrepareTruncateRel(Relation rel, BlockNumber nblocks)
{
	BlockNumber new_nfsmblocks;
	FSMAddress	first_removed_address;
	uint16		first_removed_slot;
	Buffer		buf;

	/*
	 * If no FSM has been created yet for this relation, there's nothing to
	 * truncate.
	 */
	if (!smgrexists(RelationGetSmgr(rel), FSM_FORKNUM))
		return InvalidBlockNumber;

	/* Get the location in the FSM of the first removed heap block */
	first_removed_address = fsm_get_location(nblocks, &first_removed_slot);

	/*
	 * Zero out the tail of the last remaining FSM page. If the slot
	 * representing the first removed heap block is at a page boundary, as the
	 * first slot on the FSM page that first_removed_address points to, we can
	 * just truncate that page altogether.
	 */
	if (first_removed_slot > 0)
	{
		buf = fsm_readbuf(rel, first_removed_address, false);
		if (!BufferIsValid(buf))
			return InvalidBlockNumber;	/* nothing to do; the FSM was already
										 * smaller */
		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

		/* NO EREPORT(ERROR) from here till changes are logged */
		START_CRIT_SECTION();

		fsm_truncate_avail(BufferGetPage(buf), first_removed_slot);

		/*
		 * This change is non-critical, because fsm_does_block_exist() would
		 * stop us from returning a truncated-away block.  However, since this
		 * may remove up to SlotsPerFSMPage slots, it's nice to avoid the cost
		 * of that many fsm_does_block_exist() rejections.  Use a full
		 * MarkBufferDirty(), not MarkBufferDirtyHint().
		 */
		MarkBufferDirty(buf);

		/*
		 * WAL-log like MarkBufferDirtyHint() might have done, just to avoid
		 * differing from the rest of the file in this respect.  This is
		 * optional; see README mention of full page images.  XXX consider
		 * XLogSaveBufferForHint() for even closer similarity.
		 *
		 * A higher-level operation calls us at WAL replay.  If we crash
		 * before the XLOG_SMGR_TRUNCATE flushes to disk, main fork length has
		 * not changed, and our fork remains valid.  If we crash after that
		 * flush, redo will return here.
		 */
		if (!InRecovery && RelationNeedsWAL(rel) && XLogHintBitIsNeeded())
			log_newpage_buffer(buf, false);

		END_CRIT_SECTION();

		UnlockReleaseBuffer(buf);

		new_nfsmblocks = fsm_logical_to_physical(first_removed_address) + 1;
	}
	else
	{
		new_nfsmblocks = fsm_logical_to_physical(first_removed_address);
		if (smgrnblocks(RelationGetSmgr(rel), FSM_FORKNUM) <= new_nfsmblocks)
			return InvalidBlockNumber;	/* nothing to do; the FSM was already
										 * smaller */
	}

	return new_nfsmblocks;
}

/*
 * FreeSpaceMapVacuum
 *      (中文)全树重建 FSM 的上层节点(VACUUM 后调用)
 *
 * 【作用】假定底层 FSM 页已被新的空闲信息更新,递归遍历整棵 FSM 树,
 * 从根开始向下把每个"跨页祖先"节点重算为其子树的最大值,消除上层与
 * 叶子之间的不一致,使"记录上涨"的新值对全树搜索可见。
 *
 * 【设计思想】底层页的更新(RecordPageWithFreeSpace)只传播到页内祖先;
 * 跨页的祖先由本函数统一修复。整树遍历按"物理深度优先"的存储顺序
 * 访问页面,顺序 I/O,代价可控。
 *
 * 【参数】rel —— 关系。
 * 【返回值】无。
 *
 * FreeSpaceMapVacuum - update upper-level pages in the rel's FSM
 *
 * We assume that the bottom-level pages have already been updated with
 * new free-space information.
 */
void
FreeSpaceMapVacuum(Relation rel)
{
	bool		dummy;

	/* Recursively scan the tree, starting at the root */
	(void) fsm_vacuum_page(rel, FSM_ROOT_ADDRESS,
						   (BlockNumber) 0, InvalidBlockNumber,
						   &dummy);
}

/*
 * FreeSpaceMapVacuumRange
 *      (中文)只更新覆盖指定堆块范围的上层节点
 *
 * 【作用】FreeSpaceMapVacuum 的区间版本:假定只有 [start, end) 区间的
 * 堆块有新的空闲信息,因此只重算覆盖该区间的部分上层槽。end ==
 * InvalidBlockNumber 等价于"直到关系末尾"。
 *
 * 【设计思想】VACUUM 清理关系尾部(收缩、删页)时,只有尾部页的空闲
 * 信息发生变化,整树重建会白读大量无关页面;区间版本把递归裁剪到相关
 * 子树上(具体裁剪逻辑见 fsm_vacuum_page)。
 *
 * 【参数】
 *   rel   —— 关系;
 *   start —— 区间起始堆块;
 *   end   —— 区间结束堆块(不含),可为 InvalidBlockNumber。
 * 【返回值】无。
 *
 * FreeSpaceMapVacuumRange - update upper-level pages in the rel's FSM
 *
 * As above, but assume that only heap pages between start and end-1 inclusive
 * have new free-space information, so update only the upper-level slots
 * covering that block range.  end == InvalidBlockNumber is equivalent to
 * "all the rest of the relation".
 */
void
FreeSpaceMapVacuumRange(Relation rel, BlockNumber start, BlockNumber end)
{
	bool		dummy;

	/* Recursively scan the tree, starting at the root */
	if (end > start)
		(void) fsm_vacuum_page(rel, FSM_ROOT_ADDRESS, start, end, &dummy);
}

/******** Internal routines ********/

/*
 * fsm_space_avail_to_cat
 *      (中文)空闲字节数 -> 类别(向下取整)
 *
 * 【作用】把实际空闲量换算成 0-254 的类别。类别 255 保留给 >=
 * MaxFSMRequestSize 的空闲量(见文件头宏注释)。
 *
 * 【设计思想】记录方"向下取整"保证:说"类别 5"意味着空闲量在
 * [5*step, 6*step) 之间,搜索方据此请求类别时绝不会高估空闲量——
 * 与 fsm_space_needed_to_cat 的向上取整恰好配对。
 *
 * 【参数】avail —— 空闲字节数(须 < BLCKSZ)。
 * 【返回值】类别 0-255。
 *
 * Return category corresponding x bytes of free space
 */
static uint8
fsm_space_avail_to_cat(Size avail)
{
	int			cat;

	Assert(avail < BLCKSZ);

	if (avail >= MaxFSMRequestSize)
		return 255;

	cat = avail / FSM_CAT_STEP;

	/*
	 * The highest category, 255, is reserved for MaxFSMRequestSize bytes or
	 * more.
	 */
	if (cat > 254)
		cat = 254;

	return (uint8) cat;
}

/*
 * fsm_space_cat_to_avail
 *      (中文)类别 -> 空闲字节数下限
 *
 * 【作用】fsm_space_avail_to_cat 的逆运算:返回该类别所代表的空闲
 * 区间的下界(类别 255 返回 MaxFSMRequestSize)。供读取方
 * (GetRecordedFreeSpace 等)把 FSM 记录还原为"至少有多少空闲"。
 *
 * 【参数】cat —— 类别 0-255。
 * 【返回值】对应的(下限)空闲字节数。
 *
 * Return the lower bound of the range of free space represented by given
 * category.
 */
static Size
fsm_space_cat_to_avail(uint8 cat)
{
	/* The highest category represents exactly MaxFSMRequestSize bytes. */
	if (cat == 255)
		return MaxFSMRequestSize;
	else
		return cat * FSM_CAT_STEP;
}

/*
 * fsm_space_needed_to_cat
 *      (中文)需求字节数 -> 类别(向上取整)
 *
 * 【作用】把"请求的空闲量"换算成类别。与 fsm_space_avail_to_cat 的
 * 向下取整相反,这里向上取整:保证"记录类别 >= 请求类别"必然意味着
 * 实际空闲 >= 请求量。
 *
 * 【设计思想】"可用量向下取整、需求量向上取整"这一对规则,配合 255
 * 档的保留(见文件头),使搜索语义精确成立:记录类别 >= 需求类别是
 * "页确实放得下"的充分条件。needed == 0 时返回类别 1(而非 0),因为
 * 类别 0 专门表示"无空闲",不能被一个"请求 0 字节"的正常请求命中。
 *
 * 【参数】needed —— 需求字节数(> MaxFSMRequestSize 报错;FSM 永远
 * 无法满足超出其最大档的请求)。
 * 【返回值】类别 1-255。
 *
 * Which category does a page need to have, to accommodate x bytes of data?
 * While fsm_space_avail_to_cat() rounds down, this needs to round up.
 */
static uint8
fsm_space_needed_to_cat(Size needed)
{
	int			cat;

	/* Can't ask for more space than the highest category represents */
	if (needed > MaxFSMRequestSize)
		elog(ERROR, "invalid FSM request size %zu", needed);

	if (needed == 0)
		return 1;

	cat = (needed + FSM_CAT_STEP - 1) / FSM_CAT_STEP;

	if (cat > 255)
		cat = 255;

	return (uint8) cat;
}

/*
 * fsm_logical_to_physical
 *      (中文)FSM 逻辑地址 -> 物理块号
 *
 * 【作用】把 (level, logpageno) 逻辑地址换算成 FSM fork 中的物理块号
 * (0 基)。
 *
 * 【设计思想】FSM 页在磁盘上的物理顺序是"整棵树深度优先":先根页,再
 * 根的第一个子树(递归),再第二个子树……公式分三步:
 * 1. leafno = 本页展开到最底层后对应的"叶子页序号"(把 logpageno 连续
 *    乘上每层的分叉数 SlotsPerFSMPage);
 * 2. pages = 深度优先序下"覆盖 leafno 个叶子页需要多少物理页":自底向
 *    上每层累加 leafno+1 并除以 SlotsPerFSMPage(即每层"完整页数 +
 *    不完整一页"),各层相加;
 * 3. 若本页不是底层,减去为其下层多算的 addr.level 页,最后转 0 基
 *    (pages - 1)。
 * 该布局保证递归遍历(如 fsm_vacuum_page)按物理顺序访问页面,顺序 I/O。
 *
 * 【参数】addr —— FSM 逻辑地址。
 * 【返回值】FSM fork 中的物理块号。
 *
 * Returns the physical block number of a FSM page
 */
static BlockNumber
fsm_logical_to_physical(FSMAddress addr)
{
	BlockNumber pages;
	int			leafno;
	int			l;

	/*
	 * Calculate the logical page number of the first leaf page below the
	 * given page.
	 */
	leafno = addr.logpageno;
	for (l = 0; l < addr.level; l++)
		leafno *= SlotsPerFSMPage;

	/* Count upper level nodes required to address the leaf page */
	pages = 0;
	for (l = 0; l < FSM_TREE_DEPTH; l++)
	{
		pages += leafno + 1;
		leafno /= SlotsPerFSMPage;
	}

	/*
	 * If the page we were asked for wasn't at the bottom level, subtract the
	 * additional lower level pages we counted above.
	 */
	pages -= addr.level;

	/* Turn the page count into 0-based block number */
	return pages - 1;
}

/*
 * fsm_get_location
 *      (中文)堆块号 -> 底层 FSM 页地址与槽号
 *
 * 【作用】把堆块号映射到 FSM 最底层(level 0):每 SlotsPerFSMPage 个
 * 堆块对应一个底层 FSM 页,堆块号除/模 SlotsPerFSMPage 得到页号与槽号。
 *
 * 【参数】
 *   heapblk —— 堆块号;
 *   slot    —— 输出参数:槽号(0..SlotsPerFSMPage-1)。
 * 【返回值】底层 FSM 页的逻辑地址(level = 0)。
 *
 * Return the FSM location corresponding to given heap block.
 */
static FSMAddress
fsm_get_location(BlockNumber heapblk, uint16 *slot)
{
	FSMAddress	addr;

	addr.level = FSM_BOTTOM_LEVEL;
	addr.logpageno = heapblk / SlotsPerFSMPage;
	*slot = heapblk % SlotsPerFSMPage;

	return addr;
}

/*
 * fsm_get_heap_blk
 *      (中文)底层 FSM 页地址与槽号 -> 堆块号(fsm_get_location 的逆运算)
 *
 * 【作用】把"底层 FSM 页 + 槽号"还原成堆块号,供搜索命中后返回给
 * 调用者。断言 addr 必须是最底层——上层页的槽对应的是"页"而非"堆块"。
 *
 * 【参数】
 *   addr —— FSM 页地址(必须是最底层);
 *   slot —— 槽号。
 * 【返回值】对应的堆块号。
 *
 * Return the heap block number corresponding to given location in the FSM.
 */
static BlockNumber
fsm_get_heap_blk(FSMAddress addr, uint16 slot)
{
	Assert(addr.level == FSM_BOTTOM_LEVEL);
	return ((unsigned int) addr.logpageno) * SlotsPerFSMPage + slot;
}

/*
 * fsm_get_parent
 *      (中文)求子页的父页逻辑地址与槽号
 *
 * 【作用】从子页的逻辑地址上溯一层:父页号 = 子页号 / SlotsPerFSMPage,
 * 槽号 = 子页号 % SlotsPerFSMPage(父页的每个槽对应一个子页,父子映射
 * 是"满叉树"的整除关系)。
 *
 * 【参数】
 *   child —— 子页逻辑地址(不能是根层);
 *   slot  —— 输出参数:父页中的槽号。
 * 【返回值】父页逻辑地址。
 *
 * Given a logical address of a child page, get the logical page number of
 * the parent, and the slot within the parent corresponding to the child.
 */
static FSMAddress
fsm_get_parent(FSMAddress child, uint16 *slot)
{
	FSMAddress	parent;

	Assert(child.level < FSM_ROOT_LEVEL);

	parent.level = child.level + 1;
	parent.logpageno = child.logpageno / SlotsPerFSMPage;
	*slot = child.logpageno % SlotsPerFSMPage;

	return parent;
}

/*
 * fsm_get_child
 *      (中文)求父页某槽对应的子页逻辑地址(fsm_get_parent 的逆运算)
 *
 * 【作用】从父页逻辑地址与槽号下钻一层:子页号 = 父页号 *
 * SlotsPerFSMPage + 槽号。搜索算法沿树下行时使用。
 *
 * 【参数】
 *   parent —— 父页逻辑地址(不能是最底层);
 *   slot   —— 父页中的槽号。
 * 【返回值】子页逻辑地址。
 *
 * Given a logical address of a parent page and a slot number, get the
 * logical address of the corresponding child page.
 */
static FSMAddress
fsm_get_child(FSMAddress parent, uint16 slot)
{
	FSMAddress	child;

	Assert(parent.level > FSM_BOTTOM_LEVEL);

	child.level = parent.level - 1;
	child.logpageno = parent.logpageno * SlotsPerFSMPage + slot;

	return child;
}

/*
 * fsm_readbuf
 *      (中文)读取(必要时扩展)一个 FSM 页
 *
 * 【作用】按逻辑地址读取 FSM 页,返回已 pin 的缓冲区。页不存在时:
 * extend 为 true 则先扩展 FSM fork 再读,否则返回 InvalidBuffer。
 * 读回的全零页(新页/损坏页)会就地 PageInit(初始化为全 0 空闲)。
 *
 * 【设计思想】
 * - 用 smgr 缓存的 nblocks 判断越界;缓存失效(InvalidBlockNumber)时
 *   重新向内核查询。截断会让缓存失效(smgr 失效消息),但扩展不会,所以
 *   还要在"缓存值可能过期"时复查;
 * - 读取用 RBM_ZERO_ON_ERROR:FSM 只是提示且不写 WAL,崩溃导致的 torn
 *   page 把页头写坏时,清零重来远比报错合理;
 * - 页初始化有两个并发要点:① 必须持排他锁后二次检查 PageIsNew(别的
 *   进程可能已完成初始化);② 无锁的首次检查可能看到一个"初始化到一半"
 *   的页,这对只调用 PageGetContents 的调用者是安全的(它们不依赖页头
 *   内容)。
 *
 * 【参数】
 *   rel    —— 关系;
 *   addr   —— FSM 逻辑地址;
 *   extend —— 页不存在时是否扩展 fork。
 * 【返回值】已 pin 的缓冲区;页不存在且不扩展时返回 InvalidBuffer。
 *
 * Read a FSM page.
 *
 * If the page doesn't exist, InvalidBuffer is returned, or if 'extend' is
 * true, the FSM file is extended.
 */
static Buffer
fsm_readbuf(Relation rel, FSMAddress addr, bool extend)
{
	BlockNumber blkno = fsm_logical_to_physical(addr);
	Buffer		buf;
	SMgrRelation reln = RelationGetSmgr(rel);

	/*
	 * If we haven't cached the size of the FSM yet, check it first.  Also
	 * recheck if the requested block seems to be past end, since our cached
	 * value might be stale.  (We send smgr inval messages on truncation, but
	 * not on extension.)
	 */
	if (reln->smgr_cached_nblocks[FSM_FORKNUM] == InvalidBlockNumber ||
		blkno >= reln->smgr_cached_nblocks[FSM_FORKNUM])
	{
		/* Invalidate the cache so smgrnblocks asks the kernel. */
		reln->smgr_cached_nblocks[FSM_FORKNUM] = InvalidBlockNumber;
		if (smgrexists(reln, FSM_FORKNUM))
			smgrnblocks(reln, FSM_FORKNUM);
		else
			reln->smgr_cached_nblocks[FSM_FORKNUM] = 0;
	}

	/*
	 * For reading we use ZERO_ON_ERROR mode, and initialize the page if
	 * necessary.  The FSM information is not accurate anyway, so it's better
	 * to clear corrupt pages than error out. Since the FSM changes are not
	 * WAL-logged, the so-called torn page problem on crash can lead to pages
	 * with corrupt headers, for example.
	 *
	 * We use the same path below to initialize pages when extending the
	 * relation, as a concurrent extension can end up with vm_extend()
	 * returning an already-initialized page.
	 */
	if (blkno >= reln->smgr_cached_nblocks[FSM_FORKNUM])
	{
		if (extend)
			buf = fsm_extend(rel, blkno + 1);
		else
			return InvalidBuffer;
	}
	else
		buf = ReadBufferExtended(rel, FSM_FORKNUM, blkno, RBM_ZERO_ON_ERROR, NULL);

	/*
	 * Initializing the page when needed is trickier than it looks, because of
	 * the possibility of multiple backends doing this concurrently, and our
	 * desire to not uselessly take the buffer lock in the normal path where
	 * the page is OK.  We must take the lock to initialize the page, so
	 * recheck page newness after we have the lock, in case someone else
	 * already did it.  Also, because we initially check PageIsNew with no
	 * lock, it's possible to fall through and return the buffer while someone
	 * else is still initializing the page (i.e., we might see pd_upper as set
	 * but other page header fields are still zeroes).  This is harmless for
	 * callers that will take a buffer lock themselves, but some callers
	 * inspect the page without any lock at all.  The latter is OK only so
	 * long as it doesn't depend on the page header having correct contents.
	 * Current usage is safe because PageGetContents() does not require that.
	 */
	if (PageIsNew(BufferGetPage(buf)))
	{
		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
		if (PageIsNew(BufferGetPage(buf)))
			PageInit(BufferGetPage(buf), BLCKSZ, 0);
		LockBuffer(buf, BUFFER_LOCK_UNLOCK);
	}
	return buf;
}

/*
 * fsm_extend
 *      (中文)把 FSM fork 扩展到至少 fsm_nblocks 块
 *
 * 【作用】调用 ExtendBufferedRelTo 扩展 FSM 文件,新页全零(零即表示
 * "无空闲")。EB_CREATE_FORK_IF_NEEDED 保证 FSM fork 尚不存在时自动
 * 创建,EB_CLEAR_SIZE_CACHE 强制刷新 smgr 的块数缓存。
 *
 * 【设计思想】FSM 与主 fork 一样通过共享缓冲池读写,扩展动作与普通
 * 关系的"扩展到指定长度"完全复用;零页被 fsm_readbuf 的 PageIsNew
 * 分支视为"已初始化"的空 FSM 页,无需额外处理。注意并发扩展时可能
 * 拿到"别人刚扩展好"的页,调用方(ReadBuffer 路径)负责二次检查。
 *
 * 【参数】
 *   rel         —— 关系;
 *   fsm_nblocks —— 扩展后的目标块数。
 * 【返回值】扩展后对应块的缓冲区(已 pin)。
 *
 * Ensure that the FSM fork is at least fsm_nblocks long, extending
 * it if necessary with empty pages. And by empty, I mean pages filled
 * with zeros, meaning there's no free space.
 */
static Buffer
fsm_extend(Relation rel, BlockNumber fsm_nblocks)
{
	return ExtendBufferedRelTo(BMR_REL(rel), FSM_FORKNUM, NULL,
							   EB_CREATE_FORK_IF_NEEDED |
							   EB_CLEAR_SIZE_CACHE,
							   fsm_nblocks,
							   RBM_ZERO_ON_ERROR);
}

/*
 * fsm_set_and_search
 *      (中文)写 FSM 槽值,并可选择在持锁期间就地搜索可用槽
 *
 * 【作用】核心"写"原语:在 (addr, slot) 处写新值 newValue(经 fsmpage.c
 * 的 fsm_set_avail 传播到页内祖先);若 minValue > 0,还在持有排他锁
 * 期间用 fsm_search_avail 搜索同页中值 >= minValue 的槽。
 *
 * 【设计思想】"边写边搜"是 RecordAndGetPageWithFreeSpace 的近邻优化:
 * 写入与搜索共用一把排他锁,避免"写完放锁、再拿共享锁搜索"的两次锁
 * 往返。fsm_search 在修正上层节点时也用它(minValue = 0,只写不搜)。
 *
 * 【参数】
 *   rel      —— 关系;
 *   addr     —— FSM 页逻辑地址;
 *   slot     —— 要写的槽号;
 *   newValue —— 新的类别值;
 *   minValue —— 就地搜索的最低类别;0 表示不搜索。
 * 【返回值】就地搜索到的槽号;未搜索或未找到返回 -1。
 *
 * Set value in given FSM page and slot.
 *
 * If minValue > 0, the updated page is also searched for a page with at
 * least minValue of free space. If one is found, its slot number is
 * returned, -1 otherwise.
 */
static int
fsm_set_and_search(Relation rel, FSMAddress addr, uint16 slot,
				   uint8 newValue, uint8 minValue)
{
	Buffer		buf;
	Page		page;
	int			newslot = -1;

	buf = fsm_readbuf(rel, addr, true);
	LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);

	page = BufferGetPage(buf);

	if (fsm_set_avail(page, slot, newValue))
		MarkBufferDirtyHint(buf, false);

	if (minValue != 0)
	{
		/* Search while we still hold the lock */
		newslot = fsm_search_avail(buf, minValue,
								   addr.level == FSM_BOTTOM_LEVEL,
								   true);
	}

	UnlockReleaseBuffer(buf);

	return newslot;
}

/*
 * fsm_search
 *      (中文)在 FSM 树中搜索记录空闲 >= min_cat 的堆块(主搜索算法)
 *
 * 【作用】从根页开始沿树下行:每层在当前 FSM 页内用 fsm_search_avail
 * 找"值 >= min_cat"的槽(页内带轮转指针,分散并发请求),命中就下到
 * 子页,直到最底层命中后返回对应堆块号。中途处理三类异常:
 * 1) 底层命中的块已越过关系末尾(如 WAL 重放后 FSM 超前):把该槽清零
 *    并回到根重来,连续 > 10000 次则放弃返回 InvalidBlockNumber
 *    (同下方原因,防止无限循环);
 * 2) 中间层页内找不到,但根仍够:说明上层记录过期,现场把父槽修正为
 *    本页实际最大值(fsm_set_and_search)后从根重来——同样有 10000 次
 *    应急阀,防止上层严重过期时无限循环;
 * 3) 根页都找不到:整棵树确实没有满足要求的页,返回 InvalidBlockNumber。
 *
 * 【设计思想】
 * - 每层命中后保持对当前页的 pin(放锁不放 pin),准备"立刻下钻",
 *   防止并发修改导致路径失效;
 * - "上层过期就现场修正"是 FSM 尽力而为设计的一部分:上层只是缓存,
 *   错了就修。修正时有竞态(可能用旧值覆盖新值),但概率低、会被下次
 *   VACUUM 修正,可接受;
 * - 只读搜索用共享锁,只有修正路径才升级排他锁,最大限度降低互斥。
 *
 * 【参数】
 *   rel     —— 关系;
 *   min_cat —— 需求类别。
 * 【返回值】满足条件的堆块号;找不到返回 InvalidBlockNumber。
 *
 * Search the tree for a heap page with at least min_cat of free space
 */
static BlockNumber
fsm_search(Relation rel, uint8 min_cat)
{
	int			restarts = 0;
	FSMAddress	addr = FSM_ROOT_ADDRESS;

	for (;;)
	{
		int			slot;
		Buffer		buf;
		uint8		max_avail = 0;

		/* Read the FSM page. */
		buf = fsm_readbuf(rel, addr, false);

		/* Search within the page */
		if (BufferIsValid(buf))
		{
			LockBuffer(buf, BUFFER_LOCK_SHARE);
			slot = fsm_search_avail(buf, min_cat,
									(addr.level == FSM_BOTTOM_LEVEL),
									false);
			if (slot == -1)
			{
				max_avail = fsm_get_max_avail(BufferGetPage(buf));
				UnlockReleaseBuffer(buf);
			}
			else
			{
				/* Keep the pin for possible update below */
				LockBuffer(buf, BUFFER_LOCK_UNLOCK);
			}
		}
		else
			slot = -1;

		if (slot != -1)
		{
			/*
			 * Descend the tree, or return the found block if we're at the
			 * bottom.
			 */
			if (addr.level == FSM_BOTTOM_LEVEL)
			{
				BlockNumber blkno = fsm_get_heap_blk(addr, slot);
				Page		page;

				if (fsm_does_block_exist(rel, blkno))
				{
					ReleaseBuffer(buf);
					return blkno;
				}

				/*
				 * Block is past the end of the relation.  Update FSM, and
				 * restart from root.  The usual "advancenext" behavior is
				 * pessimal for this rare scenario, since every later slot is
				 * unusable in the same way.  We could zero all affected slots
				 * on the same FSM page, but don't bet on the benefits of that
				 * optimization justifying its compiled code bulk.
				 */
				page = BufferGetPage(buf);
				LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
				fsm_set_avail(page, slot, 0);
				MarkBufferDirtyHint(buf, false);
				UnlockReleaseBuffer(buf);
				if (restarts++ > 10000) /* same rationale as below */
					return InvalidBlockNumber;
				addr = FSM_ROOT_ADDRESS;
			}
			else
			{
				ReleaseBuffer(buf);
			}
			addr = fsm_get_child(addr, slot);
		}
		else if (addr.level == FSM_ROOT_LEVEL)
		{
			/*
			 * At the root, failure means there's no page with enough free
			 * space in the FSM. Give up.
			 */
			return InvalidBlockNumber;
		}
		else
		{
			uint16		parentslot;
			FSMAddress	parent;

			/*
			 * At lower level, failure can happen if the value in the upper-
			 * level node didn't reflect the value on the lower page. Update
			 * the upper node, to avoid falling into the same trap again, and
			 * start over.
			 *
			 * There's a race condition here, if another backend updates this
			 * page right after we release it, and gets the lock on the parent
			 * page before us. We'll then update the parent page with the now
			 * stale information we had. It's OK, because it should happen
			 * rarely, and will be fixed by the next vacuum.
			 */
			parent = fsm_get_parent(addr, &parentslot);
			fsm_set_and_search(rel, parent, parentslot, max_avail, 0);

			/*
			 * If the upper pages are badly out of date, we might need to loop
			 * quite a few times, updating them as we go. Any inconsistencies
			 * should eventually be corrected and the loop should end. Looping
			 * indefinitely is nevertheless scary, so provide an emergency
			 * valve.
			 */
			if (restarts++ > 10000)
				return InvalidBlockNumber;

			/* Start search all over from the root */
			addr = FSM_ROOT_ADDRESS;
		}
	}
}


/*
 * fsm_vacuum_page
 *      (中文)递归重建一个 FSM 子树的上层节点(FreeSpaceMapVacuum 的递归体)
 *
 * 【作用】对 addr 指向的 FSM 页:若是非底层,先递归处理覆盖
 * [start, end) 区间堆块的子页,再用子页返回的最大值修正本页对应槽;
 * 最后返回本页的最大值给父页使用。页已越过 FSM 文件末尾(EOF)时置
 * *eof_p 并返回 0,上层随之把剩余槽全部清零。
 *
 * 【设计思想】
 * - 深度优先且按物理顺序存储,遍历几乎全是顺序 I/O(见
 *   fsm_logical_to_physical 的注释);
 * - 区间裁剪:先把 [start, end) 映射到本页应处理的槽区间
 *   (start_slot..end_slot,计算方式是把区间两端堆块逐步上提到本层),
 *   只递归/修正这些槽,避免扫描无关子树——这是 FreeSpaceMapVacuumRange
 *   只更新局部的依据;
 * - 值未变就不写(避免无谓标脏);子页 EOF 后本页其余槽一律清 0;
 * - 顺带把页的轮转指针 fp_next_slot 复位为 0:鼓励新插入使用低位块,
 *   提高未来 VACUUM 截断关系的可能性。这只是提示位修改,经
 *   BufferBeginSetHintBits / BufferFinishSetHintBits 基础设施完成,
 *   不写 WAL(失败也无妨)。
 *
 * 【参数】
 *   rel   —— 关系;
 *   addr  —— 待处理 FSM 页的逻辑地址;
 *   start —— 区间起始堆块;
 *   end   —— 区间结束堆块(可超出关系末尾);
 *   eof_p —— 输出参数:本页是否已越过 FSM 文件末尾。
 * 【返回值】本页(及其子树)的最大空闲类别。
 *
 * Recursive guts of FreeSpaceMapVacuum
 *
 * Examine the FSM page indicated by addr, as well as its children, updating
 * upper-level nodes that cover the heap block range from start to end-1.
 * (It's okay if end is beyond the actual end of the map.)
 * Return the maximum freespace value on this page.
 *
 * If addr is past the end of the FSM, set *eof_p to true and return 0.
 *
 * This traverses the tree in depth-first order.  The tree is stored
 * physically in depth-first order, so this should be pretty I/O efficient.
 */
static uint8
fsm_vacuum_page(Relation rel, FSMAddress addr,
				BlockNumber start, BlockNumber end,
				bool *eof_p)
{
	Buffer		buf;
	Page		page;
	uint8		max_avail;

	/* Read the page if it exists, or return EOF */
	buf = fsm_readbuf(rel, addr, false);
	if (!BufferIsValid(buf))
	{
		*eof_p = true;
		return 0;
	}
	else
		*eof_p = false;

	page = BufferGetPage(buf);

	/*
	 * If we're above the bottom level, recurse into children, and fix the
	 * information stored about them at this level.
	 */
	if (addr.level > FSM_BOTTOM_LEVEL)
	{
		FSMAddress	fsm_start,
					fsm_end;
		uint16		fsm_start_slot,
					fsm_end_slot;
		int			slot,
					start_slot,
					end_slot;
		bool		eof = false;

		/*
		 * Compute the range of slots we need to update on this page, given
		 * the requested range of heap blocks to consider.  The first slot to
		 * update is the one covering the "start" block, and the last slot is
		 * the one covering "end - 1".  (Some of this work will be duplicated
		 * in each recursive call, but it's cheap enough to not worry about.)
		 */
		fsm_start = fsm_get_location(start, &fsm_start_slot);
		fsm_end = fsm_get_location(end - 1, &fsm_end_slot);

		while (fsm_start.level < addr.level)
		{
			fsm_start = fsm_get_parent(fsm_start, &fsm_start_slot);
			fsm_end = fsm_get_parent(fsm_end, &fsm_end_slot);
		}
		Assert(fsm_start.level == addr.level);

		if (fsm_start.logpageno == addr.logpageno)
			start_slot = fsm_start_slot;
		else if (fsm_start.logpageno > addr.logpageno)
			start_slot = SlotsPerFSMPage;	/* shouldn't get here... */
		else
			start_slot = 0;

		if (fsm_end.logpageno == addr.logpageno)
			end_slot = fsm_end_slot;
		else if (fsm_end.logpageno > addr.logpageno)
			end_slot = SlotsPerFSMPage - 1;
		else
			end_slot = -1;		/* shouldn't get here... */

		for (slot = start_slot; slot <= end_slot; slot++)
		{
			int			child_avail;

			CHECK_FOR_INTERRUPTS();

			/* After we hit end-of-file, just clear the rest of the slots */
			if (!eof)
				child_avail = fsm_vacuum_page(rel, fsm_get_child(addr, slot),
											  start, end,
											  &eof);
			else
				child_avail = 0;

			/* Update information about the child */
			if (fsm_get_avail(page, slot) != child_avail)
			{
				LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
				fsm_set_avail(page, slot, child_avail);
				MarkBufferDirtyHint(buf, false);
				LockBuffer(buf, BUFFER_LOCK_UNLOCK);
			}
		}
	}

	/* Now get the maximum value on the page, to return to caller */
	max_avail = fsm_get_max_avail(page);

	/*
	 * Try to reset the next slot pointer. This encourages the use of
	 * low-numbered pages, increasing the chances that a later vacuum can
	 * truncate the relation. We don't bother with marking the page dirty if
	 * it wasn't already, since this is just a hint.
	 */
	LockBuffer(buf, BUFFER_LOCK_SHARE);
	if (BufferBeginSetHintBits(buf))
	{
		((FSMPage) PageGetContents(page))->fp_next_slot = 0;
		BufferFinishSetHintBits(buf, false, false);
	}

	UnlockReleaseBuffer(buf);

	return max_avail;
}


/*
 * fsm_does_block_exist
 *      (中文)检查堆块号是否未越过关系末尾(FSM 记录可能超前)
 *
 * 【作用】WAL 重放等场景下,FSM 可能已记录"关系尚未扩展到的块"
 * (FSM 先落盘而新扩展页的 WAL 未落盘)。搜索命中这样的块必须放弃,
 * 本函数就是这道兜底检查。
 *
 * 【设计思想】先看 smgr 缓存的 MAIN fork 长度(零额外开销);缓存不可
 * 用、或块号已到达缓存值时,宁可付出一次 lseek(RelationGetNumberOf-
 * Blocks 重新向内核查询),也不武断地认为块不存在——否则会把"刚扩展、
 * 已被 FSM 记录"的块误判为不存在,FSM 记录被清零,白白损失可用页。
 *
 * 【参数】
 *   rel       —— 关系;
 *   blknumber —— 待检查的堆块号。
 * 【返回值】块在关系范围内返回 true。
 *
 * Check whether a block number is past the end of the relation.  This can
 * happen after WAL replay, if the FSM reached disk but newly-extended pages
 * it refers to did not.
 */
static bool
fsm_does_block_exist(Relation rel, BlockNumber blknumber)
{
	SMgrRelation smgr = RelationGetSmgr(rel);

	/*
	 * If below the cached nblocks, the block surely exists.  Otherwise, we
	 * face a trade-off.  We opt to compare to a fresh nblocks, incurring
	 * lseek() overhead.  The alternative would be to assume the block does
	 * not exist, but that would cause FSM to set zero space available for
	 * blocks that main fork extension just recorded.
	 */
	return ((BlockNumberIsValid(smgr->smgr_cached_nblocks[MAIN_FORKNUM]) &&
			 blknumber < smgr->smgr_cached_nblocks[MAIN_FORKNUM]) ||
			blknumber < RelationGetNumberOfBlocks(rel));
}
