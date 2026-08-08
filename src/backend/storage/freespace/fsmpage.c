/*-------------------------------------------------------------------------
 *
 * fsmpage.c
 *	  routines to search and manipulate one FSM page.
 *
 *
 * 【模块总览(中文)】
 * 本文件实现"单个 FSM 页"内部的数据结构与算法,向上对 freespace.c
 * 提供"页 = 若干槽"的黑盒 API:fsm_set_avail / fsm_get_avail /
 * fsm_get_max_avail / fsm_search_avail / fsm_truncate_avail /
 * fsm_rebuild_page。freespace.c 通过它们把 FSM 当作"页内树 + 页间树"
 * 的两层结构使用,本文件完全不知道"页间树"的存在。
 *
 * 页内布局(见 fsm_internals.h 的 FSMPageData,数据结构细节参考
 * src/backend/storage/freespace/README):页头之后(PageGetContents)紧跟
 * fp_nodes 数组,按"数组下标即完全二叉树节点号"的方式存放一棵二叉树:
 * - 根在下标 0,节点 x 的左孩子 2x+1、右孩子 2x+2、父节点 (x-1)/2
 *   (见本文件开头的三个宏);
 * - 前 NonLeafNodesPerPage(即 BLCKSZ/2 - 1)个元素是非叶节点,其余
 *   LeafNodesPerPage 个是叶子;每个叶子对应一个"槽",槽值 0-255 表示
 *   该堆块的空闲类别;
 * - 每个非叶节点的值 = 其两个孩子的最大值,因此根值 = 全页最大空闲;
 * - 数组总长度 NodesPerPage 由"BLCKSZ - 页头 - fp_next_slot 字段"算
 *   出,恰好把整页排满(BLCKSZ = 8K 时叶节点 4020 个,即每个 FSM 页
 *   覆盖 4020 个堆块)。
 * 另有 fp_next_slot 字段:记录"下一次搜索从哪个槽开始"(轮转指针),把
 * 并发请求分散到不同的槽,减少热点页的争用;它不带锁更新(用 hint
 * bits 基础设施),因此定义为 int 以保证原子可读写。
 *
 * 页内算法要点:
 * - 写槽 fsm_set_avail:自下而上传播,直到父节点无需变化为止(空闲度
 *   下降一路改到根;上涨常在页内一小段就停住,见 freespace.c 对"新
 *   空闲要等 VACUUM 才可见"的解释);
 * - 搜索 fsm_search_avail:从轮转指针开始,"右移 + 上爬"逐步扩大搜索
 *   三角,命中后向下优先走左孩子,保证返回"起点右侧第一个可用槽"且
 *   花费 O(log n) 步;命中"父节点承诺但孩子不满足"的 torn page 时
 *   重建并重试;
 * - 重建 fsm_rebuild_page:从最底层非叶节点向上重算全部内部节点,用于
 *   修复 torn page 等导致的树不一致,以及截断(清零一批叶子)后的
 *   重建。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/freespace/fsmpage.c
 *
 * NOTES:
 *
 *	The public functions in this file form an API that hides the internal
 *	structure of a FSM page. This allows freespace.c to treat each FSM page
 *	as a black box with SlotsPerPage "slots". fsm_set_avail() and
 *	fsm_get_avail() let you get/set the value of a slot, and
 *	fsm_search_avail() lets you search for a slot with value >= X.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "storage/bufmgr.h"
#include "storage/fsm_internals.h"

/* 页内二叉树导航宏:数组下标 x 处节点的左孩子 / 右孩子 / 父节点
 * (根为下标 0 的完全二叉树的标准数组表示)。 */
#define leftchild(x)	(2 * (x) + 1)
#define rightchild(x)	(2 * (x) + 2)
#define parentof(x)		(((x) - 1) / 2)

/*
 * rightneighbor
 *      (中文)求节点在同一层的右邻居(越过层右边界时回绕到上一层最左)
 *
 * 【作用】搜索算法"向右扩展"的基础操作:把 x 加 1(通常到达其右兄弟);
 * 若因此越过了本层最右端(即 x+1 是 2 的幂——每层最左节点的编号形如
 * 2^level - 1),则回到其父节点,实现"回绕到上一层最左端"。
 *
 * 【设计思想】节点编号与层的关系:第 level 层的最左节点编号是
 * 2^level - 1。当 x+1 恰好是 2 的幂(用标准的二进制技巧 (x+1)&x == 0
 * 判定)时,说明 x 是本层最后一个节点,右移一位就会进入下一层;因为
 * 搜索过程随即上爬(parentof),这里只需把 x 折回其父节点,就能保证
 * 搜索覆盖全页而不越界(叶层右端缺失的节点也因此永远不会被访问到)。
 *
 * 【参数】x —— 当前节点下标。
 * 【返回值】"右移一位"后落在合法层内的节点下标。
 *
 * Find right neighbor of x, wrapping around within the level
 */
static int
rightneighbor(int x)
{
	/*
	 * Move right. This might wrap around, stepping to the leftmost node at
	 * the next level.
	 */
	x++;

	/*
	 * Check if we stepped to the leftmost node at next level, and correct if
	 * so. The leftmost nodes at each level are numbered x = 2^level - 1, so
	 * check if (x + 1) is a power of two, using a standard
	 * twos-complement-arithmetic trick.
	 */
	if (((x + 1) & x) == 0)
		x = parentof(x);

	return x;
}

/*
 * fsm_set_avail
 *      (中文)设置页内某槽的值并向上传播(返回页是否被修改)
 *
 * 【作用】把槽 slot 的值设为 value(0-255),并沿父链更新祖先节点
 * (每个非叶节点的值 = 两个孩子最大值),直到某个祖先的值不变为止——
 * 再往上必然也不变,传播即可停止。
 *
 * 【设计思想】
 * - 提前返回优化:值未变、且新值不超过根值时,树无需任何改动,直接
 *   返回 false(新值比根还大说明树已损坏,需走重建分支);
 * - 传播的停止条件决定了 FSM 的"提示"语义:空闲度下降(如插入后记录
 *   变 0)会一路改到根,立即对其他请求者可见;空闲度上涨则常在页内
 *   一小段就停下,跨页上层要等 FreeSpaceMapVacuum(见 freespace.c);
 * - 若写入后出现 value > 根值的自相矛盾(理论不可能,除非页被写坏),
 *   调用 fsm_rebuild_page 整体重建自愈;
 * - 调用者必须持有页的排他锁。
 *
 * 【参数】
 *   page  —— FSM 页;
 *   slot  —— 槽号(0..LeafNodesPerPage-1);
 *   value —— 新的类别值。
 * 【返回值】页内容是否被修改(供调用者决定是否标脏)。
 *
 * Sets the value of a slot on page. Returns true if the page was modified.
 *
 * The caller must hold an exclusive lock on the page.
 */
bool
fsm_set_avail(Page page, int slot, uint8 value)
{
	int			nodeno = NonLeafNodesPerPage + slot;
	FSMPage		fsmpage = (FSMPage) PageGetContents(page);
	uint8		oldvalue;

	Assert(slot < LeafNodesPerPage);

	oldvalue = fsmpage->fp_nodes[nodeno];

	/* If the value hasn't changed, we don't need to do anything */
	if (oldvalue == value && value <= fsmpage->fp_nodes[0])
		return false;

	fsmpage->fp_nodes[nodeno] = value;

	/*
	 * Propagate up, until we hit the root or a node that doesn't need to be
	 * updated.
	 */
	do
	{
		uint8		newvalue = 0;
		int			lchild;
		int			rchild;

		nodeno = parentof(nodeno);
		lchild = leftchild(nodeno);
		rchild = lchild + 1;

		newvalue = fsmpage->fp_nodes[lchild];
		if (rchild < NodesPerPage)
			newvalue = Max(newvalue,
						   fsmpage->fp_nodes[rchild]);

		oldvalue = fsmpage->fp_nodes[nodeno];
		if (oldvalue == newvalue)
			break;

		fsmpage->fp_nodes[nodeno] = newvalue;
	} while (nodeno > 0);

	/*
	 * sanity check: if the new value is (still) higher than the value at the
	 * top, the tree is corrupt.  If so, rebuild.
	 */
	if (value > fsmpage->fp_nodes[0])
		fsm_rebuild_page(page);

	return true;
}

/*
 * fsm_get_avail
 *      (中文)读取页内某槽的值
 *
 * 【作用】返回槽 slot 记录的空闲类别(0-255)。只读单个字节,在 PG
 * 支持的平台上天然原子,因此无需任何锁(调用者也可自行加共享锁以
 * 保证与相邻读取的一致性)。
 *
 * 【参数】
 *   page —— FSM 页;
 *   slot —— 槽号。
 * 【返回值】槽值(0-255)。
 *
 * Returns the value of given slot on page.
 *
 * Since this is just a read-only access of a single byte, the page doesn't
 * need to be locked.
 */
uint8
fsm_get_avail(Page page, int slot)
{
	FSMPage		fsmpage = (FSMPage) PageGetContents(page);

	Assert(slot < LeafNodesPerPage);

	return fsmpage->fp_nodes[NonLeafNodesPerPage + slot];
}

/*
 * fsm_get_max_avail
 *      (中文)读取页内根节点值(全页最大空闲类别)
 *
 * 【作用】返回根节点 fp_nodes[0] 的值,即本 FSM 页覆盖的所有堆块中
 * 最大的空闲类别。freespace.c 用它:① 判断整页是否值得继续向下搜索
 * (fsm_search);② 向父页上报本页的概值(fsm_vacuum_page)。同样是
 * 单个字节的只读,无需加锁。
 *
 * 【参数】page —— FSM 页。
 * 【返回值】根节点值(0-255)。
 *
 * Returns the value at the root of a page.
 *
 * Since this is just a read-only access of a single byte, the page doesn't
 * need to be locked.
 */
uint8
fsm_get_max_avail(Page page)
{
	FSMPage		fsmpage = (FSMPage) PageGetContents(page);

	return fsmpage->fp_nodes[0];
}

/*
 * fsm_search_avail
 *      (中文)在页内搜索值 >= minvalue 的槽(带轮转指针与左倾优先)
 *
 * 【作用】从 fp_next_slot 指向的槽开始,在页内二叉树中查找第一个
 * 值 >= minvalue 的叶子槽并返回槽号;整页都没有满足的返回 -1。
 * freespace.c 的 fsm_search 每层下行、fsm_set_and_search 的就地搜索
 * 都调用它。
 *
 * 【设计思想】核心是"右移 + 上爬"的搜索三角扩展算法(英文注释中的
 * 树形示例逐行解释了它):从起点叶子上爬时,若从右孩子上移则放弃当前
 * 三角形、转向其右侧的更大三角形;若从左孩子上移则并入父节点右子树。
 * 由此保证:
 * - 从不回看起点左侧的槽(配合轮转指针形成公平的轮转语义);
 * - 每步搜索范围翻倍,最多 O(log n) 步即可覆盖全页;
 * - 命中节点后向下时优先左孩子("左倾优先"),使同时满足时倾向较靠左
 *   (低块号)的槽,与 fp_next_slot 的复位逻辑(见 fsm_vacuum_page)共同
 *   鼓励使用低位块,便于未来截断关系;
 * - 叶层右侧缺失的节点(非满二叉树)永远不会被访问到。
 *
 * 鲁棒性与并发设计:
 * - torn page 可能让父节点承诺"两个儿子之一够",实际都不够;此时把
 *   页重建(fsm_rebuild_page,需要排他锁——只持共享锁则先升级)、标脏,
 *   然后从头重试;
 * - fp_next_slot 的更新刻意不做成排他操作:持有共享锁时借 hint bits
 *   基础设施修改(可能失败,只损失下一次搜索的起点质量),换取"纯搜索
 *   路径不用排他锁"的并发收益;
 * - advancenext 决定轮转指针指向"返回槽"还是"其后一个",由调用者决定
 *   是否避免立刻重复命中同一槽。
 *
 * 【参数】
 *   buf                 —— 目标 FSM 页缓冲区(须已 pin);
 *   minvalue            —— 需求类别;
 *   advancenext         —— true 时轮转指针指向返回槽的后一个;
 *   exclusive_lock_held —— 调用者是否已持有排他锁(是则省去锁升级)。
 * 【返回值】满足条件的槽号;无则 -1。
 *
 * Searches for a slot with category at least minvalue.
 * Returns slot number, or -1 if none found.
 *
 * The caller must hold at least a shared lock on the page, and this
 * function can unlock and lock the page again in exclusive mode if it
 * needs to be updated. exclusive_lock_held should be set to true if the
 * caller is already holding an exclusive lock, to avoid extra work.
 *
 * If advancenext is false, fp_next_slot is set to point to the returned
 * slot, and if it's true, to the slot after the returned slot.
 */
int
fsm_search_avail(Buffer buf, uint8 minvalue, bool advancenext,
				 bool exclusive_lock_held)
{
	Page		page = BufferGetPage(buf);
	FSMPage		fsmpage = (FSMPage) PageGetContents(page);
	int			nodeno;
	int			target;
	uint16		slot;

restart:

	/*
	 * Check the root first, and exit quickly if there's no leaf with enough
	 * free space
	 */
	if (fsmpage->fp_nodes[0] < minvalue)
		return -1;

	/*
	 * Start search using fp_next_slot.  It's just a hint, so check that it's
	 * sane.  (This also handles wrapping around when the prior call returned
	 * the last slot on the page.)
	 */
	target = fsmpage->fp_next_slot;
	if (target < 0 || target >= LeafNodesPerPage)
		target = 0;
	target += NonLeafNodesPerPage;

	/*----------
	 * Start the search from the target slot.  At every step, move one
	 * node to the right, then climb up to the parent.  Stop when we reach
	 * a node with enough free space (as we must, since the root has enough
	 * space).
	 *
	 * The idea is to gradually expand our "search triangle", that is, all
	 * nodes covered by the current node, and to be sure we search to the
	 * right from the start point.  At the first step, only the target slot
	 * is examined.  When we move up from a left child to its parent, we are
	 * adding the right-hand subtree of that parent to the search triangle.
	 * When we move right then up from a right child, we are dropping the
	 * current search triangle (which we know doesn't contain any suitable
	 * page) and instead looking at the next-larger-size triangle to its
	 * right.  So we never look left from our original start point, and at
	 * each step the size of the search triangle doubles, ensuring it takes
	 * only log2(N) work to search N pages.
	 *
	 * The "move right" operation will wrap around if it hits the right edge
	 * of the tree, so the behavior is still good if we start near the right.
	 * Note also that the move-and-climb behavior ensures that we can't end
	 * up on one of the missing nodes at the right of the leaf level.
	 *
	 * For example, consider this tree:
	 *
	 *		   7
	 *	   7	   6
	 *	 5	 7	 6	 5
	 *	4 5 5 7 2 6 5 2
	 *				T
	 *
	 * Assume that the target node is the node indicated by the letter T,
	 * and we're searching for a node with value of 6 or higher. The search
	 * begins at T. At the first iteration, we move to the right, then to the
	 * parent, arriving at the rightmost 5. At the second iteration, we move
	 * to the right, wrapping around, then climb up, arriving at the 7 on the
	 * third level.  7 satisfies our search, so we descend down to the bottom,
	 * following the path of sevens.  This is in fact the first suitable page
	 * to the right of (allowing for wraparound) our start point.
	 *----------
	 */
	nodeno = target;
	while (nodeno > 0)
	{
		if (fsmpage->fp_nodes[nodeno] >= minvalue)
			break;

		/*
		 * Move to the right, wrapping around on same level if necessary, then
		 * climb up.
		 */
		nodeno = parentof(rightneighbor(nodeno));
	}

	/*
	 * We're now at a node with enough free space, somewhere in the middle of
	 * the tree. Descend to the bottom, following a path with enough free
	 * space, preferring to move left if there's a choice.
	 */
	while (nodeno < NonLeafNodesPerPage)
	{
		int			childnodeno = leftchild(nodeno);

		if (childnodeno < NodesPerPage &&
			fsmpage->fp_nodes[childnodeno] >= minvalue)
		{
			nodeno = childnodeno;
			continue;
		}
		childnodeno++;			/* point to right child */
		if (childnodeno < NodesPerPage &&
			fsmpage->fp_nodes[childnodeno] >= minvalue)
		{
			nodeno = childnodeno;
		}
		else
		{
			/*
			 * Oops. The parent node promised that either left or right child
			 * has enough space, but neither actually did. This can happen in
			 * case of a "torn page", IOW if we crashed earlier while writing
			 * the page to disk, and only part of the page made it to disk.
			 *
			 * Fix the corruption and restart.
			 */
			RelFileLocator rlocator;
			ForkNumber	forknum;
			BlockNumber blknum;

			BufferGetTag(buf, &rlocator, &forknum, &blknum);
			elog(DEBUG1, "fixing corrupt FSM block %u, relation %u/%u/%u",
				 blknum, rlocator.spcOid, rlocator.dbOid, rlocator.relNumber);

			/* make sure we hold an exclusive lock */
			if (!exclusive_lock_held)
			{
				LockBuffer(buf, BUFFER_LOCK_UNLOCK);
				LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
				exclusive_lock_held = true;
			}
			fsm_rebuild_page(page);
			MarkBufferDirtyHint(buf, false);
			goto restart;
		}
	}

	/* We're now at the bottom level, at a node with enough space. */
	slot = nodeno - NonLeafNodesPerPage;

	/*
	 * Update the next-target pointer. Note that we do this even if we're only
	 * holding a shared lock, on the grounds that it's better to use a shared
	 * lock and get a garbled next pointer every now and then, than take the
	 * concurrency hit of an exclusive lock.
	 *
	 * Without an exclusive lock, we need to use the hint bit infrastructure
	 * to be allowed to modify the page.
	 *
	 * Wrap-around is handled at the beginning of this function.
	 */
	if (exclusive_lock_held || BufferBeginSetHintBits(buf))
	{
		fsmpage->fp_next_slot = slot + (advancenext ? 1 : 0);

		if (!exclusive_lock_held)
			BufferFinishSetHintBits(buf, false, false);
	}

	return slot;
}

/*
 * fsm_truncate_avail
 *      (中文)把槽号 >= nslots 的所有槽清零(关系截断时用)
 *
 * 【作用】把从 nslots 起的叶子槽全部清零(表示"这些堆块已被截掉,无
 * 空闲"),并重建内部节点。返回页是否被修改。
 *
 * 【设计思想】FreeSpaceMapPrepareTruncateRel 在截断前调用:提前把
 * "越界堆块"标记为不可用,使搜索不会命中它们(否则每次命中都要额外
 * 做一次 fsm_does_block_exist 检查)。重建只在确实有槽被改(changed)
 * 时进行。
 *
 * 【参数】
 *   page   —— FSM 页;
 *   nslots —— 起始清零槽号(0 <= nslots < LeafNodesPerPage)。
 * 【返回值】页是否被修改。
 *
 * Sets the available space to zero for all slots numbered >= nslots.
 * Returns true if the page was modified.
 */
bool
fsm_truncate_avail(Page page, int nslots)
{
	FSMPage		fsmpage = (FSMPage) PageGetContents(page);
	uint8	   *ptr;
	bool		changed = false;

	Assert(nslots >= 0 && nslots < LeafNodesPerPage);

	/* Clear all truncated leaf nodes */
	ptr = &fsmpage->fp_nodes[NonLeafNodesPerPage + nslots];
	for (; ptr < &fsmpage->fp_nodes[NodesPerPage]; ptr++)
	{
		if (*ptr != 0)
			changed = true;
		*ptr = 0;
	}

	/* Fix upper nodes. */
	if (changed)
		fsm_rebuild_page(page);

	return changed;
}

/*
 * fsm_rebuild_page
 *      (中文)重建页内所有非叶节点(从叶子重新推出整棵树)
 *
 * 【作用】从最底层的非叶节点开始,自下而上、从右往左重算每个内部节点
 * (等于两个孩子最大值;没有右孩子时即左孩子值),直到根。返回是否有
 * 任何节点值被改动。
 *
 * 【设计思想】用于三类场景:① fsm_set_avail 发现"叶子值比根还大"的
 * 自相矛盾(损坏);② fsm_search_avail 发现 torn page 导致的父子不一
 * 致;③ fsm_truncate_avail 清零一批叶子之后。整段重建就是一次
 * O(页节点数) 的自底向上扫描,比逐槽向上传播快得多,且结果必然自洽
 * (无论叶子如何,重算出的内部节点一定满足"父 = 子最大值"的不变量)。
 *
 * 【参数】page —— FSM 页。
 * 【返回值】页内容是否被修改。
 *
 * Reconstructs the upper levels of a page. Returns true if the page
 * was modified.
 */
bool
fsm_rebuild_page(Page page)
{
	FSMPage		fsmpage = (FSMPage) PageGetContents(page);
	bool		changed = false;
	int			nodeno;

	/*
	 * Start from the lowest non-leaf level, at last node, working our way
	 * backwards, through all non-leaf nodes at all levels, up to the root.
	 */
	for (nodeno = NonLeafNodesPerPage - 1; nodeno >= 0; nodeno--)
	{
		int			lchild = leftchild(nodeno);
		int			rchild = lchild + 1;
		uint8		newvalue = 0;

		/* The first few nodes we examine might have zero or one child. */
		if (lchild < NodesPerPage)
			newvalue = fsmpage->fp_nodes[lchild];

		if (rchild < NodesPerPage)
			newvalue = Max(newvalue,
						   fsmpage->fp_nodes[rchild]);

		if (fsmpage->fp_nodes[nodeno] != newvalue)
		{
			fsmpage->fp_nodes[nodeno] = newvalue;
			changed = true;
		}
	}

	return changed;
}
