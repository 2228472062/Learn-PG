/*-------------------------------------------------------------------------
 *
 * itemptr.c
 *	  POSTGRES disk item pointer code.
 *
 * 【模块总览(中文)】
 * 本文件实现"行指针(ItemPointer)"上的几个基本运算。行指针(又称 TID,
 * tuple identifier)是 PostgreSQL 定位磁盘上一条记录的二元组 (块号,
 * 行号),ItemPointerData 内部由 ip_blkid(块号,4 字节)与 ip_posid(行号,
 * 2 字节)组成,恰好 6 字节(见文件开头的静态断言),逻辑结构等价于
 * (BlockNumber, OffsetNumber)。其类型定义与绝大部分配套宏(如
 * ItemPointerGetBlockNumber、ItemPointerSet、ItemPointerIsValid)都在
 * src/include/storage/itemptr.h 中,本文件只实现少数无法用宏表达的运算:
 * - 相等判断与三态比较(ItemPointerEquals / ItemPointerCompare),供
 *   去重、排序、B-tree 等场景使用;
 * - 类型范围内的"加减一"运算(ItemPointerInc / ItemPointerDec),供
 *   顺序扫描等需要"遍历整个 TID 空间"的算法使用。
 * 这些函数都是纯计算,不涉及任何锁、缓冲或磁盘 I/O。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/page/itemptr.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "storage/itemptr.h"


/*
 * ItemPointerData 必须是恰好 6 字节:它在表/索引文件中作为固定宽度的
 * 磁盘结构出现,任何 padding 都会破坏磁盘布局兼容性。此静态断言在
 * 编译期验证结构体内存布局,防止未来修改结构体时无意破坏该不变量。
 * (此断言同时暗示"先比较块号再比较行号"的字段访问方式是安全的。)
 *
 * We really want ItemPointerData to be exactly 6 bytes.
 */
StaticAssertDecl(sizeof(ItemPointerData) == 3 * sizeof(uint16),
				 "ItemPointerData struct is improperly padded");

/*
 * ItemPointerEquals
 *      (中文)判断两个行指针是否指向同一条记录
 *
 * 【作用】比较两个行指针的块号与行号:两者都相等则说明指向同一条记录,
 * 返回 true,否则返回 false。常用于判断"两条元组是否来自同一位置"、
 * "两次扫描是否返回了同一行"等场景。
 *
 * 【设计思想】这是对"6 字节整体比较"的语义化实现:不直接按字节比较
 * 结构体内存,而是分别比较块号与行号两个逻辑字段。一方面依赖文件开头
 * 的静态断言(结构体无 padding)保证字段访问安全;另一方面,内部使用的
 * ItemPointerGet* 宏带有合法性断言——两个指针必须都是"合法"的(块号、
 * 行号均非 0)。若需要对可能不合法的指针(如用户直接构造的 TID)做比较,
 * 应改用 ItemPointerCompare(它使用无断言的 NoCheck 版本取值)。
 *
 * 【参数】
 *   pointer1 —— 第一个行指针;
 *   pointer2 —— 第二个行指针。
 * 【返回值】两者指向同一条记录返回 true,否则返回 false。
 *
 * ItemPointerEquals
 *	Returns true if both item pointers point to the same item,
 *	 otherwise returns false.
 *
 * Note:
 *	Asserts that the disk item pointers are both valid!
 */
bool
ItemPointerEquals(const ItemPointerData *pointer1, const ItemPointerData *pointer2)
{
	if (ItemPointerGetBlockNumber(pointer1) ==
		ItemPointerGetBlockNumber(pointer2) &&
		ItemPointerGetOffsetNumber(pointer1) ==
		ItemPointerGetOffsetNumber(pointer2))
		return true;
	else
		return false;
}

/*
 * ItemPointerCompare
 *      (中文)行指针之间的通用比较(B-tree 风格三态比较)
 *
 * 【作用】按"先块号、后行号"的字典序比较两个行指针,返回 -1 / 0 / 1
 * 三态结果,可直接用于 qsort、B-tree 键比较或范围判断。
 *
 * 【设计思想】
 * - 行号字段 ip_posid 在 heap 中通常是"页内行指针数组下标(1 基)",但
 *   在用户直接构造的 TID 类型值中可以为 0,因此这里特意使用不带断言
 *   检查的 NoCheck 版本宏取值,避免对任意输入触发 Assert(与
 *   ItemPointerEquals 形成对照);
 * - 块号(uint32)优先、行号(uint16)其次的字典序,正好对应物理扫描顺序:
 *   同一块的记录聚在一起、块内按行号升序,符合排序输出的自然期望。
 *
 * 【参数】
 *   arg1、arg2 —— 待比较的两个行指针。
 * 【返回值】arg1 < arg2 返回 -1;两者相等返回 0;arg1 > arg2 返回 1。
 *
 * ItemPointerCompare
 *		Generic btree-style comparison for item pointers.
 */
int32
ItemPointerCompare(const ItemPointerData *arg1, const ItemPointerData *arg2)
{
	/*
	 * Use ItemPointerGet{Offset,Block}NumberNoCheck to avoid asserting
	 * ip_posid != 0, which may not be true for a user-supplied TID.
	 */
	BlockNumber b1 = ItemPointerGetBlockNumberNoCheck(arg1);
	BlockNumber b2 = ItemPointerGetBlockNumberNoCheck(arg2);

	if (b1 < b2)
		return -1;
	else if (b1 > b2)
		return 1;
	else if (ItemPointerGetOffsetNumberNoCheck(arg1) <
			 ItemPointerGetOffsetNumberNoCheck(arg2))
		return -1;
	else if (ItemPointerGetOffsetNumberNoCheck(arg1) >
			 ItemPointerGetOffsetNumberNoCheck(arg2))
		return 1;
	else
		return 0;
}

/*
 * ItemPointerInc
 *      (中文)行指针自增 1(仅受字段类型范围限制,结果可能不是合法行指针)
 *
 * 【作用】把行指针"向后"移动一位:行号加 1;行号达到 uint16 上限
 * (65535)时进位到下一块(行号回到 0);块号已是类型上限时保持不动。
 *
 * 【设计思想】这里刻意只遵守字段类型(OffsetNumber 为 uint16、
 * BlockNumber 为 uint32)的边界,而不遵守"行号必须 >= FirstOffsetNumber
 * 且 <= MaxOffsetNumber"的语义约束,因此结果可能不是一个合法行指针
 * (例如行号为 0)。这是为"遍历整个 TID 空间"的算法准备的(如顺序扫描
 * 推进下一个候选位置):调用者需要在每一步之后再用 OffsetNumberIsValid
 * 等宏判断是否越界。"行号上限用 65535 而非 MaxOffsetNumber"同样是
 * 类型级而非语义级的选择,与 Dec 对称。
 *
 * 【参数】pointer —— 要自增的行指针(原地修改)。
 * 【返回值】无。
 *
 * ItemPointerInc
 *		Increment 'pointer' by 1 only paying attention to the ItemPointer's
 *		type's range limits and not MaxOffsetNumber and FirstOffsetNumber.
 *		This may result in 'pointer' becoming !OffsetNumberIsValid.
 *
 * If the pointer is already the maximum possible values permitted by the
 * range of the ItemPointer's types, then do nothing.
 */
void
ItemPointerInc(ItemPointer pointer)
{
	BlockNumber blk = ItemPointerGetBlockNumberNoCheck(pointer);
	OffsetNumber off = ItemPointerGetOffsetNumberNoCheck(pointer);

	if (off == PG_UINT16_MAX)
	{
		if (blk != InvalidBlockNumber)
		{
			off = 0;
			blk++;
		}
	}
	else
		off++;

	ItemPointerSet(pointer, blk, off);
}

/*
 * ItemPointerDec
 *      (中文)行指针自减 1(仅受字段类型范围限制,结果可能不是合法行指针)
 *
 * 【作用】把行指针"向前"移动一位:行号减 1;行号已为 0 时向回借位到
 * 上一块(行号回到 uint16 上限 65535);块号已是 0 时保持不动。与
 * ItemPointerInc 互为逆运算。
 *
 * 【设计思想】与 Inc 完全对称:同样只遵守字段类型边界。这里依赖
 * FirstOffsetNumber 恰好为 1 而非 0 的事实——"行号 0"在语义上永远
 * 非法,于是可以放心把它当作"向上一块借位"的哨兵值;若行号 0 是合法
 * 值,这套借位逻辑就不成立了。
 *
 * 【参数】pointer —— 要自减的行指针(原地修改)。
 * 【返回值】无。
 *
 * ItemPointerDec
 *		Decrement 'pointer' by 1 only paying attention to the ItemPointer's
 *		type's range limits and not MaxOffsetNumber and FirstOffsetNumber.
 *		This may result in 'pointer' becoming !OffsetNumberIsValid.
 *
 * If the pointer is already the minimum possible values permitted by the
 * range of the ItemPointer's types, then do nothing.  This does rely on
 * FirstOffsetNumber being 1 rather than 0.
 */
void
ItemPointerDec(ItemPointer pointer)
{
	BlockNumber blk = ItemPointerGetBlockNumberNoCheck(pointer);
	OffsetNumber off = ItemPointerGetOffsetNumberNoCheck(pointer);

	if (off == 0)
	{
		if (blk != 0)
		{
			off = PG_UINT16_MAX;
			blk--;
		}
	}
	else
		off--;

	ItemPointerSet(pointer, blk, off);
}
