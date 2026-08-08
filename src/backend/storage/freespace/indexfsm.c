/*-------------------------------------------------------------------------
 *
 * indexfsm.c
 *	  POSTGRES free space map for quickly finding free pages in relations
 *
 *
 * 【模块总览(中文)】
 * 本文件是索引文件的 FSM 入口:为需要"快速找到空闲页"的索引访问方法
 * (目前主要是 btree)提供与堆表 FSM 相同的服务,但语义退化为"二分":
 * 只记录"整页空闲"或"已使用",不记录精确空闲量。
 *
 * 实现上完全复用堆表的同一套 FSM 实现(freespace.c + fsmpage.c):
 * - 用类别 0 表示"页已使用"(没有空闲空间);
 * - 用类别 (BLCKSZ - 1)(经 fsm_space_avail_to_cat 换算落在最高档
 *   255)表示"整页空闲";
 * - "找一个空闲页"通过 GetPageWithFreeSpace(rel, BLCKSZ / 2) 完成:
 *   BLCKSZ/2 与 BLCKSZ-1 属于同一档位(都 >= MaxFSMRequestSize),因此
 *   记录与查询的判定一致。
 * 索引 AM 通过本文件"借"堆表 FSM 的能力,无需另写一套数据结构;与
 * freespace.c 的分工:这里只做"空/不空"的语义包装,所有树操作都转发
 * 到堆表那套实现。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/freespace/indexfsm.c
 *
 *
 * NOTES:
 *
 *	This is similar to the FSM used for heap, in freespace.c, but instead
 *	of tracking the amount of free space on pages, we only track whether
 *	pages are completely free or in-use. We use the same FSM implementation
 *	as for heaps, using 0 to denote used pages, and (BLCKSZ - 1) for unused.
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "storage/freespace.h"
#include "storage/indexfsm.h"

/*
 * Exported routines
 */

/*
 * GetFreeIndexPage
 *      (中文)从 FSM 取一个空闲页,并立刻标记为已使用
 *
 * 【作用】索引 AM 扩展/分裂需要新页时调用:要求"整页空闲"(请求
 * BLCKSZ/2 字节,对应最高档 255,见文件头),取到后立即通过
 * RecordUsedIndexPage 把它登记为"已使用",防止并发请求拿到同一页。
 *
 * 【设计思想】"取用 + 标记已用"在此组合成原子语义:搜索与标记之间
 * 不留窗口,避免多个后端同时选中同一页;而 FSM 本身只是提示,即便
 * 标记因并发稍有偏差,索引 AM 在拿到缓冲锁后仍会验证页可用性。
 *
 * 【参数】rel —— 索引关系。
 * 【返回值】空闲页块号;FSM 中无空闲页时返回 InvalidBlockNumber
 * (调用者应扩展索引文件)。
 *
 * GetFreeIndexPage - return a free page from the FSM
 *
 * As a side effect, the page is marked as used in the FSM.
 */
BlockNumber
GetFreeIndexPage(Relation rel)
{
	BlockNumber blkno = GetPageWithFreeSpace(rel, BLCKSZ / 2);

	if (blkno != InvalidBlockNumber)
		RecordUsedIndexPage(rel, blkno);

	return blkno;
}

/*
 * RecordFreeIndexPage
 *      (中文)把一页标记为"空闲",归还给 FSM
 *
 * 【作用】索引页被清空(如 btree 页删除、合并后)时调用,在 FSM 中
 * 记录该块有 BLCKSZ-1 字节空闲(换算为最高档 255,即"整页可用")。
 *
 * 【参数】
 *   rel        —— 索引关系;
 *   freeBlock  —— 要标记为空闲的块号。
 * 【返回值】无。
 *
 * RecordFreeIndexPage - mark a page as free in the FSM
 */
void
RecordFreeIndexPage(Relation rel, BlockNumber freeBlock)
{
	RecordPageWithFreeSpace(rel, freeBlock, BLCKSZ - 1);
}


/*
 * RecordUsedIndexPage
 *      (中文)把一页标记为"已使用"
 *
 * 【作用】索引页被占用(插入第一项、被分裂占用等)后调用,在 FSM 中
 * 记录该块空闲量为 0(类别 0),使后续搜索不再返回它。
 *
 * 【参数】
 *   rel       —— 索引关系;
 *   usedBlock —— 要标记为已使用的块号。
 * 【返回值】无。
 *
 * RecordUsedIndexPage - mark a page as used in the FSM
 */
void
RecordUsedIndexPage(Relation rel, BlockNumber usedBlock)
{
	RecordPageWithFreeSpace(rel, usedBlock, 0);
}

/*
 * IndexFreeSpaceMapVacuum
 *      (中文)扫描并修复索引 FSM 的不一致(转发给堆表实现)
 *
 * 【作用】VACUUM 索引时调用:重建上层节点,使"记录上涨"的新空闲值对
 * 全树搜索可见。由于索引 FSM 与堆表 FSM 是同一套实现,这里直接转发
 * FreeSpaceMapVacuum。
 *
 * 【参数】rel —— 索引关系。
 * 【返回值】无。
 *
 * IndexFreeSpaceMapVacuum - scan and fix any inconsistencies in the FSM
 */
void
IndexFreeSpaceMapVacuum(Relation rel)
{
	FreeSpaceMapVacuum(rel);
}
