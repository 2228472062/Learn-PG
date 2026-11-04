/*-------------------------------------------------------------------------
 *
 * xlogstats.c
 *		Functions for WAL Statistics
 *
 * Copyright (c) 2022-2026, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *		src/backend/access/transam/xlogstats.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件提供 WAL 记录的“离线/按需”统计功能，而不是 pg_stat_wal 视图的运行时计数器。
 *
 * 一、功能与调用场景
 *   XLogRecGetLen() 从一条已解码的 WAL 记录中分离出普通记录长度（rec_len）和
 *   full page image（FPI）长度（fpi_len）；XLogRecStoreStats() 在此基础上，按
 *   resource manager（RmgrId）以及“RmgrId + xl_info 高 4 位”两个维度累加记录条数、
 *   普通字节数和 FPI 字节数。结果保存在调用者提供的 XLogStats 中，由调用者负责输出：
 *     - src/bin/pg_waldump：--stats[=record] 选项在遍历 WAL 时调用，最终打印
 *       “WAL statistics between ...”表格；
 *     - contrib/pg_walinspect：SQL 函数 pg_get_wal_stats() /
 *       pg_get_wal_stats_till_end_of_wal() 在指定 LSN 区间内扫描 WAL 并调用，
 *       再把结果转换成元组返回。
 *   因此本文件既会被前端工具（定义 FRONTEND）链接，也会被后端扩展链接。
 *
 * 二、与 pg_stat_wal 的关系（两者容易混淆，特此说明）
 *   pg_stat_wal 视图（底层 SQL 函数为 pg_stat_get_wal()）由
 *   src/backend/utils/activity/pgstat_wal.c 实现，与本文件无关。它的采集方式是：
 *   各后端在插入 WAL 时把本次工作量累积到进程本地的 WalUsage（pgWalUsage）计数器
 *   （wal_records、wal_fpi、wal_bytes、wal_fpi_bytes、wal_buffers_full）；在
 *   pgstat_report_wal() / pgstat_report_stat() 时，用当前值与上一次上报值相减得到
 *   增量，再在 LWLock 保护下合并进统计共享内存中的 PgStatShared_Wal
 *   （内含 LWLock 和 PgStat_WalStats）；查询时通过 pgstat 快照机制读取。
 *   那是“数据库运行期间累计发生量”的在线统计，粒度为全集群。
 *   本文件则是“读取 WAL 字节流后重新计算”的离线统计，粒度为 rmgr / 记录类型，
 *   不访问任何共享内存，也不参与 pg_stat_wal 的采集。
 *   两者口径也不同：XLogStats 的 rec_len 不含 FPI，只有 rec_len + fpi_len 才等于
 *   记录总长；而 pg_stat_wal.wal_bytes 是写入 WAL 的记录总字节数。
 *
 * 三、数据结构
 *   XLogStats、XLogRecStats、MAX_XLINFO_TYPES 定义在 access/xlogstats.h：
 *     - XLogRecStats 保存一个统计桶的 count、rec_len、fpi_len；
 *     - XLogStats 保存总 count、rmgr_stats[RM_MAX_ID + 1] 以及
 *       record_stats[RM_MAX_ID + 1][MAX_XLINFO_TYPES]；
 *     - 在 FRONTEND 下还包含 startptr/endptr 两个 LSN，仅 pg_waldump 使用。
 *   这些结构由调用者分配（通常在栈上），生命周期限于一次扫描；本文件不持有全局
 *   状态，也没有共享内存结构、锁或持久化。
 *
 * 四、设计思想
 *   - 流式单遍扫描：每读一条记录就原地累加，不缓存 WAL 记录，内存占用固定；
 *   - 两级聚合：先按 rmgr 汇总，再按 rmgr 内的记录子类型细分，既能看到“哪类资源
 *     写得多”，也能看到具体是哪种操作；
 *   - 把 FPI 从记录长度中单独拆出：FPI 往往占据 WAL 的绝大部分，分开统计才能
 *     判断 WAL 膨胀是“记录多”还是“全页写多”；
 *   - 只使用 WAL 记录头和解码后的 block 元数据，不调用各 rmgr 的 redo/desc 回调，
 *     因此统计过程安全、快速，且不需要构造完整的页面内容。
 */
#include "postgres.h"

#include "access/xlogreader.h"
#include "access/xlogstats.h"

/*
 * 中文注释：
 * 只包含 xlogreader.h 与 xlogstats.h：前者提供已解码 WAL 记录的只读访问宏，
 * 后者提供统计聚合结构。这里刻意不依赖 xlog.h、pgstat.h 等后端统计设施，使本文件
 * 可以在 pg_waldump 这类 FRONTEND 程序中链接。
 */

/*
 * Calculate the size of a record, split into !FPI and FPI parts.
 */
/*
 * 中文注释：
 * 计算一条 WAL 记录的长度构成，分别输出“非 FPI 部分”和“FPI 部分”。
 *
 * 参数：
 *   record  - 已经由 xlogreader 解码的 WAL 记录（XLogReaderState *），不能为 NULL；
 *   rec_len - 输出参数，返回 xl_tot_len 减去所有 FPI 数据后的字节数。它包含
 *             XLogRecord 头、block header、main data 以及非 FPI 的 block data，
 *             可以理解为“记录本身（不含整页镜像）的大小”；
 *   fpi_len - 输出参数，返回本记录中所有 full page image 数据长度之和。
 *
 * 返回值：无（void），结果通过两个输出指针返回。
 *
 * 实现要点与并发/副作用：
 *   - 遍历 [0, XLogRecMaxBlockId(record)] 的所有 block 槽位，跳过未被引用的槽位；
 *     只有 XLogRecHasBlockImage() 为真时才累加 bimg_len。bimg_len 是解码器从
 *     block header 中读出的、WAL 中实际存放的镜像长度（可能是压缩后的长度）；
 *     这里不计算 hole，也不把镜像还原成 BLCKSZ。
 *   - rec_len 用减法得到：xl_tot_len - fpi_len。这样既避免重复解析记录布局，也保证
 *     rec_len + fpi_len == xl_tot_len；但要注意 FPI 所在的 block header 本身仍算在
 *     rec_len 中（因为只减去了 bimg_len）。
 *   - 使用了 xlogreader 的“私有”解码结果（原注释中的 XXX 已说明），因此调用者必须
 *     保证传入的是 XLogReadRecord()/XLogNextRecord() 刚返回且仍有效的记录；解码器
 *     已经校验过记录完整性，本函数不再做额外校验。
 *   - 纯读函数，不修改 record，不加锁，也没有全局状态；但 XLogReaderState 实例不是
 *     并发安全的，对同一实例的调用仍需由调用者串行化。
 */
void
XLogRecGetLen(XLogReaderState *record, uint32 *rec_len,
			  uint32 *fpi_len)
{
	int			block_id;

	/*
	 * Calculate the amount of FPI data in the record.
	 *
	 * XXX: We peek into xlogreader's private decoded backup blocks for the
	 * bimg_len indicating the length of FPI data.
	 */
	*fpi_len = 0;
	for (block_id = 0; block_id <= XLogRecMaxBlockId(record); block_id++)
	{
		if (!XLogRecHasBlockRef(record, block_id))
			continue;

		if (XLogRecHasBlockImage(record, block_id))
			*fpi_len += XLogRecGetBlock(record, block_id)->bimg_len;
	}

	/*
	 * Calculate the length of the record as the total length - the length of
	 * all the block images.
	 */
	*rec_len = XLogRecGetTotalLen(record) - *fpi_len;
}

/*
 * Store per-rmgr and per-record statistics for a given record.
 */
/*
 * 中文注释：
 * 把一条 WAL 记录的统计信息累加到调用者提供的 XLogStats 聚合器中。
 *
 * 参数：
 *   stats  - 调用者分配的统计累加器，必须在首次调用前清零（通常用 {0} 或 memset）；
 *            函数只做累加，不负责初始化，也不负责输出；
 *   record - 已解码的 WAL 记录，必须非 NULL。函数会读取记录头中的 xl_rmid、
 *            xl_info、xl_tot_len，以及解码后的 block 信息。
 *
 * 返回值：无（void）。副作用是原地修改 stats 的 count、rmgr_stats 和 record_stats。
 *
 * 统计维度：
 *   1. stats->count 是扫描到的记录总数，用于计算百分比；
 *   2. rmgr_stats[rmid] 按 resource manager 汇总；
 *   3. record_stats[rmid][recid] 按“rmgr + 记录子类型”汇总。recid 取 xl_info 的
 *      高 4 位（xl_info >> 4），因为 WAL 记录头的低 4 位是跨 rmgr 的通用标志
 *      （XLR_INFO_MASK），高 4 位才由各 rmgr 自由定义；这样每个 rmgr 最多有
 *      MAX_XLINFO_TYPES（16）个细分桶。
 *
 * XACT 记录的特殊处理：
 *   RM_XACT_ID 的 xl_info 高 4 位中，0x80 是 XLOG_XACT_HAS_INFO 标志位，低 3 位才是
 *   操作码（XLOG_XACT_OPMASK == 0x70）。若直接使用 info >> 4，带 HAS_INFO 的提交/
 *   中止记录会落到高半区的另一组桶（recid 8..14）里，同一操作被拆成两份。因此这里
 *   对 recid 再与 0x07 相与，把“是否携带附加信息”折叠掉，只按操作码聚合。
 *   注意：并非所有 rmgr 的高 4 位都严格表示操作码，有的用作标志位；本函数只按位
 *   模式分桶，桶的名称由输出方调用对应 rmgr 的 rm_identify() 解释。
 *
 * 并发与设计：
 *   - 本函数不加锁、不访问共享内存，也不是线程安全的；并发调用必须使用不同的
 *     XLogStats，或由调用者串行化。pg_waldump 与 pg_walinspect 都是单线程顺序
 *     扫描，所以直接使用栈上的聚合器即可。
 *   - 先调用 XLogRecGetLen() 一次，得到 rec_len/fpi_len，再同时更新两级统计，避免
 *     重复遍历 block 数组。
 *   - Assert 仅在启用断言的构建中检查参数，生产构建不会做空指针保护；调用者必须
 *     保证 stats 和 record 有效。
 *   - 计数字段使用 uint64，大范围或长时间扫描不会像 32 位计数器那样轻易溢出。
 */
void
XLogRecStoreStats(XLogStats *stats, XLogReaderState *record)
{
	RmgrId		rmid;
	uint8		recid;
	uint32		rec_len;
	uint32		fpi_len;

	Assert(stats != NULL && record != NULL);

	stats->count++;

	rmid = XLogRecGetRmid(record);

	XLogRecGetLen(record, &rec_len, &fpi_len);

	/* Update per-rmgr statistics */

	stats->rmgr_stats[rmid].count++;
	stats->rmgr_stats[rmid].rec_len += rec_len;
	stats->rmgr_stats[rmid].fpi_len += fpi_len;

	/*
	 * Update per-record statistics, where the record is identified by a
	 * combination of the RmgrId and the four bits of the xl_info field that
	 * are the rmgr's domain (resulting in sixteen possible entries per
	 * RmgrId).
	 */

	recid = XLogRecGetInfo(record) >> 4;

	/*
	 * XACT records need to be handled differently. Those records use the
	 * first bit of those four bits for an optional flag variable and the
	 * following three bits for the opcode. We filter opcode out of xl_info
	 * and use it as the identifier of the record.
	 */
	if (rmid == RM_XACT_ID)
		recid &= 0x07;

	stats->record_stats[rmid][recid].count++;
	stats->record_stats[rmid][recid].rec_len += rec_len;
	stats->record_stats[rmid][recid].fpi_len += fpi_len;
}
