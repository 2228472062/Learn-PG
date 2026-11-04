/*-------------------------------------------------------------------------
 *
 * timeline.c
 *		Functions for reading and writing timeline history files.
 *
 * A timeline history file lists the timeline changes of the timeline, in
 * a simple text format. They are archived along with the WAL segments.
 *
 * The files are named like "<tli>.history". For example, if the database
 * starts up and switches to timeline 5, the timeline history file would be
 * called "00000005.history".
 *
 * Each line in the file represents a timeline switch:
 *
 * <parentTLI> <switchpoint> <reason>
 *
 *	parentTLI	ID of the parent timeline
 *	switchpoint XLogRecPtr of the WAL location where the switch happened
 *	reason		human-readable explanation of why the timeline was changed
 *
 * The fields are separated by tabs. Lines beginning with # are comments, and
 * are ignored. Empty lines are also ignored.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/timeline.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 时间线（timeline）历史文件的读取、探测与写入，是 WAL
 * 归档恢复（archive recovery）、时间点恢复（PITR）、流复制（streaming
 * replication）和级联备库（cascading standby）正确性的基础。
 *
 * 一、什么是 timeline
 *   - WAL 是一段连续、只能追加的日志流。每次归档恢复结束并准备接受新写入时，
 *     PostgreSQL 会让 WAL 从新的“时间线”继续，用一个递增的 TimeLineID 标识，
 *     以免新产生的 WAL 覆盖或混淆旧时间线上的 WAL。
 *   - WAL 段文件名形如 TTTTTTTTXXXXXXXXYYYYYYYY，其中前 8 位十六进制是生成
 *     该段的 timeline ID，后两段分别是 log 号和 segment 号。时间线切换点
 *     （switchpoint）是一个 LSN，切换之后产生的 WAL 属于子时间线。
 *   - 时间线在概念上形成一棵以 timeline 1 为根的树：每个新时间线都有一条指向
 *     父时间线的边。实际部署中常见的是单链，但不同备库分别提升可能产生分支。
 *
 * 二、pg_wal 中的 .history 文件
 *   - 名称：<8 位十六进制 TimeLineID>.history，例如 00000005.history。
 *     timeline 1 没有 history file，它是所有时间线的根。
 *   - 位置：数据目录下的 pg_wal 子目录（宏 XLOGDIR）。归档时 history file
 *     会与 WAL 段一起被 archive_command 复制到 WAL archive。
 *   - 格式：纯文本，每行一条时间线切换记录，字段之间用 tab 分隔：
 *         <parentTLI> <switchpoint> <reason>
 *     其中 parentTLI 是被离开的父时间线 ID；switchpoint 是切换发生的 WAL
 *     位置，格式为 %X/%08X（高 32 位/低 32 位）；reason 是人类可读的切换
 *     原因。以 # 开头的行和空行被忽略，行内多余内容也被忽略。记录按
 *     parentTLI 递增排列。
 *   - 语义：文件中的每一行表示“时间线 parentTLI 在 switchpoint 处结束，其
 *     子时间线从该 LSN 开始”。目标时间线自身没有对应行，它的有效区间从最后
 *     一条记录的 switchpoint 一直延伸到无穷；解析时会额外构造这个“tip”条目。
 *
 * 三、时间线切换的时机
 *   - 归档恢复（ArchiveRecoveryRequested 为 true，即存在 recovery.signal 或
 *     standby.signal）结束时，StartupXLOG() 调用 findNewestTimeLine() 选择新
 *     ID，再调用 writeTimeLineHistory() 创建新的 history file，随后把 WAL
 *     插入时间线切换为新 ID；end-of-recovery 记录会在恢复收尾阶段稍后写出。
 *     普通崩溃恢复（crash recovery）不切换时间线，直接延续原来的时间线。
 *   - 切换后，switchpoint 所在的 WAL 段会以新 timeline ID 重新建立，避免覆盖
 *     archive 中已经归档的旧段；更早的段仍然属于旧时间线。
 *   - 备库通过 restore_command 或 walreceiver 从归档/主库获取缺失的
 *     history file；级联备库以及以旧时间线为 recovery target 的 PITR 都依赖
 *     这些文件来解释 WAL 的归属。
 *
 * 四、与恢复、归档的关系
 *   - recovery_target_timeline、pg_control 中记录的时间线、checkpoint 所在的
 *     时间线，都需要结合 history file 才能解释。readTimeLineHistory() 把文件
 *     解析成 TimeLineHistoryEntry 列表；tliOfPointInHistory() 和
 *     tliSwitchPoint() 用于判断某个 LSN 属于哪条时间线、某条时间线在何处结束。
 *   - 归档：writeTimeLineHistory() 在 fsync 并原子改名后调用
 *     XLogArchiveNotify()，让 archive_command 尽快把 history file 归档；
 *     恢复时 readTimeLineHistory()/restoreTimeLineHistoryFiles() 则通过
 *     restore_command 把 history file 取回 pg_wal。
 *   - 正确性：history file 是 WAL 解释的一部分。文件缺失时按“没有父时间线”
 *     处理；文件存在但内容非法（语法错误、ID 不递增、目标 ID 不大于最后一条
 *     记录）时以 FATAL 终止启动，避免沿着错误的时间线继续恢复。
 *
 * 五、设计思想
 *   - 自包含：每个时间线的 history file 都先复制父文件再追加一行，因此只读
 *     最新的 history file 就能还原完整祖先链，不依赖旧文件仍然存在。
 *   - 原子发布：history file 先写入 pg_wal/xlogtemp.<pid>，fsync 后再用
 *     durable_rename() 原子改名到最终名称，读方不会看到写了一半的文件；
 *     writeTimeLineHistory() 还会断言目标文件尚不存在，防止覆盖已有时间线。
 *   - 顺序与连续：解析得到的列表按“最新在前”组织，各条目的 [begin, end)
 *     首尾相接；任何不连续都被视为历史损坏。
 *   - history file 很小且正常运行时只新增、不修改，读方无需加锁；流复制场景
 *     下由 walreceiver 原样落盘，保证与主库逐字节一致。
 */

/*
 * 中文注释：
 * 本文件没有定义全局变量、宏或结构体，核心类型和辅助设施来自头文件：
 *   - TimeLineHistoryEntry（access/timeline.h）：描述时间线历史中的一段 WAL。
 *     tli 是时间线 ID；begin 是闭区间起点，end 是开区间终点；begin/end 为
 *     InvalidXLogRecPtr 时分别表示“负无穷/正无穷”。列表按从新到旧排列，
 *     所有条目的区间首尾相接，覆盖从时间起点到无穷的整个 WAL 历史。
 *   - TimeLineID（access/xlogdefs.h）：uint32 类型的时间线 ID。
 *   - TLHistoryFileName()/TLHistoryFilePath()（access/xlog_internal.h）：
 *     static inline 辅助函数，由 TimeLineID 生成 "<8 位十六进制>.history"
 *     文件名或 "pg_wal/<8 位十六进制>.history" 完整路径；格式串为 %08X，
 *     因此 timeline 1 对应 00000001.history（实际不会创建该文件）。
 *   - XLOGDIR（access/xlog_internal.h）：WAL 目录名 "pg_wal"。
 *   - MAXPGPATH/MAXFNAMELEN：路径和文件名缓冲区大小。
 *   - WAIT_EVENT_TIMELINE_HISTORY_*（utils/wait_event.h）：pgstat 等待事件，
 *     用于把 history file 的读、写、fsync 等待归类到 timeline 相关操作。
 */

#include "postgres.h"

#include <sys/stat.h>
#include <unistd.h>

#include "access/timeline.h"
#include "access/xlog.h"
#include "access/xlog_internal.h"
#include "access/xlogarchive.h"
#include "access/xlogdefs.h"
#include "pgstat.h"
#include "storage/fd.h"
#include "utils/wait_event.h"

/*
 * Copies all timeline history files with id's between 'begin' and 'end'
 * from archive to pg_wal.
 */
/*
 * 中文注释：
 * 把 timeline ID 位于 [begin, end) 区间内的所有 .history 文件从 WAL archive
 * 复制到 pg_wal，供级联备库获取历史、重新归档到另一个 archive，以及后续
 * 运维/启动时使用。
 *
 * 调用场景：
 *   - StartupXLOG() 开始恢复时调用
 *     restoreTimeLineHistoryFiles(checkPoint.ThisTimeLineID, recoveryTargetTLI)，
 *     补齐 checkpoint 所在时间线到 recovery target 时间线之间的 history file；
 *   - rescanLatestTimeLine() 在恢复期间发现 archive 中出现新时间线后调用
 *     restoreTimeLineHistoryFiles(oldtarget + 1, newtarget)。
 * 注意 end 是开区间：目标时间线自己的 history file 由 readTimeLineHistory()
 * 负责读取/取回，这里不重复处理；timeline 1 没有 history file，直接跳过。
 *
 * 参数：begin 为起始 timeline ID（含），end 为结束 timeline ID（不含）。
 * 返回值：无。
 *
 * 实现与副作用：对每个 tli 调用 RestoreArchivedFile(path, histfname,
 * "RECOVERYHISTORY", 0, false)，即执行 restore_command 把文件取到
 * pg_wal/RECOVERYHISTORY；成功（返回 true）后再用
 * KeepFileRestoredFromArchive() 原子改名为 pg_wal/<tli>.history。取不到时
 * RestoreArchivedFile 会回退为 pg_wal 中同名本地路径并返回 false，本函数
 * 不报错，因为某些时间线可能本来就没有归档文件；这符合“尽量补齐、缺失不
 * 致命”的设计。
 *
 * 并发：只由 startup process 调用，运行在单进程恢复上下文中；但
 * restore_command 可能耗时，并且会写入 pg_wal，因此不要在持有 WAL 相关
 * 关键锁时调用。history file 很小，宁可多复制也不要漏复制，否则级联备库
 * 可能无法解析完整的时间线链。
 */
void
restoreTimeLineHistoryFiles(TimeLineID begin, TimeLineID end)
{
	char		path[MAXPGPATH];
	char		histfname[MAXFNAMELEN];
	TimeLineID	tli;

	for (tli = begin; tli < end; tli++)
	{
		if (tli == 1)
			continue;

		TLHistoryFileName(histfname, tli);
		if (RestoreArchivedFile(path, histfname, "RECOVERYHISTORY", 0, false))
			KeepFileRestoredFromArchive(path, histfname);
	}
}

/*
 * Try to read a timeline's history file.
 *
 * If successful, return the list of component TLIs (the given TLI followed by
 * its ancestor TLIs).  If we can't find the history file, assume that the
 * timeline has no parents, and return a list of just the specified timeline
 * ID.
 */
/*
 * 中文注释：
 * 读取并解析指定时间线的 history file，返回该时间线及其所有祖先的
 * TimeLineHistoryEntry 列表（按“最新在前”排序，并包含目标时间线自身的 tip
 * 条目）。
 *
 * 参数 targetTLI：要读取的时间线 ID。
 * 返回值：palloc 得到的 List，元素为 TimeLineHistoryEntry *，调用方负责
 * list_free_deep()。每个条目表示一段连续 WAL：
 *   - entry->begin 是闭区间起点，entry->end 是开区间终点；
 *   - begin == InvalidXLogRecPtr 表示负无穷（最老祖先的起点）；
 *   - end == InvalidXLogRecPtr 表示正无穷（目标时间线的 tip）。
 * 因此整个列表从时间起点到无穷首尾相接。
 *
 * 特殊路径：
 *   1. targetTLI == 1：timeline 1 没有 history file，直接返回仅含
 *      {tli=1, begin=end=InvalidXLogRecPtr} 的单元素列表；
 *   2. 文件不存在（ENOENT）：同样假定该时间线没有父时间线，返回单元素列表。
 *      这条规则让只有一个时间线的普通实例无需 history file；
 *   3. 其他打开错误：FATAL，恢复过程不能带着无法读取的历史继续。
 *
 * 归档恢复路径：ArchiveRecoveryRequested 为 true 时，先用
 * RestoreArchivedFile() 执行 restore_command，把 <targetTLI>.history 取到
 * pg_wal/RECOVERYHISTORY；成功后 fromArchive=true，函数末尾调用
 * KeepFileRestoredFromArchive() 将其保存为 pg_wal/<targetTLI>.history，供
 * 后续读取和归档使用。取不到时 RestoreArchivedFile 会把 path 设置为 pg_wal
 * 中的本地路径，随后仍尝试打开本地副本。
 *
 * 解析规则与校验：
 *   - 跳过行首空白、空行和以 # 开头的注释行；
 *   - 每行用 sscanf("%u\t%X/%08X") 解析 parentTLI 和 switchpoint，行尾多余
 *     内容忽略；
 *   - 缺少 timeline ID、缺少 switchpoint 都视为语法错误，FATAL；
 *   - timeline ID 必须严格递增（文件从祖先到子代排列），否则 FATAL；
 *   - 文件最后一条记录的 ID 必须小于 targetTLI，否则说明文件不属于目标
 *     时间线或已经损坏，FATAL。
 * 解析时 entry->begin 取上一条记录的 switchpoint，entry->end 取本条记录的
 * switchpoint，并用 lcons() 头插，最终得到最新在前的列表；循环结束后再为
 * targetTLI 插入 tip 条目 {begin=最后一个 switchpoint, end=Invalid}。
 *
 * 并发与副作用：用 AllocateFile()/FreeFile() 只读打开，不修改文件内容
 * （归档恢复时可能把它从 RECOVERYHISTORY 改名落地）。history file 一旦发布
 * 就被视为不可变，多个进程可以并发读取；文件通过临时文件 + 原子 rename
 * 发布，读方不会看到半截内容。返回的列表和条目都分配在
 * CurrentMemoryContext 中，生命周期由调用方管理。
 */
List *
readTimeLineHistory(TimeLineID targetTLI)
{
	List	   *result;
	char		path[MAXPGPATH];
	char		histfname[MAXFNAMELEN];
	FILE	   *fd;
	TimeLineHistoryEntry *entry;
	TimeLineID	lasttli = 0;
	XLogRecPtr	prevend;
	bool		fromArchive = false;

	/* Timeline 1 does not have a history file, so no need to check */
	if (targetTLI == 1)
	{
		entry = palloc_object(TimeLineHistoryEntry);
		entry->tli = targetTLI;
		entry->begin = entry->end = InvalidXLogRecPtr;
		return list_make1(entry);
	}

	if (ArchiveRecoveryRequested)
	{
		TLHistoryFileName(histfname, targetTLI);
		fromArchive =
			RestoreArchivedFile(path, histfname, "RECOVERYHISTORY", 0, false);
	}
	else
		TLHistoryFilePath(path, targetTLI);

	fd = AllocateFile(path, "r");
	if (fd == NULL)
	{
		if (errno != ENOENT)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\": %m", path)));
		/* Not there, so assume no parents */
		entry = palloc_object(TimeLineHistoryEntry);
		entry->tli = targetTLI;
		entry->begin = entry->end = InvalidXLogRecPtr;
		return list_make1(entry);
	}

	result = NIL;

	/*
	 * Parse the file...
	 */
	prevend = InvalidXLogRecPtr;
	for (;;)
	{
		char		fline[MAXPGPATH];
		char	   *res;
		char	   *ptr;
		TimeLineID	tli;
		uint32		switchpoint_hi;
		uint32		switchpoint_lo;
		int			nfields;

		pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_READ);
		res = fgets(fline, sizeof(fline), fd);
		pgstat_report_wait_end();
		if (res == NULL)
		{
			if (ferror(fd))
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not read file \"%s\": %m", path)));

			break;
		}

		/* skip leading whitespace and check for # comment */
		for (ptr = fline; *ptr; ptr++)
		{
			if (!isspace((unsigned char) *ptr))
				break;
		}
		if (*ptr == '\0' || *ptr == '#')
			continue;

		nfields = sscanf(fline, "%u\t%X/%08X", &tli, &switchpoint_hi, &switchpoint_lo);

		if (nfields < 1)
		{
			/* expect a numeric timeline ID as first field of line */
			ereport(FATAL,
					(errmsg("syntax error in history file: %s", fline),
					 errhint("Expected a numeric timeline ID.")));
		}
		if (nfields != 3)
			ereport(FATAL,
					(errmsg("syntax error in history file: %s", fline),
					 errhint("Expected a write-ahead log switchpoint location.")));

		if (result && tli <= lasttli)
			ereport(FATAL,
					(errmsg("invalid data in history file: %s", fline),
					 errhint("Timeline IDs must be in increasing sequence.")));

		lasttli = tli;

		entry = palloc_object(TimeLineHistoryEntry);
		entry->tli = tli;
		entry->begin = prevend;
		entry->end = ((uint64) (switchpoint_hi)) << 32 | (uint64) switchpoint_lo;
		prevend = entry->end;

		/* Build list with newest item first */
		result = lcons(entry, result);

		/* we ignore the remainder of each line */
	}

	FreeFile(fd);

	if (result && targetTLI <= lasttli)
		ereport(FATAL,
				(errmsg("invalid data in history file \"%s\"", path),
				 errhint("Timeline IDs must be less than child timeline's ID.")));

	/*
	 * Create one more entry for the "tip" of the timeline, which has no entry
	 * in the history file.
	 */
	entry = palloc_object(TimeLineHistoryEntry);
	entry->tli = targetTLI;
	entry->begin = prevend;
	entry->end = InvalidXLogRecPtr;

	result = lcons(entry, result);

	/*
	 * If the history file was fetched from archive, save it in pg_wal for
	 * future reference.
	 */
	if (fromArchive)
		KeepFileRestoredFromArchive(path, histfname);

	return result;
}

/*
 * Probe whether a timeline history file exists for the given timeline ID
 */
/*
 * 中文注释：
 * 探测指定时间线的 history file 是否存在。
 *
 * 参数 probeTLI：待探测的 timeline ID。
 * 返回值：存在返回 true，不存在（ENOENT）返回 false；timeline 1 恒为
 * false，因为它没有 history file。其他打开错误以 FATAL 报错，避免把权限、
 * I/O 故障误判成“历史不存在”。
 *
 * 查找顺序：ArchiveRecoveryRequested 为 true 时先调用
 * RestoreArchivedFile(path, histfname, "RECOVERYHISTORY", 0, false) 尝试从
 * WAL archive 取回；无论是否取到，RestoreArchivedFile 都会把 path 设置为
 * 可打开的位置（成功时是 pg_wal/RECOVERYHISTORY，失败时是
 * pg_wal/<probeTLI>.history），因此后续统一用 AllocateFile() 打开判断。
 * 非归档恢复时直接使用 pg_wal 路径。
 *
 * 副作用：归档恢复下可能执行 restore_command 并留下
 * pg_wal/RECOVERYHISTORY；本函数只探测存在性，不调用
 * KeepFileRestoredFromArchive()，临时文件会在下次 RestoreArchivedFile()
 * 时被清理或覆盖。若真正需要文件内容，应调用 readTimeLineHistory()。
 *
 * 调用场景：findNewestTimeLine() 逐个探测 ID；xlogrecovery 校验
 * recovery_target_timeline；walreceiver 判断是否需要向主库请求 history
 * file。并发：结果只是调用瞬间的快照，history file 可能被其他进程同时
 * 创建，调用方不能依赖“探测为 false”永久成立。
 */
bool
existsTimeLineHistory(TimeLineID probeTLI)
{
	char		path[MAXPGPATH];
	char		histfname[MAXFNAMELEN];
	FILE	   *fd;

	/* Timeline 1 does not have a history file, so no need to check */
	if (probeTLI == 1)
		return false;

	if (ArchiveRecoveryRequested)
	{
		TLHistoryFileName(histfname, probeTLI);
		RestoreArchivedFile(path, histfname, "RECOVERYHISTORY", 0, false);
	}
	else
		TLHistoryFilePath(path, probeTLI);

	fd = AllocateFile(path, "r");
	if (fd != NULL)
	{
		FreeFile(fd);
		return true;
	}
	else
	{
		if (errno != ENOENT)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\": %m", path)));
		return false;
	}
}

/*
 * Find the newest existing timeline, assuming that startTLI exists.
 *
 * Note: while this is somewhat heuristic, it does positively guarantee
 * that (result + 1) is not a known timeline, and therefore it should
 * be safe to assign that ID to a new timeline.
 */
/*
 * 中文注释：
 * 假定 startTLI 存在，从 startTLI + 1 开始连续探测 history file，返回找到的
 * 最新（最大）时间线 ID；如果下一个 ID 就没有 history file，则直接返回
 * startTLI。
 *
 * 参数 startTLI：探测起点，调用方必须保证该时间线存在；函数本身不校验。
 * 返回值：存在的最大的连续时间线 ID。
 *
 * 设计要点：只检查 .history 文件，不读取 pg_control，也不扫描 pg_wal 中的
 * WAL 段；timeline 1 由 existsTimeLineHistory() 特判为“无 history file”。
 * 因为探测在第一个不存在的 ID 处停止，函数保证“返回值 + 1”不是已知时间线，
 * 所以调用方可以安全地把该 ID 分配给新时间线。代价是：如果历史中人为留下
 * ID 空洞（例如手工删除中间的 .history），探测会提前停止，从而忽略已经
 * 存在但不连续的更大 ID；上游注释中的 “XXX is it useful to allow gaps”
 * 正是在讨论这个取舍。实践中 timeline ID 由恢复流程顺序分配，不会出现空洞。
 *
 * 调用场景：
 *   - StartupXLOG() 在归档恢复结束、需要选择新 timeline ID 时调用
 *     findNewestTimeLine(recoveryTargetTLI) + 1；
 *   - recovery_target_timeline = 'latest' 时用它找到 archive 中的最新
 *     时间线；
 *   - rescanLatestTimeLine() 在恢复期间检测 archive 中是否出现了新时间线。
 * 由于 existsTimeLineHistory() 在归档恢复下可能执行 restore_command，本函数
 * 也可能触发归档访问，并留下 pg_wal/RECOVERYHISTORY 临时文件。
 *
 * 并发：通常在 startup process 中调用，不持有锁，探测结果只是快照。探测
 * 期间若有其他进程创建了更大的 timeline，返回值可能偏小；但新时间线只会在
 * 恢复结束时由单一 startup process 创建，正常流程不存在这种竞争。
 */
TimeLineID
findNewestTimeLine(TimeLineID startTLI)
{
	TimeLineID	newestTLI;
	TimeLineID	probeTLI;

	/*
	 * The algorithm is just to probe for the existence of timeline history
	 * files.  XXX is it useful to allow gaps in the sequence?
	 */
	newestTLI = startTLI;

	for (probeTLI = startTLI + 1;; probeTLI++)
	{
		if (existsTimeLineHistory(probeTLI))
		{
			newestTLI = probeTLI;	/* probeTLI exists */
		}
		else
		{
			/* doesn't exist, assume we're done */
			break;
		}
	}

	return newestTLI;
}

/*
 * Create a new timeline history file.
 *
 *	newTLI: ID of the new timeline
 *	parentTLI: ID of its immediate parent
 *	switchpoint: WAL location where the system switched to the new timeline
 *	reason: human-readable explanation of why the timeline was switched
 *
 * Currently this is only used at the end recovery, and so there are no locking
 * considerations.  But we should be just as tense as XLogFileInit to avoid
 * emplacing a bogus file.
 */
/*
 * 中文注释：
 * 在归档恢复结束时创建一个新的 timeline history file：
 * pg_wal/<newTLI>.history。内容为父时间线的 history file 原样复制（如果
 * 存在），再追加一行本次分叉记录：
 *     <parentTLI>\t<switchpoint>\t<reason>\n
 *
 * 参数：
 *   newTLI      新时间线 ID；
 *   parentTLI   新时间线的直接父时间线 ID，必须小于 newTLI（函数中有
 *               Assert）；
 *   switchpoint 分叉发生的 WAL 位置（LSN），新时间线从该点之后产生 WAL；
 *   reason      人类可读的切换原因，来自 end-of-recovery 信息，例如
 *               "reached consistency"、"at restore point \"...\""、
 *               "no recovery target specified" 等；部分 reason 自带换行，
 *               追加后会形成空行，解析时会被忽略。
 * 返回值：无。失败时 ereport(ERROR)。
 *
 * 调用场景：目前只在 StartupXLOG() 的归档恢复结束路径中调用。写完
 * history file 后，StartupXLOG() 立即把 XLogCtl->InsertTimeLineID 设为
 * newTLI；end-of-recovery 记录会在恢复收尾流程中稍后写出。普通崩溃恢复不
 * 创建新时间线，因此不会调用本函数；这也是上游注释说“当前没有锁考虑”的
 * 原因——只有单个 startup process 在恢复收尾阶段执行。
 *
 * 实现步骤与持久化保证：
 *   1. 以 pg_wal/xlogtemp.<pid> 为临时文件名，先 unlink 再用
 *      OpenTransientFile(O_RDWR|O_CREAT|O_EXCL) 创建；不使用
 *      get_sync_bit()，因为只在全部内容写完后 fsync 一次；
 *   2. 读取父时间线的 history file：归档恢复下通过 RestoreArchivedFile()
 *      从 archive 取到 pg_wal/RECOVERYHISTORY，否则读取
 *      pg_wal/<parentTLI>.history。父文件不存在（例如父为 timeline 1，或
 *      归档恢复中只拿到部分历史）时视为“父没有更早的祖先”，继续执行；
 *   3. 用 BLCKSZ 缓冲区循环 read/write 复制父文件；读写分别使用
 *      WAIT_EVENT_TIMELINE_HISTORY_READ/WRITE 统计等待。写失败时先 unlink
 *      临时文件释放空间，再在 errno 未设置时按 ENOSPC 报错；
 *   4. 追加一行分叉记录。若确实复制过父文件，先补一个 '\n'，防止父文件
 *      末尾缺少换行导致两行粘连；
 *   5. pg_fsync() 临时文件（使用 data_sync_elevel(ERROR)，受
 *      data_sync_retry 影响），关闭后计算最终路径，断言目标不存在，再用
 *      durable_rename() 原子改名；durable_rename() 还会 fsync 目录，保证
 *      崩溃后文件名持久；
 *   6. 若 XLogArchivingActive()（archive_mode 为 on/always），调用
 *      XLogArchiveNotify() 创建 archive_status/<newTLI>.history.ready，
 *      让 archive_command 尽快归档，使主库/备库和 archive 尽早看到新时间线。
 *
 * 副作用：写 pg_wal 文件、fsync 文件与目录、可能执行 restore_command、可能
 * 触发归档通知。设计上通过“临时文件 + fsync + 原子 rename + 目标不存在
 * 断言”避免留下半截或伪造的 history file；若 history file 已归档但
 * end-of-recovery 记录尚未写出时崩溃，备库可能误以为新时间线已经生效，
 * 因此调用方应尽量缩短这两步之间的窗口（见 xlog.c 中的相关注释）。
 */
void
writeTimeLineHistory(TimeLineID newTLI, TimeLineID parentTLI,
					 XLogRecPtr switchpoint, const char *reason)
{
	char		path[MAXPGPATH];
	char		tmppath[MAXPGPATH];
	char		histfname[MAXFNAMELEN];
	char		buffer[BLCKSZ];
	int			srcfd;
	int			fd;
	ssize_t		nbytes;

	Assert(newTLI > parentTLI); /* else bad selection of newTLI */

	/*
	 * Write into a temp file name.
	 */
	snprintf(tmppath, MAXPGPATH, XLOGDIR "/xlogtemp.%d", (int) getpid());

	unlink(tmppath);

	/* do not use get_sync_bit() here --- want to fsync only at end of fill */
	fd = OpenTransientFile(tmppath, O_RDWR | O_CREAT | O_EXCL);
	if (fd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not create file \"%s\": %m", tmppath)));

	/*
	 * If a history file exists for the parent, copy it verbatim
	 */
	if (ArchiveRecoveryRequested)
	{
		TLHistoryFileName(histfname, parentTLI);
		RestoreArchivedFile(path, histfname, "RECOVERYHISTORY", 0, false);
	}
	else
		TLHistoryFilePath(path, parentTLI);

	srcfd = OpenTransientFile(path, O_RDONLY);
	if (srcfd < 0)
	{
		if (errno != ENOENT)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\": %m", path)));
		/* Not there, so assume parent has no parents */
	}
	else
	{
		for (;;)
		{
			errno = 0;
			pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_READ);
			nbytes = read(srcfd, buffer, sizeof(buffer));
			pgstat_report_wait_end();
			if (nbytes < 0 || errno != 0)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not read file \"%s\": %m", path)));
			if (nbytes == 0)
				break;
			errno = 0;
			pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_WRITE);
			if (write(fd, buffer, nbytes) != nbytes)
			{
				int			save_errno = errno;

				/*
				 * If we fail to make the file, delete it to release disk
				 * space
				 */
				unlink(tmppath);

				/*
				 * if write didn't set errno, assume problem is no disk space
				 */
				errno = save_errno ? save_errno : ENOSPC;

				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not write to file \"%s\": %m", tmppath)));
			}
			pgstat_report_wait_end();
		}

		if (CloseTransientFile(srcfd) != 0)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not close file \"%s\": %m", path)));
	}

	/*
	 * Append one line with the details of this timeline split.
	 *
	 * If we did have a parent file, insert an extra newline just in case the
	 * parent file failed to end with one.
	 */
	snprintf(buffer, sizeof(buffer),
			 "%s%u\t%X/%08X\t%s\n",
			 (srcfd < 0) ? "" : "\n",
			 parentTLI,
			 LSN_FORMAT_ARGS(switchpoint),
			 reason);

	nbytes = strlen(buffer);
	errno = 0;
	pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_WRITE);
	if (write(fd, buffer, nbytes) != nbytes)
	{
		int			save_errno = errno;

		/*
		 * If we fail to make the file, delete it to release disk space
		 */
		unlink(tmppath);
		/* if write didn't set errno, assume problem is no disk space */
		errno = save_errno ? save_errno : ENOSPC;

		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to file \"%s\": %m", tmppath)));
	}
	pgstat_report_wait_end();

	pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_SYNC);
	if (pg_fsync(fd) != 0)
		ereport(data_sync_elevel(ERROR),
				(errcode_for_file_access(),
				 errmsg("could not fsync file \"%s\": %m", tmppath)));
	pgstat_report_wait_end();

	if (CloseTransientFile(fd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", tmppath)));

	/*
	 * Now move the completed history file into place with its final name.
	 */
	TLHistoryFilePath(path, newTLI);
	Assert(access(path, F_OK) != 0 && errno == ENOENT);
	durable_rename(tmppath, path, ERROR);

	/* The history file can be archived immediately. */
	if (XLogArchivingActive())
	{
		TLHistoryFileName(histfname, newTLI);
		XLogArchiveNotify(histfname);
	}
}

/*
 * Writes a history file for given timeline and contents.
 *
 * Currently this is only used in the walreceiver process, and so there are
 * no locking considerations.  But we should be just as tense as XLogFileInit
 * to avoid emplacing a bogus file.
 */
/*
 * 中文注释：
 * 把一段已经准备好的 history file 内容原样写入 pg_wal/<tli>.history，用于
 * 流复制场景：备库的 walreceiver 从主库收到缺失时间线的 history file 后，
 * 调用本函数落盘。
 *
 * 参数：
 *   tli     该 history file 对应的时间线 ID；
 *   content 文件内容（纯文本，格式同 .history，由主库生成）；
 *   size    内容字节数。
 * 返回值：无。失败时 ereport(ERROR)。
 *
 * 与 writeTimeLineHistory() 的区别：
 *   - 不做解析、不复制父文件、不追加内容，完全信任主库发来的字节流，从而
 *     保证备库上的 history file 与主库逐字节一致；
 *   - 允许覆盖同名文件（最后用 durable_rename() 替换），以便调用方在需要时
 *     刷新本地副本；而 writeTimeLineHistory() 用于创建全新时间线，会断言
 *     目标不存在；
 *   - 不负责归档状态：调用方 walreceiver 根据 archive_mode 决定调用
 *     XLogArchiveNotify()（archive_mode=always）或
 *     XLogArchiveForceDone()，避免备库重复归档主库已经归档的文件。
 *
 * 实现：同样先写 pg_wal/xlogtemp.<pid>（unlink +
 * O_RDWR|O_CREAT|O_EXCL），用 write() 一次写入全部内容（短写视为错误并
 * 清理临时文件），然后 pg_fsync()（WAIT_EVENT_TIMELINE_HISTORY_FILE_SYNC）、
 * 关闭，最后 durable_rename() 到最终路径。临时文件 + 原子 rename 保证并发
 * 读方不会看到半截文件；fsync 保证崩溃后已发布的 history file 内容完整。
 *
 * 并发：只由 walreceiver 进程调用，同一时刻一个备库只有一个 walreceiver
 * 在写；但 startup process、walsender 等可能并发读取同一文件，因此必须
 * 依赖原子 rename 而不是原地覆盖。
 */
void
writeTimeLineHistoryFile(TimeLineID tli, const char *content, size_t size)
{
	char		path[MAXPGPATH];
	char		tmppath[MAXPGPATH];
	int			fd;

	/*
	 * Write into a temp file name.
	 */
	snprintf(tmppath, MAXPGPATH, XLOGDIR "/xlogtemp.%d", (int) getpid());

	unlink(tmppath);

	/* do not use get_sync_bit() here --- want to fsync only at end of fill */
	fd = OpenTransientFile(tmppath, O_RDWR | O_CREAT | O_EXCL);
	if (fd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not create file \"%s\": %m", tmppath)));

	errno = 0;
	pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_FILE_WRITE);
	if (write(fd, content, size) != size)
	{
		int			save_errno = errno;

		/*
		 * If we fail to make the file, delete it to release disk space
		 */
		unlink(tmppath);
		/* if write didn't set errno, assume problem is no disk space */
		errno = save_errno ? save_errno : ENOSPC;

		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to file \"%s\": %m", tmppath)));
	}
	pgstat_report_wait_end();

	pgstat_report_wait_start(WAIT_EVENT_TIMELINE_HISTORY_FILE_SYNC);
	if (pg_fsync(fd) != 0)
		ereport(data_sync_elevel(ERROR),
				(errcode_for_file_access(),
				 errmsg("could not fsync file \"%s\": %m", tmppath)));
	pgstat_report_wait_end();

	if (CloseTransientFile(fd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", tmppath)));

	/*
	 * Now move the completed history file into place with its final name,
	 * replacing any existing file with the same name.
	 */
	TLHistoryFilePath(path, tli);
	durable_rename(tmppath, path, ERROR);
}

/*
 * Returns true if 'expectedTLEs' contains a timeline with id 'tli'
 */
/*
 * 中文注释：
 * 判断时间线 ID tli 是否出现在 expectedTLEs 所描述的历史链中。
 *
 * 参数：
 *   tli         待检查的时间线 ID；
 *   expectedTLEs readTimeLineHistory() 返回的 TimeLineHistoryEntry 列表
 *               （最新在前，并包含目标时间线自身的 tip 条目）。
 * 返回值：找到返回 true，否则返回 false。
 *
 * 调用场景：恢复和流复制中校验从外部收到的时间线信息是否属于本机认可的
 * 历史。例如 xlogrecovery.c 在读取 WAL 页或尝试切换 timeline 时检查记录中
 * 的 latestPageTLI，防止接受不属于当前恢复历史的 WAL；也用于判断新时间线
 * 是否为当前时间线的后代。
 *
 * 实现与复杂度：简单的线性遍历，O(时间线数量)。时间线通常只有个位数到
 * 几十个，无需哈希表；保持列表结构简单，可直接由 readTimeLineHistory()
 * 构造。函数无副作用，不修改列表；列表由调用方拥有，调用期间必须保持有效。
 * 这是纯只读操作，各进程可以安全地并发调用（各自持有各自的列表副本）。
 */
bool
tliInHistory(TimeLineID tli, List *expectedTLEs)
{
	ListCell   *cell;

	foreach(cell, expectedTLEs)
	{
		if (((TimeLineHistoryEntry *) lfirst(cell))->tli == tli)
			return true;
	}

	return false;
}

/*
 * Returns the ID of the timeline in use at a particular point in time, in
 * the given timeline history.
 */
/*
 * 中文注释：
 * 在给定时间线历史中，查找包含 WAL 位置 ptr 的时间线 ID。
 *
 * 参数：
 *   ptr     WAL 位置（LSN）；
 *   history readTimeLineHistory() 返回的列表，最新在前，各条目的区间
 *           [begin, end) 首尾相接覆盖整个历史。
 * 返回值：ptr 所属的时间线 ID。
 *
 * 匹配规则：对每个条目检查
 *     (begin 无效 || begin <= ptr) && (end 无效 || ptr < end)
 * 其中 begin 无效表示负无穷（最老祖先），end 无效表示正无穷（最新时间线的
 * tip）；end 是开区间，恰好等于 switchpoint 的 LSN 属于子时间线，而不属于
 * 父时间线。这与 tliSwitchPoint() 返回的“父时间线结束位置”相配合。
 *
 * 调用场景：恢复时判断 checkpoint、recovery target、minRecoveryPoint 等
 * LSN 属于哪条时间线；读取 WAL 段时确定段内最后一个 LSN 所在的时间线，
 * 从而决定用哪个 TLI 的段文件名去读取；walsender 计算复制槽 restart_lsn
 * 所在时间线。这是“同一段 WAL 可能以不同 TLI 文件名存在”这一机制的核心
 * 查询。
 *
 * 错误处理：如果遍历完仍未匹配，说明 history 列表有空洞或不连续，抛出
 * ERROR "timeline history was not contiguous"。理论上不会发生，因为
 * readTimeLineHistory() 已保证首尾相接；这里选择报错而不是静默返回错误的
 * 时间线，避免读取到语义错误的 WAL。
 *
 * 并发：只读，不修改 history；调用方需保证列表在调用期间有效。线性扫描
 * O(n)，n 为时间线数量，通常很小。
 */
TimeLineID
tliOfPointInHistory(XLogRecPtr ptr, List *history)
{
	ListCell   *cell;

	foreach(cell, history)
	{
		TimeLineHistoryEntry *tle = (TimeLineHistoryEntry *) lfirst(cell);

		if ((!XLogRecPtrIsValid(tle->begin) || tle->begin <= ptr) &&
			(!XLogRecPtrIsValid(tle->end) || ptr < tle->end))
		{
			/* found it */
			return tle->tli;
		}
	}

	/* shouldn't happen. */
	elog(ERROR, "timeline history was not contiguous");
	return 0;					/* keep compiler quiet */
}

/*
 * Returns the point in history where we branched off the given timeline,
 * and the timeline we branched to (*nextTLI). Returns InvalidXLogRecPtr if
 * the timeline is current, ie. we have not branched off from it, and throws
 * an error if the timeline is not part of this server's history.
 */
/*
 * 中文注释：
 * 返回指定时间线在历史中结束（分叉到子时间线）的 WAL 位置，并通过
 * nextTLI 输出分叉后进入的子时间线 ID。
 *
 * 参数：
 *   tli     要查询的时间线 ID；
 *   history readTimeLineHistory() 返回的列表，最新在前；
 *   nextTLI 输出参数，可以为 NULL。找到 tli 时写入其直接子时间线 ID；若
 *           tli 已经是最新时间线（tip），写入 0（0 不是合法的 timeline
 *           ID）。
 * 返回值：tli 的结束位置，即对应 TimeLineHistoryEntry.end。若 tli 是最新
 * 时间线，返回 InvalidXLogRecPtr，表示它尚未结束、一直延伸到无穷。
 *
 * 调用场景：
 *   - xlogrecovery 校验 checkpoint 所在时间线的 switchpoint，判断恢复起点
 *     是否合法；
 *   - walsender 在时间线变为历史时间线时，计算还能向备库发送到哪个 LSN
 *     （sendTimeLineValidUpto），并用 nextTLI 通知备库切换到新时间线；
 *   - xlogutils 在读取 WAL 段时计算 currTLIValidUntil，决定何时重新检查
 *     时间线；
 *   - walsummarizer 计算 WAL 摘要的边界。
 *
 * 实现：因为列表最新在前，从新到旧遍历；在遇到 tli 之前经过的每个条目都是
 * 比 tli 更新的时间线，最后一次经过的条目就是 tli 的直接子时间线，所以
 * 循环中先设置 *nextTLI = tle->tli，再判断是否命中。命中后直接返回
 * tle->end，无需第二次遍历。
 *
 * 错误处理：若 tli 不在 history 中，抛出 ERROR
 * "requested timeline %u is not in this server's history"，防止调用方基于
 * 不存在的时间线做恢复或复制决策。
 *
 * 并发：只读遍历 history，并写入调用方提供的 nextTLI；不持有锁，不修改
 * 列表。若 nextTLI 为 NULL，则跳过输出，只返回 switchpoint。
 */
XLogRecPtr
tliSwitchPoint(TimeLineID tli, List *history, TimeLineID *nextTLI)
{
	ListCell   *cell;

	if (nextTLI)
		*nextTLI = 0;
	foreach(cell, history)
	{
		TimeLineHistoryEntry *tle = (TimeLineHistoryEntry *) lfirst(cell);

		if (tle->tli == tli)
			return tle->end;
		if (nextTLI)
			*nextTLI = tle->tli;
	}

	ereport(ERROR,
			(errmsg("requested timeline %u is not in this server's history",
					tli)));
	return InvalidXLogRecPtr;	/* keep compiler quiet */
}
