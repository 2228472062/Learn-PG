/*-------------------------------------------------------------------------
 *
 * xlogbackup.c
 *		Internal routines for base backups.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *      src/backend/access/transam/xlogbackup.c
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 base backup（基础备份/在线备份）的内部辅助逻辑，目前只有一个公开
 * 函数 build_backup_content()：把 BackupState 中的元数据格式化为 backup_label
 * 或 backup history file 的文本内容。它不负责拷贝数据文件，也不写 WAL；真正的
 * 备份流程位于 xlog.c（do_pg_backup_start/do_pg_backup_stop）、xlogfuncs.c
 * （pg_backup_start/pg_backup_stop）和 backup/basebackup.c（pg_basebackup 的
 * BASE_BACKUP 协议）中。
 *
 * 在线备份涉及的两个标签文件：
 *   - backup_label：放在备份集根目录（$PGDATA/backup_label）。恢复时由
 *     xlogrecovery.c 的 read_backup_label() 读取，用其中的 START WAL LOCATION
 *     和 CHECKPOINT LOCATION 覆盖 pg_control 中的恢复起点，确保从备份开始时所需
 *     的 WAL 位置开始回放，而不是从备份结束后归档的 pg_control 位置开始。
 *     pg_backup_stop()、basebackup.c 会生成它；其他工具（如 pg_rewind）也可能
 *     生成或使用同格式的标签。
 *   - backup history file：备份在 primary 上正常结束时，由 do_pg_backup_stop()
 *     写入 pg_wal，文件名由 startpoint 所在 WAL 段及段内偏移推导（*.backup），
 *     并随 WAL 一起归档。它比 backup_label 多出 STOP WAL LOCATION、STOP TIME、
 *     STOP TIMELINE，完整描述备份覆盖的 WAL 区间；当前源码注释说明它主要用于
 *     informational/debug 目的，不是在线备份恢复所必需的文件。备份在 standby
 *     上结束时不会写 history file。
 *
 * 一次 streamed base backup 的 WAL 区间：
 *   startpoint（checkpoint 的 REDO 位置，恢复必须从这里开始）
 *     --> 备份期间产生的 WAL（备份期间强制 full-page writes）
 *     --> stoppoint（primary 上为 XLOG_BACKUP_END 记录的位置，standby 上为
 *         minRecoveryPoint）。
 * 恢复端必须至少回放到 stoppoint（或等价的备份结束标记）才能得到一致的数据库；
 * backup_label / backup history file 中的 LSN 与 timeline 字段正是为定位该区间
 * 服务的。
 *
 * 核心数据结构：本文件不定义全局变量、宏或结构体；所操作的核心数据结构
 * BackupState 定义在 src/include/access/xlogbackup.h。
 *   - name、startpoint、starttli、checkpointloc、starttime、
 *     started_in_recovery 在 do_pg_backup_start() 中填写；
 *   - istartpoint、istarttli 仅在增量备份时由 basebackup_incremental.c 填写，
 *     指向本次增量备份所基于的更早备份的 WAL 起点；
 *   - stoppoint、stoptli、stoptime 在 do_pg_backup_stop() 中填写。
 * build_backup_content() 只读取该结构，不修改它；生成的字符串通过 palloc 返回，
 * 调用方负责 pfree。
 *
 * 设计思想：
 *   - 标签文件采用简单、稳定的逐行 ASCII 格式，便于恢复代码、归档工具和人工检查；
 *     字段前缀和顺序构成与 read_backup_label() 之间的格式契约，新增字段应追加在
 *     末尾以兼容旧解析逻辑；
 *   - backup_label 只包含恢复起点所需信息，backup history file 额外记录结束点，
 *     两者复用同一个构造函数，避免格式漂移和字段遗漏；
 *   - LSN 统一通过 LSN_FORMAT_ARGS() 输出为“高 32 位/低 32 位”的形式；
 *   - 时间统一使用 log_timezone 而非会话时区，保证同一集群生成的备份元数据不受
 *     各会话 timezone 设置影响；
 *   - 用 ishistoryfile 分支而不是两个独立的构造函数来生成内容，减少重复代码。
 */

#include "postgres.h"

#include "access/xlog.h"
#include "access/xlog_internal.h"
#include "access/xlogbackup.h"

/*
 * Build contents for backup_label or backup history file.
 *
 * When ishistoryfile is true, it creates the contents for a backup history
 * file, otherwise it creates contents for a backup_label file.
 *
 * Returns the result generated as a palloc'd string.
 */
/*
 * 中文注释：
 * 构造 backup_label 或 backup history file 的文本内容。
 *
 * 作用：把 BackupState 中记录的备份元数据按 PostgreSQL 约定的逐行格式拼接成一
 * 个以 '\n' 结尾、以 '\0' 结尾的字符串。ishistoryfile 为 false 时生成
 * backup_label，只包含恢复起点所需的 START WAL LOCATION、CHECKPOINT LOCATION
 * 等信息；为 true 时生成 backup history file，额外追加 STOP WAL LOCATION、
 * STOP TIME 和 STOP TIMELINE，描述备份覆盖的完整 WAL 区间。
 *
 * 调用场景：
 *   - xlogfuncs.c 的 pg_backup_stop()：备份结束后生成 backup_label，作为
 *     pg_backup_stop() 的返回值交给 SQL 调用方；
 *   - backup/basebackup.c：pg_basebackup / BASE_BACKUP 协议路径生成
 *     backup_label，并随备份集一起发送；
 *   - xlog.c 的 do_pg_backup_stop()：在 primary 上正常结束备份时生成 backup
 *     history file，写入 pg_wal 并交由归档流程处理。
 * 恢复端由 xlogrecovery.c 的 read_backup_label() 解析 backup_label 中的
 * START WAL LOCATION、CHECKPOINT LOCATION、BACKUP METHOD、BACKUP FROM 等字段。
 *
 * 参数：
 *   state：备份状态，不能为 NULL（函数内只有 Assert 检查）。本函数只读取该结构，
 *     不会修改任何字段。所需字段必须已经填写：
 *       - do_pg_backup_start() 填写 name、startpoint、starttli、checkpointloc、
 *         starttime、started_in_recovery；
 *       - do_pg_backup_stop() 填写 stoppoint、stoptli、stoptime；
 *       - 增量备份时 basebackup_incremental.c 可选地填写 istartpoint、
 *         istarttli。
 *   ishistoryfile：false 生成 backup_label；true 生成 backup history file。
 *
 * 返回值：在 CurrentMemoryContext 中 palloc 得到的、以 '\0' 结尾的字符串，调用方
 * 负责 pfree。即使所有字段都为空，StringInfo 也至少返回空字符串而不是 NULL。
 *
 * 副作用与并发注意事项：除内存分配外没有副作用；不写 WAL、不获取锁、不访问共享
 * 内存。state 是每个备份会话私有的结构，在备份开始/结束阶段由单一进程填写，
 * 因此读取时无需加锁。函数依赖启动后固定的全局 wal_segment_size 来把 LSN 映射为
 * WAL 段名；时间格式化使用 log_timezone 而非会话时区，避免会话 GUC 影响备份元
 * 数据的一致性。pg_localtime() 返回进程内静态缓冲区，但 PostgreSQL 后端是单线程
 * 模型，且每次调用后立即用 pg_strftime() 拷贝到局部缓冲区，因此是安全的。
 *
 * 输出字段与设计思想：
 *   - START WAL LOCATION：startpoint 的 LSN，以及由 startpoint/starttli 调用
 *     XLByteToSeg()、XLogFileName() 计算出的 WAL 段名。它是恢复所需的最早 WAL
 *     位置，也是备份的唯一标识之一；
 *   - STOP WAL LOCATION（仅 history file）：stoppoint 及其 WAL 段名，表示备份
 *     结束点（primary 上为 XLOG_BACKUP_END 记录，standby 上为 minRecoveryPoint）
 *     的位置；
 *   - CHECKPOINT LOCATION：备份起点对应的 checkpoint 记录位置，恢复时据此定位
 *     checkpoint 记录及其 redo 指针；
 *   - BACKUP METHOD：固定输出 "streamed"，恢复端据此知道必须回放到备份结束点；
 *   - BACKUP FROM：根据 started_in_recovery 输出 "standby" 或 "primary"，供恢复
 *     端与 pg_control 状态做一致性检查；
 *   - START TIME、LABEL、START TIMELINE：备份开始时间（log_timezone）、用户指定
 *     的备份标签、起始 timeline；
 *   - STOP TIME、STOP TIMELINE（仅 history file）：备份结束时间与结束 timeline；
 *   - INCREMENTAL FROM LSN/TLI：仅当 istartpoint 有效时输出，标明增量备份依赖
 *     的更早备份的 WAL 起点；代码用 Assert 保证 istartpoint 与 istarttli 要么
 *     同时存在、要么同时缺省。
 * 这些字段的名称、顺序和 LSN 格式（LSN_FORMAT_ARGS() 的“%X/%08X”）是与恢复
 * 代码之间的契约，必须保持稳定；新增字段应追加到末尾，以免破坏旧解析器。
 */
char *
build_backup_content(BackupState *state, bool ishistoryfile)
{
	char		startstrbuf[128];
	char		startxlogfile[MAXFNAMELEN]; /* backup start WAL file */
	XLogSegNo	startsegno;
	StringInfoData result;

	Assert(state != NULL);

	initStringInfo(&result);

	/* Use the log timezone here, not the session timezone */
	pg_strftime(startstrbuf, sizeof(startstrbuf), "%Y-%m-%d %H:%M:%S %Z",
				pg_localtime(&state->starttime, log_timezone));

	XLByteToSeg(state->startpoint, startsegno, wal_segment_size);
	XLogFileName(startxlogfile, state->starttli, startsegno, wal_segment_size);
	appendStringInfo(&result, "START WAL LOCATION: %X/%08X (file %s)\n",
					 LSN_FORMAT_ARGS(state->startpoint), startxlogfile);

	if (ishistoryfile)
	{
		char		stopxlogfile[MAXFNAMELEN];	/* backup stop WAL file */
		XLogSegNo	stopsegno;

		XLByteToSeg(state->stoppoint, stopsegno, wal_segment_size);
		XLogFileName(stopxlogfile, state->stoptli, stopsegno, wal_segment_size);
		appendStringInfo(&result, "STOP WAL LOCATION: %X/%08X (file %s)\n",
						 LSN_FORMAT_ARGS(state->stoppoint), stopxlogfile);
	}

	appendStringInfo(&result, "CHECKPOINT LOCATION: %X/%08X\n",
					 LSN_FORMAT_ARGS(state->checkpointloc));
	appendStringInfoString(&result, "BACKUP METHOD: streamed\n");
	appendStringInfo(&result, "BACKUP FROM: %s\n",
					 state->started_in_recovery ? "standby" : "primary");
	appendStringInfo(&result, "START TIME: %s\n", startstrbuf);
	appendStringInfo(&result, "LABEL: %s\n", state->name);
	appendStringInfo(&result, "START TIMELINE: %u\n", state->starttli);

	if (ishistoryfile)
	{
		char		stopstrfbuf[128];

		/* Use the log timezone here, not the session timezone */
		pg_strftime(stopstrfbuf, sizeof(stopstrfbuf), "%Y-%m-%d %H:%M:%S %Z",
					pg_localtime(&state->stoptime, log_timezone));

		appendStringInfo(&result, "STOP TIME: %s\n", stopstrfbuf);
		appendStringInfo(&result, "STOP TIMELINE: %u\n", state->stoptli);
	}

	/* either both istartpoint and istarttli should be set, or neither */
	Assert(XLogRecPtrIsValid(state->istartpoint) == (state->istarttli != 0));
	if (XLogRecPtrIsValid(state->istartpoint))
	{
		appendStringInfo(&result, "INCREMENTAL FROM LSN: %X/%08X\n",
						 LSN_FORMAT_ARGS(state->istartpoint));
		appendStringInfo(&result, "INCREMENTAL FROM TLI: %u\n",
						 state->istarttli);
	}

	return result.data;
}
