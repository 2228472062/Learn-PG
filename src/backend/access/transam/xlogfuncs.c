/*-------------------------------------------------------------------------
 *
 * xlogfuncs.c
 *
 * PostgreSQL write-ahead log manager user interface functions
 *
 * This file contains WAL control and information functions.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/xlogfuncs.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件是 PostgreSQL 在 SQL 层暴露的 WAL（write-ahead log）、在线备份
 * （online backup）与恢复（recovery）控制函数集合，通常由超级用户、备份工具
 * （如 pg_basebackup、pgBackRest 等）或运维脚本通过普通 SQL 调用。按用途可分为
 * 以下几组：
 *   1. 备份控制：
 *      - pg_backup_start()（历史名 pg_start_backup()）：开始一次在线基础备份，
 *        强制 checkpoint 并记录备份起点，返回恢复所需的最早 WAL LSN
 *        （checkpoint 的 REDO 位置）；
 *      - pg_backup_stop()（历史名 pg_stop_backup()）：结束备份，返回 backup
 *        stop LSN、backup_label 内容和 tablespace_map 内容，并可选等待所需
 *        WAL 归档完成。
 *   2. WAL 切换与标记：
 *      - pg_switch_wal()：强制切换到下一个 WAL 段；
 *      - pg_log_standby_snapshot()：立即把 running transactions 快照和
 *        AccessExclusiveLock 信息写入 WAL，供 standby 上的 logical decoding
 *        等场景使用；
 *      - pg_create_restore_point()：写入一个命名 restore point，供
 *        recovery_target_name 使用。
 *   3. WAL/LSN 信息查询：
 *      - pg_current_wal_lsn()/pg_current_wal_insert_lsn()/
 *        pg_current_wal_flush_lsn()：分别返回 write/insert/flush 位置；
 *      - pg_last_wal_receive_lsn()/pg_last_wal_replay_lsn()：返回 walreceiver
 *        已接收并落盘的位置、startup process 已重放的位置；
 *      - pg_walfile_name_offset()/pg_walfile_name()/pg_split_walfile_name()：
 *        在 LSN 与 WAL 段名之间转换；
 *      - pg_wal_lsn_diff()：计算两个 LSN 之间的字节差；
 *      - pg_last_xact_replay_timestamp()：最后一次重放的 COMMIT/ABORT 记录的
 *        原始事务时间；
 *      - pg_is_in_recovery()：当前是否仍在恢复中。
 *   4. 恢复控制与状态：
 *      - pg_wal_replay_pause()/pg_wal_replay_resume()：请求暂停/恢复 WAL replay；
 *      - pg_is_wal_replay_paused()/pg_get_wal_replay_pause_state()：查询暂停
 *        请求与实际暂停状态；
 *      - pg_promote()：把 standby 提升为 primary；
 *      - pg_stat_get_recovery()：pg_stat_recovery 视图的底层记录函数。
 *
 * 权限与会话限制：
 *   - 备份/切换/restore point/promotion/pause 等有副作用的函数在 pg_proc.dat 中
 *     通过 proacl => '{POSTGRES=X}' 默认只允许超级用户执行，其他角色需要显式
 *     GRANT EXECUTE；普通信息查询函数默认对 PUBLIC 开放。函数体内的
 *     “Permission checking ... managed through the normal GRANT system”即指此。
 *   - pg_backup_start()/pg_backup_stop() 依赖会话级状态（xlog.c 中的
 *     sessionBackupState、本文件的 backup_state/tablespace_map/backupcontext），
 *     必须在同一连接中配对调用；连接断开时由 before_shmem_exit 回调
 *     do_pg_abort_backup() 自动中止备份。
 *   - 备份函数在 primary 和 standby 上都可调用，但 standby 上的 backup 以
 *     minRecoveryPoint 作为结束点，且需要 full_page_writes 保证。
 *   - 大多数 WAL 控制函数禁止在 recovery 中执行；恢复控制函数则只能在 recovery
 *     中执行。每个函数会给出明确的 ERROR 与 errhint。
 *   - pg_stat_get_recovery() 还会在函数内部检查 pg_read_all_stats 成员资格，
 *     无权限时返回 NULL 而不是报错，避免通过 pg_stat_recovery 视图泄露恢复细节。
 *
 * 与其他模块的关系：
 *   - xlog.c：WAL 缓冲区、插入/刷写、checkpoint、备份主体流程
 *     （do_pg_backup_start()/do_pg_backup_stop()/do_pg_abort_backup()），以及
 *     GetXLogWriteRecPtr()/GetXLogInsertRecPtr()/GetFlushRecPtr()、
 *     RequestXLogSwitch()、XLogRestorePoint() 等底层例程；
 *   - xlogbackup.c：build_backup_content() 负责把 BackupState 渲染成
 *     backup_label / backup history file 文本；
 *   - xlogrecovery.c：RecoveryInProgress()、GetXLogReplayRecPtr()、
 *     GetRecoveryPauseState()/SetRecoveryPause()、PromoteIsTriggered()、
 *     WakeupRecovery()、GetLatestXTime() 等恢复状态与暂停/提升控制；
 *   - xlogarchive.c：pg_backup_stop() 等待归档、pg_switch_wal() 触发归档时所
 *     依赖的 .ready/.done 状态与归档检查；
 *   - replication/walreceiver.c：GetWalRcvFlushRecPtr() 提供接收位置；
 *   - storage/ipc/standby.c：LogStandbySnapshot() 写入 running-xacts 记录。
 *
 * 设计思想：
 *   - 本文件只做“薄封装”：参数校验、权限/状态检查、调用底层例程、组装 SQL
 *     返回值；真正的 WAL 与备份逻辑留在 xlog.c/xlogrecovery.c 中，避免 SQL
 *     接口与核心机制耦合；
 *   - 返回值统一使用 LSN（pg_lsn）或 record，便于 SQL 直接参与监控、比较和
 *     归档脚本计算；对无效位置返回 NULL 而不是 0，以区分“未知”与“WAL 起点”；
 *   - 有副作用的操作先做前置条件检查（是否在 recovery、wal_level、是否已触发
 *     promotion 等），并给出可操作的 hint，降低误用风险；
 *   - 备份状态按会话隔离，允许多个会话同时做 base backup，但同一会话只允许
 *     一个进行中的备份；backup_state、tablespace_map 放在专用的
 *     backupcontext 中，保证跨语句存活，并在 pg_backup_stop() 后整体释放；
 *   - 恢复控制在共享内存中使用自旋锁、latch 和 condition variable 通信，
 *     SQL 函数只修改请求状态或唤醒 startup process，实际暂停/提升由 startup
 *     process 在安全点完成，避免在任意后端上下文中直接操作恢复流程。
 */
#include "postgres.h"

#include <unistd.h>

#include "access/htup_details.h"
#include "access/xlog_internal.h"
#include "access/xlogbackup.h"
#include "access/xlogrecovery.h"
#include "catalog/pg_authid.h"
#include "catalog/pg_type.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "utils/acl.h"
#include "replication/walreceiver.h"
#include "storage/fd.h"
#include "storage/latch.h"
#include "storage/standby.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
#include "utils/pg_lsn.h"
#include "utils/timestamp.h"
#include "utils/wait_event.h"

/*
 * Backup-related variables.
 */
/*
 * 中文注释：
 * backup_state：当前会话正在进行的在线备份的元数据（BackupState 定义于
 * access/xlogbackup.h）。pg_backup_start() 在 backupcontext 中分配并交给
 * do_pg_backup_start() 填写 name、startpoint、starttli、checkpointloc、
 * starttime、started_in_recovery 等字段；pg_backup_stop() 再交给
 * do_pg_backup_stop() 填写 stoppoint、stoptli、stoptime，随后
 * build_backup_content() 读取它以生成 backup_label。值为 NULL 表示本会话当前
 * 没有进行中的备份。
 *
 * tablespace_map：当前备份的 tablespace_map 文本内容（每行“OID 路径”），由
 * do_pg_backup_start() 追加、pg_backup_stop() 作为结果的一列返回；调用方负责
 * 把它写入备份集的 tablespace_map 文件。该映射主要用于 tar 格式备份在 Windows
 * 上无法创建符号链接的场景，但所有平台都统一生成。
 *
 * 并发说明：这两个变量是每个后端进程的私有静态变量，不是共享内存，因而不同
 * 会话可以并行执行 base backup；同一会话内的互斥由 xlog.c 中的
 * sessionBackupState（SESSION_BACKUP_RUNNING）保证。它们只在备份开始/结束的
 * 单一上下文中被读写，无需加锁。
 */
static BackupState *backup_state = NULL;
static StringInfo tablespace_map = NULL;

/* Session-level context for the SQL-callable backup functions */
/*
 * 中文注释：
 * backupcontext：备份相关对象的专用内存上下文，父上下文为 TopMemoryContext。
 * backup_state 和 tablespace_map 必须活过 pg_backup_start() 所在语句，直到
 * pg_backup_stop() 才使用，因此不能放在事务/语句级上下文中。首次
 * pg_backup_start() 时创建；同一会话再次开始时若上下文已存在则先
 * MemoryContextReset() 复用；pg_backup_stop() 成功后 MemoryContextDelete()
 * 并置 NULL。若在 start 与 stop 之间出错，上下文会保留到下一次 start（或会话
 * 结束），这是有意的简单性权衡，避免在 error cleanup 中操作可能已损坏的
 * 半初始化状态。
 */
static MemoryContext backupcontext = NULL;


/*
 * Return a string constant representing the recovery pause state. This is
 * used in system functions and views, and should *not* be translated.
 */
/*
 * 中文注释：
 * 把内部枚举 RecoveryPauseState 映射为 pg_stat_recovery.pause_state 和
 * pg_get_wal_replay_pause_state() 对外显示的固定英文串：
 *   RECOVERY_NOT_PAUSED      -> "not paused"
 *   RECOVERY_PAUSE_REQUESTED -> "pause requested"
 *   RECOVERY_PAUSED          -> "paused"
 * 这些字符串是 SQL 可见值，不能翻译；switch 覆盖所有枚举值，末尾 Assert
 * 保证不会返回 NULL。无副作用、无锁，只读取传入的枚举。
 */
static const char *
GetRecoveryPauseStateString(RecoveryPauseState pause_state)
{
	const char *statestr = NULL;

	switch (pause_state)
	{
		case RECOVERY_NOT_PAUSED:
			statestr = "not paused";
			break;
		case RECOVERY_PAUSE_REQUESTED:
			statestr = "pause requested";
			break;
		case RECOVERY_PAUSED:
			statestr = "paused";
			break;
	}

	Assert(statestr != NULL);
	return statestr;
}

/*
 * pg_backup_start: set up for taking an on-line backup dump
 *
 * Essentially what this does is to create the contents required for the
 * backup_label file and the tablespace map.
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_backup_start(label text, fast boolean DEFAULT false)，返回
 * pg_lsn，用于开始一次在线基础备份（online base backup）。
 *
 * 作用与流程：
 *   1. 读取 label（备份标识，通常为备份文件存放名称），转换为 C 字符串；
 *   2. 通过 get_backup_status() 检查本会话是否已有备份，若有则报
 *      ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE；
 *   3. 准备会话级 backupcontext，并在其中分配 backup_state 与 tablespace_map；
 *   4. 注册持久化的 abort 处理器（会话退出时若备份未结束则告警并清理
 *      runningBackups）；
 *   5. 调用 do_pg_backup_start()：递增共享 runningBackups、强制 full-page
 *      writes、执行（fast 时快速）CHECKPOINT、读取 checkpoint 的 REDO 位置，
 *      并生成 tablespace_map；standby 上则以最近 restartpoint 为起点；
 *   6. 返回 backup_state->startpoint，即恢复该备份所需的最早 WAL 位置。
 *
 * 参数：
 *   backupid：text，备份标签，长度超过 MAXPGPATH 会被底层拒绝；函数默认
 *     strict，NULL 输入不会进入函数体。
 *   fast：boolean，默认 false；true 表示请求 CHECKPOINT_FAST，尽快完成
 *     checkpoint，但会造成 I/O 峰值。
 * 返回值：pg_lsn，checkpoint 的 REDO 位置（备份起点）。
 *
 * SQL 可见行为/副作用：会写 WAL（checkpoint 及相关记录）、强制 full-page
 * writes、可能等待 checkpoint 完成；备份期间数据库仍可正常读写。同一会话
 * 重复调用报错；不同会话可并发备份。权限由 GRANT 系统控制，pg_proc.dat 中
 * 默认仅超级用户可执行。备份开始后必须由同一会话调用 pg_backup_stop()，或
 * 在会话结束时由 do_pg_abort_backup() 清理。
 *
 * 设计思想：把“获取一致备份起点”这件需要跨语句保持状态的事情交给会话级
 * BackupState，而不是让 SQL 调用方自己拼 checkpoint/LSN；底层
 * do_pg_backup_start() 负责保证并发的两次备份获得不同起点（lastBackupStart
 * 循环），SQL 层只负责生命周期管理。
 */
Datum
pg_backup_start(PG_FUNCTION_ARGS)
{
	text	   *backupid = PG_GETARG_TEXT_PP(0);
	bool		fast = PG_GETARG_BOOL(1);
	char	   *backupidstr;
	SessionBackupState status = get_backup_status();
	MemoryContext oldcontext;

	backupidstr = text_to_cstring(backupid);

	if (status == SESSION_BACKUP_RUNNING)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("a backup is already in progress in this session")));

	/*
	 * backup_state and tablespace_map need to be long-lived as they are used
	 * in pg_backup_stop().  These are allocated in a dedicated memory context
	 * child of TopMemoryContext, deleted at the end of pg_backup_stop().  If
	 * an error happens before ending the backup, memory would be leaked in
	 * this context until pg_backup_start() is called again.
	 */
	if (backupcontext == NULL)
	{
		backupcontext = AllocSetContextCreate(TopMemoryContext,
											  "on-line backup context",
											  ALLOCSET_START_SMALL_SIZES);
	}
	else
	{
		backup_state = NULL;
		tablespace_map = NULL;
		MemoryContextReset(backupcontext);
	}

	oldcontext = MemoryContextSwitchTo(backupcontext);
	backup_state = palloc0_object(BackupState);
	tablespace_map = makeStringInfo();
	MemoryContextSwitchTo(oldcontext);

	register_persistent_abort_backup_handler();
	do_pg_backup_start(backupidstr, fast, NULL, backup_state, tablespace_map);

	PG_RETURN_LSN(backup_state->startpoint);
}


/*
 * pg_backup_stop: finish taking an on-line backup.
 *
 * The first parameter (variable 'waitforarchive'), which is optional,
 * allows the user to choose if they want to wait for the WAL to be archived
 * or if we should just return as soon as the WAL record is written.
 *
 * This function stops an in-progress backup, creates backup_label contents and
 * it returns the backup stop LSN, backup_label and tablespace_map contents.
 *
 * The backup_label contains the user-supplied label string (typically this
 * would be used to tell where the backup dump will be stored), the starting
 * time, starting WAL location for the dump and so on.  It is the caller's
 * responsibility to write the backup_label and tablespace_map files in the
 * data folder that will be restored from this backup.
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_backup_stop(wait_for_archive boolean DEFAULT true)，返回
 * record(lsn pg_lsn, labelfile text, spcmapfile text)，用于结束本会话中由
 * pg_backup_start() 开始的在线备份。
 *
 * 流程：
 *   1. 校验返回类型必须是 RECORD，并检查 sessionBackupState 必须为
 *      SESSION_BACKUP_RUNNING，否则报错并提示先调用 pg_backup_start()；
 *   2. 调用 do_pg_backup_stop()：primary 上写 XLOG_BACKUP_END 记录、强制
 *      WAL 段切换、生成 backup history file；standby 上则以
 *      minRecoveryPoint 作为结束点，不写 history file；同时递减
 *      runningBackups 并清空 sessionBackupState；
 *   3. 调用 build_backup_content(backup_state, false) 生成 backup_label 文本；
 *   4. 组装返回值：stoppoint、backup_label、tablespace_map->data；
 *   5. 清理 backup_state/tablespace_map，删除 backupcontext。
 *
 * 参数 wait_for_archive：true（默认）时，若启用了归档（primary 上
 * archive_mode=on，standby 上 archive_mode=always），会等待备份所需的最后一个
 * WAL 段完成归档；primary 上还会等待 backup history file 归档。false 则写完
 * 备份结束记录即返回。等待可能持续很久，可用 statement_timeout 限制。
 *
 * 返回值：lsn 为备份结束 WAL 位置（primary 上为 XLOG_BACKUP_END 记录位置，
 * standby 上为 minRecoveryPoint）；labelfile 是 backup_label 内容；spcmapfile
 * 是 tablespace_map 内容。调用方必须把后两者写入备份集，不能写入正在运行的
 * 数据目录。
 *
 * 权限/并发：默认仅超级用户可执行，底层 do_pg_backup_stop() 假定调用方已做
 * 权限检查。必须在开始备份的同一会话中调用；重复调用或没有 start 会报错。
 * 若备份期间 standby 被提升，会报错并提示备份已损坏。
 */
Datum
pg_backup_stop(PG_FUNCTION_ARGS)
{
	/*
	 * 中文注释：返回元组的输出列数，必须与 pg_proc.dat 中 pg_backup_stop 的
	 * proargmodes（1 个 'i' + 3 个 'o'）以及下面的 values/nulls 下标一致；
	 * 输入参数 wait_for_archive 不计入结果描述符。
	 */
#define PG_BACKUP_STOP_V2_COLS 3
	TupleDesc	tupdesc;
	Datum		values[PG_BACKUP_STOP_V2_COLS] = {0};
	bool		nulls[PG_BACKUP_STOP_V2_COLS] = {0};
	bool		waitforarchive = PG_GETARG_BOOL(0);
	char	   *backup_label;
	SessionBackupState status = get_backup_status();

	/* Initialize attributes information in the tuple descriptor */
	if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");

	if (status != SESSION_BACKUP_RUNNING)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("backup is not in progress"),
				 errhint("Did you call pg_backup_start()?")));

	Assert(backup_state != NULL);
	Assert(tablespace_map != NULL);

	/* Stop the backup */
	do_pg_backup_stop(backup_state, waitforarchive);

	/* Build the contents of backup_label */
	backup_label = build_backup_content(backup_state, false);

	values[0] = LSNGetDatum(backup_state->stoppoint);
	values[1] = CStringGetTextDatum(backup_label);
	values[2] = CStringGetTextDatum(tablespace_map->data);

	/* Deallocate backup-related variables */
	pfree(backup_label);

	/* Clean up the session-level state and its memory context */
	backup_state = NULL;
	tablespace_map = NULL;
	MemoryContextDelete(backupcontext);
	backupcontext = NULL;

	/* Returns the record as Datum */
	PG_RETURN_DATUM(HeapTupleGetDatum(heap_form_tuple(tupdesc, values, nulls)));
}

/*
 * pg_switch_wal: switch to next xlog file
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_switch_wal()，返回 pg_lsn。强制结束当前 WAL 段并切换到下一个
 * 段，使已完成的段可以被 archive_command 归档（连续归档场景）。
 *
 * 实现：先检查不能在 recovery 中执行（恢复期间 WAL 由 startup process 读取，
 * 不允许普通后端切换）；然后调用 RequestXLogSwitch(false)，写入一条
 * XLOG_SWITCH 记录。false 表示该记录按“重要记录”处理，不设置
 * XLOG_MARK_UNIMPORTANT，从而正常参与确定可回收 WAL 的位置。
 *
 * 返回值：若确实写入了 switch 记录，返回该记录结束位置 + 1；若当前已经位于
 * 段首、无需写记录，则返回当前段的起始 LSN。注意函数只负责写记录，不等待
 * 归档完成，也不保证 WAL 已 fsync。
 *
 * 权限：默认仅超级用户可执行（proacl POSTGRES=X），可通过 GRANT 授权。
 * 副作用：产生一条 WAL 记录并触发段切换，archiver 随后会收到 .ready 通知；
 * 频繁调用会产生大量小段文件，应避免滥用。
 */
Datum
pg_switch_wal(PG_FUNCTION_ARGS)
{
	XLogRecPtr	switchpoint;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("WAL control functions cannot be executed during recovery.")));

	switchpoint = RequestXLogSwitch(false);

	/*
	 * As a convenience, return the WAL location of the switch record
	 */
	PG_RETURN_LSN(switchpoint);
}

/*
 * pg_log_standby_snapshot: call LogStandbySnapshot()
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_log_standby_snapshot()，返回 pg_lsn。立即把当前运行事务快照
 * （running transactions）以及当前持有的 AccessExclusiveLock 信息写入 WAL，
 * 而不必等待 bgwriter/checkpointer 周期性地调用 LogStandbySnapshot()。
 *
 * 前置条件：
 *   - 不能在 recovery 中执行（恢复中的 standby 不产生新 WAL）；
 *   - wal_level 必须 >= replica（XLogStandbyInfoActive()），否则报错，因为
 *     只有该级别才会写 XLOG_RUNNING_XACTS / XLOG_STANDBY_LOCK 记录。
 *
 * 调用场景：standby 上的 logical decoding 需要等到一条 running-xacts 记录
 * 被重放后才能创建 logical slot；本函数让主库立即产生这样一条记录，缩短
 * 等待时间。也用于测试和需要显式推进 standby 可见性的运维场景。
 *
 * 返回值：LogStandbySnapshot() 返回的最后一条记录（通常是
 * XLOG_RUNNING_XACTS）的 LSN。
 * 副作用/并发：写 WAL，可能短暂持有 ProcArrayLock/XidGenLock；对热备而言
 * 记录顺序很重要（先写 AccessExclusiveLock 记录，再写 running-xacts 记录）。
 * 权限默认仅超级用户。
 */
Datum
pg_log_standby_snapshot(PG_FUNCTION_ARGS)
{
	XLogRecPtr	recptr;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("%s cannot be executed during recovery.",
						 "pg_log_standby_snapshot()")));

	if (!XLogStandbyInfoActive())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("pg_log_standby_snapshot() can only be used if \"wal_level\" >= \"replica\"")));

	recptr = LogStandbySnapshot();

	/*
	 * As a convenience, return the WAL location of the last inserted record
	 */
	PG_RETURN_LSN(recptr);
}

/*
 * pg_create_restore_point: a named point for restore
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_create_restore_point(name text)，返回 pg_lsn。在 WAL 中写入
 * 一条 XLOG_RESTORE_POINT 记录，作为命名恢复目标（named restore point）。
 *
 * 前置条件：
 *   - 不能在 recovery 中执行；
 *   - XLogIsNeeded() 为真，即 wal_level 必须是 replica 或 logical；
 *   - name 长度必须小于 MAXFNAMELEN（64），即最多 63 个字节（对 UTF-8 等
 *     多字节编码而言，实际可用的字符数会更少），否则报
 *     ERRCODE_INVALID_PARAMETER_VALUE。
 *
 * 实现：text_to_cstring() 后调用 XLogRestorePoint()，后者用
 * GetCurrentTimestamp() 记录时间、把 name 拷贝进 xl_restore_point 并写 WAL，
 * 同时在 server log 中记录 “restore point ... created at ...”。
 *
 * 返回值：restore point 记录的 LSN。
 * 使用方式：后续可用 recovery_target_name = 'name' 让恢复停在该点；同名
 * restore point 应避免重复创建，因为恢复会在第一个匹配名称的位置停止。
 * 权限默认仅超级用户。副作用是写 WAL；不阻塞其他事务。
 */
Datum
pg_create_restore_point(PG_FUNCTION_ARGS)
{
	text	   *restore_name = PG_GETARG_TEXT_PP(0);
	char	   *restore_name_str;
	XLogRecPtr	restorepoint;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("WAL control functions cannot be executed during recovery.")));

	if (!XLogIsNeeded())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("WAL level not sufficient for creating a restore point"),
				 errhint("\"wal_level\" must be set to \"replica\" or \"logical\" at server start.")));

	restore_name_str = text_to_cstring(restore_name);

	if (strlen(restore_name_str) >= MAXFNAMELEN)
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("value too long for restore point (maximum %d characters)", MAXFNAMELEN - 1)));

	restorepoint = XLogRestorePoint(restore_name_str);

	/*
	 * As a convenience, return the WAL location of the restore point record
	 */
	PG_RETURN_LSN(restorepoint);
}

/*
 * Report the current WAL write location (same format as pg_backup_start etc)
 *
 * This is useful for determining how much of WAL is visible to an external
 * archiving process.  Note that the data before this point is written out
 * to the kernel, but is not necessarily synced to disk.
 */
/*
 * 中文注释：
 * SQL 函数 pg_current_wal_lsn()，返回 pg_lsn。返回当前 WAL write location，
 * 即服务器内部 WAL 缓冲区已经写出到内核（write(2)）的末尾位置
 * （GetXLogWriteRecPtr() -> LogwrtResult.Write）。
 *
 * 用途：外部归档工具据此判断“哪些 WAL 已经可以被读取/归档”，它通常也是
 * 用户想观察的“对外可见的 WAL 末尾”。注意该位置的数据已经写出到内核，但
 * 不保证已经 fsync 到磁盘；若需要持久化保证，应使用
 * pg_current_wal_flush_lsn()。
 *
 * 限制：不能在 recovery 中调用（GetXLogWriteRecPtr 依赖 primary 的 WAL 写
 * 状态）。返回值只增不减，但可能因并发插入而跳跃；它是瞬时快照。
 * 权限：默认 PUBLIC 可执行，只读、无副作用。
 */
Datum
pg_current_wal_lsn(PG_FUNCTION_ARGS)
{
	XLogRecPtr	current_recptr;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("WAL control functions cannot be executed during recovery.")));

	current_recptr = GetXLogWriteRecPtr();

	PG_RETURN_LSN(current_recptr);
}

/*
 * Report the current WAL insert location (same format as pg_backup_start etc)
 *
 * This function is mostly for debugging purposes.
 */
/*
 * 中文注释：
 * SQL 函数 pg_current_wal_insert_lsn()，返回 pg_lsn。返回当前 WAL insert
 * location，即 WAL 的逻辑末尾（GetXLogInsertRecPtr()），可能包含已经被
 * XLogInsert 预留、但尚未写出到内核的空间，因此可能领先于 write/flush
 * location。
 *
 * 用途：主要用于服务器调试、测试以及需要知道“最新预留 LSN”的场景；普通
 * 归档/复制监控应使用 pg_current_wal_lsn() 或 flush LSN。不能在 recovery
 * 中调用。只读、无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_current_wal_insert_lsn(PG_FUNCTION_ARGS)
{
	XLogRecPtr	current_recptr;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("WAL control functions cannot be executed during recovery.")));

	current_recptr = GetXLogInsertRecPtr();

	PG_RETURN_LSN(current_recptr);
}

/*
 * Report the current WAL flush location (same format as pg_backup_start etc)
 *
 * This function is mostly for debugging purposes.
 */
/*
 * 中文注释：
 * SQL 函数 pg_current_wal_flush_lsn()，返回 pg_lsn。返回当前 WAL flush
 * location，即已知被 fsync 到持久存储的最后一个位置
 * （GetFlushRecPtr(NULL)）。
 *
 * 用途：判断 WAL 的持久化边界，常用于调试、性能分析以及确认某条记录是否
 * 已经真正落盘。该函数只能在非恢复状态调用：GetFlushRecPtr() 内部断言
 * SharedRecoveryState == RECOVERY_STATE_DONE，因此函数体先检查
 * RecoveryInProgress()。只读、无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_current_wal_flush_lsn(PG_FUNCTION_ARGS)
{
	XLogRecPtr	current_recptr;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("WAL control functions cannot be executed during recovery.")));

	current_recptr = GetFlushRecPtr(NULL);

	PG_RETURN_LSN(current_recptr);
}

/*
 * Report the last WAL receive location (same format as pg_backup_start etc)
 *
 * This is useful for determining how much of WAL is guaranteed to be received
 * and synced to disk by walreceiver.
 */
/*
 * 中文注释：
 * SQL 函数 pg_last_wal_receive_lsn()，返回 pg_lsn 或 NULL。返回 walreceiver
 * 最近一次接收并刷写到磁盘的 WAL 位置 + 1（GetWalRcvFlushRecPtr(NULL,
 * NULL)）。
 *
 * 语义：
 *   - 在 streaming replication 进行中单调递增；
 *   - 恢复结束后保持为恢复期间最后接收并落盘的位置；
 *   - 未启用 streaming replication、walreceiver 尚未启动或没有有效位置时，
 *     XLogRecPtrIsValid() 为假，返回 NULL。
 * 用途：判断 standby 已安全收到多少 WAL，评估复制延迟和归档/流复制覆盖范围。
 * 该函数在 primary 和 standby 上都可以调用（primary 上通常没有 walreceiver，
 * 因而返回 NULL）。只读、无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_last_wal_receive_lsn(PG_FUNCTION_ARGS)
{
	XLogRecPtr	recptr;

	recptr = GetWalRcvFlushRecPtr(NULL, NULL);

	if (!XLogRecPtrIsValid(recptr))
		PG_RETURN_NULL();

	PG_RETURN_LSN(recptr);
}

/*
 * Report the last WAL replay location (same format as pg_backup_start etc)
 *
 * This is useful for determining how much of WAL is visible to read-only
 * connections during recovery.
 */
/*
 * 中文注释：
 * SQL 函数 pg_last_wal_replay_lsn()，返回 pg_lsn 或 NULL。返回 startup
 * process 最后重放完成的 WAL 记录结束位置 + 1（GetXLogReplayRecPtr(NULL)）。
 *
 * 语义：
 *   - 恢复进行中单调递增；
 *   - 恢复结束后保持为最后应用的 WAL 位置；
 *   - 服务器正常启动且未经历恢复时，位置无效，返回 NULL。
 * 用途：衡量只读查询在 standby 上能看到多少 WAL（热备可见性边界）、计算
 * replay lag。注意它只表示“已重放”，不表示已经 flush 到 standby 的数据文件；
 * 与 pg_last_wal_receive_lsn() 的差值反映 replay 延迟。只读、无副作用，
 * 默认 PUBLIC 可执行。
 */
Datum
pg_last_wal_replay_lsn(PG_FUNCTION_ARGS)
{
	XLogRecPtr	recptr;

	recptr = GetXLogReplayRecPtr(NULL);

	if (!XLogRecPtrIsValid(recptr))
		PG_RETURN_NULL();

	PG_RETURN_LSN(recptr);
}

/*
 * Compute an xlog file name and decimal byte offset given a WAL location,
 * such as is returned by pg_backup_stop() or pg_switch_wal().
 */
/*
 * 中文注释：
 * SQL 函数 pg_walfile_name_offset(lsn pg_lsn)，返回
 * record(file_name text, file_offset integer)。把 WAL LSN 换算为所在 WAL
 * 段文件名及段内字节偏移。
 *
 * 实现：
 *   - 检查不能在 recovery 中执行；
 *   - 手工构造与 pg_proc.dat 中 proallargtypes/proargnames 一致的
 *     TupleDesc（file_name text、file_offset int4），并用 BlessTupleDesc()
 *     缓存；
 *   - XLByteToSeg(locationpoint, xlogsegno, wal_segment_size) 得到段号；
 *   - XLogFileName() 使用 GetWALInsertionTimeLine() 的当前插入时间线生成
 *     24 字符段名；XLogSegmentOffset() 得到段内偏移。
 *
 * 返回值：file_name 形如 "00000001000000000000000D"；file_offset 为 0 到
 * wal_segment_size-1 的字节偏移。注意文件名使用“当前插入时间线”，如果传入的
 * LSN 来自旧 timeline，段名中的 timeline 部分可能不是该 LSN 实际所属的
 * timeline，调用方需自行判断。该函数不做 LSN 有效性检查。
 * 权限：默认 PUBLIC；只读、无副作用。
 */
Datum
pg_walfile_name_offset(PG_FUNCTION_ARGS)
{
	XLogSegNo	xlogsegno;
	uint32		xrecoff;
	XLogRecPtr	locationpoint = PG_GETARG_LSN(0);
	char		xlogfilename[MAXFNAMELEN];
	Datum		values[2];
	bool		isnull[2];
	TupleDesc	resultTupleDesc;
	HeapTuple	resultHeapTuple;
	Datum		result;

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("%s cannot be executed during recovery.",
						 "pg_walfile_name_offset()")));

	/*
	 * Construct a tuple descriptor for the result row.  This must match this
	 * function's pg_proc entry!
	 */
	resultTupleDesc = CreateTemplateTupleDesc(2);
	TupleDescInitEntry(resultTupleDesc, (AttrNumber) 1, "file_name",
					   TEXTOID, -1, 0);
	TupleDescInitEntry(resultTupleDesc, (AttrNumber) 2, "file_offset",
					   INT4OID, -1, 0);

	TupleDescFinalize(resultTupleDesc);
	resultTupleDesc = BlessTupleDesc(resultTupleDesc);

	/*
	 * xlogfilename
	 */
	XLByteToSeg(locationpoint, xlogsegno, wal_segment_size);
	XLogFileName(xlogfilename, GetWALInsertionTimeLine(), xlogsegno,
				 wal_segment_size);

	values[0] = CStringGetTextDatum(xlogfilename);
	isnull[0] = false;

	/*
	 * offset
	 */
	xrecoff = XLogSegmentOffset(locationpoint, wal_segment_size);

	values[1] = Int32GetDatum(xrecoff);
	isnull[1] = false;

	/*
	 * Tuple jam: Having first prepared your Datums, then squash together
	 */
	resultHeapTuple = heap_form_tuple(resultTupleDesc, values, isnull);

	result = HeapTupleGetDatum(resultHeapTuple);

	PG_RETURN_DATUM(result);
}

/*
 * Compute an xlog file name given a WAL location,
 * such as is returned by pg_backup_stop() or pg_switch_wal().
 */
/*
 * 中文注释：
 * SQL 函数 pg_walfile_name(lsn pg_lsn)，返回 text。与
 * pg_walfile_name_offset() 相同地计算 WAL 段名，但只返回文件名，不返回段内
 * 偏移；实现更简单，省去构造 record 的开销。
 *
 * 限制与注意事项同 pg_walfile_name_offset()：不能在 recovery 中执行；
 * 使用当前 WAL insert timeline 生成文件名；不校验 LSN 是否有效或是否已存在。
 * 默认 PUBLIC 可执行，只读、无副作用。
 */
Datum
pg_walfile_name(PG_FUNCTION_ARGS)
{
	XLogSegNo	xlogsegno;
	XLogRecPtr	locationpoint = PG_GETARG_LSN(0);
	char		xlogfilename[MAXFNAMELEN];

	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is in progress"),
				 errhint("%s cannot be executed during recovery.",
						 "pg_walfile_name()")));

	XLByteToSeg(locationpoint, xlogsegno, wal_segment_size);
	XLogFileName(xlogfilename, GetWALInsertionTimeLine(), xlogsegno,
				 wal_segment_size);

	PG_RETURN_TEXT_P(cstring_to_text(xlogfilename));
}

/*
 * Extract the sequence number and the timeline ID from given a WAL file
 * name.
 */
/*
 * 中文注释：
 * SQL 函数 pg_split_walfile_name(file_name text)，返回
 * record(segment_number numeric, timeline_id bigint)。从 WAL 段文件名反解出
 * 段序号（XLogSegNo）和 timeline ID。
 *
 * 实现：
 *   - 复制输入并逐字符 pg_ascii_toupper()，因此大小写十六进制均可接受；
 *   - IsXLogFileName() 要求恰好 24 个十六进制字符，否则报
 *     ERRCODE_INVALID_PARAMETER_VALUE；
 *   - XLogFromFileName() 按 wal_segment_size 把 log/seg 两部分组合成 64 位
 *     段号；
 *   - segment_number 用 numeric 表示（段号是 uint64，可能超过 int8 范围），
 *     通过 numeric_in 转换；timeline_id 用 int8 返回。
 *
 * 用途：配合 pg_walfile_name()/pg_walfile_name_offset() 在 LSN 与文件名之间
 * 双向换算；文档示例用它和 wal_segment_size 计算 LSN。
 * 限制：只校验“24 位十六进制”这一形式，不验证 timeline 是否存在、段号是否
 * 在合法范围内；可在 recovery 中调用。默认 PUBLIC 可执行，只读、无副作用。
 */
Datum
pg_split_walfile_name(PG_FUNCTION_ARGS)
{
	/*
	 * 中文注释：返回元组的输出列数，必须与 pg_proc.dat 中
	 * pg_split_walfile_name 的 proallargtypes/proargmodes（1 个输入 +
	 * segment_number、timeline_id 两个输出）以及数组下标一致。
	 */
#define PG_SPLIT_WALFILE_NAME_COLS 2
	char	   *fname = text_to_cstring(PG_GETARG_TEXT_PP(0));
	char	   *fname_upper;
	char	   *p;
	TimeLineID	tli;
	XLogSegNo	segno;
	Datum		values[PG_SPLIT_WALFILE_NAME_COLS] = {0};
	bool		isnull[PG_SPLIT_WALFILE_NAME_COLS] = {0};
	TupleDesc	tupdesc;
	HeapTuple	tuple;
	char		buf[256];
	Datum		result;

	fname_upper = pstrdup(fname);

	/* Capitalize WAL file name. */
	for (p = fname_upper; *p; p++)
		*p = pg_ascii_toupper((unsigned char) *p);

	if (!IsXLogFileName(fname_upper))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("invalid WAL file name \"%s\"", fname)));

	XLogFromFileName(fname_upper, &tli, &segno, wal_segment_size);

	if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");

	/* Convert to numeric. */
	snprintf(buf, sizeof buf, UINT64_FORMAT, segno);
	values[0] = DirectFunctionCall3(numeric_in,
									CStringGetDatum(buf),
									ObjectIdGetDatum(0),
									Int32GetDatum(-1));

	values[1] = Int64GetDatum(tli);

	tuple = heap_form_tuple(tupdesc, values, isnull);
	result = HeapTupleGetDatum(tuple);

	PG_RETURN_DATUM(result);

#undef PG_SPLIT_WALFILE_NAME_COLS
}

/*
 * pg_wal_replay_pause - Request to pause recovery
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_wal_replay_pause()，返回 void。请求暂停 WAL replay。
 *
 * 前置条件：必须在 recovery 中；若 promotion 已经触发则报错，因为此时
 * startup process 正在结束恢复，暂停请求会阻碍 promotion 完成。
 *
 * 实现：SetRecoveryPause(true) 在共享内存 XLogRecoveryCtl 中把
 * recoveryPauseState 从 RECOVERY_NOT_PAUSED 置为 RECOVERY_PAUSE_REQUESTED
 * （若已经是 paused 则保持），然后 WakeupRecovery() 设置
 * recoveryWakeupLatch，唤醒可能正在等待 WAL 的 startup process。
 *
 * SQL 可见行为：请求是异步的，函数返回时恢复未必已经暂停；应轮询
 * pg_get_wal_replay_pause_state() 直到 "paused"。暂停后不再应用新的数据库
 * 变更（热备查询看到固定快照），但 walreceiver 仍可继续接收/刷写 WAL。
 * 权限默认仅超级用户（proacl POSTGRES=X），可通过 GRANT 授权。
 * 设计思想：只设置请求标志并唤醒，不在后端上下文中直接等待或停止
 * startup process，避免死锁和职责混乱。
 */
Datum
pg_wal_replay_pause(PG_FUNCTION_ARGS)
{
	if (!RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is not in progress"),
				 errhint("Recovery control functions can only be executed during recovery.")));

	if (PromoteIsTriggered())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("standby promotion is ongoing"),
				 errhint("%s cannot be executed after promotion is triggered.",
						 "pg_wal_replay_pause()")));

	SetRecoveryPause(true);

	/* wake up the recovery process so that it can process the pause request */
	WakeupRecovery();

	PG_RETURN_VOID();
}

/*
 * pg_wal_replay_resume - resume recovery now
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * 中文注释：
 * SQL 函数 pg_wal_replay_resume()，返回 void。请求结束 WAL replay 暂停。
 *
 * 前置条件：必须在 recovery 中；promotion 已触发时报错（此时恢复本来就会
 * 继续，不需要也不允许恢复暂停状态）。
 *
 * 实现：SetRecoveryPause(false) 把 recoveryPauseState 直接置为
 * RECOVERY_NOT_PAUSED，并 ConditionVariableBroadcast() 唤醒在
 * recoveryNotPausedCV 上睡眠的 startup process。与 pause 不同，这里不需要
 * WakeupRecovery()，因为被暂停的进程等待的正是该条件变量。
 *
 * SQL 可见行为：下一次恢复循环会继续应用 WAL；函数返回不代表已经恢复到最新，
 * 只代表暂停请求被取消。权限默认仅超级用户。
 */
Datum
pg_wal_replay_resume(PG_FUNCTION_ARGS)
{
	if (!RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is not in progress"),
				 errhint("Recovery control functions can only be executed during recovery.")));

	if (PromoteIsTriggered())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("standby promotion is ongoing"),
				 errhint("%s cannot be executed after promotion is triggered.",
						 "pg_wal_replay_resume()")));

	SetRecoveryPause(false);

	PG_RETURN_VOID();
}

/*
 * pg_is_wal_replay_paused
 */
/*
 * 中文注释：
 * SQL 函数 pg_is_wal_replay_paused()，返回 boolean。判断当前是否“请求了”
 * 恢复暂停，即 GetRecoveryPauseState() != RECOVERY_NOT_PAUSED。
 *
 * 注意：该函数在 RECOVERY_PAUSE_REQUESTED 和 RECOVERY_PAUSED 两种状态下都
 * 返回 true，因此它回答的是“是否有暂停请求”，而不是“恢复是否已经真正
 * 暂停”。若需要后者，请使用 pg_get_wal_replay_pause_state()。
 * 只能在 recovery 中调用。只读、无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_is_wal_replay_paused(PG_FUNCTION_ARGS)
{
	if (!RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is not in progress"),
				 errhint("Recovery control functions can only be executed during recovery.")));

	PG_RETURN_BOOL(GetRecoveryPauseState() != RECOVERY_NOT_PAUSED);
}

/*
 * pg_get_wal_replay_pause_state - Returns the recovery pause state.
 *
 * Returned values:
 *
 * 'not paused' - if pause is not requested
 * 'pause requested' - if pause is requested but recovery is not yet paused
 * 'paused' - if recovery is paused
 */
/*
 * 中文注释：
 * SQL 函数 pg_get_wal_replay_pause_state()，返回 text。返回恢复暂停状态：
 *   "not paused"      —— 没有暂停请求；
 *   "pause requested" —— 已请求暂停，但 startup process 尚未到达暂停点；
 *   "paused"          —— 恢复已经实际暂停。
 * 字符串通过 GetRecoveryPauseStateString() 生成，是 SQL 可见的固定值，不翻译。
 * 实现：先检查必须在 recovery 中，再在自旋锁保护下读取
 * XLogRecoveryCtl->recoveryPauseState，最后转换为 text。
 * 用途：在调用 pg_wal_replay_pause() 后确认恢复是否真的已经暂停，或实现
 * 基于暂停点的运维流程。只读、无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_get_wal_replay_pause_state(PG_FUNCTION_ARGS)
{
	RecoveryPauseState state;

	if (!RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is not in progress"),
				 errhint("Recovery control functions can only be executed during recovery.")));

	state = GetRecoveryPauseState();

	/* get the recovery pause state */
	PG_RETURN_TEXT_P(cstring_to_text(GetRecoveryPauseStateString(state)));
}

/*
 * Returns timestamp of latest processed commit/abort record.
 *
 * When the server has been started normally without recovery the function
 * returns NULL.
 */
/*
 * 中文注释：
 * SQL 函数 pg_last_xact_replay_timestamp()，返回 timestamptz 或 NULL。返回
 * 最近一次重放的 COMMIT/ABORT 记录所携带的事务提交/中止时间（在 primary 上
 * 生成该记录的时间），由 GetLatestXTime() 在自旋锁保护下读取
 * XLogRecoveryCtl->recoveryLastXTime。
 *
 * 返回 NULL 的情况：时间值为 0，即恢复中没有重放任何事务，或服务器正常启动
 * 且未经历恢复。
 * 用途：判断 standby 的数据新鲜度、估算复制延迟（注意它是“最后事务时间”，
 * 不是“最后重放时间”，空闲主库上可能长期不变）；也是 recovery_min_apply_delay
 * 计算的基础数据之一。只读、无副作用，默认 PUBLIC 可执行，恢复前后均可调用。
 */
Datum
pg_last_xact_replay_timestamp(PG_FUNCTION_ARGS)
{
	TimestampTz xtime;

	xtime = GetLatestXTime();
	if (xtime == 0)
		PG_RETURN_NULL();

	PG_RETURN_TIMESTAMPTZ(xtime);
}

/*
 * Returns bool with current recovery mode, a global state.
 */
/*
 * 中文注释：
 * SQL 函数 pg_is_in_recovery()，返回 boolean。直接调用 RecoveryInProgress()，
 * 判断服务器当前是否仍处于恢复（包括 crash recovery、archive recovery、
 * standby 的持续恢复）中。
 *
 * 语义细节：RecoveryInProgress() 会在首次观察到恢复结束后缓存结果并直接返回
 * false，因此一旦返回 false，后续不会再变回 true（PostgreSQL 不支持重新进入
 * 恢复）。返回值 true 也只是一个瞬时快照，调用返回后恢复可能立即结束。
 * 用途：运维脚本、连接路由、只读/读写判断；也是许多 SQL 函数内部的前置检查。
 * 只读、无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_is_in_recovery(PG_FUNCTION_ARGS)
{
	PG_RETURN_BOOL(RecoveryInProgress());
}

/*
 * Compute the difference in bytes between two WAL locations.
 */
/*
 * 中文注释：
 * SQL 函数 pg_wal_lsn_diff(lsn1 pg_lsn, lsn2 pg_lsn)，返回 numeric。计算
 * lsn1 - lsn2 的字节差（可为负），实现上直接调用 pg_lsn_mi。
 *
 * 用途：计算复制延迟、WAL 生成量、归档进度等；常与 pg_stat_replication 的
 * sent_lsn/write_lsn/flush_lsn/replay_lsn 或本文件的其他 LSN 函数配合。
 * 使用 numeric 而不是 int8，是为了完整表示 64 位无符号 LSN 的差值范围。
 * 该函数不要求处于非恢复状态，在 primary 和 standby 上都可调用；只读、
 * 无副作用，默认 PUBLIC 可执行。
 */
Datum
pg_wal_lsn_diff(PG_FUNCTION_ARGS)
{
	Datum		result;

	result = DirectFunctionCall2(pg_lsn_mi,
								 PG_GETARG_DATUM(0),
								 PG_GETARG_DATUM(1));

	PG_RETURN_DATUM(result);
}

/*
 * Promotes a standby server.
 *
 * A result of "true" means that promotion has been completed if "wait" is
 * "true", or initiated if "wait" is false.
 */
/*
 * 中文注释：
 * SQL 函数 pg_promote(wait boolean DEFAULT true, wait_seconds integer
 * DEFAULT 60)，返回 boolean。把 standby 提升为 primary。
 *
 * 流程：
 *   1. 检查必须处于 recovery，否则报错；
 *   2. 检查 wait_seconds > 0，否则报 ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE；
 *   3. 在当前数据目录创建 PROMOTE_SIGNAL_FILE（"promote"）空文件；
 *   4. 向 postmaster 发送 SIGUSR1。postmaster 在 PM_STARTUP/PM_RECOVERY/
 *      PM_HOT_STANDBY 状态下检测到 promote 文件后，会向 startup process 发送
 *      SIGUSR2，startup process 结束恢复并完成 promotion；
 *   5. wait=false：立即返回 true（只表示信号已发出/请求已提交）；
 *      wait=true：循环等待 RecoveryInProgress() 变 false，最多 wait_seconds
 *      秒；成功返回 true，超时发出 WARNING 并返回 false。
 *
 * 等待实现：使用 MyLatch + WL_LATCH_SET/WL_TIMEOUT/WL_POSTMASTER_DEATH，
 * 每 100ms 超时一次并 CHECK_FOR_INTERRUPTS()，因此可被查询取消/statement_timeout
 * 打断；若 postmaster 意外退出则 FATAL 终止连接。
 *
 * 权限：默认仅超级用户（proacl POSTGRES=X），可通过 GRANT 授权。
 * 副作用：写 promote 信号文件、向 postmaster 发信号；promotion 一旦触发不可
 * 撤销，且会结束 standby 的只读状态。并发调用是幂等的（文件已存在时
 * AllocateFile("w") 会截断/重建，随后同样发信号），但应避免同时发起多个。
 */
Datum
pg_promote(PG_FUNCTION_ARGS)
{
	bool		wait = PG_GETARG_BOOL(0);
	int			wait_seconds = PG_GETARG_INT32(1);
	FILE	   *promote_file;
	TimestampTz end_time;

	if (!RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("recovery is not in progress"),
				 errhint("Recovery control functions can only be executed during recovery.")));

	if (wait_seconds <= 0)
		ereport(ERROR,
				(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
				 errmsg("\"wait_seconds\" must not be negative or zero")));

	/* create the promote signal file */
	promote_file = AllocateFile(PROMOTE_SIGNAL_FILE, "w");
	if (!promote_file)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not create file \"%s\": %m",
						PROMOTE_SIGNAL_FILE)));

	if (FreeFile(promote_file))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write file \"%s\": %m",
						PROMOTE_SIGNAL_FILE)));

	/* signal the postmaster */
	if (kill(PostmasterPid, SIGUSR1) != 0)
	{
		(void) unlink(PROMOTE_SIGNAL_FILE);
		ereport(ERROR,
				(errcode(ERRCODE_SYSTEM_ERROR),
				 errmsg("failed to send signal to postmaster: %m")));
	}

	/* return immediately if waiting was not requested */
	if (!wait)
		PG_RETURN_BOOL(true);

	/* wait for the amount of time wanted until promotion */
	end_time = TimestampTzPlusSeconds(GetCurrentTimestamp(), wait_seconds);
	while (GetCurrentTimestamp() < end_time)
	{
		int			rc;

		ResetLatch(MyLatch);

		if (!RecoveryInProgress())
			PG_RETURN_BOOL(true);

		CHECK_FOR_INTERRUPTS();

		rc = WaitLatch(MyLatch,
					   WL_LATCH_SET | WL_TIMEOUT | WL_POSTMASTER_DEATH,
					   100L,
					   WAIT_EVENT_PROMOTE);

		/*
		 * Emergency bailout if postmaster has died.  This is to avoid the
		 * necessity for manual cleanup of all postmaster children.
		 */
		if (rc & WL_POSTMASTER_DEATH)
			ereport(FATAL,
					(errcode(ERRCODE_ADMIN_SHUTDOWN),
					 errmsg("terminating connection due to unexpected postmaster exit"),
					 errcontext("while waiting on promotion")));
	}

	ereport(WARNING,
			(errmsg_plural("server did not promote within %d second",
						   "server did not promote within %d seconds",
						   wait_seconds,
						   wait_seconds)));
	PG_RETURN_BOOL(false);
}

/*
 * pg_stat_get_recovery - returns information about WAL recovery state
 *
 * Returns NULL when not in recovery or when the caller lacks
 * pg_read_all_stats privileges; one row otherwise.
 */
/*
 * 中文注释：
 * SQL 函数 pg_stat_get_recovery()，返回 record，是 pg_stat_recovery 视图的
 * 底层数据源（system_views.sql 中定义，过滤 promote_triggered IS NOT NULL）。
 * 用于暴露 WAL 恢复运行状态，供监控复制延迟、暂停状态和 promotion 进度。
 *
 * 权限与返回：
 *   - 不在 recovery 中时直接返回 NULL（视图中因此不显示行）；
 *   - 调用者不是 pg_read_all_stats 成员时也返回 NULL，而不是报错，避免
 *     普通用户通过视图获取恢复细节；这是函数内的权限检查，函数本身在
 *     pg_proc.dat 中默认 PUBLIC 可执行。
 *
 * 读取方式：在 XLogRecoveryCtl->info_lck 自旋锁保护下一次性拷贝一组共享
 * 字段，保证同一个 record 内各列来自同一时刻，避免出现“LSN 与 TLI 不匹配”
 * 之类的撕裂读。读取的字段与返回列（按 pg_proc.dat 的 proargnames 顺序）：
 *   0 promote_triggered          bool，是否已触发 promotion；
 *   1 last_replayed_read_lsn     pg_lsn，最后重放记录的起始位置（无效则 NULL）；
 *   2 last_replayed_end_lsn      pg_lsn，最后重放记录的结束位置 + 1；
 *   3 last_replayed_tli          int4，最后重放记录的 timeline；
 *   4 replay_end_lsn             pg_lsn，当前正在重放记录的结束位置 + 1
 *                                （不在重放时等于 last_replayed_end_lsn）；
 *   5 replay_end_tli             int4，对应的 timeline；
 *   6 recovery_last_xact_time    timestamptz，最后重放的 COMMIT/ABORT 时间；
 *   7 current_chunk_start_time   timestamptz，追平 walreceiver 最新 WAL chunk
 *                                的时间；
 *   8 pause_state                text，恢复暂停状态字符串。
 * 无效 LSN/时间为 0 时把对应列置 NULL，而不是返回 0/epoch，便于 SQL 区分
 * “未知”和真实值。
 *
 * 设计思想：函数只做快照式读取，不修改共享状态；把权限检查放在函数内部而
 * 不是依赖 GRANT，是因为该信息对所有监控角色有价值，但不应向普通用户公开。
 * 返回单行 record 而非 SETOF，配合视图的 WHERE 条件实现“无权限/非恢复时
 * 零行”的语义。
 */
Datum
pg_stat_get_recovery(PG_FUNCTION_ARGS)
{
	TupleDesc	tupdesc;
	Datum	   *values;
	bool	   *nulls;

	/* Local copies of shared state */
	bool		promote_triggered;
	XLogRecPtr	last_replayed_read_lsn;
	XLogRecPtr	last_replayed_end_lsn;
	TimeLineID	last_replayed_tli;
	XLogRecPtr	replay_end_lsn;
	TimeLineID	replay_end_tli;
	TimestampTz recovery_last_xact_time;
	TimestampTz current_chunk_start_time;
	RecoveryPauseState pause_state;

	if (!RecoveryInProgress())
		PG_RETURN_NULL();

	if (!has_privs_of_role(GetUserId(), ROLE_PG_READ_ALL_STATS))
		PG_RETURN_NULL();

	/* Take a lock to ensure value consistency */
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	promote_triggered = XLogRecoveryCtl->SharedPromoteIsTriggered;
	last_replayed_read_lsn = XLogRecoveryCtl->lastReplayedReadRecPtr;
	last_replayed_end_lsn = XLogRecoveryCtl->lastReplayedEndRecPtr;
	last_replayed_tli = XLogRecoveryCtl->lastReplayedTLI;
	replay_end_lsn = XLogRecoveryCtl->replayEndRecPtr;
	replay_end_tli = XLogRecoveryCtl->replayEndTLI;
	recovery_last_xact_time = XLogRecoveryCtl->recoveryLastXTime;
	current_chunk_start_time = XLogRecoveryCtl->currentChunkStartTime;
	pause_state = XLogRecoveryCtl->recoveryPauseState;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
		elog(ERROR, "return type must be a row type");

	values = palloc0_array(Datum, tupdesc->natts);
	nulls = palloc0_array(bool, tupdesc->natts);

	values[0] = BoolGetDatum(promote_triggered);

	if (XLogRecPtrIsValid(last_replayed_read_lsn))
		values[1] = LSNGetDatum(last_replayed_read_lsn);
	else
		nulls[1] = true;

	if (XLogRecPtrIsValid(last_replayed_end_lsn))
		values[2] = LSNGetDatum(last_replayed_end_lsn);
	else
		nulls[2] = true;

	if (XLogRecPtrIsValid(last_replayed_end_lsn))
		values[3] = Int32GetDatum(last_replayed_tli);
	else
		nulls[3] = true;

	if (XLogRecPtrIsValid(replay_end_lsn))
		values[4] = LSNGetDatum(replay_end_lsn);
	else
		nulls[4] = true;

	if (XLogRecPtrIsValid(replay_end_lsn))
		values[5] = Int32GetDatum(replay_end_tli);
	else
		nulls[5] = true;

	if (recovery_last_xact_time != 0)
		values[6] = TimestampTzGetDatum(recovery_last_xact_time);
	else
		nulls[6] = true;

	if (current_chunk_start_time != 0)
		values[7] = TimestampTzGetDatum(current_chunk_start_time);
	else
		nulls[7] = true;

	values[8] = CStringGetTextDatum(GetRecoveryPauseStateString(pause_state));

	PG_RETURN_DATUM(HeapTupleGetDatum(heap_form_tuple(tupdesc, values, nulls)));
}
