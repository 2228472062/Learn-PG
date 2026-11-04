/*-------------------------------------------------------------------------
 *
 * xlogarchive.c
 *		Functions for archiving WAL files and restoring from the archive.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/xlogarchive.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 WAL 归档（archiving）与归档恢复（archive recovery）所需的底层文件
 * 操作，是 archive_command 与 restore_command 两个 GUC 参数在源码中的主要落点。
 * 内容可分为三类：
 *   1. 恢复侧：RestoreArchivedFile() 执行 restore_command 从归档中取回 WAL 段或
 *      timeline history 文件；KeepFileRestoredFromArchive() 把取回的临时文件转正；
 *      ExecuteRecoveryCommand() 执行 recovery_end_command / archive_cleanup_command；
 *   2. 归档通知：XLogArchiveNotify() / XLogArchiveNotifySeg() 在 archive_status
 *      目录下创建 <XLOG>.ready 文件并唤醒 archiver；XLogArchiveForceDone() 直接
 *      创建 <XLOG>.done，用于“这段已归档/无需归档”的场景；
 *   3. 状态查询与清理：XLogArchiveCheckDone()、XLogArchiveIsBusy()、
 *      XLogArchiveIsReady()、XLogArchiveIsReadyOrDone()、XLogArchiveCleanup()，
 *      供 checkpoint、时间线切换、基础备份和 WAL 段回收判断某个文件能否删除/回收。
 *
 * 文件系统状态协议（状态文件位于 $PGDATA/pg_wal/archive_status/）：
 *   - <XLOG>.ready：表示该 WAL 文件“等待归档”，由产生 WAL 的进程创建；
 *   - <XLOG>.done ：表示 archiver 已成功执行完 archive_command（或该文件无需归档）。
 * 两者都是空文件，内容不重要，“存在性”本身就是状态。archiver（postmaster/pgarch.c）
 * 扫描该目录时只处理 .ready 文件；archive_command 成功返回后由 archiver 把 .ready
 * 重命名为 .done，失败则保留 .ready，下一轮扫描自动重试。checkpoint 只有在看到
 * .done（或归档未启用、当前处于不需要本地归档的恢复阶段）时才允许删除/回收对应
 * WAL 段。因此 .ready/.done 实际是“WAL 是否已安全复制到归档”的持久化证据：它跨
 * 重启有效，无需额外的共享内存状态，DBA 也可以直接查看和手工修复。
 *
 * 核心流程（正常归档）：
 *   WAL 段写满（或时间线历史文件产生）-> XLogArchiveNotifySeg()/XLogArchiveNotify()
 *   创建 .ready 并 PgArchWakeup() 唤醒 archiver -> archiver 替换 %p/%f 后执行
 *   archive_command -> 成功则 .ready 改名 .done -> checkpoint 的
 *   XLogArchiveCheckDone() 看到 .done，允许该段被删除或回收。
 *
 * 核心流程（归档恢复）：
 *   startup process 需要某个 WAL 段但 pg_wal 中没有可用副本（或在恢复早期按策略
 *   优先使用归档）-> RestoreArchivedFile() 用 %f/%p/%r 构造并执行 restore_command
 *   -> 归档文件被恢复到 pg_wal 下固定的临时文件名（RECOVERYXLOG / RECOVERYHISTORY）
 *   并校验大小 -> KeepFileRestoredFromArchive() 通过 durable_rename() 改成正式
 *   文件名，同时写状态文件，防止刚恢复的段又被归档一次。
 *
 * 失败与重试策略：
 *   - 恢复是“向前滚动直到 restore 失败”的过程，因此 restore_command 的普通失败
 *     （非零退出、归档中没有该文件）只记 DEBUG2 并返回 false，由上层决定改用
 *     pg_wal 中的本地文件，或据此判定已到达 WAL 末尾并结束恢复；
 *   - 但若子进程被信号杀死（SIGINT/SIGQUIT 等）或取回的文件大小不符（standby 中
 *     文件仍在被拷贝的场景除外），则升级为 FATAL，避免把“命令配错”误判成
 *     “WAL 已到末尾”而提前结束恢复；
 *   - 收到 SIGTERM 视为 fast shutdown 请求，在 system() 返回后直接 proc_exit(1)；
 *   - 归档侧失败不阻塞主库：archiver 保留 .ready 并周期性重试，必要时发出告警。
 *
 * 设计思想：
 *   - 用普通文件的存在性表达状态，简单、可持久、可由 DBA 手工检查/修复，并让后端
 *     与归档进程解耦：后端只创建 .ready，不在前台执行 archive_command；
 *   - 恢复时永远优先使用归档副本：pg_wal 中的同名文件可能来自基础备份，是尚未
 *     写满的旧副本；
 *   - 恢复时始终写入同一个固定临时文件名，长时间恢复不会因临时文件堆积耗尽磁盘；
 *   - 用 .done 抑制重复归档，用 %r（最老 restartpoint）向 archive_cleanup_command
 *     告知可安全删除的归档边界，使归档清理保持幂等、可重试；
 *   - 状态转换尽量借助 rename 的原子性，并使用 durable_rename()/fsync 保证崩溃后
 *     状态文件与实际文件一致。
 *
 * 说明：本文件不定义全局变量、宏或结构体，所有状态都体现在 pg_wal 与
 * pg_wal/archive_status 目录中。它依赖 xlog_internal.h 的 XLOGDIR（"pg_wal"）与
 * StatusFilePath()（拼出 archive_status/<name><suffix>），以及 xlog.h 中的
 * ARCHIVE_MODE_*、XLogArchivingActive()、XLogArchivingAlways()。
 */
/*
 * 中文注释：
 * 关键外部依赖（便于阅读时定位）：
 *   - common/archive.h 的 BuildRestoreCommand()：替换 restore_command 中的
 *     %f（WAL 文件名）、%p（目标路径）、%r（最老 restartpoint 文件名）；
 *   - common/percentrepl.h 的 replace_percent_placeholders()：ExecuteRecoveryCommand()
 *     用它只替换 %r；
 *   - postmaster/pgarch.h 的 PgArchWakeup()/PgArchForceDirScan()：唤醒 archiver、
 *     强制其丢弃缓存并重新扫描 archive_status；
 *   - postmaster/startup.h 的 PreRestoreCommand()/PostRestoreCommand()：在 system()
 *     期间调整 startup process 对 SIGTERM 的处理方式；
 *   - storage/fd.h 的 AllocateFile()/FreeFile()/durable_rename()：带错误处理的
 *     文件创建与持久化重命名；
 *   - replication/walsender.h 的 WalSndRqstFileReload()/WalSndWakeup()：段文件被
 *     替换或新增后通知 walsender。
 */

#include "postgres.h"

#include <sys/stat.h>
#include <sys/wait.h>
#include <signal.h>
#include <unistd.h>

#include "access/xlog.h"
#include "access/xlog_internal.h"
#include "access/xlogarchive.h"
#include "common/archive.h"
#include "common/percentrepl.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/pgarch.h"
#include "postmaster/startup.h"
#include "replication/walsender.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "utils/wait_event.h"

/*
 * Attempt to retrieve the specified file from off-line archival storage.
 * If successful, fill "path" with its complete path (note that this will be
 * a temp file name that doesn't follow the normal naming convention), and
 * return true.
 *
 * If not successful, fill "path" with the name of the normal on-line file
 * (which may or may not actually exist, but we'll try to use it), and return
 * false.
 *
 * For fixed-size files, the caller may pass the expected size as an
 * additional crosscheck on successful recovery.  If the file size is not
 * known, set expectedSize = 0.
 *
 * When 'cleanupEnabled' is false, refrain from deleting any old WAL segments
 * in the archive. This is used when fetching the initial checkpoint record,
 * when we are not yet sure how far back we need the WAL.
 */
/*
 * 中文注释：
 * 尝试用 restore_command 从离线归档中取回指定 WAL 文件（WAL 段、.partial 段、
 * timeline history 文件或 backup history 文件），是 archive recovery 的取数入口。
 *
 * 参数：
 *   path           —— 输出缓冲区（至少 MAXPGPATH 字节）。成功时写入临时文件的完整
 *                     路径（XLOGDIR/recovername，不符合普通 WAL 命名规范）；失败时
 *                     写入 XLOGDIR/xlogfname，调用方仍可尝试打开本地文件；
 *   xlogfname      —— 期望取回的文件名（如 0000000100000001000000C6 或
 *                     00000002.history），用于替换 %f；
 *   recovername    —— 取回文件落盘时使用的固定临时文件名（调用方传 RECOVERYXLOG
 *                     或 RECOVERYHISTORY），用于替换 %p；
 *   expectedSize   —— 已知文件大小时用于交叉校验（WAL 段通常传 wal_segment_size）；
 *                     0 表示大小未知，跳过检查（history 文件的常见情况）；
 *   cleanupEnabled —— 是否允许在 %r 中给出“可删除边界”。它在恢复进入 redo 之前为
 *                     false（调用方传 InRedo）：此时还没定位到起始 checkpoint，
 *                     不确定需要回溯多远，于是把 %r 设为 InvalidXLogRecPtr 对应的
 *                     全零文件名；由于 WAL 文件名按字典序排序，任何真实归档文件都
 *                     “大于”它，archive_cleanup_command 因而不会删除任何文件。
 *
 * 返回值：true 表示文件已成功恢复到临时路径且通过大小检查；false 表示归档中不可
 * 用（restore_command 未配置、命令失败或文件不存在），此时 path 指向本地
 * XLOGDIR/xlogfname。上层（xlogrecovery.c 的 XLogFileRead）在 false 时会尝试本地
 * 文件，最终可能据此判定到达 WAL 末尾并结束恢复。
 *
 * 主要流程：
 *   1. 非 archive recovery（即 crash recovery）或 restore_command 为空时直接跳到
 *      not_available，避免在崩溃恢复中误用归档；
 *   2. 删除上次遗留的临时文件，确保不会误用旧内容；
 *   3. 根据最老 restartpoint 计算 %r 的文件名，并断言请求的段不早于它；
 *   4. 构造命令，fflush(NULL) 刷出所有 stdio 缓冲，上报 WAIT_EVENT_RESTORE_COMMAND
 *      等待事件，然后在 PreRestoreCommand()/PostRestoreCommand() 保护下执行
 *      system()；
 *   5. 命令返回 0 时 stat 临时文件，确认它确实存在且大小正确，再返回临时路径。
 *
 * 副作用/并发注意：
 *   - 会 fork 子进程执行 shell 命令并阻塞等待，只应由 startup process 调用；
 *   - PreRestoreCommand() 期间 SIGTERM 处理函数会直接 proc_exit()，因此该区间内
 *     不要做需要清理的额外工作（这也是函数把其他逻辑放在区间外的原因）；
 *   - 失败路径可能 ereport(FATAL) 终止恢复；收到 SIGTERM 时主动 proc_exit(1)；
 *   - 命令字符串由 palloc 分配，函数结束前 pfree。
 *
 * 设计思想：恢复时永远优先使用归档副本，因为 pg_wal 中的同名文件可能是基础备份
 * 中尚未写满的旧副本；取回时先写固定临时名，再由调用方转正，既不覆盖本地段，
 * 也避免长时间恢复时临时副本撑满磁盘；对“命令失败”和“文件中确实没有”不作区分，
 * 是因为恢复模型本来就是“restore 失败即视为 WAL 结束”，但信号导致的失败必须
 * 升级为 FATAL，防止把管理员配置错误误判成正常结束。
 */
bool
RestoreArchivedFile(char *path, const char *xlogfname,
					const char *recovername, off_t expectedSize,
					bool cleanupEnabled)
{
	char		xlogpath[MAXPGPATH];
	char	   *xlogRestoreCmd;
	char		lastRestartPointFname[MAXPGPATH];
	int			rc;
	struct stat stat_buf;
	XLogSegNo	restartSegNo;
	XLogRecPtr	restartRedoPtr;
	TimeLineID	restartTli;

	/*
	 * Ignore restore_command when not in archive recovery (meaning we are in
	 * crash recovery).
	 */
	if (!ArchiveRecoveryRequested)
		goto not_available;

	/* In standby mode, restore_command might not be supplied */
	if (recoveryRestoreCommand == NULL || strcmp(recoveryRestoreCommand, "") == 0)
		goto not_available;

	/*
	 * When doing archive recovery, we always prefer an archived log file even
	 * if a file of the same name exists in XLOGDIR.  The reason is that the
	 * file in XLOGDIR could be an old, un-filled or partly-filled version
	 * that was copied and restored as part of backing up $PGDATA.
	 *
	 * We could try to optimize this slightly by checking the local copy
	 * lastchange timestamp against the archived copy, but we have no API to
	 * do this, nor can we guarantee that the lastchange timestamp was
	 * preserved correctly when we copied to archive. Our aim is robustness,
	 * so we elect not to do this.
	 *
	 * If we cannot obtain the log file from the archive, however, we will try
	 * to use the XLOGDIR file if it exists.  This is so that we can make use
	 * of log segments that weren't yet transferred to the archive.
	 *
	 * Notice that we don't actually overwrite any files when we copy back
	 * from archive because the restore_command may inadvertently restore
	 * inappropriate xlogs, or they may be corrupt, so we may wish to fallback
	 * to the segments remaining in current XLOGDIR later. The
	 * copy-from-archive filename is always the same, ensuring that we don't
	 * run out of disk space on long recoveries.
	 */
	snprintf(xlogpath, MAXPGPATH, XLOGDIR "/%s", recovername);

	/*
	 * Make sure there is no existing file named recovername.
	 */
	if (stat(xlogpath, &stat_buf) != 0)
	{
		if (errno != ENOENT)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not stat file \"%s\": %m",
							xlogpath)));
	}
	else
	{
		if (unlink(xlogpath) != 0)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not remove file \"%s\": %m",
							xlogpath)));
	}

	/*
	 * Calculate the archive file cutoff point for use during log shipping
	 * replication. All files earlier than this point can be deleted from the
	 * archive, though there is no requirement to do so.
	 *
	 * If cleanup is not enabled, initialise this with the filename of
	 * InvalidXLogRecPtr, which will prevent the deletion of any WAL files
	 * from the archive because of the alphabetic sorting property of WAL
	 * filenames.
	 *
	 * Once we have successfully located the redo pointer of the checkpoint
	 * from which we start recovery we never request a file prior to the redo
	 * pointer of the last restartpoint. When redo begins we know that we have
	 * successfully located it, so there is no need for additional status
	 * flags to signify the point when we can begin deleting WAL files from
	 * the archive.
	 */
	if (cleanupEnabled)
	{
		GetOldestRestartPoint(&restartRedoPtr, &restartTli);
		XLByteToSeg(restartRedoPtr, restartSegNo, wal_segment_size);
		XLogFileName(lastRestartPointFname, restartTli, restartSegNo,
					 wal_segment_size);
		/* we shouldn't need anything earlier than last restart point */
		Assert(strcmp(lastRestartPointFname, xlogfname) <= 0);
	}
	else
		XLogFileName(lastRestartPointFname, 0, 0, wal_segment_size);

	/* Build the restore command to execute */
	xlogRestoreCmd = BuildRestoreCommand(recoveryRestoreCommand,
										 xlogpath, xlogfname,
										 lastRestartPointFname);

	ereport(DEBUG3,
			(errmsg_internal("executing restore command \"%s\"",
							 xlogRestoreCmd)));

	fflush(NULL);
	pgstat_report_wait_start(WAIT_EVENT_RESTORE_COMMAND);

	/*
	 * PreRestoreCommand() informs the SIGTERM handler for the startup process
	 * that it should proc_exit() right away.  This is done for the duration
	 * of the system() call because there isn't a good way to break out while
	 * it is executing.  Since we might call proc_exit() in a signal handler,
	 * it is best to put any additional logic before or after the
	 * PreRestoreCommand()/PostRestoreCommand() section.
	 */
	PreRestoreCommand();

	/*
	 * Copy xlog from archival storage to XLOGDIR
	 */
	rc = system(xlogRestoreCmd);

	PostRestoreCommand();

	pgstat_report_wait_end();
	pfree(xlogRestoreCmd);

	if (rc == 0)
	{
		/*
		 * command apparently succeeded, but let's make sure the file is
		 * really there now and has the correct size.
		 */
		if (stat(xlogpath, &stat_buf) == 0)
		{
			if (expectedSize > 0 && stat_buf.st_size != expectedSize)
			{
				int			elevel;

				/*
				 * If we find a partial file in standby mode, we assume it's
				 * because it's just being copied to the archive, and keep
				 * trying.
				 *
				 * Otherwise treat a wrong-sized file as FATAL to ensure the
				 * DBA would notice it, but is that too strong? We could try
				 * to plow ahead with a local copy of the file ... but the
				 * problem is that there probably isn't one, and we'd
				 * incorrectly conclude we've reached the end of WAL and we're
				 * done recovering ...
				 */
				if (StandbyMode && stat_buf.st_size < expectedSize)
					elevel = DEBUG1;
				else
					elevel = FATAL;
				ereport(elevel,
						(errmsg("archive file \"%s\" has wrong size: %lld instead of %lld",
								xlogfname,
								(long long int) stat_buf.st_size,
								(long long int) expectedSize)));
				return false;
			}
			else
			{
				ereport(LOG,
						(errmsg("restored log file \"%s\" from archive",
								xlogfname)));
				strcpy(path, xlogpath);
				return true;
			}
		}
		else
		{
			/* stat failed */
			int			elevel = (errno == ENOENT) ? LOG : FATAL;

			ereport(elevel,
					(errcode_for_file_access(),
					 errmsg("could not stat file \"%s\": %m", xlogpath),
					 errdetail("\"restore_command\" returned a zero exit status, but stat() failed.")));
		}
	}

	/*
	 * Remember, we rollforward UNTIL the restore fails so failure here is
	 * just part of the process... that makes it difficult to determine
	 * whether the restore failed because there isn't an archive to restore,
	 * or because the administrator has specified the restore program
	 * incorrectly.  We have to assume the former.
	 *
	 * However, if the failure was due to any sort of signal, it's best to
	 * punt and abort recovery.  (If we "return false" here, upper levels will
	 * assume that recovery is complete and start up the database!) It's
	 * essential to abort on child SIGINT and SIGQUIT, because per spec
	 * system() ignores SIGINT and SIGQUIT while waiting; if we see one of
	 * those it's a good bet we should have gotten it too.
	 *
	 * On SIGTERM, assume we have received a fast shutdown request, and exit
	 * cleanly. It's pure chance whether we receive the SIGTERM first, or the
	 * child process. If we receive it first, the signal handler will call
	 * proc_exit, otherwise we do it here. If we or the child process received
	 * SIGTERM for any other reason than a fast shutdown request, postmaster
	 * will perform an immediate shutdown when it sees us exiting
	 * unexpectedly.
	 *
	 * We treat hard shell errors such as "command not found" as fatal, too.
	 */
	if (wait_result_is_signal(rc, SIGTERM))
		proc_exit(1);

	ereport(wait_result_is_any_signal(rc, true) ? FATAL : DEBUG2,
			(errmsg("could not restore file \"%s\" from archive: %s",
					xlogfname, wait_result_to_str(rc))));

not_available:

	/*
	 * if an archived file is not available, there might still be a version of
	 * this file in XLOGDIR, so return that as the filename to open.
	 *
	 * In many recovery scenarios we expect this to fail also, but if so that
	 * just means we've reached the end of WAL.
	 */
	snprintf(path, MAXPGPATH, XLOGDIR "/%s", xlogfname);
	return false;
}

/*
 * Attempt to execute an external shell command during recovery.
 *
 * 'command' is the shell command to be executed, 'commandName' is a
 * human-readable name describing the command emitted in the logs. If
 * 'failOnSignal' is true and the command is killed by a signal, a FATAL
 * error is thrown. Otherwise a WARNING is emitted.
 *
 * This is currently used for recovery_end_command and archive_cleanup_command.
 */
/*
 * 中文注释：
 * 在恢复过程中执行一条外部 shell 命令。目前有两个调用点：CleanupAfterArchiveRecovery()
 * 用它执行 recovery_end_command（归档恢复结束时执行一次）；CreateRestartPoint()
 * 用它执行 archive_cleanup_command（每次 restartpoint 后执行，用于清理归档）。
 *
 * 参数：
 *   command         —— 要执行的完整 shell 命令，可包含 %r 占位符；
 *   commandName     —— 人类可读的命令名（如 "recovery_end_command"），用于日志、
 *                      以及 replace_percent_placeholders() 的错误信息；
 *   failOnSignal    —— 命令被信号杀死时是否升级为 FATAL；false 时只发 WARNING；
 *   wait_event_info —— 等待事件编号（WAIT_EVENT_RECOVERY_END_COMMAND 或
 *                      WAIT_EVENT_ARCHIVE_CLEANUP_COMMAND），供 pg_stat_activity 展示。
 *
 * 返回值：无。失败只记录日志，不会中断恢复（除非因信号且 failOnSignal 为真而报
 * FATAL）。命令普通非零退出都只报 WARNING，符合“清理失败可以下次再来”的定位。
 *
 * 实现要点：先用 GetOldestRestartPoint() 在 ControlFileLock 共享锁下读取最近一次
 * checkpoint/restartpoint 的 redo 位置与时间线，算出 %r 的文件名；再用
 * replace_percent_placeholders() 替换命令中的 %r；最后 fflush(NULL) 并 system()。
 * %r 告诉清理脚本“早于该段名的归档文件都可以删除”，从而支持基于日志传送的归档
 * 清理。注意这里与 RestoreArchivedFile() 不同，没有 PreRestoreCommand()/
 * PostRestoreCommand() 保护：system() 期间收到的 SIGTERM 只置位 shutdown_requested，
 * 命令仍会执行完，随后由恢复主循环处理关闭请求。
 *
 * 并发注意：system() 会阻塞 startup process；命令内容来自 GUC，执行前已做 % 占位符
 * 校验（非法占位符会 ERROR）。
 */
void
ExecuteRecoveryCommand(const char *command, const char *commandName,
					   bool failOnSignal, uint32 wait_event_info)
{
	char	   *xlogRecoveryCmd;
	char		lastRestartPointFname[MAXPGPATH];
	int			rc;
	XLogSegNo	restartSegNo;
	XLogRecPtr	restartRedoPtr;
	TimeLineID	restartTli;

	Assert(command && commandName);

	/*
	 * Calculate the archive file cutoff point for use during log shipping
	 * replication. All files earlier than this point can be deleted from the
	 * archive, though there is no requirement to do so.
	 */
	GetOldestRestartPoint(&restartRedoPtr, &restartTli);
	XLByteToSeg(restartRedoPtr, restartSegNo, wal_segment_size);
	XLogFileName(lastRestartPointFname, restartTli, restartSegNo,
				 wal_segment_size);

	/*
	 * construct the command to be executed
	 */
	xlogRecoveryCmd = replace_percent_placeholders(command, commandName, "r", lastRestartPointFname);

	ereport(DEBUG3,
			(errmsg_internal("executing %s \"%s\"", commandName, command)));

	/*
	 * execute the constructed command
	 */
	fflush(NULL);
	pgstat_report_wait_start(wait_event_info);
	rc = system(xlogRecoveryCmd);
	pgstat_report_wait_end();

	pfree(xlogRecoveryCmd);

	if (rc != 0)
	{
		/*
		 * If the failure was due to any sort of signal, it's best to punt and
		 * abort recovery.  See comments in RestoreArchivedFile().
		 */
		ereport((failOnSignal && wait_result_is_any_signal(rc, true)) ? FATAL : WARNING,
		/*------
		   translator: First %s represents a postgresql.conf parameter name like
		  "recovery_end_command", the 2nd is the value of that parameter, the
		  third an already translated error message. */
				(errmsg("%s \"%s\": %s", commandName,
						command, wait_result_to_str(rc))));
	}
}


/*
 * A file was restored from the archive under a temporary filename (path),
 * and now we want to keep it. Rename it under the permanent filename in
 * pg_wal (xlogfname), replacing any existing file with the same name.
 */
/*
 * 中文注释：
 * 把 RestoreArchivedFile() 取回到临时文件 path 的内容转正为 pg_wal 下的正式文件
 * xlogfname，并维护对应的归档状态文件。
 *
 * 调用场景：xlogrecovery.c 的 XLogFileRead()（WAL 段恢复成功后）与 timeline.c
 * （timeline history 文件恢复成功后）。只在 startup process 中调用。
 *
 * 参数：
 *   path      —— 临时文件路径（XLOGDIR/RECOVERYXLOG 或 XLOGDIR/RECOVERYHISTORY）；
 *   xlogfname —— 正式文件名（如 0000000100000001000000C6、00000002.history）。
 *
 * 主要流程与副作用：
 *   1. 若目标文件已存在，置 reload = true，表示 walsender 可能持有旧文件的句柄；
 *      Windows 上还会先把旧文件 rename 成 <name>.deletedN 再 unlink：因为处于
 *      FILE_SHARE_DELETE 模式的文件被删除后，在最后一个句柄关闭前仍会出现在目录
 *      列表里，导致新文件无法就位。counter 保证同一段被多次恢复时临时名不冲突；
 *      这段窗口内目标名短暂不存在，并发 walsender 打开该段可能失败（可接受）；
 *   2. 用 durable_rename()（fsync + rename，失败 ERROR）把临时文件原子地替换为
 *      正式文件；
 *   3. 写归档状态文件：archive_mode 不是 always 时调用 XLogArchiveForceDone() 强制
 *      生成 .done，防止刚恢复的段再次被归档；archive_mode = always 时调用
 *      XLogArchiveNotify() 生成 .ready，让本机上的这个段也进入归档流程（always 表示
 *      即使处于恢复中也要归档）；
 *   4. 若替换过旧文件，调用 WalSndRqstFileReload() 请求 walsender 重新打开当前段
 *      （否则它们可能继续读已被替换的旧 inode）；最后 WalSndWakeup(true, false)
 *      唤醒 walsender，让它们发现新到达的 WAL 数据。
 *
 * 并发注意：rename/unlink 与 walsender 的并发打开存在竞态，但最坏情况只是打开失败
 * 后重试；本函数只在 startup process 中调用，相对于其他恢复动作天然串行，但此时
 * 热备连接可能已经建立，因此必须依赖 durable_rename() 的原子替换和上面的 walsender
 * 通知协议。
 */
void
KeepFileRestoredFromArchive(const char *path, const char *xlogfname)
{
	char		xlogfpath[MAXPGPATH];
	bool		reload = false;
	struct stat statbuf;

	snprintf(xlogfpath, MAXPGPATH, XLOGDIR "/%s", xlogfname);

	if (stat(xlogfpath, &statbuf) == 0)
	{
#ifdef WIN32
		char		oldpath[MAXPGPATH];
		static unsigned int deletedcounter = 1;

		/*
		 * On Windows, if another process (e.g a walsender process) holds the
		 * file open in FILE_SHARE_DELETE mode, unlink will succeed, but the
		 * file will still show up in directory listing until the last handle
		 * is closed, and we cannot rename the new file in its place until
		 * that. To avoid that problem, rename the old file to a temporary
		 * name first. Use a counter to create a unique filename, because the
		 * same file might be restored from the archive multiple times, and a
		 * walsender could still be holding onto an old deleted version of it.
		 *
		 * Note that this leaves a short window where the target name does not
		 * exist, during which a concurrent walsender opening the segment
		 * could fail.
		 */
		snprintf(oldpath, MAXPGPATH, "%s.deleted%u",
				 xlogfpath, deletedcounter++);
		if (rename(xlogfpath, oldpath) != 0)
		{
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not rename file \"%s\" to \"%s\": %m",
							xlogfpath, oldpath)));
		}

		if (unlink(oldpath) != 0)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not remove file \"%s\": %m",
							xlogfpath)));
#endif
		reload = true;
	}

	durable_rename(path, xlogfpath, ERROR);

	/*
	 * Create .done file forcibly to prevent the restored segment from being
	 * archived again later.
	 */
	if (XLogArchiveMode != ARCHIVE_MODE_ALWAYS)
		XLogArchiveForceDone(xlogfname);
	else
		XLogArchiveNotify(xlogfname);

	/*
	 * If the existing file was replaced, since walsenders might have it open,
	 * request them to reload a currently-open segment. This is only required
	 * for WAL segments, walsenders don't hold other files open, but there's
	 * no harm in doing this too often, and we don't know what kind of a file
	 * we're dealing with here.
	 */
	if (reload)
		WalSndRqstFileReload();

	/*
	 * Signal walsender that new WAL has arrived. Again, this isn't necessary
	 * if we restored something other than a WAL segment, but it does no harm
	 * either.
	 */
	WalSndWakeup(true, false);
}

/*
 * XLogArchiveNotify
 *
 * Create an archive notification file
 *
 * The name of the notification file is the message that will be picked up
 * by the archiver, e.g. we write 0000000100000001000000C6.ready
 * and the archiver then knows to archive XLOGDIR/0000000100000001000000C6,
 * then when complete, rename it to 0000000100000001000000C6.done
 */
/*
 * 中文注释：
 * 为指定的 WAL 文件创建归档通知文件 <XLOG>.ready，告诉 archiver “这个文件需要
 * 归档”。
 *
 * 调用场景：
 *   - WAL 段写满切换时（xlog.c 的 XLogWrite() 在写完一个完整段后通过
 *     XLogArchiveNotifySeg() 调用）；
 *   - 创建 timeline history 文件后（timeline.c）；
 *   - archive_mode = always 时，walreceiver 接收完的段 / standby 恢复出的段；
 *   - CleanupAfterArchiveRecovery() 为 .partial 段补发通知；
 *   - XLogArchiveCheckDone() 在既无 .ready 也无 .done 时重试创建。
 *
 * 参数 xlog：文件名（可带 .partial 后缀），用于拼出 archive_status/<xlog>.ready。
 * 返回值：无。创建/写入失败只报 LOG 而不报 ERROR——归档是尽力而为的辅助功能，
 * 不能因为磁盘暂时写满就阻断主库写入；后续 checkpoint 调用 XLogArchiveCheckDone()
 * 时会再尝试创建 .ready（这正是 CheckDone 除查询之外还要“重试通知”的原因）。
 *
 * 副作用：
 *   - 在 pg_wal/archive_status 下创建空文件（若已存在则截断，幂等）；
 *   - 时间线历史文件（IsTLHistoryFileName）调用 PgArchForceDirScan()：archiver
 *     平时会缓存一批待归档文件名以减少目录扫描，而 history 文件需要最高优先级
 *     尽快归档（降低提升后选中已被占用时间线的风险），因此强制它下次重新扫描；
 *   - 在 postmaster 子进程中调用 PgArchWakeup()，通过 latch 立即唤醒 archiver，
 *     不必等 60 秒的周期唤醒。
 *
 * 并发注意：多个进程可能并发为同一个文件创建 .ready，结果都是同一个空文件，
 * 内容无意义，因此无害；与 archiver 把 .ready rename 为 .done 的竞态由
 * XLogArchiveCheckDone()/IsBusy() 的“二次检查 .done”处理。
 */
void
XLogArchiveNotify(const char *xlog)
{
	char		archiveStatusPath[MAXPGPATH];
	FILE	   *fd;

	/* insert an otherwise empty file called <XLOG>.ready */
	StatusFilePath(archiveStatusPath, xlog, ".ready");
	fd = AllocateFile(archiveStatusPath, "w");
	if (fd == NULL)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not create archive status file \"%s\": %m",
						archiveStatusPath)));
		return;
	}
	if (FreeFile(fd))
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not write archive status file \"%s\": %m",
						archiveStatusPath)));
		return;
	}

	/*
	 * Timeline history files are given the highest archival priority to lower
	 * the chance that a promoted standby will choose a timeline that is
	 * already in use.  However, the archiver ordinarily tries to gather
	 * multiple files to archive from each scan of the archive_status
	 * directory, which means that newly created timeline history files could
	 * be left unarchived for a while.  To ensure that the archiver picks up
	 * timeline history files as soon as possible, we force the archiver to
	 * scan the archive_status directory the next time it looks for a file to
	 * archive.
	 */
	if (IsTLHistoryFileName(xlog))
		PgArchForceDirScan();

	/* Notify archiver that it's got something to do */
	if (IsUnderPostmaster)
		PgArchWakeup();
}

/*
 * Convenience routine to notify using segment number representation of filename
 */
/*
 * 中文注释：
 * XLogArchiveNotify() 的便捷封装：调用方给出段号和时间线，而不是拼好的文件名。
 *
 * 参数：segno 为 WAL 段号（以 wal_segment_size 为单位），tli 为时间线 ID，必须非 0
 * （函数内用 Assert 检查）。函数用 XLogFileName() 生成标准 24 位十六进制段名，
 * 再交给 XLogArchiveNotify() 创建 .ready 并唤醒 archiver。
 *
 * 调用场景：WAL 段写满、准备切换到下一段时由 xlog.c 调用，是正常归档流程的起点。
 * 返回值：无；错误处理与副作用同 XLogArchiveNotify()。
 */
void
XLogArchiveNotifySeg(XLogSegNo segno, TimeLineID tli)
{
	char		xlog[MAXFNAMELEN];

	Assert(tli != 0);

	XLogFileName(xlog, tli, segno, wal_segment_size);
	XLogArchiveNotify(xlog);
}

/*
 * XLogArchiveForceDone
 *
 * Emit notification forcibly that an XLOG segment file has been successfully
 * archived, by creating <XLOG>.done regardless of whether <XLOG>.ready
 * exists or not.
 */
/*
 * 中文注释：
 * 强制声明某个 WAL 文件“已归档/无需归档”：无论是否存在 .ready，都保证最终存在
 * <XLOG>.done，从而阻止 archiver 再处理它。
 *
 * 参数 xlog：WAL 段名、timeline history 文件名或 .partial 文件名。
 *
 * 实现分三种情况：
 *   1. .done 已存在：直接返回（幂等，无副作用）；
 *   2. .ready 存在：用 durable_rename() 把它改名为 .done。这一步同时“取消”了待归档
 *      请求；若重命名失败只报 WARNING 并返回（下次检查仍会看到 .ready）；
 *   3. 两者都不存在：直接创建空 .done 文件；AllocateFile/FreeFile 失败只报 LOG。
 *
 * 调用场景：
 *   - walreceiver 接收完一个流式 WAL 段后（archive_mode != always）：该段已由主库
 *     负责归档，备库不应再归档一次，否则 archive_command 可能因目标已存在而失败；
 *   - KeepFileRestoredFromArchive() 恢复出段后，防止它被再次归档；
 *   - 接收完 timeline history 文件后同理。
 * 注意 archive_mode = always 时调用方会改用 XLogArchiveNotify()，因为此时本机
 * 生成/接收的每个文件都应进入归档。
 *
 * 并发注意：与 archiver 的“重命名 .ready -> .done”可能并发，但两者目标一致；
 * 若 archiver 正在执行 archive_command，之后它再 rename 时 .ready 已不存在，会
 * 安静地失败。函数不主动唤醒 archiver，因为这里产生的是“完成”状态而非待办。
 */
void
XLogArchiveForceDone(const char *xlog)
{
	char		archiveReady[MAXPGPATH];
	char		archiveDone[MAXPGPATH];
	struct stat stat_buf;
	FILE	   *fd;

	/* Exit if already known done */
	StatusFilePath(archiveDone, xlog, ".done");
	if (stat(archiveDone, &stat_buf) == 0)
		return;

	/* If .ready exists, rename it to .done */
	StatusFilePath(archiveReady, xlog, ".ready");
	if (stat(archiveReady, &stat_buf) == 0)
	{
		(void) durable_rename(archiveReady, archiveDone, WARNING);
		return;
	}

	/* insert an otherwise empty file called <XLOG>.done */
	fd = AllocateFile(archiveDone, "w");
	if (fd == NULL)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not create archive status file \"%s\": %m",
						archiveDone)));
		return;
	}
	if (FreeFile(fd))
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not write archive status file \"%s\": %m",
						archiveDone)));
		return;
	}
}

/*
 * XLogArchiveCheckDone
 *
 * This is called when we are ready to delete or recycle an old XLOG segment
 * file or backup history file.  If it is okay to delete it then return true.
 * If it is not time to delete it, make sure a .ready file exists, and return
 * false.
 *
 * If <XLOG>.done exists, then return true; else if <XLOG>.ready exists,
 * then return false; else create <XLOG>.ready and return false.
 *
 * The reason we do things this way is so that if the original attempt to
 * create <XLOG>.ready fails, we'll retry during subsequent checkpoints.
 */
/*
 * 中文注释：
 * 判断某个 WAL 段/备份历史文件是否可以安全删除或回收；若还不能删除，则顺便确保
 * .ready 存在，让 archiver 最终会处理它。
 *
 * 参数 xlog：待检查的文件名（WAL 段名或 backup history 文件名）。
 * 返回值：true 表示可以删除；false 表示需要保留（等待归档或已排队）。
 *
 * 判定顺序：
 *   1. archive_mode = off（!XLogArchivingActive()）→ 直接 true；
 *   2. 处于 archive recovery 且 archive_mode != always → true。此时正在重放归档
 *      中的 WAL，本机不负责归档这些文件（always 模式除外），因此可以直接删除/回收；
 *   3. 否则（主库 on/always，或备库 always）：
 *        .done 存在 → true（archiver 已完成）；
 *        .ready 存在 → false（archiver 正在处理或尚未处理）；
 *        再次检查 .done → true（处理“检查 .ready 时 archiver 刚好完成并改名”的竞态）；
 *        都不存在 → 调用 XLogArchiveNotify() 重试创建 .ready，返回 false。
 *
 * 调用场景：checkpoint 的 RemoveOldXlogFiles()/CleanupBackupHistory() 逐个文件调用，
 * 决定是否删除或回收；只有返回 true 才会真正 unlink/recycle。
 *
 * 设计思想：把“判断 + 补建 .ready”合并在一起，使最初 XLogArchiveNotify() 失败
 * （例如瞬时 ENOSPC）的文件能在后续 checkpoint 自动恢复归档流程，无需人工干预，
 * 也不需要额外的重试队列。函数无锁，完全依赖目录项存在性与 rename 的原子性；
 * 与 archiver 的竞态通过“先查 .ready 再复查 .done”的固定顺序收敛到保守结果。
 */
bool
XLogArchiveCheckDone(const char *xlog)
{
	char		archiveStatusPath[MAXPGPATH];
	struct stat stat_buf;

	/* The file is always deletable if archive_mode is "off". */
	if (!XLogArchivingActive())
		return true;

	/*
	 * During archive recovery, the file is deletable if archive_mode is not
	 * "always".
	 */
	if (!XLogArchivingAlways() &&
		GetRecoveryState() == RECOVERY_STATE_ARCHIVE)
		return true;

	/*
	 * At this point of the logic, note that we are either a primary with
	 * archive_mode set to "on" or "always", or a standby with archive_mode
	 * set to "always".
	 */

	/* First check for .done --- this means archiver is done with it */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	/* check for .ready --- this means archiver is still busy with it */
	StatusFilePath(archiveStatusPath, xlog, ".ready");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return false;

	/* Race condition --- maybe archiver just finished, so recheck */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	/* Retry creation of the .ready file */
	XLogArchiveNotify(xlog);
	return false;
}

/*
 * XLogArchiveIsBusy
 *
 * Check to see if an XLOG segment file is still unarchived.
 * This is almost but not quite the inverse of XLogArchiveCheckDone: in
 * the first place we aren't chartered to recreate the .ready file, and
 * in the second place we should consider that if the file is already gone
 * then it's not busy.  (This check is needed to handle the race condition
 * that a checkpoint already deleted the no-longer-needed file.)
 */
/*
 * 中文注释：
 * 判断某个 WAL 文件是否“仍在等待归档”（busy）。它是 XLogArchiveCheckDone() 的
 * 近似逆操作，但有两个关键区别：不负责补建 .ready；如果 WAL 文件本身已经消失，
 * 则视为不 busy。
 *
 * 参数 xlog：WAL 段名或 backup history 文件名。
 * 返回值：true 表示可能尚未归档完成，调用方应继续等待；false 表示已归档或无需归档。
 *
 * 判定顺序：
 *   1. .done 存在 → false；
 *   2. .ready 存在 → true；
 *   3. 复查 .done → false（处理检查 .ready 期间 archiver 刚好完成的竞态）；
 *   4. 检查 XLOGDIR/xlog 本身：若 stat 失败且 errno == ENOENT，说明 checkpoint 已经
 *      把这个不再需要的文件删掉了；而删除前必然经过 XLogArchiveCheckDone() 的许可，
 *      因此它要么已归档、要么无需归档 → false；
 *   5. 其余情况（既无状态文件、WAL 文件又存在）→ 保守地返回 true。
 *
 * 调用场景：基础备份结束时若要求等待归档（waitforarchive），xlog.c 会循环调用本
 * 函数等待最后一个 WAL 段和 backup history 文件归档完成，确保备份集在归档中自洽。
 *
 * 并发注意：无锁，纯文件系统查询。检查过程中 archiver/checkpoint 可能并发改变状态，
 * 但第 3 步复查与第 4 步的 ENOENT 判断共同保证不会把“已完成”误判为“仍在忙”；
 * 反过来短暂误判为 busy 只会让调用方多重试一次，是安全的方向。
 */
bool
XLogArchiveIsBusy(const char *xlog)
{
	char		archiveStatusPath[MAXPGPATH];
	struct stat stat_buf;

	/* First check for .done --- this means archiver is done with it */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return false;

	/* check for .ready --- this means archiver is still busy with it */
	StatusFilePath(archiveStatusPath, xlog, ".ready");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	/* Race condition --- maybe archiver just finished, so recheck */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return false;

	/*
	 * Check to see if the WAL file has been removed by checkpoint, which
	 * implies it has already been archived, and explains why we can't see a
	 * status file for it.
	 */
	snprintf(archiveStatusPath, MAXPGPATH, XLOGDIR "/%s", xlog);
	if (stat(archiveStatusPath, &stat_buf) != 0 &&
		errno == ENOENT)
		return false;

	return true;
}

/*
 * XLogArchiveIsReadyOrDone
 *
 * Check to see if an XLOG segment file has a .ready or .done file.
 * This is similar to XLogArchiveIsBusy(), but returns true if the file
 * is already archived or is about to be archived.
 *
 * This is currently only used at recovery.  During normal operation this
 * would be racy: the file might get removed or marked with .ready as we're
 * checking it, or immediately after we return.
 */
/*
 * 中文注释：
 * 判断某个 WAL 文件是否已经有 .ready 或 .done 状态文件，也就是“已经在归档队列中
 * 或已经归档完成”。
 *
 * 参数 xlog：文件名。
 * 返回值：true 表示 .done 或 .ready 至少存在一个（先查 .done，再查 .ready，最后
 * 复查 .done 以处理 archiver 并发完成改名的竞态）；false 表示两者都没有。
 *
 * 调用场景：CleanupAfterArchiveRecovery() 在时间线切换且最后一段只写了一半时，用它
 * 决定是否要把该段改名为 .partial 后归档：若已有 .ready/.done，说明该段已经被判定
 * 为完整、正在归档或已经归档，就不再做 .partial 转换，避免与原始主库的归档动作
 * 冲突。
 *
 * 并发注意：正如函数上方英文注释所述，这个函数只在恢复期间可靠。正常运行时状态
 * 随时可能变化——检查的瞬间可能刚好被标记 .ready，或文件刚好被 checkpoint 删除，
 * 因此不能用于运行期的删除决策（那种场景应使用 XLogArchiveCheckDone() 或
 * XLogArchiveIsBusy()）。这里不重试、不创建任何文件，属于纯查询。
 */
bool
XLogArchiveIsReadyOrDone(const char *xlog)
{
	char		archiveStatusPath[MAXPGPATH];
	struct stat stat_buf;

	/* First check for .done --- this means archiver is done with it */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	/* check for .ready --- this means archiver is still busy with it */
	StatusFilePath(archiveStatusPath, xlog, ".ready");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	/* Race condition --- maybe archiver just finished, so recheck */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	return false;
}

/*
 * XLogArchiveIsReady
 *
 * Check to see if an XLOG segment file has an archive notification (.ready)
 * file.
 */
/*
 * 中文注释：
 * 只检查 <XLOG>.ready 是否存在，即该文件是否已被明确排入归档队列。
 *
 * 参数 xlog：文件名；返回值：存在 .ready 时为 true，否则为 false。纯查询，
 * 不创建文件、不重试、不加锁。
 *
 * 调用场景：RemoveNonParentXlogFiles() 在时间线切换后清理旧时间线的段时调用。
 * 这些旧段即使不归档也不影响恢复，但如果已经创建了 .ready，说明归档流程已经把它
 * 纳入待办，贸然删除会让 archiver 找不到文件并报错，因此选择先保留、让归档完成
 * 后再由 checkpoint 正常删除。
 *
 * 注意：与 XLogArchiveIsReadyOrDone() 不同，这里不把 .done 视为“可保留”的理由——
 * 已归档的旧时间线段可以安全删除。
 */
bool
XLogArchiveIsReady(const char *xlog)
{
	char		archiveStatusPath[MAXPGPATH];
	struct stat stat_buf;

	StatusFilePath(archiveStatusPath, xlog, ".ready");
	if (stat(archiveStatusPath, &stat_buf) == 0)
		return true;

	return false;
}

/*
 * XLogArchiveCleanup
 *
 * Cleanup archive notification file(s) for a particular xlog segment
 */
/*
 * 中文注释：
 * 删除某个 WAL 文件对应的归档状态文件（.done 和 .ready），即清空它在
 * archive_status 目录中的记录。
 *
 * 参数 xlog：已被删除或回收的文件名（也可能带 .partial 后缀）。
 * 返回值：无。两次 unlink() 的返回值都被忽略——状态文件本来就可能不存在，
 * “清理一个不存在的状态”不是错误。
 *
 * 调用场景：
 *   - RemoveXlogFile()/RemoveOldXlogFiles() 删除或回收 WAL 段后调用，避免
 *     archive_status 里残留孤儿状态文件（也避免之后同名段复用时被误认为已归档）；
 *   - 时间线切换、创建新时间线首个段后调用（XLogInitNewTimeline），确保新段没有
 *     从旧时间线继承来的 .ready/.done；
 *   - CleanupAfterArchiveRecovery() 在把段改名为 .partial 前清理 .partial 的状态。
 *
 * 设计思想：状态文件的生命周期跟随 WAL 文件；删除是幂等的，失败也只留下无害的
 * 空文件，后续 XLogArchiveCheckDone() 不会因此误删数据（最多让某个文件名多保留
 * 一段时间）。先删 .done 再删 .ready 的顺序无关紧要，因为调用方已经把 WAL 文件
 * 本身删除/改名，archiver 即使看到 .ready 也只会因文件不存在而跳过。
 */
void
XLogArchiveCleanup(const char *xlog)
{
	char		archiveStatusPath[MAXPGPATH];

	/* Remove the .done file */
	StatusFilePath(archiveStatusPath, xlog, ".done");
	unlink(archiveStatusPath);
	/* should we complain about failure? */

	/* Remove the .ready file if present --- normally it shouldn't be */
	StatusFilePath(archiveStatusPath, xlog, ".ready");
	unlink(archiveStatusPath);
	/* should we complain about failure? */
}
