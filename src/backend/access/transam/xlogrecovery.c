/*-------------------------------------------------------------------------
 *
 * xlogrecovery.c
 *		Functions for WAL recovery, standby mode
 *
 * This source file contains functions controlling WAL recovery.
 * InitWalRecovery() initializes the system for crash or archive recovery,
 * or standby mode, depending on configuration options and the state of
 * the control file and possible backup label file.  PerformWalRecovery()
 * performs the actual WAL replay, calling the rmgr-specific redo routines.
 * FinishWalRecovery() performs end-of-recovery checks and cleanup actions,
 * and prepares information needed to initialize the WAL for writes.  In
 * addition to these three main functions, there are a bunch of functions
 * for interrogating recovery state and controlling the recovery process.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/xlogrecovery.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <ctype.h>
#include <time.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>

#include "access/timeline.h"
#include "access/transam.h"
#include "access/xact.h"
#include "access/xlog_internal.h"
#include "access/xlogarchive.h"
#include "access/xlogprefetcher.h"
#include "access/xlogreader.h"
#include "access/xlogrecovery.h"
#include "access/xlogutils.h"
#include "access/xlogwait.h"
#include "backup/basebackup.h"
#include "catalog/pg_control.h"
#include "commands/tablespace.h"
#include "common/file_utils.h"
#include "miscadmin.h"
#include "nodes/miscnodes.h"
#include "pgstat.h"
#include "postmaster/bgwriter.h"
#include "postmaster/startup.h"
#include "replication/slot.h"
#include "replication/slotsync.h"
#include "replication/walreceiver.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/latch.h"
#include "storage/pmsignal.h"
#include "storage/procarray.h"
#include "storage/spin.h"
#include "storage/subsystems.h"
#include "utils/datetime.h"
#include "utils/fmgrprotos.h"
#include "utils/guc.h"
#include "utils/guc_hooks.h"
#include "utils/pgstat_internal.h"
#include "utils/pg_lsn.h"
#include "utils/ps_status.h"
#include "utils/pg_rusage.h"
#include "utils/wait_event.h"

/* Unsupported old recovery command file names (relative to $PGDATA) */
#define RECOVERY_COMMAND_FILE	"recovery.conf"
#define RECOVERY_COMMAND_DONE	"recovery.done"

/*
 * GUC support
 */
const struct config_enum_entry recovery_target_action_options[] = {
	{"pause", RECOVERY_TARGET_ACTION_PAUSE, false},
	{"promote", RECOVERY_TARGET_ACTION_PROMOTE, false},
	{"shutdown", RECOVERY_TARGET_ACTION_SHUTDOWN, false},
	{NULL, 0, false}
};

/* options formerly taken from recovery.conf for archive recovery */
char	   *recoveryRestoreCommand = NULL;
char	   *recoveryEndCommand = NULL;
char	   *archiveCleanupCommand = NULL;
RecoveryTargetType recoveryTarget = RECOVERY_TARGET_UNSET;
bool		recoveryTargetInclusive = true;
int			recoveryTargetAction = RECOVERY_TARGET_ACTION_PAUSE;
TransactionId recoveryTargetXid;
char	   *recovery_target_time_string;
TimestampTz recoveryTargetTime;
char	   *recoveryTargetName;
XLogRecPtr	recoveryTargetLSN;
int			recovery_min_apply_delay = 0;

/* options formerly taken from recovery.conf for XLOG streaming */
char	   *PrimaryConnInfo = NULL;
char	   *PrimarySlotName = NULL;
bool		wal_receiver_create_temp_slot = false;

/*
 * recoveryTargetTimeLineGoal: what the user requested, if any
 *
 * recoveryTargetTLIRequested: numeric value of requested timeline, if constant
 *
 * recoveryTargetTLI: the currently understood target timeline; changes
 *
 * expectedTLEs: a list of TimeLineHistoryEntries for recoveryTargetTLI and
 * the timelines of its known parents, newest first (so recoveryTargetTLI is
 * always the first list member).  Only these TLIs are expected to be seen in
 * the WAL segments we read, and indeed only these TLIs will be considered as
 * candidate WAL files to open at all.
 *
 * curFileTLI: the TLI appearing in the name of the current input WAL file.
 * (This is not necessarily the same as the timeline from which we are
 * replaying WAL, which StartupXLOG calls replayTLI, because we could be
 * scanning data that was copied from an ancestor timeline when the current
 * file was created.)  During a sequential scan we do not allow this value
 * to decrease.
 */
RecoveryTargetTimeLineGoal recoveryTargetTimeLineGoal = RECOVERY_TARGET_TIMELINE_LATEST;
TimeLineID	recoveryTargetTLIRequested = 0;
TimeLineID	recoveryTargetTLI = 0;
static List *expectedTLEs;
static TimeLineID curFileTLI;

/*
 * When ArchiveRecoveryRequested is set, archive recovery was requested,
 * ie. signal files were present.  When InArchiveRecovery is set, we are
 * currently recovering using offline XLOG archives.  These variables are only
 * valid in the startup process.
 *
 * When ArchiveRecoveryRequested is true, but InArchiveRecovery is false, we're
 * currently performing crash recovery using only XLOG files in pg_wal, but
 * will switch to using offline XLOG archives as soon as we reach the end of
 * WAL in pg_wal.
 */
bool		ArchiveRecoveryRequested = false;
bool		InArchiveRecovery = false;

/*
 * When StandbyModeRequested is set, standby mode was requested, i.e.
 * standby.signal file was present.  When StandbyMode is set, we are currently
 * in standby mode.  These variables are only valid in the startup process.
 * They work similarly to ArchiveRecoveryRequested and InArchiveRecovery.
 */
static bool StandbyModeRequested = false;
bool		StandbyMode = false;

/* was a signal file present at startup? */
static bool standby_signal_file_found = false;
static bool recovery_signal_file_found = false;

/*
 * CheckPointLoc is the position of the checkpoint record that determines
 * where to start the replay.  It comes from the backup label file or the
 * control file.
 *
 * RedoStartLSN is the checkpoint's REDO location, also from the backup label
 * file or the control file.  In standby mode, XLOG streaming usually starts
 * from the position where an invalid record was found.  But if we fail to
 * read even the initial checkpoint record, we use the REDO location instead
 * of the checkpoint location as the start position of XLOG streaming.
 * Otherwise we would have to jump backwards to the REDO location after
 * reading the checkpoint record, because the REDO record can precede the
 * checkpoint record.
 */
static XLogRecPtr CheckPointLoc = InvalidXLogRecPtr;
static TimeLineID CheckPointTLI = 0;
static XLogRecPtr RedoStartLSN = InvalidXLogRecPtr;
static TimeLineID RedoStartTLI = 0;

/*
 * Local copy of SharedHotStandbyActive variable. False actually means "not
 * known, need to check the shared state".
 */
static bool LocalHotStandbyActive = false;

/*
 * Local copy of SharedPromoteIsTriggered variable. False actually means "not
 * known, need to check the shared state".
 */
static bool LocalPromoteIsTriggered = false;

/* Has the recovery code requested a walreceiver wakeup? */
static bool doRequestWalReceiverReply;

/* XLogReader object used to parse the WAL records */
static XLogReaderState *xlogreader = NULL;

/* XLogPrefetcher object used to consume WAL records with read-ahead */
static XLogPrefetcher *xlogprefetcher = NULL;

/* Parameters passed down from ReadRecord to the XLogPageRead callback. */
typedef struct XLogPageReadPrivate
{
	int			emode;
	bool		fetching_ckpt;	/* are we fetching a checkpoint record? */
	bool		randAccess;
	TimeLineID	replayTLI;
} XLogPageReadPrivate;

/* flag to tell XLogPageRead that we have started replaying */
static bool InRedo = false;

/*
 * Codes indicating where we got a WAL file from during recovery, or where
 * to attempt to get one.
 */
typedef enum
{
	XLOG_FROM_ANY = 0,			/* request to read WAL from any source */
	XLOG_FROM_ARCHIVE,			/* restored using restore_command */
	XLOG_FROM_PG_WAL,			/* existing file in pg_wal */
	XLOG_FROM_STREAM,			/* streamed from primary */
} XLogSource;

/* human-readable names for XLogSources, for debugging output */
static const char *const xlogSourceNames[] = {"any", "archive", "pg_wal", "stream"};

/*
 * readFile is -1 or a kernel FD for the log file segment that's currently
 * open for reading.  readSegNo identifies the segment.  readOff is the offset
 * of the page just read, readLen indicates how much of it has been read into
 * readBuf, and readSource indicates where we got the currently open file from.
 *
 * Note: we could use Reserve/ReleaseExternalFD to track consumption of this
 * FD too (like for openLogFile in xlog.c); but it doesn't currently seem
 * worthwhile, since the XLOG is not read by general-purpose sessions.
 */
static int	readFile = -1;
static XLogSegNo readSegNo = 0;
static uint32 readOff = 0;
static uint32 readLen = 0;
static XLogSource readSource = XLOG_FROM_ANY;

/*
 * Keeps track of which source we're currently reading from. This is
 * different from readSource in that this is always set, even when we don't
 * currently have a WAL file open. If lastSourceFailed is set, our last
 * attempt to read from currentSource failed, and we should try another source
 * next.
 *
 * pendingWalRcvRestart is set when a config change occurs that requires a
 * walreceiver restart.  This is only valid in XLOG_FROM_STREAM state.
 */
static XLogSource currentSource = XLOG_FROM_ANY;
static bool lastSourceFailed = false;
static bool pendingWalRcvRestart = false;

/*
 * These variables track when we last obtained some WAL data to process,
 * and where we got it from.  (XLogReceiptSource is initially the same as
 * readSource, but readSource gets reset to zero when we don't have data
 * to process right now.  It is also different from currentSource, which
 * also changes when we try to read from a source and fail, while
 * XLogReceiptSource tracks where we last successfully read some WAL.)
 */
static TimestampTz XLogReceiptTime = 0;
static XLogSource XLogReceiptSource = XLOG_FROM_ANY;

/* Local copy of WalRcv->flushedUpto */
static XLogRecPtr flushedUpto = InvalidXLogRecPtr;
static TimeLineID receiveTLI = 0;

/*
 * Copy of minRecoveryPoint and backupEndPoint from the control file.
 *
 * In order to reach consistency, we must replay the WAL up to
 * minRecoveryPoint.  If backupEndRequired is true, we must also reach
 * backupEndPoint, or if it's invalid, an end-of-backup record corresponding
 * to backupStartPoint.
 *
 * Note: In archive recovery, after consistency has been reached, the
 * functions in xlog.c will start updating minRecoveryPoint in the control
 * file.  But this copy of minRecoveryPoint variable reflects the value at the
 * beginning of recovery, and is *not* updated after consistency is reached.
 */
static XLogRecPtr minRecoveryPoint;
static TimeLineID minRecoveryPointTLI;

static XLogRecPtr backupStartPoint;
static XLogRecPtr backupEndPoint;
static bool backupEndRequired = false;

/*
 * Have we reached a consistent database state?  In crash recovery, we have
 * to replay all the WAL, so reachedConsistency is never set.  During archive
 * recovery, the database is consistent once minRecoveryPoint is reached.
 *
 * Consistent state means that the system is internally consistent, all
 * the WAL has been replayed up to a certain point, and importantly, there
 * is no trace of later actions on disk.
 *
 * This flag is used only by the startup process and postmaster. When
 * minRecoveryPoint is reached, the startup process sets it to true and
 * sends a PMSIGNAL_RECOVERY_CONSISTENT signal to the postmaster,
 * which then sets it to true upon receiving the signal.
 */
bool		reachedConsistency = false;

/* Buffers dedicated to consistency checks of size BLCKSZ */
static char *replay_image_masked = NULL;
static char *primary_image_masked = NULL;

XLogRecoveryCtlData *XLogRecoveryCtl = NULL;

static void XLogRecoveryShmemRequest(void *arg);
static void XLogRecoveryShmemInit(void *arg);

const ShmemCallbacks XLogRecoveryShmemCallbacks = {
	.request_fn = XLogRecoveryShmemRequest,
	.init_fn = XLogRecoveryShmemInit,
};

/*
 * abortedRecPtr is the start pointer of a broken record at end of WAL when
 * recovery completes; missingContrecPtr is the location of the first
 * contrecord that went missing.  See CreateOverwriteContrecordRecord for
 * details.
 */
static XLogRecPtr abortedRecPtr;
static XLogRecPtr missingContrecPtr;

/*
 * if recoveryStopsBefore/After returns true, it saves information of the stop
 * point here
 */
static TransactionId recoveryStopXid;
static TimestampTz recoveryStopTime;
static XLogRecPtr recoveryStopLSN;
static char recoveryStopName[MAXFNAMELEN];
static bool recoveryStopAfter;

/* prototypes for local functions */
static void ApplyWalRecord(XLogReaderState *xlogreader, XLogRecord *record, TimeLineID *replayTLI);

static void EnableStandbyMode(void);
static void readRecoverySignalFile(void);
static void validateRecoveryParameters(void);
static bool read_backup_label(XLogRecPtr *checkPointLoc,
							  TimeLineID *backupLabelTLI,
							  bool *backupEndRequired, bool *backupFromStandby);
static bool read_tablespace_map(List **tablespaces);

static void xlogrecovery_redo(XLogReaderState *record, TimeLineID replayTLI);
static void CheckRecoveryConsistency(void);
static void rm_redo_error_callback(void *arg);
#ifdef WAL_DEBUG
static void xlog_outrec(StringInfo buf, XLogReaderState *record);
#endif
static void xlog_block_info(StringInfo buf, XLogReaderState *record);
static void checkTimeLineSwitch(XLogRecPtr lsn, TimeLineID newTLI,
								TimeLineID prevTLI, TimeLineID replayTLI);
static bool getRecordTimestamp(XLogReaderState *record, TimestampTz *recordXtime);
static void verifyBackupPageConsistency(XLogReaderState *record);

static bool recoveryStopsBefore(XLogReaderState *record);
static bool recoveryStopsAfter(XLogReaderState *record);
static char *getRecoveryStopReason(void);
static void recoveryPausesHere(bool endOfRecovery);
static bool recoveryApplyDelay(XLogReaderState *record);
static void ConfirmRecoveryPaused(void);

static XLogRecord *ReadRecord(XLogPrefetcher *xlogprefetcher,
							  int emode, bool fetching_ckpt,
							  TimeLineID replayTLI);

static int	XLogPageRead(XLogReaderState *xlogreader, XLogRecPtr targetPagePtr,
						 int reqLen, XLogRecPtr targetRecPtr, char *readBuf);
static XLogPageReadResult WaitForWALToBecomeAvailable(XLogRecPtr RecPtr,
													  bool randAccess,
													  bool fetching_ckpt,
													  XLogRecPtr tliRecPtr,
													  TimeLineID replayTLI,
													  XLogRecPtr replayLSN,
													  bool nonblocking);
static int	emode_for_corrupt_record(int emode, XLogRecPtr RecPtr);
static XLogRecord *ReadCheckpointRecord(XLogPrefetcher *xlogprefetcher,
										XLogRecPtr RecPtr, TimeLineID replayTLI);
static bool rescanLatestTimeLine(TimeLineID replayTLI, XLogRecPtr replayLSN);
static int	XLogFileRead(XLogSegNo segno, TimeLineID tli,
						 XLogSource source, bool notfoundOk);
static int	XLogFileReadAnyTLI(XLogSegNo segno, XLogSource source);

static bool CheckForStandbyTrigger(void);
static void SetPromoteIsTriggered(void);
static bool HotStandbyActiveInReplay(void);

static void SetCurrentChunkStartTime(TimestampTz xtime);
static void SetLatestXTime(TimestampTz xtime);
static RecoveryTargetType DetermineRecoveryTargetType(void);

/*
 * Register shared memory for WAL recovery
 */
/*
 * 中文注释：
 * 向共享内存框架登记 WAL 恢复控制结构 XLogRecoveryCtlData。
 *
 * 该结构保存 startup 进程与普通后端共享的恢复进度（lastReplayedEndRecPtr、
 * replayEndRecPtr、replayEndTLI）、暂停状态、热备是否激活、提升是否触发以及
 * recoveryWakeupLatch 等。所有字段由 info_lck 自旋锁保护，读者包括 walsender、
 * 检查点进程和 SQL 函数。
 */
static void
XLogRecoveryShmemRequest(void *arg)
{
	ShmemRequestStruct(.name = "XLOG Recovery Ctl",
					   .size = sizeof(XLogRecoveryCtlData),
					   .ptr = (void **) &XLogRecoveryCtl,
		);
}

/*
 * 中文注释：
 * 初始化共享的 WAL 恢复控制结构。
 *
 * 先整体清零，再初始化 info_lck 自旋锁、recoveryWakeupLatch 共享闩锁和
 * recoveryNotPausedCV 条件变量。latch 由 startup 进程在进入归档恢复时
 * OwnLatch，其他进程通过 WakeupRecovery 触发；条件变量用于恢复暂停/继续。
 */
static void
XLogRecoveryShmemInit(void *arg)
{
	memset(XLogRecoveryCtl, 0, sizeof(XLogRecoveryCtlData));

	SpinLockInit(&XLogRecoveryCtl->info_lck);
	InitSharedLatch(&XLogRecoveryCtl->recoveryWakeupLatch);
	ConditionVariableInit(&XLogRecoveryCtl->recoveryNotPausedCV);
}

/*
 * A thin wrapper to enable StandbyMode and do other preparatory work as
 * needed.
 */
/*
 * 中文注释：
 * 启用备库模式并做相应准备。
 *
 * 设置全局 StandbyMode=true，使 WAL 读取状态机在本地 WAL 用尽后尝试从主库流式
 * 接收；同时关闭 startup progress timeout，因为备库会长期处于恢复状态，周期性
 * 输出进度只会造成日志膨胀。
 */
static void
EnableStandbyMode(void)
{
	StandbyMode = true;

	/*
	 * To avoid server log bloat, we don't report recovery progress in a
	 * standby as it will always be in recovery unless promoted. We disable
	 * startup progress timeout in standby mode to avoid calling
	 * startup_progress_timeout_handler() unnecessarily.
	 */
	disable_startup_progress_timeout();
}

/*
 * Prepare the system for WAL recovery, if needed.
 *
 * This is called by StartupXLOG() which coordinates the server startup
 * sequence.  This function analyzes the control file and the backup label
 * file, if any, and figures out whether we need to perform crash recovery or
 * archive recovery, and how far we need to replay the WAL to reach a
 * consistent state.
 *
 * This doesn't yet change the on-disk state, except for creating the symlinks
 * from table space map file if any, and for fetching WAL files needed to find
 * the checkpoint record.  On entry, the caller has already read the control
 * file into memory, and passes it as argument.  This function updates it to
 * reflect the recovery state, and the caller is expected to write it back to
 * disk after initializing other subsystems, but before calling
 * PerformWalRecovery().
 *
 * This initializes some global variables like ArchiveRecoveryRequested, and
 * StandbyModeRequested and InRecovery.
 */
/*
 * 中文注释：
 * 为 WAL 恢复做初始化：分析 pg_control 和 backup_label，决定恢复类型和起点。
 *
 * 本函数由 StartupXLOG 调用，是恢复流程的第一阶段，尚不修改磁盘状态（除了根据
 * tablespace_map 建立符号链接、以及读取定位 checkpoint 所需的 WAL）。主要工作：
 *   1. 根据 minRecoveryPointTLI/checkpoint TLI 设定 recoveryTargetTLI；
 *   2. readRecoverySignalFile 判断是否请求归档恢复/备库模式，
 *      validateRecoveryParameters 校验 recovery_target* 参数；
 *   3. 若需要归档恢复，取得 recoveryWakeupLatch 的所有权；
 *   4. 分配 xlogreader、解码缓冲区、prefetcher 和两个用于页一致性校验的
 *      BLCKSZ 缓冲区；
 *   5. 有 backup_label 时从标签指定的 checkpoint 开始（而不是 pg_control），
 *      必要时读 tablespace_map 建符号链接；没有 backup_label 时从 pg_control 的
 *      checkpoint 开始，并处理孤立的 tablespace_map；
 *   6. 校验 checkpoint 所在时间线确实位于目标时间线历史中，minRecoveryPoint
 *      也在同一历史中；
 *   7. 根据是否干净关闭、是否存在恢复信号、redo 是否小于 checkpoint 等决定
 *      InRecovery/InArchiveRecovery，并更新内存中的 ControlFile 副本；
 *   8. 设置 backupStartPoint/backupEndPoint/minRecoveryPoint 等全局变量。
 * 返回前通过输出参数告知调用者 wasShutdown、是否使用了 backup_label 和
 * tablespace_map，调用者稍后负责删除这些文件并写回 ControlFile。
 */
void
InitWalRecovery(ControlFileData *ControlFile, bool *wasShutdown_ptr,
				bool *haveBackupLabel_ptr, bool *haveTblspcMap_ptr)
{
	XLogPageReadPrivate *private;
	struct stat st;
	bool		wasShutdown;
	XLogRecord *record;
	DBState		dbstate_at_startup;
	bool		haveTblspcMap = false;
	bool		haveBackupLabel = false;
	CheckPoint	checkPoint;
	bool		backupFromStandby = false;

	dbstate_at_startup = ControlFile->state;

	/*
	 * Initialize on the assumption we want to recover to the latest timeline
	 * that's active according to pg_control.
	 */
	if (ControlFile->minRecoveryPointTLI >
		ControlFile->checkPointCopy.ThisTimeLineID)
		recoveryTargetTLI = ControlFile->minRecoveryPointTLI;
	else
		recoveryTargetTLI = ControlFile->checkPointCopy.ThisTimeLineID;

	/*
	 * Check for signal files, and if so set up state for offline recovery
	 */
	readRecoverySignalFile();
	validateRecoveryParameters();

	/*
	 * Take ownership of the wakeup latch if we're going to sleep during
	 * recovery, if required.
	 */
	if (ArchiveRecoveryRequested)
		OwnLatch(&XLogRecoveryCtl->recoveryWakeupLatch);

	/*
	 * Set the WAL reading processor now, as it will be needed when reading
	 * the checkpoint record required (backup_label or not).
	 */
	private = palloc0_object(XLogPageReadPrivate);
	xlogreader =
		XLogReaderAllocate(wal_segment_size, NULL,
						   XL_ROUTINE(.page_read = &XLogPageRead,
									  .segment_open = NULL,
									  .segment_close = wal_segment_close),
						   private);
	if (!xlogreader)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of memory"),
				 errdetail("Failed while allocating a WAL reading processor.")));
	xlogreader->system_identifier = ControlFile->system_identifier;

	/*
	 * Set the WAL decode buffer size.  This limits how far ahead we can read
	 * in the WAL.
	 */
	XLogReaderSetDecodeBuffer(xlogreader, NULL, wal_decode_buffer_size);

	/* Create a WAL prefetcher. */
	xlogprefetcher = XLogPrefetcherAllocate(xlogreader);

	/*
	 * Allocate two page buffers dedicated to WAL consistency checks.  We do
	 * it this way, rather than just making static arrays, for two reasons:
	 * (1) no need to waste the storage in most instantiations of the backend;
	 * (2) a static char array isn't guaranteed to have any particular
	 * alignment, whereas palloc() will provide MAXALIGN'd storage.
	 */
	replay_image_masked = (char *) palloc(BLCKSZ);
	primary_image_masked = (char *) palloc(BLCKSZ);

	/*
	 * Read the backup_label file.  We want to run this part of the recovery
	 * process after checking for signal files and after performing validation
	 * of the recovery parameters.
	 */
	if (read_backup_label(&CheckPointLoc, &CheckPointTLI, &backupEndRequired,
						  &backupFromStandby))
	{
		List	   *tablespaces = NIL;

		/*
		 * Archive recovery was requested, and thanks to the backup label
		 * file, we know how far we need to replay to reach consistency. Enter
		 * archive recovery directly.
		 */
		InArchiveRecovery = true;
		if (StandbyModeRequested)
			EnableStandbyMode();

		/*
		 * Omitting backup_label when creating a new replica, PITR node etc.
		 * unfortunately is a common cause of corruption.  Logging that
		 * backup_label was used makes it a bit easier to exclude that as the
		 * cause of observed corruption.
		 *
		 * Do so before we try to read the checkpoint record (which can fail),
		 * as otherwise it can be hard to understand why a checkpoint other
		 * than ControlFile->checkPoint is used.
		 */
		ereport(LOG,
				errmsg("starting backup recovery with redo LSN %X/%08X, checkpoint LSN %X/%08X, on timeline ID %u",
					   LSN_FORMAT_ARGS(RedoStartLSN),
					   LSN_FORMAT_ARGS(CheckPointLoc),
					   CheckPointTLI));

		/*
		 * When a backup_label file is present, we want to roll forward from
		 * the checkpoint it identifies, rather than using pg_control.
		 */
		record = ReadCheckpointRecord(xlogprefetcher, CheckPointLoc,
									  CheckPointTLI);
		if (record != NULL)
		{
			memcpy(&checkPoint, XLogRecGetData(xlogreader), sizeof(CheckPoint));
			wasShutdown = ((record->xl_info & ~XLR_INFO_MASK) == XLOG_CHECKPOINT_SHUTDOWN);
			ereport(DEBUG1,
					errmsg_internal("checkpoint record is at %X/%08X",
									LSN_FORMAT_ARGS(CheckPointLoc)));
			InRecovery = true;	/* force recovery even if SHUTDOWNED */

			/*
			 * Make sure that REDO location exists. This may not be the case
			 * if there was a crash during an online backup, which left a
			 * backup_label around that references a WAL segment that's
			 * already been archived.
			 */
			if (checkPoint.redo < CheckPointLoc)
			{
				XLogPrefetcherBeginRead(xlogprefetcher, checkPoint.redo);
				if (!ReadRecord(xlogprefetcher, LOG, false,
								checkPoint.ThisTimeLineID))
					ereport(FATAL,
							errmsg("could not find redo location %X/%08X referenced by checkpoint record at %X/%08X",
								   LSN_FORMAT_ARGS(checkPoint.redo), LSN_FORMAT_ARGS(CheckPointLoc)),
							errhint("If you are restoring from a backup, touch \"%s/recovery.signal\" or \"%s/standby.signal\" and add required recovery options.\n"
									"If you are not restoring from a backup, try removing the file \"%s/backup_label\".\n"
									"Be careful: removing \"%s/backup_label\" will result in a corrupt cluster if restoring from a backup.",
									DataDir, DataDir, DataDir, DataDir));
			}
		}
		else
		{
			ereport(FATAL,
					errmsg("could not locate required checkpoint record at %X/%08X",
						   LSN_FORMAT_ARGS(CheckPointLoc)),
					errhint("If you are restoring from a backup, touch \"%s/recovery.signal\" or \"%s/standby.signal\" and add required recovery options.\n"
							"If you are not restoring from a backup, try removing the file \"%s/backup_label\".\n"
							"Be careful: removing \"%s/backup_label\" will result in a corrupt cluster if restoring from a backup.",
							DataDir, DataDir, DataDir, DataDir));
			wasShutdown = false;	/* keep compiler quiet */
		}

		/* Read the tablespace_map file if present and create symlinks. */
		if (read_tablespace_map(&tablespaces))
		{
			ListCell   *lc;

			foreach(lc, tablespaces)
			{
				tablespaceinfo *ti = lfirst(lc);
				char	   *linkloc;

				linkloc = psprintf("%s/%u", PG_TBLSPC_DIR, ti->oid);

				/*
				 * Remove the existing symlink if any and Create the symlink
				 * under PGDATA.
				 */
				remove_tablespace_symlink(linkloc);

				if (symlink(ti->path, linkloc) < 0)
					ereport(ERROR,
							(errcode_for_file_access(),
							 errmsg("could not create symbolic link \"%s\": %m",
									linkloc)));

				pfree(ti->path);
				pfree(ti);
			}

			/* tell the caller to delete it later */
			haveTblspcMap = true;
		}

		/* tell the caller to delete it later */
		haveBackupLabel = true;
	}
	else
	{
		/* No backup_label file has been found if we are here. */

		/*
		 * If tablespace_map file is present without backup_label file, there
		 * is no use of such file.  There is no harm in retaining it, but it
		 * is better to get rid of the map file so that we don't have any
		 * redundant file in data directory and it will avoid any sort of
		 * confusion.  It seems prudent though to just rename the file out of
		 * the way rather than delete it completely, also we ignore any error
		 * that occurs in rename operation as even if map file is present
		 * without backup_label file, it is harmless.
		 */
		if (stat(TABLESPACE_MAP, &st) == 0)
		{
			unlink(TABLESPACE_MAP_OLD);
			if (durable_rename(TABLESPACE_MAP, TABLESPACE_MAP_OLD, DEBUG1) == 0)
				ereport(LOG,
						(errmsg("ignoring file \"%s\" because no file \"%s\" exists",
								TABLESPACE_MAP, BACKUP_LABEL_FILE),
						 errdetail("File \"%s\" was renamed to \"%s\".",
								   TABLESPACE_MAP, TABLESPACE_MAP_OLD)));
			else
				ereport(LOG,
						(errmsg("ignoring file \"%s\" because no file \"%s\" exists",
								TABLESPACE_MAP, BACKUP_LABEL_FILE),
						 errdetail("Could not rename file \"%s\" to \"%s\": %m.",
								   TABLESPACE_MAP, TABLESPACE_MAP_OLD)));
		}

		/*
		 * It's possible that archive recovery was requested, but we don't
		 * know how far we need to replay the WAL before we reach consistency.
		 * This can happen for example if a base backup is taken from a
		 * running server using an atomic filesystem snapshot, without calling
		 * pg_backup_start/stop. Or if you just kill a running primary server
		 * and put it into archive recovery by creating a recovery signal
		 * file.
		 *
		 * Our strategy in that case is to perform crash recovery first,
		 * replaying all the WAL present in pg_wal, and only enter archive
		 * recovery after that.
		 *
		 * But usually we already know how far we need to replay the WAL (up
		 * to minRecoveryPoint, up to backupEndPoint, or until we see an
		 * end-of-backup record), and we can enter archive recovery directly.
		 */
		if (ArchiveRecoveryRequested &&
			(XLogRecPtrIsValid(ControlFile->minRecoveryPoint) ||
			 ControlFile->backupEndRequired ||
			 XLogRecPtrIsValid(ControlFile->backupEndPoint) ||
			 ControlFile->state == DB_SHUTDOWNED))
		{
			InArchiveRecovery = true;
			if (StandbyModeRequested)
				EnableStandbyMode();
		}

		/*
		 * For the same reason as when starting up with backup_label present,
		 * emit a log message when we continue initializing from a base
		 * backup.
		 */
		if (XLogRecPtrIsValid(ControlFile->backupStartPoint))
			ereport(LOG,
					errmsg("restarting backup recovery with redo LSN %X/%08X",
						   LSN_FORMAT_ARGS(ControlFile->backupStartPoint)));

		/* Get the last valid checkpoint record. */
		CheckPointLoc = ControlFile->checkPoint;
		CheckPointTLI = ControlFile->checkPointCopy.ThisTimeLineID;
		RedoStartLSN = ControlFile->checkPointCopy.redo;
		RedoStartTLI = ControlFile->checkPointCopy.ThisTimeLineID;
		record = ReadCheckpointRecord(xlogprefetcher, CheckPointLoc,
									  CheckPointTLI);
		if (record != NULL)
		{
			ereport(DEBUG1,
					errmsg_internal("checkpoint record is at %X/%08X",
									LSN_FORMAT_ARGS(CheckPointLoc)));
		}
		else
		{
			/*
			 * We used to attempt to go back to a secondary checkpoint record
			 * here, but only when not in standby mode. We now just fail if we
			 * can't read the last checkpoint because this allows us to
			 * simplify processing around checkpoints.
			 */
			ereport(FATAL,
					errmsg("could not locate a valid checkpoint record at %X/%08X",
						   LSN_FORMAT_ARGS(CheckPointLoc)));
		}
		memcpy(&checkPoint, XLogRecGetData(xlogreader), sizeof(CheckPoint));
		wasShutdown = ((record->xl_info & ~XLR_INFO_MASK) == XLOG_CHECKPOINT_SHUTDOWN);

		/* Make sure that REDO location exists. */
		if (checkPoint.redo < CheckPointLoc)
		{
			XLogPrefetcherBeginRead(xlogprefetcher, checkPoint.redo);
			if (!ReadRecord(xlogprefetcher, LOG, false, checkPoint.ThisTimeLineID))
				ereport(FATAL,
						errmsg("could not find redo location %X/%08X referenced by checkpoint record at %X/%08X",
							   LSN_FORMAT_ARGS(checkPoint.redo), LSN_FORMAT_ARGS(CheckPointLoc)));
		}
	}

	if (ArchiveRecoveryRequested)
	{
		if (StandbyModeRequested)
			ereport(LOG,
					(errmsg("entering standby mode")));
		else if (recoveryTarget == RECOVERY_TARGET_XID)
			ereport(LOG,
					(errmsg("starting point-in-time recovery to XID %u",
							recoveryTargetXid)));
		else if (recoveryTarget == RECOVERY_TARGET_TIME)
			ereport(LOG,
					(errmsg("starting point-in-time recovery to %s",
							timestamptz_to_str(recoveryTargetTime))));
		else if (recoveryTarget == RECOVERY_TARGET_NAME)
			ereport(LOG,
					(errmsg("starting point-in-time recovery to \"%s\"",
							recoveryTargetName)));
		else if (recoveryTarget == RECOVERY_TARGET_LSN)
			ereport(LOG,
					errmsg("starting point-in-time recovery to WAL location (LSN) \"%X/%08X\"",
						   LSN_FORMAT_ARGS(recoveryTargetLSN)));
		else if (recoveryTarget == RECOVERY_TARGET_IMMEDIATE)
			ereport(LOG,
					(errmsg("starting point-in-time recovery to earliest consistent point")));
		else
			ereport(LOG,
					(errmsg("starting archive recovery")));
	}

	/*
	 * If the location of the checkpoint record is not on the expected
	 * timeline in the history of the requested timeline, we cannot proceed:
	 * the backup is not part of the history of the requested timeline.
	 */
	Assert(expectedTLEs);		/* was initialized by reading checkpoint
								 * record */
	if (tliOfPointInHistory(CheckPointLoc, expectedTLEs) !=
		CheckPointTLI)
	{
		XLogRecPtr	switchpoint;

		/*
		 * tliSwitchPoint will throw an error if the checkpoint's timeline is
		 * not in expectedTLEs at all.
		 */
		switchpoint = tliSwitchPoint(CheckPointTLI, expectedTLEs, NULL);
		ereport(FATAL,
				(errmsg("requested timeline %u is not a child of this server's history",
						recoveryTargetTLI),
		/* translator: %s is a backup_label file or a pg_control file */
				 errdetail("Latest checkpoint in file \"%s\" is at %X/%08X on timeline %u, but in the history of the requested timeline, the server forked off from that timeline at %X/%08X.",
						   haveBackupLabel ? "backup_label" : "pg_control",
						   LSN_FORMAT_ARGS(CheckPointLoc),
						   CheckPointTLI,
						   LSN_FORMAT_ARGS(switchpoint))));
	}

	/*
	 * The min recovery point should be part of the requested timeline's
	 * history, too.
	 */
	if (XLogRecPtrIsValid(ControlFile->minRecoveryPoint) &&
		tliOfPointInHistory(ControlFile->minRecoveryPoint - 1, expectedTLEs) !=
		ControlFile->minRecoveryPointTLI)
		ereport(FATAL,
				errmsg("requested timeline %u does not contain minimum recovery point %X/%08X on timeline %u",
					   recoveryTargetTLI,
					   LSN_FORMAT_ARGS(ControlFile->minRecoveryPoint),
					   ControlFile->minRecoveryPointTLI));

	ereport(DEBUG1,
			errmsg_internal("redo record is at %X/%08X; shutdown %s",
							LSN_FORMAT_ARGS(checkPoint.redo),
							wasShutdown ? "true" : "false"));
	ereport(DEBUG1,
			(errmsg_internal("next transaction ID: " UINT64_FORMAT "; next OID: %u",
							 U64FromFullTransactionId(checkPoint.nextXid),
							 checkPoint.nextOid)));
	ereport(DEBUG1,
			(errmsg_internal("next MultiXactId: %u; next MultiXactOffset: %" PRIu64,
							 checkPoint.nextMulti, checkPoint.nextMultiOffset)));
	ereport(DEBUG1,
			(errmsg_internal("oldest unfrozen transaction ID: %u, in database %u",
							 checkPoint.oldestXid, checkPoint.oldestXidDB)));
	ereport(DEBUG1,
			(errmsg_internal("oldest MultiXactId: %u, in database %u",
							 checkPoint.oldestMulti, checkPoint.oldestMultiDB)));
	ereport(DEBUG1,
			(errmsg_internal("commit timestamp Xid oldest/newest: %u/%u",
							 checkPoint.oldestCommitTsXid,
							 checkPoint.newestCommitTsXid)));
	if (!TransactionIdIsNormal(XidFromFullTransactionId(checkPoint.nextXid)))
		ereport(PANIC,
				(errmsg("invalid next transaction ID")));

	/* sanity check */
	if (checkPoint.redo > CheckPointLoc)
		ereport(PANIC,
				(errmsg("invalid redo in checkpoint record")));

	/*
	 * Check whether we need to force recovery from WAL.  If it appears to
	 * have been a clean shutdown and we did not have a recovery signal file,
	 * then assume no recovery needed.
	 */
	if (checkPoint.redo < CheckPointLoc)
	{
		if (wasShutdown)
			ereport(PANIC,
					(errmsg("invalid redo record in shutdown checkpoint")));
		InRecovery = true;
	}
	else if (ControlFile->state != DB_SHUTDOWNED)
		InRecovery = true;
	else if (ArchiveRecoveryRequested)
	{
		/* force recovery due to presence of recovery signal file */
		InRecovery = true;
	}

	/*
	 * If recovery is needed, update our in-memory copy of pg_control to show
	 * that we are recovering and to show the selected checkpoint as the place
	 * we are starting from. We also mark pg_control with any minimum recovery
	 * stop point obtained from a backup history file.
	 *
	 * We don't write the changes to disk yet, though. Only do that after
	 * initializing various subsystems.
	 */
	if (InRecovery)
	{
		if (InArchiveRecovery)
		{
			ControlFile->state = DB_IN_ARCHIVE_RECOVERY;
		}
		else
		{
			ereport(LOG,
					(errmsg("database system was not properly shut down; "
							"automatic recovery in progress")));
			if (recoveryTargetTLI > ControlFile->checkPointCopy.ThisTimeLineID)
				ereport(LOG,
						(errmsg("crash recovery starts in timeline %u "
								"and has target timeline %u",
								ControlFile->checkPointCopy.ThisTimeLineID,
								recoveryTargetTLI)));
			ControlFile->state = DB_IN_CRASH_RECOVERY;
		}
		ControlFile->checkPoint = CheckPointLoc;
		ControlFile->checkPointCopy = checkPoint;
		if (InArchiveRecovery)
		{
			/* initialize minRecoveryPoint if not set yet */
			if (ControlFile->minRecoveryPoint < checkPoint.redo)
			{
				ControlFile->minRecoveryPoint = checkPoint.redo;
				ControlFile->minRecoveryPointTLI = checkPoint.ThisTimeLineID;
			}
		}

		/*
		 * Set backupStartPoint if we're starting recovery from a base backup.
		 *
		 * Also set backupEndPoint and use minRecoveryPoint as the backup end
		 * location if we're starting recovery from a base backup which was
		 * taken from a standby. In this case, the database system status in
		 * pg_control must indicate that the database was already in recovery.
		 * Usually that will be DB_IN_ARCHIVE_RECOVERY but also can be
		 * DB_SHUTDOWNED_IN_RECOVERY if recovery previously was interrupted
		 * before reaching this point; e.g. because restore_command or
		 * primary_conninfo were faulty.
		 *
		 * Any other state indicates that the backup somehow became corrupted
		 * and we can't sensibly continue with recovery.
		 */
		if (haveBackupLabel)
		{
			ControlFile->backupStartPoint = checkPoint.redo;
			ControlFile->backupEndRequired = backupEndRequired;

			if (backupFromStandby)
			{
				if (dbstate_at_startup != DB_IN_ARCHIVE_RECOVERY &&
					dbstate_at_startup != DB_SHUTDOWNED_IN_RECOVERY)
					ereport(FATAL,
							(errmsg("backup_label contains data inconsistent with control file"),
							 errhint("This means that the backup is corrupted and you will "
									 "have to use another backup for recovery.")));
				ControlFile->backupEndPoint = ControlFile->minRecoveryPoint;
			}
		}
	}

	/* remember these, so that we know when we have reached consistency */
	backupStartPoint = ControlFile->backupStartPoint;
	backupEndRequired = ControlFile->backupEndRequired;
	backupEndPoint = ControlFile->backupEndPoint;
	if (InArchiveRecovery)
	{
		minRecoveryPoint = ControlFile->minRecoveryPoint;
		minRecoveryPointTLI = ControlFile->minRecoveryPointTLI;
	}
	else
	{
		minRecoveryPoint = InvalidXLogRecPtr;
		minRecoveryPointTLI = 0;
	}

	/*
	 * Start recovery assuming that the final record isn't lost.
	 */
	abortedRecPtr = InvalidXLogRecPtr;
	missingContrecPtr = InvalidXLogRecPtr;

	*wasShutdown_ptr = wasShutdown;
	*haveBackupLabel_ptr = haveBackupLabel;
	*haveTblspcMap_ptr = haveTblspcMap;
}

/*
 * See if there are any recovery signal files and if so, set state for
 * recovery.
 *
 * See if there is a recovery command file (recovery.conf), and if so
 * throw an ERROR since as of PG12 we no longer recognize that.
 */
/*
 * 中文注释：
 * 检查数据目录中的恢复信号文件，设置 ArchiveRecoveryRequested/StandbyModeRequested。
 *
 * 规则：
 *   - 存在 recovery.conf 直接 FATAL（PG12 起不再支持该接口）；
 *   - 删除遗留的 recovery.conf.done；
 *   - standby.signal 优先于 recovery.signal；前者同时启用归档恢复和备库模式，
 *     后者只启用归档恢复（PITR）；
 *   - 信号文件代表服务器状态，找到后尽量 fsync（失败不致命）；
 *   - 单用户模式不支持备库模式，因为需要 walreceiver 等辅助进程。
 * 两个信号文件都不存在时不进入归档恢复，后续按崩溃恢复处理。
 */
static void
readRecoverySignalFile(void)
{
	struct stat stat_buf;

	if (IsBootstrapProcessingMode())
		return;

	/*
	 * Check for old recovery API file: recovery.conf
	 */
	if (stat(RECOVERY_COMMAND_FILE, &stat_buf) == 0)
		ereport(FATAL,
				(errcode_for_file_access(),
				 errmsg("using recovery command file \"%s\" is not supported",
						RECOVERY_COMMAND_FILE)));

	/*
	 * Remove unused .done file, if present. Ignore if absent.
	 */
	unlink(RECOVERY_COMMAND_DONE);

	/*
	 * Check for recovery signal files and if found, fsync them since they
	 * represent server state information.  We don't sweat too much about the
	 * possibility of fsync failure, however.
	 */
	if (stat(STANDBY_SIGNAL_FILE, &stat_buf) == 0)
	{
		int			fd;

		fd = BasicOpenFilePerm(STANDBY_SIGNAL_FILE, O_RDWR | PG_BINARY,
							   S_IRUSR | S_IWUSR);
		if (fd >= 0)
		{
			(void) pg_fsync(fd);
			close(fd);
		}
		standby_signal_file_found = true;
	}

	if (stat(RECOVERY_SIGNAL_FILE, &stat_buf) == 0)
	{
		int			fd;

		fd = BasicOpenFilePerm(RECOVERY_SIGNAL_FILE, O_RDWR | PG_BINARY,
							   S_IRUSR | S_IWUSR);
		if (fd >= 0)
		{
			(void) pg_fsync(fd);
			close(fd);
		}
		recovery_signal_file_found = true;
	}

	/*
	 * If both signal files are present, standby signal file takes precedence.
	 * If neither is present then we won't enter archive recovery.
	 */
	StandbyModeRequested = false;
	ArchiveRecoveryRequested = false;
	if (standby_signal_file_found)
	{
		StandbyModeRequested = true;
		ArchiveRecoveryRequested = true;
	}
	else if (recovery_signal_file_found)
	{
		StandbyModeRequested = false;
		ArchiveRecoveryRequested = true;
	}
	else
		return;

	/*
	 * We don't support standby mode in standalone backends; that requires
	 * other processes such as the WAL receiver to be alive.
	 */
	if (StandbyModeRequested && !IsUnderPostmaster)
		ereport(FATAL,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("standby mode is not supported by single-user servers")));
}

/*
 * 中文注释：
 * 校验并补全恢复相关 GUC，确定最终恢复目标和目标时间线。
 *
 * 即使没有请求归档恢复，也先调用 DetermineRecoveryTargetType 拒绝同时设置多个
 * recovery_target*（这是配置错误）。归档恢复时：
 *   - 备库模式要求至少配置 primary_conninfo 或 restore_command，否则只警告，
 *     因为还可能直接从 pg_wal 轮询；
 *   - 非备库的 PITR 必须配置 restore_command；
 *   - 若 recovery_target_action=pause 但 hot_standby=off，则降级为 shutdown，
 *     避免暂停后无人能连接执行 resume；
 *   - 对 recovery_target_time 做最终解析：check hook 阶段只验证语法，此时时区
 *     等 GUC 已确定，才把字符串转成 TimestampTz；
 *   - 解析 recovery_target_timeline：numeric 要求时间线存在（1 号除外），latest
 *     调用 findNewestTimeLine 求最新，current 则沿用 pg_control 的时间线。
 */
static void
validateRecoveryParameters(void)
{
	/* Reject conflicting targets even when recovery was not requested */
	recoveryTarget = DetermineRecoveryTargetType();

	if (!ArchiveRecoveryRequested)
		return;

	/*
	 * Check for compulsory parameters
	 */
	if (StandbyModeRequested)
	{
		if ((PrimaryConnInfo == NULL || strcmp(PrimaryConnInfo, "") == 0) &&
			(recoveryRestoreCommand == NULL || strcmp(recoveryRestoreCommand, "") == 0))
			ereport(WARNING,
					(errmsg("specified neither \"primary_conninfo\" nor \"restore_command\""),
					 errhint("The database server will regularly poll the pg_wal subdirectory to check for files placed there.")));
	}
	else
	{
		if (recoveryRestoreCommand == NULL ||
			strcmp(recoveryRestoreCommand, "") == 0)
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("must specify \"restore_command\" when standby mode is not enabled")));
	}

	/*
	 * Override any inconsistent requests. Note that this is a change of
	 * behaviour in 9.5; prior to this we simply ignored a request to pause if
	 * hot_standby = off, which was surprising behaviour.
	 */
	if (recoveryTargetAction == RECOVERY_TARGET_ACTION_PAUSE &&
		!EnableHotStandby)
		recoveryTargetAction = RECOVERY_TARGET_ACTION_SHUTDOWN;

	/*
	 * Final parsing of recovery_target_time string; see also
	 * check_recovery_target_time().
	 */
	if (recoveryTarget == RECOVERY_TARGET_TIME)
	{
		recoveryTargetTime = DatumGetTimestampTz(DirectFunctionCall3(timestamptz_in,
																	 CStringGetDatum(recovery_target_time_string),
																	 ObjectIdGetDatum(InvalidOid),
																	 Int32GetDatum(-1)));
	}

	/*
	 * If user specified recovery_target_timeline, validate it or compute the
	 * "latest" value.  We can't do this until after we've gotten the restore
	 * command and set InArchiveRecovery, because we need to fetch timeline
	 * history files from the archive.
	 */
	if (recoveryTargetTimeLineGoal == RECOVERY_TARGET_TIMELINE_NUMERIC)
	{
		TimeLineID	rtli = recoveryTargetTLIRequested;

		/* Timeline 1 does not have a history file, all else should */
		if (rtli != 1 && !existsTimeLineHistory(rtli))
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("recovery target timeline %u does not exist",
							rtli)));
		recoveryTargetTLI = rtli;
	}
	else if (recoveryTargetTimeLineGoal == RECOVERY_TARGET_TIMELINE_LATEST)
	{
		/* We start the "latest" search from pg_control's timeline */
		recoveryTargetTLI = findNewestTimeLine(recoveryTargetTLI);
	}
	else
	{
		/*
		 * else we just use the recoveryTargetTLI as already read from
		 * ControlFile
		 */
		Assert(recoveryTargetTimeLineGoal == RECOVERY_TARGET_TIMELINE_CONTROLFILE);
	}
}

/*
 * read_backup_label: check to see if a backup_label file is present
 *
 * If we see a backup_label during recovery, we assume that we are recovering
 * from a backup dump file, and we therefore roll forward from the checkpoint
 * identified by the label file, NOT what pg_control says.  This avoids the
 * problem that pg_control might have been archived one or more checkpoints
 * later than the start of the dump, and so if we rely on it as the start
 * point, we will fail to restore a consistent database state.
 *
 * Returns true if a backup_label was found (and fills the checkpoint
 * location and TLI into *checkPointLoc and *backupLabelTLI, respectively);
 * returns false if not. If this backup_label came from a streamed backup,
 * *backupEndRequired is set to true. If this backup_label was created during
 * recovery, *backupFromStandby is set to true.
 *
 * Also sets the global variables RedoStartLSN and RedoStartTLI with the LSN
 * and TLI read from the backup file.
 */
/*
 * 中文注释：
 * 读取并解析备份标签文件 backup_label。
 *
 * 存在 backup_label 说明数据目录来自基础备份，恢复必须从标签中记录的 checkpoint
 * 开始，而不能相信 pg_control（后者可能是备份结束后更新的检查点）。函数解析：
 *   - START WAL LOCATION：设置 RedoStartLSN/RedoStartTLI（备份开始位置）；
 *   - CHECKPOINT LOCATION：返回 checkpoint 位置和其 TLI；
 *   - BACKUP METHOD：streamed 表示需要一直重放到备份结束记录
 *     （backupEndRequired=true）；
 *   - BACKUP FROM：standby 表示备份取自备库，后续要校验控制文件状态；
 *   - START TIME/LABEL/START TIMELINE：仅用于日志和一致性检查；
 *   - INCREMENTAL FROM LSN：说明这是增量备份，必须先用 pg_combinebackup 合并。
 * 文件不存在返回 false；格式错误或读取失败直接 FATAL。
 */
static bool
read_backup_label(XLogRecPtr *checkPointLoc, TimeLineID *backupLabelTLI,
				  bool *backupEndRequired, bool *backupFromStandby)
{
	char		startxlogfilename[MAXFNAMELEN];
	TimeLineID	tli_from_walseg,
				tli_from_file;
	FILE	   *lfp;
	char		ch;
	char		backuptype[20];
	char		backupfrom[20];
	char		backuplabel[MAXPGPATH];
	char		backuptime[128];
	uint32		hi,
				lo;

	/* suppress possible uninitialized-variable warnings */
	*checkPointLoc = InvalidXLogRecPtr;
	*backupLabelTLI = 0;
	*backupEndRequired = false;
	*backupFromStandby = false;

	/*
	 * See if label file is present
	 */
	lfp = AllocateFile(BACKUP_LABEL_FILE, "r");
	if (!lfp)
	{
		if (errno != ENOENT)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not read file \"%s\": %m",
							BACKUP_LABEL_FILE)));
		return false;			/* it's not there, all is fine */
	}

	/*
	 * Read and parse the START WAL LOCATION and CHECKPOINT lines (this code
	 * is pretty crude, but we are not expecting any variability in the file
	 * format).
	 */
	if (fscanf(lfp, "START WAL LOCATION: %X/%08X (file %08X%16s)%c",
			   &hi, &lo, &tli_from_walseg, startxlogfilename, &ch) != 5 || ch != '\n')
		ereport(FATAL,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("invalid data in file \"%s\"", BACKUP_LABEL_FILE)));
	RedoStartLSN = ((uint64) hi) << 32 | lo;
	RedoStartTLI = tli_from_walseg;
	if (fscanf(lfp, "CHECKPOINT LOCATION: %X/%08X%c",
			   &hi, &lo, &ch) != 3 || ch != '\n')
		ereport(FATAL,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("invalid data in file \"%s\"", BACKUP_LABEL_FILE)));
	*checkPointLoc = ((uint64) hi) << 32 | lo;
	*backupLabelTLI = tli_from_walseg;

	/*
	 * BACKUP METHOD lets us know if this was a typical backup ("streamed",
	 * which could mean either pg_basebackup or the pg_backup_start/stop
	 * method was used) or if this label came from somewhere else (the only
	 * other option today being from pg_rewind).  If this was a streamed
	 * backup then we know that we need to play through until we get to the
	 * end of the WAL which was generated during the backup (at which point we
	 * will have reached consistency and backupEndRequired will be reset to be
	 * false).
	 */
	if (fscanf(lfp, "BACKUP METHOD: %19s\n", backuptype) == 1)
	{
		if (strcmp(backuptype, "streamed") == 0)
			*backupEndRequired = true;
	}

	/*
	 * BACKUP FROM lets us know if this was from a primary or a standby.  If
	 * it was from a standby, we'll double-check that the control file state
	 * matches that of a standby.
	 */
	if (fscanf(lfp, "BACKUP FROM: %19s\n", backupfrom) == 1)
	{
		if (strcmp(backupfrom, "standby") == 0)
			*backupFromStandby = true;
	}

	/*
	 * Parse START TIME and LABEL. Those are not mandatory fields for recovery
	 * but checking for their presence is useful for debugging and the next
	 * sanity checks. Cope also with the fact that the result buffers have a
	 * pre-allocated size, hence if the backup_label file has been generated
	 * with strings longer than the maximum assumed here an incorrect parsing
	 * happens. That's fine as only minor consistency checks are done
	 * afterwards.
	 */
	if (fscanf(lfp, "START TIME: %127[^\n]\n", backuptime) == 1)
		ereport(DEBUG1,
				(errmsg_internal("backup time %s in file \"%s\"",
								 backuptime, BACKUP_LABEL_FILE)));

	if (fscanf(lfp, "LABEL: %1023[^\n]\n", backuplabel) == 1)
		ereport(DEBUG1,
				(errmsg_internal("backup label %s in file \"%s\"",
								 backuplabel, BACKUP_LABEL_FILE)));

	/*
	 * START TIMELINE is new as of 11. Its parsing is not mandatory, still use
	 * it as a sanity check if present.
	 */
	if (fscanf(lfp, "START TIMELINE: %u\n", &tli_from_file) == 1)
	{
		if (tli_from_walseg != tli_from_file)
			ereport(FATAL,
					(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
					 errmsg("invalid data in file \"%s\"", BACKUP_LABEL_FILE),
					 errdetail("Timeline ID parsed is %u, but expected %u.",
							   tli_from_file, tli_from_walseg)));

		ereport(DEBUG1,
				(errmsg_internal("backup timeline %u in file \"%s\"",
								 tli_from_file, BACKUP_LABEL_FILE)));
	}

	if (fscanf(lfp, "INCREMENTAL FROM LSN: %X/%08X\n", &hi, &lo) > 0)
		ereport(FATAL,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("this is an incremental backup, not a data directory"),
				 errhint("Use pg_combinebackup to reconstruct a valid data directory.")));

	if (ferror(lfp) || FreeFile(lfp))
		ereport(FATAL,
				(errcode_for_file_access(),
				 errmsg("could not read file \"%s\": %m",
						BACKUP_LABEL_FILE)));

	return true;
}

/*
 * read_tablespace_map: check to see if a tablespace_map file is present
 *
 * If we see a tablespace_map file during recovery, we assume that we are
 * recovering from a backup dump file, and we therefore need to create symlinks
 * as per the information present in tablespace_map file.
 *
 * Returns true if a tablespace_map file was found (and fills *tablespaces
 * with a tablespaceinfo struct for each tablespace listed in the file);
 * returns false if not.
 */
/*
 * 中文注释：
 * 读取 tablespace_map 文件，返回其中每个表空间的 OID 和原始路径。
 *
 * 基础备份可能把表空间放在与原始集簇不同的位置，恢复时需要按该文件重建
 * pg_tblspc/<oid> 符号链接。每行格式为 "<oid> <path>"，路径中的反斜杠用于转义
 * 换行和反斜杠，函数边读边反转义。路径可以以空格开头，因此只按第一个空格分隔
 * OID 与路径。格式错误、OID 非法、最后一行未终止或读取失败都 FATAL；文件不存在
 * 返回 false。
 */
static bool
read_tablespace_map(List **tablespaces)
{
	tablespaceinfo *ti;
	FILE	   *lfp;
	char		str[MAXPGPATH];
	int			ch,
				i,
				n;
	bool		was_backslash;

	/*
	 * See if tablespace_map file is present
	 */
	lfp = AllocateFile(TABLESPACE_MAP, "r");
	if (!lfp)
	{
		if (errno != ENOENT)
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not read file \"%s\": %m",
							TABLESPACE_MAP)));
		return false;			/* it's not there, all is fine */
	}

	/*
	 * Read and parse the link name and path lines from tablespace_map file
	 * (this code is pretty crude, but we are not expecting any variability in
	 * the file format).  De-escape any backslashes that were inserted.
	 */
	i = 0;
	was_backslash = false;
	while ((ch = fgetc(lfp)) != EOF)
	{
		if (!was_backslash && (ch == '\n' || ch == '\r'))
		{
			char	   *endp;

			if (i == 0)
				continue;		/* \r immediately followed by \n */

			/*
			 * The de-escaped line should contain an OID followed by exactly
			 * one space followed by a path.  The path might start with
			 * spaces, so don't be too liberal about parsing.
			 */
			str[i] = '\0';
			n = 0;
			while (str[n] && str[n] != ' ')
				n++;
			if (n < 1 || n >= i - 1)
				ereport(FATAL,
						(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
						 errmsg("invalid data in file \"%s\"", TABLESPACE_MAP)));
			str[n++] = '\0';

			ti = palloc0_object(tablespaceinfo);
			errno = 0;
			ti->oid = strtoul(str, &endp, 10);
			if (*endp != '\0' || errno == EINVAL || errno == ERANGE)
				ereport(FATAL,
						(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
						 errmsg("invalid data in file \"%s\"", TABLESPACE_MAP)));
			ti->path = pstrdup(str + n);
			*tablespaces = lappend(*tablespaces, ti);

			i = 0;
			continue;
		}
		else if (!was_backslash && ch == '\\')
			was_backslash = true;
		else
		{
			if (i < sizeof(str) - 1)
				str[i++] = ch;
			was_backslash = false;
		}
	}

	if (i != 0 || was_backslash)	/* last line not terminated? */
		ereport(FATAL,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("invalid data in file \"%s\"", TABLESPACE_MAP)));

	if (ferror(lfp) || FreeFile(lfp))
		ereport(FATAL,
				(errcode_for_file_access(),
				 errmsg("could not read file \"%s\": %m",
						TABLESPACE_MAP)));

	return true;
}

/*
 * Finish WAL recovery.
 *
 * This does not close the 'xlogreader' yet, because in some cases the caller
 * still wants to re-read the last checkpoint record by calling
 * ReadCheckpointRecord().
 *
 * Returns the position of the last valid or applied record, after which new
 * WAL should be appended, information about why recovery was ended, and some
 * other things. See the EndOfWalRecoveryInfo struct for details.
 */
/*
 * 中文注释：
 * 结束 WAL 恢复，计算新 WAL 的追加位置并返回恢复结果。
 *
 * 主要步骤：
 *   1. 关闭 walreceiver 和 slot sync worker，确保后续写 WAL 不会被流式接收覆盖；
 *      关闭后才可以退出 StandbyMode；
 *   2. 重新读取最后一条有效/已重放记录，得到精确的 endOfLog；若之前发现不完整的
 *      continuation record，abortedRecPtr/missingContrecPtr 会通过返回值交给调用者
 *      写 XLOG_OVERWRITE_CONTRECORD；
 *   3. 记录 endOfLog 所在 WAL 段文件名中的 TLI（时间线切换可能使它与记录名义上的
 *      TLI 不同）；
 *   4. 退出归档恢复，关闭仍打开的 WAL 文件；
 *   5. 若 endOfLog 位于页中间，把该页已有效的部分复制出来，供调用者初始化 WAL
 *      写缓冲；
 *   6. 生成时间线历史文件中的停止原因，填充 EndOfWalRecoveryInfo。
 * 本函数不关闭 xlogreader，因为调用者可能还要用 ReadCheckpointRecord 重读最后的
 * 检查点；真正的清理在 ShutdownWalRecovery。
 */
EndOfWalRecoveryInfo *
FinishWalRecovery(void)
{
	EndOfWalRecoveryInfo *result = palloc_object(EndOfWalRecoveryInfo);
	XLogRecPtr	lastRec;
	TimeLineID	lastRecTLI;
	XLogRecPtr	endOfLog;

	/*
	 * Kill WAL receiver, if it's still running, before we continue to write
	 * the startup checkpoint and aborted-contrecord records. It will trump
	 * over these records and subsequent ones if it's still alive when we
	 * start writing WAL.
	 */
	XLogShutdownWalRcv();

	/*
	 * Shutdown the slot sync worker to drop any temporary slots acquired by
	 * it and to prevent it from keep trying to fetch the failover slots.
	 *
	 * We do not update the 'synced' column in 'pg_replication_slots' system
	 * view from true to false here, as any failed update could leave 'synced'
	 * column false for some slots. This could cause issues during slot sync
	 * after restarting the server as a standby. While updating the 'synced'
	 * column after switching to the new timeline is an option, it does not
	 * simplify the handling for the 'synced' column. Therefore, we retain the
	 * 'synced' column as true after promotion as it may provide useful
	 * information about the slot origin.
	 */
	ShutDownSlotSync();

	/*
	 * We are now done reading the xlog from stream. Turn off streaming
	 * recovery to force fetching the files (which would be required at end of
	 * recovery, e.g., timeline history file) from archive or pg_wal.
	 *
	 * Note that standby mode must be turned off after killing WAL receiver,
	 * i.e., calling XLogShutdownWalRcv().
	 */
	Assert(!WalRcvStreaming());
	StandbyMode = false;

	/*
	 * Determine where to start writing WAL next.
	 *
	 * Re-fetch the last valid or last applied record, so we can identify the
	 * exact endpoint of what we consider the valid portion of WAL.  There may
	 * be an incomplete continuation record after that, in which case
	 * 'abortedRecPtr' and 'missingContrecPtr' are set and the caller will
	 * write a special OVERWRITE_CONTRECORD message to mark that the rest of
	 * it is intentionally missing.  See CreateOverwriteContrecordRecord().
	 *
	 * An important side-effect of this is to load the last page into
	 * xlogreader. The caller uses it to initialize the WAL for writing.
	 */
	if (!InRecovery)
	{
		lastRec = CheckPointLoc;
		lastRecTLI = CheckPointTLI;
	}
	else
	{
		lastRec = XLogRecoveryCtl->lastReplayedReadRecPtr;
		lastRecTLI = XLogRecoveryCtl->lastReplayedTLI;
	}
	XLogPrefetcherBeginRead(xlogprefetcher, lastRec);
	(void) ReadRecord(xlogprefetcher, PANIC, false, lastRecTLI);
	endOfLog = xlogreader->EndRecPtr;

	/*
	 * Remember the TLI in the filename of the XLOG segment containing the
	 * end-of-log.  It could be different from the timeline that endOfLog
	 * nominally belongs to, if there was a timeline switch in that segment,
	 * and we were reading the old WAL from a segment belonging to a higher
	 * timeline.
	 */
	result->endOfLogTLI = xlogreader->seg.ws_tli;

	if (ArchiveRecoveryRequested)
	{
		/*
		 * We are no longer in archive recovery state.
		 *
		 * We are now done reading the old WAL.  Turn off archive fetching if
		 * it was active.
		 */
		Assert(InArchiveRecovery);
		InArchiveRecovery = false;

		/*
		 * If the ending log segment is still open, close it (to avoid
		 * problems on Windows with trying to rename or delete an open file).
		 */
		if (readFile >= 0)
		{
			close(readFile);
			readFile = -1;
		}
	}

	/*
	 * Copy the last partial block to the caller, for initializing the WAL
	 * buffer for appending new WAL.
	 */
	if (endOfLog % XLOG_BLCKSZ != 0)
	{
		char	   *page;
		int			len;
		XLogRecPtr	pageBeginPtr;

		pageBeginPtr = endOfLog - (endOfLog % XLOG_BLCKSZ);
		Assert(readOff == XLogSegmentOffset(pageBeginPtr, wal_segment_size));

		/* Copy the valid part of the last block */
		len = endOfLog % XLOG_BLCKSZ;
		page = palloc(len);
		memcpy(page, xlogreader->readBuf, len);

		result->lastPageBeginPtr = pageBeginPtr;
		result->lastPage = page;
	}
	else
	{
		/* There is no partial block to copy. */
		result->lastPageBeginPtr = endOfLog;
		result->lastPage = NULL;
	}

	/*
	 * Create a comment for the history file to explain why and where timeline
	 * changed.
	 */
	result->recoveryStopReason = getRecoveryStopReason();

	result->lastRec = lastRec;
	result->lastRecTLI = lastRecTLI;
	result->endOfLog = endOfLog;

	result->abortedRecPtr = abortedRecPtr;
	result->missingContrecPtr = missingContrecPtr;

	result->standby_signal_file_found = standby_signal_file_found;
	result->recovery_signal_file_found = recovery_signal_file_found;

	return result;
}

/*
 * Clean up the WAL reader and leftovers from restoring WAL from archive
 */
/*
 * 中文注释：
 * 释放 WAL 恢复使用的 reader、prefetcher 和归档临时文件。
 *
 * 先输出最后一次 pg_stat_recovery_prefetch 统计，关闭可能仍打开的 WAL 段文件，
 * 释放 xlogreader 的 private_data 并调用 XLogReaderFree/XLogPrefetcherFree。
 * 归档恢复还会删除 pg_wal/RECOVERYXLOG（未完成的恢复段）和
 * pg_wal/RECOVERYHISTORY（临时时间线历史），最后 DisownLatch 释放恢复唤醒闩锁。
 * unlink 失败被忽略，因为这些只是临时文件。
 */
void
ShutdownWalRecovery(void)
{
	char		recoveryPath[MAXPGPATH];

	/* Final update of pg_stat_recovery_prefetch. */
	XLogPrefetcherComputeStats(xlogprefetcher);

	/* Shut down xlogreader */
	if (readFile >= 0)
	{
		close(readFile);
		readFile = -1;
	}
	pfree(xlogreader->private_data);
	XLogReaderFree(xlogreader);
	XLogPrefetcherFree(xlogprefetcher);

	if (ArchiveRecoveryRequested)
	{
		/*
		 * Since there might be a partial WAL segment named RECOVERYXLOG, get
		 * rid of it.
		 */
		snprintf(recoveryPath, MAXPGPATH, XLOGDIR "/RECOVERYXLOG");
		unlink(recoveryPath);	/* ignore any error */

		/* Get rid of any remaining recovered timeline-history file, too */
		snprintf(recoveryPath, MAXPGPATH, XLOGDIR "/RECOVERYHISTORY");
		unlink(recoveryPath);	/* ignore any error */
	}

	/*
	 * We don't need the latch anymore. It's not strictly necessary to disown
	 * it, but let's do it for the sake of tidiness.
	 */
	if (ArchiveRecoveryRequested)
		DisownLatch(&XLogRecoveryCtl->recoveryWakeupLatch);
}

/*
 * Perform WAL recovery.
 *
 * If the system was shut down cleanly, this is never called.
 */
void
/*
 * 中文注释：
 * 执行实际的 WAL 重放主循环。
 *
 * 调用前 InitWalRecovery 已确定 RedoStartLSN/CheckPointLoc，系统若为干净关闭则
 * 本函数不会被调用。流程：
 *   1. 在 info_lck 下初始化共享的 lastReplayed*/replayEnd* 进度变量，使其表示
 *      “REDO 位置之前”或检查点记录本身；
 *   2. 通知 postmaster 恢复已开始（以便启动归档进程），并调用
 *      CheckRecoveryConsistency 判断是否已可接受只读连接；
 *   3. 定位第一条要重放的记录：redo 指针早于 checkpoint 时先读到
 *      XLOG_CHECKPOINT_REDO 记录，否则读 checkpoint 之后的记录；
 *   4. 进入 do-while 主循环：处理中断、响应恢复暂停请求、检查 recovery target、
 *      执行 recovery_min_apply_delay 延迟、调用 ApplyWalRecord 重放、唤醒等待
 *      standby replay/write/flush LSN 的进程、检查 inclusive target、读取下一条；
 *   5. 达到目标后根据 recovery_target_action 选择 shutdown(exit 3)、pause 或
 *      promote；未达到一致性就停止会 FATAL；
 *   6. 调用 RmgrCleanup，输出 redo 结束统计和最后事务时间。
 * 若配置了恢复目标但 WAL 在到达前耗尽，归档恢复会 FATAL，提示恢复未完成。
 */
PerformWalRecovery(void)
{
	XLogRecord *record;
	bool		reachedRecoveryTarget = false;
	TimeLineID	replayTLI;

	/*
	 * Initialize shared variables for tracking progress of WAL replay, as if
	 * we had just replayed the record before the REDO location (or the
	 * checkpoint record itself, if it's a shutdown checkpoint).
	 */
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	if (RedoStartLSN < CheckPointLoc)
	{
		XLogRecoveryCtl->lastReplayedReadRecPtr = InvalidXLogRecPtr;
		XLogRecoveryCtl->lastReplayedEndRecPtr = RedoStartLSN;
		XLogRecoveryCtl->lastReplayedTLI = RedoStartTLI;
	}
	else
	{
		XLogRecoveryCtl->lastReplayedReadRecPtr = xlogreader->ReadRecPtr;
		XLogRecoveryCtl->lastReplayedEndRecPtr = xlogreader->EndRecPtr;
		XLogRecoveryCtl->lastReplayedTLI = CheckPointTLI;
	}
	XLogRecoveryCtl->replayEndRecPtr = XLogRecoveryCtl->lastReplayedEndRecPtr;
	XLogRecoveryCtl->replayEndTLI = XLogRecoveryCtl->lastReplayedTLI;
	XLogRecoveryCtl->recoveryLastXTime = 0;
	XLogRecoveryCtl->currentChunkStartTime = 0;
	XLogRecoveryCtl->recoveryPauseState = RECOVERY_NOT_PAUSED;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	/* Also ensure XLogReceiptTime has a sane value */
	XLogReceiptTime = GetCurrentTimestamp();

	/*
	 * Let postmaster know we've started redo now, so that it can launch the
	 * archiver if necessary.
	 */
	if (IsUnderPostmaster)
		SendPostmasterSignal(PMSIGNAL_RECOVERY_STARTED);

	/*
	 * Allow read-only connections immediately if we're consistent already.
	 */
	CheckRecoveryConsistency();

	/*
	 * Find the first record that logically follows the checkpoint --- it
	 * might physically precede it, though.
	 */
	if (RedoStartLSN < CheckPointLoc)
	{
		/* back up to find the record */
		replayTLI = RedoStartTLI;
		XLogPrefetcherBeginRead(xlogprefetcher, RedoStartLSN);
		record = ReadRecord(xlogprefetcher, PANIC, false, replayTLI);

		/*
		 * If a checkpoint record's redo pointer points back to an earlier
		 * LSN, the record at that LSN should be an XLOG_CHECKPOINT_REDO
		 * record.
		 */
		if (record->xl_rmid != RM_XLOG_ID ||
			(record->xl_info & ~XLR_INFO_MASK) != XLOG_CHECKPOINT_REDO)
			ereport(FATAL,
					errmsg("unexpected record type found at redo point %X/%08X",
						   LSN_FORMAT_ARGS(xlogreader->ReadRecPtr)));
	}
	else
	{
		/* just have to read next record after CheckPoint */
		Assert(xlogreader->ReadRecPtr == CheckPointLoc);
		replayTLI = CheckPointTLI;
		record = ReadRecord(xlogprefetcher, LOG, false, replayTLI);
	}

	if (record != NULL)
	{
		TimestampTz xtime;
		PGRUsage	ru0;

		pg_rusage_init(&ru0);

		InRedo = true;

		RmgrStartup();

		ereport(LOG,
				errmsg("redo starts at %X/%08X",
					   LSN_FORMAT_ARGS(xlogreader->ReadRecPtr)));

		/* Prepare to report progress of the redo phase. */
		if (!StandbyMode)
			begin_startup_progress_phase();

		/*
		 * main redo apply loop
		 */
		do
		{
			if (!StandbyMode)
				ereport_startup_progress("redo in progress, elapsed time: %ld.%02d s, current LSN: %X/%08X",
										 LSN_FORMAT_ARGS(xlogreader->ReadRecPtr));

#ifdef WAL_DEBUG
			if (XLOG_DEBUG)
			{
				StringInfoData buf;

				initStringInfo(&buf);
				appendStringInfo(&buf, "REDO @ %X/%08X; LSN %X/%08X: ",
								 LSN_FORMAT_ARGS(xlogreader->ReadRecPtr),
								 LSN_FORMAT_ARGS(xlogreader->EndRecPtr));
				xlog_outrec(&buf, xlogreader);
				appendStringInfoString(&buf, " - ");
				xlog_outdesc(&buf, xlogreader);
				elog(LOG, "%s", buf.data);
				pfree(buf.data);
			}
#endif

			/* Handle interrupt signals of startup process */
			ProcessStartupProcInterrupts();

			/*
			 * Pause WAL replay, if requested by a hot-standby session via
			 * SetRecoveryPause().
			 *
			 * Note that we intentionally don't take the info_lck spinlock
			 * here.  We might therefore read a slightly stale value of the
			 * recoveryPause flag, but it can't be very stale (no worse than
			 * the last spinlock we did acquire).  Since a pause request is a
			 * pretty asynchronous thing anyway, possibly responding to it one
			 * WAL record later than we otherwise would is a minor issue, so
			 * it doesn't seem worth adding another spinlock cycle to prevent
			 * that.
			 */
			if (((volatile XLogRecoveryCtlData *) XLogRecoveryCtl)->recoveryPauseState !=
				RECOVERY_NOT_PAUSED)
				recoveryPausesHere(false);

			/*
			 * Have we reached our recovery target?
			 */
			if (recoveryStopsBefore(xlogreader))
			{
				reachedRecoveryTarget = true;
				break;
			}

			/*
			 * If we've been asked to lag the primary, wait on latch until
			 * enough time has passed.
			 */
			if (recoveryApplyDelay(xlogreader))
			{
				/*
				 * We test for paused recovery again here. If user sets
				 * delayed apply, it may be because they expect to pause
				 * recovery in case of problems, so we must test again here
				 * otherwise pausing during the delay-wait wouldn't work.
				 */
				if (((volatile XLogRecoveryCtlData *) XLogRecoveryCtl)->recoveryPauseState !=
					RECOVERY_NOT_PAUSED)
					recoveryPausesHere(false);
			}

			/*
			 * Apply the record
			 */
			ApplyWalRecord(xlogreader, record, &replayTLI);

			/*
			 * Wake up processes waiting for standby replay, write, or flush
			 * LSN to reach current replay position.  Replay implies that the
			 * WAL was already written and flushed to disk, so write and flush
			 * waiters can be woken at the replay position too.
			 */
			WaitLSNWakeup(WAIT_LSN_TYPE_STANDBY_REPLAY,
						  XLogRecoveryCtl->lastReplayedEndRecPtr);
			WaitLSNWakeup(WAIT_LSN_TYPE_STANDBY_WRITE,
						  XLogRecoveryCtl->lastReplayedEndRecPtr);
			WaitLSNWakeup(WAIT_LSN_TYPE_STANDBY_FLUSH,
						  XLogRecoveryCtl->lastReplayedEndRecPtr);

			/* Exit loop if we reached inclusive recovery target */
			if (recoveryStopsAfter(xlogreader))
			{
				reachedRecoveryTarget = true;
				break;
			}

			/* Else, try to fetch the next WAL record */
			record = ReadRecord(xlogprefetcher, LOG, false, replayTLI);
		} while (record != NULL);

		/*
		 * end of main redo apply loop
		 */

		if (reachedRecoveryTarget)
		{
			if (!reachedConsistency)
				ereport(FATAL,
						(errmsg("requested recovery stop point is before consistent recovery point")));

			/*
			 * This is the last point where we can restart recovery with a new
			 * recovery target, if we shutdown and begin again. After this,
			 * Resource Managers may choose to do permanent corrective actions
			 * at end of recovery.
			 */
			switch (recoveryTargetAction)
			{
				case RECOVERY_TARGET_ACTION_SHUTDOWN:

					/*
					 * exit with special return code to request shutdown of
					 * postmaster.  Log messages issued from postmaster.
					 */
					proc_exit(3);

				case RECOVERY_TARGET_ACTION_PAUSE:
					SetRecoveryPause(true);
					recoveryPausesHere(true);

					/* drop into promote */
					pg_fallthrough;

				case RECOVERY_TARGET_ACTION_PROMOTE:
					break;
			}
		}

		RmgrCleanup();

		ereport(LOG,
				errmsg("redo done at %X/%08X system usage: %s",
					   LSN_FORMAT_ARGS(xlogreader->ReadRecPtr),
					   pg_rusage_show(&ru0)));
		xtime = GetLatestXTime();
		if (xtime)
			ereport(LOG,
					(errmsg("last completed transaction was at log time %s",
							timestamptz_to_str(xtime))));

		InRedo = false;
	}
	else
	{
		/* there are no WAL records following the checkpoint */
		ereport(LOG,
				(errmsg("redo is not required")));
	}

	/*
	 * This check is intentionally after the above log messages that indicate
	 * how far recovery went.
	 */
	if (ArchiveRecoveryRequested &&
		recoveryTarget != RECOVERY_TARGET_UNSET &&
		!reachedRecoveryTarget)
		ereport(FATAL,
				(errcode(ERRCODE_CONFIG_FILE_ERROR),
				 errmsg("recovery ended before configured recovery target was reached")));
}

/*
 * Subroutine of PerformWalRecovery, to apply one WAL record.
 */
/*
 * 中文注释：
 * 重放单条 WAL 记录，是主循环的核心步骤。
 *
 * 处理顺序：
 *   1. 压入 rm_redo_error_callback，使重放报错时能打印记录描述和块信息；
 *   2. 确保 TransamVariables->nextXid 超过记录的 xl_xid；
 *   3. 若记录是 shutdown checkpoint 或 XLOG_END_OF_RECOVERY，检查并切换 replayTLI：
 *      新时间线必须在期望历史中、不能倒退，且不能越过尚未到达的 minRecoveryPoint；
 *   4. 在 info_lck 下更新 replayEndRecPtr/TLI，供 XLogFlush 正确推进
 *      minRecoveryPoint；
 *   5. 热备已初始化时，把记录中的 XID 登记为 known-assigned XID；
 *   6. RM_XLOG_ID 中与恢复直接相关的记录交给 xlogrecovery_redo，其余交给
 *      GetRmgr(...).rm_redo；
 *   7. 若记录带 XLR_CHECK_CONSISTENCY，调用 verifyBackupPageConsistency 比较
 *      重放页与 WAL 中的 FPI；
 *   8. 更新 lastReplayed* 进度，按需唤醒 walsender、请求 walreceiver 回复、
 *      检查一致性；发生时间线切换时删除旧时间线的未来 WAL 段并重配 prefetcher。
 * 错误上下文在函数返回前弹出，保证后续错误不受本条记录影响。
 */
static void
ApplyWalRecord(XLogReaderState *xlogreader, XLogRecord *record, TimeLineID *replayTLI)
{
	ErrorContextCallback errcallback;
	bool		switchedTLI = false;

	/* Setup error traceback support for ereport() */
	errcallback.callback = rm_redo_error_callback;
	errcallback.arg = xlogreader;
	errcallback.previous = error_context_stack;
	error_context_stack = &errcallback;

	/*
	 * TransamVariables->nextXid must be beyond record's xid.
	 */
	AdvanceNextFullTransactionIdPastXid(record->xl_xid);

	/*
	 * Before replaying this record, check if this record causes the current
	 * timeline to change. The record is already considered to be part of the
	 * new timeline, so we update replayTLI before replaying it. That's
	 * important so that replayEndTLI, which is recorded as the minimum
	 * recovery point's TLI if recovery stops after this record, is set
	 * correctly.
	 */
	if (record->xl_rmid == RM_XLOG_ID)
	{
		TimeLineID	newReplayTLI = *replayTLI;
		TimeLineID	prevReplayTLI = *replayTLI;
		uint8		info = record->xl_info & ~XLR_INFO_MASK;

		if (info == XLOG_CHECKPOINT_SHUTDOWN)
		{
			CheckPoint	checkPoint;

			memcpy(&checkPoint, XLogRecGetData(xlogreader), sizeof(CheckPoint));
			newReplayTLI = checkPoint.ThisTimeLineID;
			prevReplayTLI = checkPoint.PrevTimeLineID;
		}
		else if (info == XLOG_END_OF_RECOVERY)
		{
			xl_end_of_recovery xlrec;

			memcpy(&xlrec, XLogRecGetData(xlogreader), sizeof(xl_end_of_recovery));
			newReplayTLI = xlrec.ThisTimeLineID;
			prevReplayTLI = xlrec.PrevTimeLineID;
		}

		if (newReplayTLI != *replayTLI)
		{
			/* Check that it's OK to switch to this TLI */
			checkTimeLineSwitch(xlogreader->EndRecPtr,
								newReplayTLI, prevReplayTLI, *replayTLI);

			/* Following WAL records should be run with new TLI */
			*replayTLI = newReplayTLI;
			switchedTLI = true;
		}
	}

	/*
	 * Update shared replayEndRecPtr before replaying this record, so that
	 * XLogFlush will update minRecoveryPoint correctly.
	 */
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	XLogRecoveryCtl->replayEndRecPtr = xlogreader->EndRecPtr;
	XLogRecoveryCtl->replayEndTLI = *replayTLI;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	/*
	 * If we are attempting to enter Hot Standby mode, process XIDs we see
	 */
	if (standbyState >= STANDBY_INITIALIZED &&
		TransactionIdIsValid(record->xl_xid))
		RecordKnownAssignedTransactionIds(record->xl_xid);

	/*
	 * Some XLOG record types that are related to recovery are processed
	 * directly here, rather than in xlog_redo()
	 */
	if (record->xl_rmid == RM_XLOG_ID)
		xlogrecovery_redo(xlogreader, *replayTLI);

	/* Now apply the WAL record itself */
	GetRmgr(record->xl_rmid).rm_redo(xlogreader);

	/*
	 * After redo, check whether the backup pages associated with the WAL
	 * record are consistent with the existing pages. This check is done only
	 * if consistency check is enabled for this record.
	 */
	if ((record->xl_info & XLR_CHECK_CONSISTENCY) != 0)
		verifyBackupPageConsistency(xlogreader);

	/* Pop the error context stack */
	error_context_stack = errcallback.previous;

	/*
	 * Update lastReplayedEndRecPtr after this record has been successfully
	 * replayed.
	 */
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	XLogRecoveryCtl->lastReplayedReadRecPtr = xlogreader->ReadRecPtr;
	XLogRecoveryCtl->lastReplayedEndRecPtr = xlogreader->EndRecPtr;
	XLogRecoveryCtl->lastReplayedTLI = *replayTLI;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	/* ------
	 * Wakeup walsenders:
	 *
	 * On the standby, the WAL is flushed first (which will only wake up
	 * physical walsenders) and then applied, which will only wake up logical
	 * walsenders.
	 *
	 * Indeed, logical walsenders on standby can't decode and send data until
	 * it's been applied.
	 *
	 * Physical walsenders don't need to be woken up during replay unless
	 * cascading replication is allowed and time line change occurred (so that
	 * they can notice that they are on a new time line).
	 *
	 * That's why the wake up conditions are for:
	 *
	 *  - physical walsenders in case of new time line and cascade
	 *    replication is allowed
	 *  - logical walsenders in case cascade replication is allowed (could not
	 *    be created otherwise)
	 * ------
	 */
	if (AllowCascadeReplication())
		WalSndWakeup(switchedTLI, true);

	/*
	 * If rm_redo called XLogRequestWalReceiverReply, then we wake up the
	 * receiver so that it notices the updated lastReplayedEndRecPtr and sends
	 * a reply to the primary.
	 */
	if (doRequestWalReceiverReply)
	{
		doRequestWalReceiverReply = false;
		WalRcvRequestApplyReply();
	}

	/* Allow read-only connections if we're consistent now */
	CheckRecoveryConsistency();

	/* Is this a timeline switch? */
	if (switchedTLI)
	{
		/*
		 * Before we continue on the new timeline, clean up any (possibly
		 * bogus) future WAL segments on the old timeline.
		 */
		RemoveNonParentXlogFiles(xlogreader->EndRecPtr, *replayTLI);

		/* Reset the prefetcher. */
		XLogPrefetchReconfigure();
	}
}

/*
 * Some XLOG RM record types that are directly related to WAL recovery are
 * handled here rather than in the xlog_redo()
 */
/*
 * 中文注释：
 * 处理与恢复流程强相关、因而不放在 xlog_redo() 中的 RM_XLOG_ID 记录。
 *
 * 目前包括两类：
 *   - XLOG_OVERWRITE_CONTRECORD：校验记录中的 overwritten_lsn 与 reader 记录的
 *     一致，确认之前不完整的 continuation record 已被安全跳过，清除
 *     abortedRecPtr/missingContrecPtr，并把 overwrittenRecPtr 复位，防止重复校验；
 *   - XLOG_BACKUP_END：若记录中的备份起点等于当前 backupStartPoint，说明基础备份
 *     的 WAL 已重放完毕，把 backupEndPoint 设为当前记录末尾；下一次
 *     CheckRecoveryConsistency 会据此完成 end-of-backup 处理。起点不匹配则只记
 *     DEBUG 日志（可能属于另一个备份）。
 */
static void
xlogrecovery_redo(XLogReaderState *record, TimeLineID replayTLI)
{
	uint8		info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;
	XLogRecPtr	lsn = record->EndRecPtr;

	Assert(XLogRecGetRmid(record) == RM_XLOG_ID);

	if (info == XLOG_OVERWRITE_CONTRECORD)
	{
		/* Verify the payload of a XLOG_OVERWRITE_CONTRECORD record. */
		xl_overwrite_contrecord xlrec;

		memcpy(&xlrec, XLogRecGetData(record), sizeof(xl_overwrite_contrecord));
		if (xlrec.overwritten_lsn != record->overwrittenRecPtr)
			elog(FATAL, "mismatching overwritten LSN %X/%08X -> %X/%08X",
				 LSN_FORMAT_ARGS(xlrec.overwritten_lsn),
				 LSN_FORMAT_ARGS(record->overwrittenRecPtr));

		/* We have safely skipped the aborted record */
		abortedRecPtr = InvalidXLogRecPtr;
		missingContrecPtr = InvalidXLogRecPtr;

		ereport(LOG,
				errmsg("successfully skipped missing contrecord at %X/%08X, overwritten at %s",
					   LSN_FORMAT_ARGS(xlrec.overwritten_lsn),
					   timestamptz_to_str(xlrec.overwrite_time)));

		/* Verifying the record should only happen once */
		record->overwrittenRecPtr = InvalidXLogRecPtr;
	}
	else if (info == XLOG_BACKUP_END)
	{
		XLogRecPtr	startpoint;

		memcpy(&startpoint, XLogRecGetData(record), sizeof(startpoint));

		if (backupStartPoint == startpoint)
		{
			/*
			 * We have reached the end of base backup, the point where
			 * pg_backup_stop() was done.  The data on disk is now consistent
			 * (assuming we have also reached minRecoveryPoint).  Set
			 * backupEndPoint to the current LSN, so that the next call to
			 * CheckRecoveryConsistency() will notice it and do the
			 * end-of-backup processing.
			 */
			elog(DEBUG1, "end of backup record reached");

			backupEndPoint = lsn;
		}
		else
			elog(DEBUG1, "saw end-of-backup record for backup starting at %X/%08X, waiting for %X/%08X",
				 LSN_FORMAT_ARGS(startpoint), LSN_FORMAT_ARGS(backupStartPoint));
	}
}

/*
 * Verify that, in non-test mode, ./pg_tblspc doesn't contain any real
 * directories.
 *
 * Replay of database creation XLOG records for databases that were later
 * dropped can create fake directories in pg_tblspc.  By the time consistency
 * is reached these directories should have been removed; here we verify
 * that this did indeed happen.  This is to be called at the point where
 * consistent state is reached.
 *
 * allow_in_place_tablespaces turns the PANIC into a WARNING, which is
 * useful for testing purposes, and also allows for an escape hatch in case
 * things go south.
 */
/*
 * 中文注释：
 * 在达到一致性时检查 pg_tblspc 下没有真实目录。
 *
 * 重放“创建后又删除数据库”的记录可能在 pg_tblspc 留下伪造目录；正常情况下到
 * 一致性点时它们应已被删除。检测到非符号链接的 OID 命名项时，默认 PANIC（数据
 * 损坏），allow_in_place_tablespaces 开启时降级为 WARNING，便于测试或在紧急情况下
 * 放行。非纯数字命名的条目直接跳过。
 */
static void
CheckTablespaceDirectory(void)
{
	DIR		   *dir;
	struct dirent *de;

	dir = AllocateDir(PG_TBLSPC_DIR);
	while ((de = ReadDir(dir, PG_TBLSPC_DIR)) != NULL)
	{
		char		path[MAXPGPATH + sizeof(PG_TBLSPC_DIR)];

		/* Skip entries of non-oid names */
		if (strspn(de->d_name, "0123456789") != strlen(de->d_name))
			continue;

		snprintf(path, sizeof(path), "%s/%s", PG_TBLSPC_DIR, de->d_name);

		if (get_dirent_type(path, de, false, ERROR) != PGFILETYPE_LNK)
			ereport(allow_in_place_tablespaces ? WARNING : PANIC,
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("unexpected directory entry \"%s\" found in %s",
							de->d_name, PG_TBLSPC_DIR),
					 errdetail("All directory entries in %s/ should be symbolic links.",
							   PG_TBLSPC_DIR),
					 errhint("Remove those directories, or set \"allow_in_place_tablespaces\" to ON transiently to let recovery complete.")));
	}
}

/*
 * Checks if recovery has reached a consistent state. When consistency is
 * reached and we have a valid starting standby snapshot, tell postmaster
 * that it can start accepting read-only connections.
 */
/*
 * 中文注释：
 * 检查恢复是否已经达到一致状态，并在条件满足时允许热备连接。
 *
 * 崩溃恢复没有 minRecoveryPoint，函数直接返回，只有重放完全部 WAL 才算一致。
 * 归档恢复中：
 *   1. 若已到达 backupEndPoint，调用 ReachedEndOfBackup 更新控制文件，清除
 *      backupStartPoint/EndPoint 和 backupEndRequired；
 *   2. 若 !backupEndRequired 且 minRecoveryPoint <= 最后重放位置，执行
 *      XLogCheckInvalidPages 和 CheckTablespaceDirectory，置 reachedConsistency，
 *      向 postmaster 发送 PMSIGNAL_RECOVERY_CONSISTENT；
 *   3. 若 standbyState 已达到 STANDBY_SNAPSHOT_READY，在自旋锁下设置共享
 *      SharedHotStandbyActive，向 postmaster 发送 PMSIGNAL_BEGIN_HOT_STANDBY，
 *      开始接受只读查询。
 * 该函数可能被每条记录调用，但大部分工作在条件不满足时快速返回。
 */
static void
CheckRecoveryConsistency(void)
{
	XLogRecPtr	lastReplayedEndRecPtr;
	TimeLineID	lastReplayedTLI;

	/*
	 * During crash recovery, we don't reach a consistent state until we've
	 * replayed all the WAL.
	 */
	if (!XLogRecPtrIsValid(minRecoveryPoint))
		return;

	Assert(InArchiveRecovery);

	/*
	 * assume that we are called in the startup process, and hence don't need
	 * a lock to read lastReplayedEndRecPtr
	 */
	lastReplayedEndRecPtr = XLogRecoveryCtl->lastReplayedEndRecPtr;
	lastReplayedTLI = XLogRecoveryCtl->lastReplayedTLI;

	/*
	 * Have we reached the point where our base backup was completed?
	 */
	if (XLogRecPtrIsValid(backupEndPoint) &&
		backupEndPoint <= lastReplayedEndRecPtr)
	{
		XLogRecPtr	saveBackupStartPoint = backupStartPoint;
		XLogRecPtr	saveBackupEndPoint = backupEndPoint;

		elog(DEBUG1, "end of backup reached");

		/*
		 * We have reached the end of base backup, as indicated by pg_control.
		 * Update the control file accordingly.
		 */
		ReachedEndOfBackup(lastReplayedEndRecPtr, lastReplayedTLI);
		backupStartPoint = InvalidXLogRecPtr;
		backupEndPoint = InvalidXLogRecPtr;
		backupEndRequired = false;

		ereport(LOG,
				errmsg("completed backup recovery with redo LSN %X/%08X and end LSN %X/%08X",
					   LSN_FORMAT_ARGS(saveBackupStartPoint),
					   LSN_FORMAT_ARGS(saveBackupEndPoint)));
	}

	/*
	 * Have we passed our safe starting point? Note that minRecoveryPoint is
	 * known to be incorrectly set if recovering from a backup, until the
	 * XLOG_BACKUP_END arrives to advise us of the correct minRecoveryPoint.
	 * All we know prior to that is that we're not consistent yet.
	 */
	if (!reachedConsistency && !backupEndRequired &&
		minRecoveryPoint <= lastReplayedEndRecPtr)
	{
		/*
		 * Check to see if the XLOG sequence contained any unresolved
		 * references to uninitialized pages.
		 */
		XLogCheckInvalidPages();

		/*
		 * Check that pg_tblspc doesn't contain any real directories. Replay
		 * of Database/CREATE_* records may have created fictitious tablespace
		 * directories that should have been removed by the time consistency
		 * was reached.
		 */
		CheckTablespaceDirectory();

		reachedConsistency = true;
		SendPostmasterSignal(PMSIGNAL_RECOVERY_CONSISTENT);
		ereport(LOG,
				errmsg("consistent recovery state reached at %X/%08X",
					   LSN_FORMAT_ARGS(lastReplayedEndRecPtr)));
	}

	/*
	 * Have we got a valid starting snapshot that will allow queries to be
	 * run? If so, we can tell postmaster that the database is consistent now,
	 * enabling connections.
	 */
	if (standbyState == STANDBY_SNAPSHOT_READY &&
		!LocalHotStandbyActive &&
		reachedConsistency &&
		IsUnderPostmaster)
	{
		SpinLockAcquire(&XLogRecoveryCtl->info_lck);
		XLogRecoveryCtl->SharedHotStandbyActive = true;
		SpinLockRelease(&XLogRecoveryCtl->info_lck);

		LocalHotStandbyActive = true;

		SendPostmasterSignal(PMSIGNAL_BEGIN_HOT_STANDBY);
	}
}

/*
 * Error context callback for errors occurring during rm_redo().
 */
/*
 * 中文注释：
 * rm_redo 执行期间的 error context 回调。
 *
 * 当重放某条记录时报错，PostgreSQL 的错误报告机制会调用本函数追加上下文，
 * 输出记录起始 LSN、rmgr 名称、记录类型描述以及所有 block reference 的
 * relfilenode/fork/block 和是否带 FPI。这样 DBA 能定位是哪条 WAL 记录导致失败。
 * 使用临时 StringInfo，输出后立即释放。
 */
static void
rm_redo_error_callback(void *arg)
{
	XLogReaderState *record = (XLogReaderState *) arg;
	StringInfoData buf;

	initStringInfo(&buf);
	xlog_outdesc(&buf, record);
	xlog_block_info(&buf, record);

	/* translator: %s is a WAL record description */
	errcontext("WAL redo at %X/%08X for %s",
			   LSN_FORMAT_ARGS(record->ReadRecPtr),
			   buf.data);

	pfree(buf.data);
}

/*
 * Returns a string describing an XLogRecord, consisting of its identity
 * optionally followed by a colon, a space, and a further description.
 */
/*
 * 中文注释：
 * 把一条 WAL 记录的类型和描述追加到 StringInfo。
 *
 * 先从 GetRmgr 取得 rmgr 名称，再调用 rm_identify 识别具体记录类型；未知类型输出
 * "UNKNOWN (info)"。然后调用 rm_desc 追加 rmgr 私有的详细描述。输出格式大致为
 * "<rmgr>/<type>: <details>"，用于日志、错误上下文和 WAL_DEBUG 输出。
 */
void
xlog_outdesc(StringInfo buf, XLogReaderState *record)
{
	RmgrData	rmgr = GetRmgr(XLogRecGetRmid(record));
	uint8		info = XLogRecGetInfo(record);
	const char *id;

	appendStringInfoString(buf, rmgr.rm_name);
	appendStringInfoChar(buf, '/');

	id = rmgr.rm_identify(info);
	if (id == NULL)
		appendStringInfo(buf, "UNKNOWN (%X): ", info & ~XLR_INFO_MASK);
	else
		appendStringInfo(buf, "%s: ", id);

	rmgr.rm_desc(buf, record);
}

#ifdef WAL_DEBUG

/*
 * 中文注释：
 * 在 WAL_DEBUG 构建中输出记录头信息：xl_prev、xl_xid、main data 长度以及所有
 * block reference。仅用于调试日志，不影响正常运行。
 */
static void
xlog_outrec(StringInfo buf, XLogReaderState *record)
{
	appendStringInfo(buf, "prev %X/%08X; xid %u",
					 LSN_FORMAT_ARGS(XLogRecGetPrev(record)),
					 XLogRecGetXid(record));

	appendStringInfo(buf, "; len %u",
					 XLogRecGetDataLen(record));

	xlog_block_info(buf, record);
}
#endif							/* WAL_DEBUG */

/*
 * Returns a string giving information about all the blocks in an
 * XLogRecord.
 */
/*
 * 中文注释：
 * 把所有 block reference 的信息追加到 StringInfo。
 *
 * 遍历 block_id 直到 XLogRecMaxBlockId，用 XLogRecGetBlockTagExtended 取得
 * RelFileLocator/fork/block number；主 fork 省略 fork 字段，其他 fork 显示编号。
 * 若该块带 full-page image，追加 " FPW"。用于错误上下文和调试输出。
 */
static void
xlog_block_info(StringInfo buf, XLogReaderState *record)
{
	int			block_id;

	/* decode block references */
	for (block_id = 0; block_id <= XLogRecMaxBlockId(record); block_id++)
	{
		RelFileLocator rlocator;
		ForkNumber	forknum;
		BlockNumber blk;

		if (!XLogRecGetBlockTagExtended(record, block_id,
										&rlocator, &forknum, &blk, NULL))
			continue;

		if (forknum != MAIN_FORKNUM)
			appendStringInfo(buf, "; blkref #%d: rel %u/%u/%u, fork %u, blk %u",
							 block_id,
							 rlocator.spcOid, rlocator.dbOid,
							 rlocator.relNumber,
							 forknum,
							 blk);
		else
			appendStringInfo(buf, "; blkref #%d: rel %u/%u/%u, blk %u",
							 block_id,
							 rlocator.spcOid, rlocator.dbOid,
							 rlocator.relNumber,
							 blk);
		if (XLogRecHasBlockImage(record, block_id))
			appendStringInfoString(buf, " FPW");
	}
}


/*
 * Check that it's OK to switch to new timeline during recovery.
 *
 * 'lsn' is the address of the shutdown checkpoint record we're about to
 * replay. (Currently, timeline can only change at a shutdown checkpoint).
 */
/*
 * 中文注释：
 * 校验恢复中切换到新时间线是否合法。
 *
 * 检查三点：
 *   1. 记录声明的 PrevTimeLineID 必须等于当前 replayTLI，否则记录与恢复上下文
 *      不一致；
 *   2. newTLI 不能小于当前 TLI，且必须出现在 expectedTLEs（由时间线历史推导）
 *      中；
 *   3. 若尚未到达 minRecoveryPoint，不能切换到比 minRecoveryPointTLI 更新的
 *      时间线：切换后将永远无法在正确时间线上访问 minRecoveryPoint。
 * 任一条件不满足都 PANIC，因为继续重放会破坏时间线历史的一致性。
 */
static void
checkTimeLineSwitch(XLogRecPtr lsn, TimeLineID newTLI, TimeLineID prevTLI,
					TimeLineID replayTLI)
{
	/* Check that the record agrees on what the current (old) timeline is */
	if (prevTLI != replayTLI)
		ereport(PANIC,
				(errmsg("unexpected previous timeline ID %u (current timeline ID %u) in checkpoint record",
						prevTLI, replayTLI)));

	/*
	 * The new timeline better be in the list of timelines we expect to see,
	 * according to the timeline history. It should also not decrease.
	 */
	if (newTLI < replayTLI || !tliInHistory(newTLI, expectedTLEs))
		ereport(PANIC,
				(errmsg("unexpected timeline ID %u (after %u) in checkpoint record",
						newTLI, replayTLI)));

	/*
	 * If we have not yet reached min recovery point, and we're about to
	 * switch to a timeline greater than the timeline of the min recovery
	 * point: trouble. After switching to the new timeline, we could not
	 * possibly visit the min recovery point on the correct timeline anymore.
	 * This can happen if there is a newer timeline in the archive that
	 * branched before the timeline the min recovery point is on, and you
	 * attempt to do PITR to the new timeline.
	 */
	if (XLogRecPtrIsValid(minRecoveryPoint) &&
		lsn < minRecoveryPoint &&
		newTLI > minRecoveryPointTLI)
		ereport(PANIC,
				errmsg("unexpected timeline ID %u in checkpoint record, before reaching minimum recovery point %X/%08X on timeline %u",
					   newTLI,
					   LSN_FORMAT_ARGS(minRecoveryPoint),
					   minRecoveryPointTLI));

	/* Looks good */
}


/*
 * Extract timestamp from WAL record.
 *
 * If the record contains a timestamp, returns true, and saves the timestamp
 * in *recordXtime. If the record type has no timestamp, returns false.
 * Currently, only transaction commit/abort records and restore points contain
 * timestamps.
 */
/*
 * 中文注释：
 * 从 WAL 记录中提取时间戳。
 *
 * 目前只有 restore point 和事务 commit/abort（含 prepared 变体）记录带时间戳。
 * 命中时把时间写入 *recordXtime 并返回 true；其他记录返回 false，调用者不应
 * 使用输出值。用于 PITR 按时间停止和 recovery_min_apply_delay 计算延迟。
 */
static bool
getRecordTimestamp(XLogReaderState *record, TimestampTz *recordXtime)
{
	uint8		info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;
	uint8		xact_info = info & XLOG_XACT_OPMASK;
	uint8		rmid = XLogRecGetRmid(record);

	if (rmid == RM_XLOG_ID && info == XLOG_RESTORE_POINT)
	{
		*recordXtime = ((xl_restore_point *) XLogRecGetData(record))->rp_time;
		return true;
	}
	if (rmid == RM_XACT_ID && (xact_info == XLOG_XACT_COMMIT ||
							   xact_info == XLOG_XACT_COMMIT_PREPARED))
	{
		*recordXtime = ((xl_xact_commit *) XLogRecGetData(record))->xact_time;
		return true;
	}
	if (rmid == RM_XACT_ID && (xact_info == XLOG_XACT_ABORT ||
							   xact_info == XLOG_XACT_ABORT_PREPARED))
	{
		*recordXtime = ((xl_xact_abort *) XLogRecGetData(record))->xact_time;
		return true;
	}
	return false;
}

/*
 * Checks whether the current buffer page and backup page stored in the
 * WAL record are consistent or not. Before comparing the two pages, a
 * masking can be applied to the pages to ignore certain areas like hint bits,
 * unused space between pd_lower and pd_upper among other things. This
 * function should be called once WAL replay has been completed for a
 * given record.
 */
/*
 * 中文注释：
 * 校验重放后的页与 WAL 记录中的 full-page image 是否一致。
 *
 * 仅对带 XLR_CHECK_CONSISTENCY 且含 block reference 的记录执行。对每个块：
 *   - 若 FPI 已经在 redo 中应用，跳过（否则等于拿记录和自己比较）；
 *   - 以 RBM_NORMAL_NO_LOG 读取当前页并复制到 replay_image_masked，随后立即解锁；
 *   - 若页 LSN 已超过本记录末尾（恢复被重启过），无法期望内容匹配，跳过；
 *   - 用 RestoreBlockImage 把 WAL 中的镜像还原到 primary_image_masked；
 *   - 若 rmgr 定义 rm_mask，对两页应用相同的掩码，忽略 hint bit、页内空洞等
 *     允许不同的区域；
 *   - memcmp 不一致则 FATAL，报告 relfilenode/fork/blkno。
 * 该检查用于开发/测试期间发现 redo 逻辑或 FPI 生成错误，正常生产可关闭。
 */
static void
verifyBackupPageConsistency(XLogReaderState *record)
{
	RmgrData	rmgr = GetRmgr(XLogRecGetRmid(record));
	RelFileLocator rlocator;
	ForkNumber	forknum;
	BlockNumber blkno;
	int			block_id;

	/* Records with no backup blocks have no need for consistency checks. */
	if (!XLogRecHasAnyBlockRefs(record))
		return;

	Assert((XLogRecGetInfo(record) & XLR_CHECK_CONSISTENCY) != 0);

	for (block_id = 0; block_id <= XLogRecMaxBlockId(record); block_id++)
	{
		Buffer		buf;
		Page		page;

		if (!XLogRecGetBlockTagExtended(record, block_id,
										&rlocator, &forknum, &blkno, NULL))
		{
			/*
			 * WAL record doesn't contain a block reference with the given id.
			 * Do nothing.
			 */
			continue;
		}

		Assert(XLogRecHasBlockImage(record, block_id));

		if (XLogRecBlockImageApply(record, block_id))
		{
			/*
			 * WAL record has already applied the page, so bypass the
			 * consistency check as that would result in comparing the full
			 * page stored in the record with itself.
			 */
			continue;
		}

		/*
		 * Read the contents from the current buffer and store it in a
		 * temporary page.
		 */
		buf = XLogReadBufferExtended(rlocator, forknum, blkno,
									 RBM_NORMAL_NO_LOG,
									 InvalidBuffer);
		if (!BufferIsValid(buf))
			continue;

		LockBuffer(buf, BUFFER_LOCK_EXCLUSIVE);
		page = BufferGetPage(buf);

		/*
		 * Take a copy of the local page where WAL has been applied to have a
		 * comparison base before masking it...
		 */
		memcpy(replay_image_masked, page, BLCKSZ);

		/* No need for this page anymore now that a copy is in. */
		UnlockReleaseBuffer(buf);

		/*
		 * If the block LSN is already ahead of this WAL record, we can't
		 * expect contents to match.  This can happen if recovery is
		 * restarted.
		 */
		if (PageGetLSN(replay_image_masked) > record->EndRecPtr)
			continue;

		/*
		 * Read the contents from the backup copy, stored in WAL record and
		 * store it in a temporary page. There is no need to allocate a new
		 * page here, a local buffer is fine to hold its contents and a mask
		 * can be directly applied on it.
		 */
		if (!RestoreBlockImage(record, block_id, primary_image_masked))
			ereport(ERROR,
					(errcode(ERRCODE_INTERNAL_ERROR),
					 errmsg_internal("%s", record->errormsg_buf)));

		/*
		 * If masking function is defined, mask both the primary and replay
		 * images
		 */
		if (rmgr.rm_mask != NULL)
		{
			rmgr.rm_mask(replay_image_masked, blkno);
			rmgr.rm_mask(primary_image_masked, blkno);
		}

		/* Time to compare the primary and replay images. */
		if (memcmp(replay_image_masked, primary_image_masked, BLCKSZ) != 0)
		{
			elog(FATAL,
				 "inconsistent page found, rel %u/%u/%u, forknum %u, blkno %u",
				 rlocator.spcOid, rlocator.dbOid, rlocator.relNumber,
				 forknum, blkno);
		}
	}
}

/*
 * For point-in-time recovery, this function decides whether we want to
 * stop applying the XLOG before the current record.
 *
 * Returns true if we are stopping, false otherwise. If stopping, some
 * information is saved in recoveryStopXid et al for use in annotating the
 * new timeline's history file.
 */
/*
 * 中文注释：
 * 判断是否应在重放当前记录之前停止（exclusive recovery target）。
 *
 * 非归档恢复直接返回 false，崩溃恢复不受 recovery_target 影响。依次处理：
 *   - recovery_target=immediate 且已达到一致性：立即停止；
 *   - recovery_target_lsn 且非 inclusive：记录起始 LSN >= 目标时停止；
 *   - 只对 RM_XACT_ID 的 commit/abort（含 prepared）记录继续判断；
 *   - XID 目标必须用相等比较：事务按开始顺序编号而非结束顺序，不能比较大小；
 *   - 时间目标：inclusive 时在 recordXtime > target 时停止（即停在最后一条
 *     等于目标时间的记录之后），exclusive 时在 >= target 时停止。
 * 停止时填充 recoveryStopXid/Time/LSN/Name 和 recoveryStopAfter，供生成时间线
 * 历史文件注释使用。
 */
static bool
recoveryStopsBefore(XLogReaderState *record)
{
	bool		stopsHere = false;
	uint8		xact_info;
	bool		isCommit;
	TimestampTz recordXtime = 0;
	TransactionId recordXid;

	/*
	 * Ignore recovery target settings when not in archive recovery (meaning
	 * we are in crash recovery).
	 */
	if (!ArchiveRecoveryRequested)
		return false;

	/* Check if we should stop as soon as reaching consistency */
	if (recoveryTarget == RECOVERY_TARGET_IMMEDIATE && reachedConsistency)
	{
		ereport(LOG,
				(errmsg("recovery stopping after reaching consistency")));

		recoveryStopAfter = false;
		recoveryStopXid = InvalidTransactionId;
		recoveryStopLSN = InvalidXLogRecPtr;
		recoveryStopTime = 0;
		recoveryStopName[0] = '\0';
		return true;
	}

	/* Check if target LSN has been reached */
	if (recoveryTarget == RECOVERY_TARGET_LSN &&
		!recoveryTargetInclusive &&
		record->ReadRecPtr >= recoveryTargetLSN)
	{
		recoveryStopAfter = false;
		recoveryStopXid = InvalidTransactionId;
		recoveryStopLSN = record->ReadRecPtr;
		recoveryStopTime = 0;
		recoveryStopName[0] = '\0';
		ereport(LOG,
				errmsg("recovery stopping before WAL location (LSN) \"%X/%08X\"",
					   LSN_FORMAT_ARGS(recoveryStopLSN)));
		return true;
	}

	/* Otherwise we only consider stopping before COMMIT or ABORT records. */
	if (XLogRecGetRmid(record) != RM_XACT_ID)
		return false;

	xact_info = XLogRecGetInfo(record) & XLOG_XACT_OPMASK;

	if (xact_info == XLOG_XACT_COMMIT)
	{
		isCommit = true;
		recordXid = XLogRecGetXid(record);
	}
	else if (xact_info == XLOG_XACT_COMMIT_PREPARED)
	{
		xl_xact_commit *xlrec = (xl_xact_commit *) XLogRecGetData(record);
		xl_xact_parsed_commit parsed;

		isCommit = true;
		ParseCommitRecord(XLogRecGetInfo(record),
						  xlrec,
						  &parsed);
		recordXid = parsed.twophase_xid;
	}
	else if (xact_info == XLOG_XACT_ABORT)
	{
		isCommit = false;
		recordXid = XLogRecGetXid(record);
	}
	else if (xact_info == XLOG_XACT_ABORT_PREPARED)
	{
		xl_xact_abort *xlrec = (xl_xact_abort *) XLogRecGetData(record);
		xl_xact_parsed_abort parsed;

		isCommit = false;
		ParseAbortRecord(XLogRecGetInfo(record),
						 xlrec,
						 &parsed);
		recordXid = parsed.twophase_xid;
	}
	else
		return false;

	if (recoveryTarget == RECOVERY_TARGET_XID && !recoveryTargetInclusive)
	{
		/*
		 * There can be only one transaction end record with this exact
		 * transactionid
		 *
		 * when testing for an xid, we MUST test for equality only, since
		 * transactions are numbered in the order they start, not the order
		 * they complete. A higher numbered xid will complete before you about
		 * 50% of the time...
		 */
		stopsHere = (recordXid == recoveryTargetXid);
	}

	/*
	 * Note: we must fetch recordXtime regardless of recoveryTarget setting.
	 * We don't expect getRecordTimestamp ever to fail, since we already know
	 * this is a commit or abort record; but test its result anyway.
	 */
	if (getRecordTimestamp(record, &recordXtime) &&
		recoveryTarget == RECOVERY_TARGET_TIME)
	{
		/*
		 * There can be many transactions that share the same commit time, so
		 * we stop after the last one, if we are inclusive, or stop at the
		 * first one if we are exclusive
		 */
		if (recoveryTargetInclusive)
			stopsHere = (recordXtime > recoveryTargetTime);
		else
			stopsHere = (recordXtime >= recoveryTargetTime);
	}

	if (stopsHere)
	{
		recoveryStopAfter = false;
		recoveryStopXid = recordXid;
		recoveryStopTime = recordXtime;
		recoveryStopLSN = InvalidXLogRecPtr;
		recoveryStopName[0] = '\0';

		if (isCommit)
		{
			ereport(LOG,
					(errmsg("recovery stopping before commit of transaction %u, time %s",
							recoveryStopXid,
							timestamptz_to_str(recoveryStopTime))));
		}
		else
		{
			ereport(LOG,
					(errmsg("recovery stopping before abort of transaction %u, time %s",
							recoveryStopXid,
							timestamptz_to_str(recoveryStopTime))));
		}
	}

	return stopsHere;
}

/*
 * Same as recoveryStopsBefore, but called after applying the record.
 *
 * We also track the timestamp of the latest applied COMMIT/ABORT
 * record in XLogRecoveryCtl->recoveryLastXTime.
 */
/*
 * 中文注释：
 * 判断是否应在重放当前记录之后停止（inclusive recovery target）。
 *
 * 与 recoveryStopsBefore 对称，但在记录应用后调用，并且还负责把最新
 * commit/abort 的时间记录到 XLogRecoveryCtl->recoveryLastXTime。处理：
 *   - recovery_target_name：遇到同名 restore point 停在第一条；
 *   - recovery_target_lsn 且 inclusive：记录起始 LSN >= 目标时停止；
 *   - XID inclusive：commit/abort 记录的 XID 等于目标时停止；
 *   - immediate：达到一致性后停止。
 * 停止时设置 recoveryStopAfter=true 并填充停止位置信息。prepared 事务需要先从
 * commit/abort 记录中解析出 twophase_xid 再比较。
 */
static bool
recoveryStopsAfter(XLogReaderState *record)
{
	uint8		info;
	uint8		xact_info;
	uint8		rmid;
	TimestampTz recordXtime = 0;

	/*
	 * Ignore recovery target settings when not in archive recovery (meaning
	 * we are in crash recovery).
	 */
	if (!ArchiveRecoveryRequested)
		return false;

	info = XLogRecGetInfo(record) & ~XLR_INFO_MASK;
	rmid = XLogRecGetRmid(record);

	/*
	 * There can be many restore points that share the same name; we stop at
	 * the first one.
	 */
	if (recoveryTarget == RECOVERY_TARGET_NAME &&
		rmid == RM_XLOG_ID && info == XLOG_RESTORE_POINT)
	{
		xl_restore_point *recordRestorePointData;

		recordRestorePointData = (xl_restore_point *) XLogRecGetData(record);

		if (strcmp(recordRestorePointData->rp_name, recoveryTargetName) == 0)
		{
			recoveryStopAfter = true;
			recoveryStopXid = InvalidTransactionId;
			recoveryStopLSN = InvalidXLogRecPtr;
			(void) getRecordTimestamp(record, &recoveryStopTime);
			strlcpy(recoveryStopName, recordRestorePointData->rp_name, MAXFNAMELEN);

			ereport(LOG,
					(errmsg("recovery stopping at restore point \"%s\", time %s",
							recoveryStopName,
							timestamptz_to_str(recoveryStopTime))));
			return true;
		}
	}

	/* Check if the target LSN has been reached */
	if (recoveryTarget == RECOVERY_TARGET_LSN &&
		recoveryTargetInclusive &&
		record->ReadRecPtr >= recoveryTargetLSN)
	{
		recoveryStopAfter = true;
		recoveryStopXid = InvalidTransactionId;
		recoveryStopLSN = record->ReadRecPtr;
		recoveryStopTime = 0;
		recoveryStopName[0] = '\0';
		ereport(LOG,
				errmsg("recovery stopping after WAL location (LSN) \"%X/%08X\"",
					   LSN_FORMAT_ARGS(recoveryStopLSN)));
		return true;
	}

	if (rmid != RM_XACT_ID)
		return false;

	xact_info = info & XLOG_XACT_OPMASK;

	if (xact_info == XLOG_XACT_COMMIT ||
		xact_info == XLOG_XACT_COMMIT_PREPARED ||
		xact_info == XLOG_XACT_ABORT ||
		xact_info == XLOG_XACT_ABORT_PREPARED)
	{
		TransactionId recordXid;

		/* Update the last applied transaction timestamp */
		if (getRecordTimestamp(record, &recordXtime))
			SetLatestXTime(recordXtime);

		/* Extract the XID of the committed/aborted transaction */
		if (xact_info == XLOG_XACT_COMMIT_PREPARED)
		{
			xl_xact_commit *xlrec = (xl_xact_commit *) XLogRecGetData(record);
			xl_xact_parsed_commit parsed;

			ParseCommitRecord(XLogRecGetInfo(record),
							  xlrec,
							  &parsed);
			recordXid = parsed.twophase_xid;
		}
		else if (xact_info == XLOG_XACT_ABORT_PREPARED)
		{
			xl_xact_abort *xlrec = (xl_xact_abort *) XLogRecGetData(record);
			xl_xact_parsed_abort parsed;

			ParseAbortRecord(XLogRecGetInfo(record),
							 xlrec,
							 &parsed);
			recordXid = parsed.twophase_xid;
		}
		else
			recordXid = XLogRecGetXid(record);

		/*
		 * There can be only one transaction end record with this exact
		 * transactionid
		 *
		 * when testing for an xid, we MUST test for equality only, since
		 * transactions are numbered in the order they start, not the order
		 * they complete. A higher numbered xid will complete before you about
		 * 50% of the time...
		 */
		if (recoveryTarget == RECOVERY_TARGET_XID && recoveryTargetInclusive &&
			recordXid == recoveryTargetXid)
		{
			recoveryStopAfter = true;
			recoveryStopXid = recordXid;
			recoveryStopTime = recordXtime;
			recoveryStopLSN = InvalidXLogRecPtr;
			recoveryStopName[0] = '\0';

			if (xact_info == XLOG_XACT_COMMIT ||
				xact_info == XLOG_XACT_COMMIT_PREPARED)
			{
				ereport(LOG,
						(errmsg("recovery stopping after commit of transaction %u, time %s",
								recoveryStopXid,
								timestamptz_to_str(recoveryStopTime))));
			}
			else if (xact_info == XLOG_XACT_ABORT ||
					 xact_info == XLOG_XACT_ABORT_PREPARED)
			{
				ereport(LOG,
						(errmsg("recovery stopping after abort of transaction %u, time %s",
								recoveryStopXid,
								timestamptz_to_str(recoveryStopTime))));
			}
			return true;
		}
	}

	/* Check if we should stop as soon as reaching consistency */
	if (recoveryTarget == RECOVERY_TARGET_IMMEDIATE && reachedConsistency)
	{
		ereport(LOG,
				(errmsg("recovery stopping after reaching consistency")));

		recoveryStopAfter = true;
		recoveryStopXid = InvalidTransactionId;
		recoveryStopTime = 0;
		recoveryStopLSN = InvalidXLogRecPtr;
		recoveryStopName[0] = '\0';
		return true;
	}

	return false;
}

/*
 * Create a comment for the history file to explain why and where
 * timeline changed.
 */
/*
 * 中文注释：
 * 生成时间线历史文件中的恢复停止原因字符串。
 *
 * 根据 recovery_target 类型和 recoveryStopAfter 描述是“在某事务/LSN/时间之前
 * 还是之后”停止，或停在某个 restore point、达到一致性，或未指定目标。返回
 * pstrdup 的字符串，调用者负责释放。该文本会写入新时间线的 .history 文件，
 * 帮助后续判断分支原因。
 */
static char *
getRecoveryStopReason(void)
{
	char		reason[200];

	if (recoveryTarget == RECOVERY_TARGET_XID)
		snprintf(reason, sizeof(reason),
				 "%s transaction %u",
				 recoveryStopAfter ? "after" : "before",
				 recoveryStopXid);
	else if (recoveryTarget == RECOVERY_TARGET_TIME)
		snprintf(reason, sizeof(reason),
				 "%s %s\n",
				 recoveryStopAfter ? "after" : "before",
				 timestamptz_to_str(recoveryStopTime));
	else if (recoveryTarget == RECOVERY_TARGET_LSN)
		snprintf(reason, sizeof(reason),
				 "%s LSN %X/%08X\n",
				 recoveryStopAfter ? "after" : "before",
				 LSN_FORMAT_ARGS(recoveryStopLSN));
	else if (recoveryTarget == RECOVERY_TARGET_NAME)
		snprintf(reason, sizeof(reason),
				 "at restore point \"%s\"",
				 recoveryStopName);
	else if (recoveryTarget == RECOVERY_TARGET_IMMEDIATE)
		snprintf(reason, sizeof(reason), "reached consistency");
	else
		snprintf(reason, sizeof(reason), "no recovery target specified");

	return pstrdup(reason);
}

/*
 * Wait until shared recoveryPauseState is set to RECOVERY_NOT_PAUSED.
 *
 * endOfRecovery is true if the recovery target is reached and
 * the paused state starts at the end of recovery because of
 * recovery_target_action=pause, and false otherwise.
 */
/*
 * 中文注释：
 * 在恢复暂停请求生效时阻塞 startup 进程，直到状态恢复为 RECOVERY_NOT_PAUSED。
 *
 * 只有热备已经激活（用户可以连接并执行 pg_wal_replay_resume）且尚未触发提升时
 * 才真正暂停。endOfRecovery 为 true 表示因 recovery_target_action=pause 在恢复
 * 结束时暂停，提示用户 resume 即触发提升。
 *
 * 循环中处理 startup 进程中断、检查提升触发、调用 ConfirmRecoveryPaused 把
 * REQUESTED 状态确认为 PAUSED，然后在 recoveryNotPausedCV 上带 1 秒超时睡眠；
 * 超时用于周期性重新检查退出条件，而 resume 会 broadcast 条件变量立即唤醒。
 * 退出时取消条件变量睡眠，避免残留等待状态。
 */
static void
recoveryPausesHere(bool endOfRecovery)
{
	/* Don't pause unless users can connect! */
	if (!LocalHotStandbyActive)
		return;

	/* Don't pause after standby promotion has been triggered */
	if (LocalPromoteIsTriggered)
		return;

	if (endOfRecovery)
		ereport(LOG,
				(errmsg("pausing at the end of recovery"),
				 errhint("Execute pg_wal_replay_resume() to promote.")));
	else
		ereport(LOG,
				(errmsg("recovery has paused"),
				 errhint("Execute pg_wal_replay_resume() to continue.")));

	/* loop until recoveryPauseState is set to RECOVERY_NOT_PAUSED */
	while (GetRecoveryPauseState() != RECOVERY_NOT_PAUSED)
	{
		ProcessStartupProcInterrupts();
		if (CheckForStandbyTrigger())
			return;

		/*
		 * If recovery pause is requested then set it paused.  While we are in
		 * the loop, user might resume and pause again so set this every time.
		 */
		ConfirmRecoveryPaused();

		/*
		 * We wait on a condition variable that will wake us as soon as the
		 * pause ends, but we use a timeout so we can check the above exit
		 * condition periodically too.
		 */
		ConditionVariableTimedSleep(&XLogRecoveryCtl->recoveryNotPausedCV, 1000,
									WAIT_EVENT_RECOVERY_PAUSE);
	}
	ConditionVariableCancelSleep();
}

/*
 * When recovery_min_apply_delay is set, we wait long enough to make sure
 * certain record types are applied at least that interval behind the primary.
 *
 * Returns true if we waited.
 *
 * Note that the delay is calculated between the WAL record log time and
 * the current time on standby. We would prefer to keep track of when this
 * standby received each WAL record, which would allow a more consistent
 * approach and one not affected by time synchronisation issues, but that
 * is significantly more effort and complexity for little actual gain in
 * usability.
 */
/*
 * 中文注释：
 * 实现 recovery_min_apply_delay：让备库的提交记录至少落后主库指定时间。
 *
 * 仅对归档恢复、已达到一致性且 recovery_min_apply_delay > 0 的场景生效；只延迟
 * COMMIT/COMMIT_PREPARED，不延迟 ABORT（中止不影响 MVCC 可见性）。延迟基于记录
 * 中的提交时间戳与本地当前时间之差，而不是备库收到 WAL 的时间；函数头注释解释了
 * 这一取舍。
 *
 * 若尚未到时间，在 recoveryWakeupLatch 上等待差值毫秒；循环中处理中断、检查提升
 * 触发，并重新读取 recovery_min_apply_delay（GUC 可能在等待期间被修改）。返回
 * true 表示确实等待过。提升触发会提前结束等待。
 */
static bool
recoveryApplyDelay(XLogReaderState *record)
{
	uint8		xact_info;
	TimestampTz xtime;
	TimestampTz delayUntil;
	long		msecs;

	/* nothing to do if no delay configured */
	if (recovery_min_apply_delay <= 0)
		return false;

	/* no delay is applied on a database not yet consistent */
	if (!reachedConsistency)
		return false;

	/* nothing to do if crash recovery is requested */
	if (!ArchiveRecoveryRequested)
		return false;

	/*
	 * Is it a COMMIT record?
	 *
	 * We deliberately choose not to delay aborts since they have no effect on
	 * MVCC. We already allow replay of records that don't have a timestamp,
	 * so there is already opportunity for issues caused by early conflicts on
	 * standbys.
	 */
	if (XLogRecGetRmid(record) != RM_XACT_ID)
		return false;

	xact_info = XLogRecGetInfo(record) & XLOG_XACT_OPMASK;

	if (xact_info != XLOG_XACT_COMMIT &&
		xact_info != XLOG_XACT_COMMIT_PREPARED)
		return false;

	if (!getRecordTimestamp(record, &xtime))
		return false;

	delayUntil = TimestampTzPlusMilliseconds(xtime, recovery_min_apply_delay);

	/*
	 * Exit without arming the latch if it's already past time to apply this
	 * record
	 */
	msecs = TimestampDifferenceMilliseconds(GetCurrentTimestamp(), delayUntil);
	if (msecs <= 0)
		return false;

	while (true)
	{
		ResetLatch(&XLogRecoveryCtl->recoveryWakeupLatch);

		/* This might change recovery_min_apply_delay. */
		ProcessStartupProcInterrupts();

		if (CheckForStandbyTrigger())
			break;

		/*
		 * Recalculate delayUntil as recovery_min_apply_delay could have
		 * changed while waiting in this loop.
		 */
		delayUntil = TimestampTzPlusMilliseconds(xtime, recovery_min_apply_delay);

		/*
		 * Wait for difference between GetCurrentTimestamp() and delayUntil.
		 */
		msecs = TimestampDifferenceMilliseconds(GetCurrentTimestamp(),
												delayUntil);

		if (msecs <= 0)
			break;

		elog(DEBUG2, "recovery apply delay %ld milliseconds", msecs);

		(void) WaitLatch(&XLogRecoveryCtl->recoveryWakeupLatch,
						 WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
						 msecs,
						 WAIT_EVENT_RECOVERY_APPLY_DELAY);
	}
	return true;
}

/*
 * Get the current state of the recovery pause request.
 */
/*
 * 中文注释：
 * 在 info_lck 下读取共享的 recoveryPauseState 并返回。
 *
 * 状态包括 NOT_PAUSED、PAUSE_REQUESTED、PAUSED。请求方设置 REQUESTED，startup
 * 进程在安全点确认后变为 PAUSED；resume 直接置 NOT_PAUSED 并广播条件变量。
 */
RecoveryPauseState
GetRecoveryPauseState(void)
{
	RecoveryPauseState state;

	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	state = XLogRecoveryCtl->recoveryPauseState;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	return state;
}

/*
 * Set the recovery pause state.
 *
 * If recovery pause is requested then sets the recovery pause state to
 * 'pause requested' if it is not already 'paused'.  Otherwise, sets it
 * to 'not paused' to resume the recovery.  The recovery pause will be
 * confirmed by the ConfirmRecoveryPaused.
 */
/*
 * 中文注释：
 * 请求暂停或恢复 WAL 重放。
 *
 * recoveryPause=false 时无条件把状态置为 NOT_PAUSED 并 broadcast
 * recoveryNotPausedCV，唤醒阻塞在 recoveryPausesHere 的 startup 进程。
 * recoveryPause=true 时仅在当前为 NOT_PAUSED 的情况下把状态改为
 * PAUSE_REQUESTED；若已经请求或已暂停则不重复改变。真正的“已暂停”由 startup
 * 进程调用 ConfirmRecoveryPaused 确认。
 */
void
SetRecoveryPause(bool recoveryPause)
{
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);

	if (!recoveryPause)
		XLogRecoveryCtl->recoveryPauseState = RECOVERY_NOT_PAUSED;
	else if (XLogRecoveryCtl->recoveryPauseState == RECOVERY_NOT_PAUSED)
		XLogRecoveryCtl->recoveryPauseState = RECOVERY_PAUSE_REQUESTED;

	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	if (!recoveryPause)
		ConditionVariableBroadcast(&XLogRecoveryCtl->recoveryNotPausedCV);
}

/*
 * Confirm the recovery pause by setting the recovery pause state to
 * RECOVERY_PAUSED.
 */
/*
 * 中文注释：
 * 由 startup 进程确认暂停请求已经生效。
 *
 * 在 info_lck 下把 PAUSE_REQUESTED 改为 RECOVERY_PAUSED。若用户在此期间已经
 * resume（状态变为 NOT_PAUSED），则保持不变。该函数在 recoveryPausesHere 的
 * 循环中反复调用，以处理“暂停-恢复-再暂停”的竞态。
 */
static void
ConfirmRecoveryPaused(void)
{
	/* If recovery pause is requested then set it paused */
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	if (XLogRecoveryCtl->recoveryPauseState == RECOVERY_PAUSE_REQUESTED)
		XLogRecoveryCtl->recoveryPauseState = RECOVERY_PAUSED;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);
}


/*
 * Attempt to read the next XLOG record.
 *
 * Before first call, the reader needs to be positioned to the first record
 * by calling XLogPrefetcherBeginRead().
 *
 * If no valid record is available, returns NULL, or fails if emode is PANIC.
 * (emode must be either PANIC, LOG). In standby mode, retries until a valid
 * record is available.
 */
/*
 * 中文注释：
 * 通过 prefetcher 读取下一条 WAL 记录，是恢复读取路径的入口。
 *
 * 调用前 reader 必须已由 XLogPrefetcherBeginRead 定位。函数把 emode、
 * fetching_ckpt、randAccess、replayTLI 等参数放入 XLogPageReadPrivate，供底层的
 * XLogPageRead 使用，并清除 lastSourceFailed 表示这是本轮第一次尝试。
 *
 * 循环调用 XLogPrefetcherReadRecord：
 *   - 读到记录后检查其页 TLI 是否在 expectedTLEs 中，不在则按损坏记录处理；
 *   - 读不到时，若发现 WAL 末尾有不完整记录且不是归档恢复，记录
 *     abortedRecPtr/missingContrecPtr，供恢复结束后写 OVERWRITE_CONTRECORD；
 *   - 若尚在崩溃恢复但已请求归档恢复，且不是在取 checkpoint，则切换到归档恢复、
 *     设置 minRecoveryPoint，并重新尝试（先从 pg_wal 读完再进归档）；
 *   - 备库模式下循环重试，直到有记录或触发提升；否则返回 NULL。
 * emode 只能是 PANIC 或 LOG，决定“无有效记录”时是终止还是返回 NULL。
 */
static XLogRecord *
ReadRecord(XLogPrefetcher *xlogprefetcher, int emode,
		   bool fetching_ckpt, TimeLineID replayTLI)
{
	XLogRecord *record;
	XLogReaderState *xlogreader = XLogPrefetcherGetReader(xlogprefetcher);
	XLogPageReadPrivate *private = (XLogPageReadPrivate *) xlogreader->private_data;

	Assert(AmStartupProcess() || !IsUnderPostmaster);

	/* Pass through parameters to XLogPageRead */
	private->fetching_ckpt = fetching_ckpt;
	private->emode = emode;
	private->randAccess = !XLogRecPtrIsValid(xlogreader->ReadRecPtr);
	private->replayTLI = replayTLI;

	/* This is the first attempt to read this page. */
	lastSourceFailed = false;

	for (;;)
	{
		char	   *errormsg;

		record = XLogPrefetcherReadRecord(xlogprefetcher, &errormsg);
		if (record == NULL)
		{
			/*
			 * When we find that WAL ends in an incomplete record, keep track
			 * of that record.  After recovery is done, we'll write a record
			 * to indicate to downstream WAL readers that that portion is to
			 * be ignored.
			 *
			 * However, when ArchiveRecoveryRequested = true, we're going to
			 * switch to a new timeline at the end of recovery. We will only
			 * copy WAL over to the new timeline up to the end of the last
			 * complete record, so if we did this, we would later create an
			 * overwrite contrecord in the wrong place, breaking everything.
			 */
			if (!ArchiveRecoveryRequested &&
				XLogRecPtrIsValid(xlogreader->abortedRecPtr))
			{
				abortedRecPtr = xlogreader->abortedRecPtr;
				missingContrecPtr = xlogreader->missingContrecPtr;
			}

			if (readFile >= 0)
			{
				close(readFile);
				readFile = -1;
			}

			/*
			 * We only end up here without a message when XLogPageRead()
			 * failed - in that case we already logged something. In
			 * StandbyMode that only happens if we have been triggered, so we
			 * shouldn't loop anymore in that case.
			 */
			if (errormsg)
				ereport(emode_for_corrupt_record(emode, xlogreader->EndRecPtr),
						(errmsg_internal("%s", errormsg) /* already translated */ ));
		}

		/*
		 * Check page TLI is one of the expected values.
		 */
		else if (!tliInHistory(xlogreader->latestPageTLI, expectedTLEs))
		{
			char		fname[MAXFNAMELEN];
			XLogSegNo	segno;
			int32		offset;

			XLByteToSeg(xlogreader->latestPagePtr, segno, wal_segment_size);
			offset = XLogSegmentOffset(xlogreader->latestPagePtr,
									   wal_segment_size);
			XLogFileName(fname, xlogreader->seg.ws_tli, segno,
						 wal_segment_size);
			ereport(emode_for_corrupt_record(emode, xlogreader->EndRecPtr),
					errmsg("unexpected timeline ID %u in WAL segment %s, LSN %X/%08X, offset %u",
						   xlogreader->latestPageTLI,
						   fname,
						   LSN_FORMAT_ARGS(xlogreader->latestPagePtr),
						   offset));
			record = NULL;
		}

		if (record)
		{
			/* Great, got a record */
			return record;
		}
		else
		{
			/* No valid record available from this source */
			lastSourceFailed = true;

			/*
			 * If archive recovery was requested, but we were still doing
			 * crash recovery, switch to archive recovery and retry using the
			 * offline archive. We have now replayed all the valid WAL in
			 * pg_wal, so we are presumably now consistent.
			 *
			 * We require that there's at least some valid WAL present in
			 * pg_wal, however (!fetching_ckpt).  We could recover using the
			 * WAL from the archive, even if pg_wal is completely empty, but
			 * we'd have no idea how far we'd have to replay to reach
			 * consistency.  So err on the safe side and give up.
			 */
			if (!InArchiveRecovery && ArchiveRecoveryRequested &&
				!fetching_ckpt)
			{
				ereport(DEBUG1,
						(errmsg_internal("reached end of WAL in pg_wal, entering archive recovery")));
				InArchiveRecovery = true;
				if (StandbyModeRequested)
					EnableStandbyMode();

				SwitchIntoArchiveRecovery(xlogreader->EndRecPtr, replayTLI);
				minRecoveryPoint = xlogreader->EndRecPtr;
				minRecoveryPointTLI = replayTLI;

				CheckRecoveryConsistency();

				/*
				 * Before we retry, reset lastSourceFailed and currentSource
				 * so that we will check the archive next.
				 */
				lastSourceFailed = false;
				currentSource = XLOG_FROM_ANY;

				continue;
			}

			/* In standby mode, loop back to retry. Otherwise, give up. */
			if (StandbyMode && !CheckForStandbyTrigger())
				continue;
			else
				return NULL;
		}
	}
}

/*
 * Read the XLOG page containing targetPagePtr into readBuf (if not read
 * already).  Returns number of bytes read, if the page is read successfully,
 * or XLREAD_FAIL in case of errors.  When errors occur, they are ereport'ed,
 * but only if they have not been previously reported.
 *
 * See XLogReaderRoutine.page_read for more details.
 *
 * While prefetching, xlogreader->nonblocking may be set.  In that case,
 * returns XLREAD_WOULDBLOCK if we'd otherwise have to wait for more WAL.
 *
 * This is responsible for restoring files from archive as needed, as well
 * as for waiting for the requested WAL record to arrive in standby mode.
 *
 * xlogreader->private_data->emode specifies the log level used for reporting
 * "file not found" or "end of WAL" situations in archive recovery, or in
 * standby mode when promotion is triggered. If set to WARNING or below,
 * XLogPageRead() returns XLREAD_FAIL in those situations, on higher log
 * levels the ereport() won't return.
 *
 * In standby mode, if after a successful return of XLogPageRead() the
 * caller finds the record it's interested in to be broken, it should
 * ereport the error with the level determined by
 * emode_for_corrupt_record(), and then set lastSourceFailed
 * and call XLogPageRead() again with the same arguments. This lets
 * XLogPageRead() to try fetching the record from another source, or to
 * sleep and retry.
 */
/*
 * 中文注释：
 * XLogReaderRoutine.page_read 的实现：确保目标 WAL 页可读并读入 readBuf。
 *
 * 这是恢复期间 I/O 的核心：
 *   1. 若请求页不在当前打开的段中，关闭旧文件；归档恢复中若重放过久还会请求
 *      restartpoint，避免 WAL 无限堆积；
 *   2. 若无打开文件、或流式来源的数据尚未 flush 到目标页，调用
 *      WaitForWALToBecomeAvailable 选择/等待来源（归档、pg_wal、流复制）；
 *      非阻塞预取时返回 XLREAD_WOULDBLOCK；
 *   3. 计算本页已可读的长度（流式来源可能只收到半页），pg_pread 读取整页；
 *   4. 记录 I/O 统计和等待事件；短读/错误按损坏记录级别报告，然后关闭文件、
 *      标记 lastSourceFailed；备库模式重试，否则返回 XLREAD_FAIL；
 *   5. 备库模式下额外校验页头：若页是某段第一页且页头无效，立即重试其他来源，
 *      避免读到主库已回收、本地残留的垃圾段。其他情况由 ReadPageInternal 统一
 *      校验。
 * 函数返回实际可用的字节数或 XLREAD_* 结果，并更新 readFile/readSource/
 * curFileTLI 等全局状态。
 */
static int
XLogPageRead(XLogReaderState *xlogreader, XLogRecPtr targetPagePtr, int reqLen,
			 XLogRecPtr targetRecPtr, char *readBuf)
{
	XLogPageReadPrivate *private =
		(XLogPageReadPrivate *) xlogreader->private_data;
	int			emode = private->emode;
	uint32		targetPageOff;
	XLogSegNo	targetSegNo PG_USED_FOR_ASSERTS_ONLY;
	ssize_t		r;
	instr_time	io_start;

	Assert(AmStartupProcess() || !IsUnderPostmaster);

	XLByteToSeg(targetPagePtr, targetSegNo, wal_segment_size);
	targetPageOff = XLogSegmentOffset(targetPagePtr, wal_segment_size);

	/*
	 * See if we need to switch to a new segment because the requested record
	 * is not in the currently open one.
	 */
	if (readFile >= 0 &&
		!XLByteInSeg(targetPagePtr, readSegNo, wal_segment_size))
	{
		/*
		 * Request a restartpoint if we've replayed too much xlog since the
		 * last one.
		 */
		if (ArchiveRecoveryRequested && IsUnderPostmaster)
		{
			if (XLogCheckpointNeeded(readSegNo))
			{
				(void) GetRedoRecPtr();
				if (XLogCheckpointNeeded(readSegNo))
					RequestCheckpoint(CHECKPOINT_CAUSE_XLOG);
			}
		}

		close(readFile);
		readFile = -1;
		readSource = XLOG_FROM_ANY;
	}

	XLByteToSeg(targetPagePtr, readSegNo, wal_segment_size);

retry:
	/* See if we need to retrieve more data */
	if (readFile < 0 ||
		(readSource == XLOG_FROM_STREAM &&
		 flushedUpto < targetPagePtr + reqLen))
	{
		if (readFile >= 0 &&
			xlogreader->nonblocking &&
			readSource == XLOG_FROM_STREAM &&
			flushedUpto < targetPagePtr + reqLen)
			return XLREAD_WOULDBLOCK;

		switch (WaitForWALToBecomeAvailable(targetPagePtr + reqLen,
											private->randAccess,
											private->fetching_ckpt,
											targetRecPtr,
											private->replayTLI,
											xlogreader->EndRecPtr,
											xlogreader->nonblocking))
		{
			case XLREAD_WOULDBLOCK:
				return XLREAD_WOULDBLOCK;
			case XLREAD_FAIL:
				if (readFile >= 0)
					close(readFile);
				readFile = -1;
				readLen = 0;
				readSource = XLOG_FROM_ANY;
				return XLREAD_FAIL;
			case XLREAD_SUCCESS:
				break;
		}
	}

	/*
	 * At this point, we have the right segment open and if we're streaming we
	 * know the requested record is in it.
	 */
	Assert(readFile != -1);

	/*
	 * If the current segment is being streamed from the primary, calculate
	 * how much of the current page we have received already. We know the
	 * requested record has been received, but this is for the benefit of
	 * future calls, to allow quick exit at the top of this function.
	 */
	if (readSource == XLOG_FROM_STREAM)
	{
		if (((targetPagePtr) / XLOG_BLCKSZ) != (flushedUpto / XLOG_BLCKSZ))
			readLen = XLOG_BLCKSZ;
		else
			readLen = XLogSegmentOffset(flushedUpto, wal_segment_size) -
				targetPageOff;
	}
	else
		readLen = XLOG_BLCKSZ;

	/* Read the requested page */
	readOff = targetPageOff;

	/* Measure I/O timing when reading segment */
	io_start = pgstat_prepare_io_time(track_wal_io_timing);

	pgstat_report_wait_start(WAIT_EVENT_WAL_READ);
	r = pg_pread(readFile, readBuf, XLOG_BLCKSZ, (pgoff_t) readOff);
	if (r != XLOG_BLCKSZ)
	{
		char		fname[MAXFNAMELEN];
		int			save_errno = errno;

		pgstat_report_wait_end();

		/* Count I/O stats only for successful short reads */
		if (r > 0)
			pgstat_count_io_op_time(IOOBJECT_WAL, IOCONTEXT_NORMAL, IOOP_READ,
									io_start, 1, r);

		XLogFileName(fname, curFileTLI, readSegNo, wal_segment_size);
		if (r < 0)
		{
			errno = save_errno;
			ereport(emode_for_corrupt_record(emode, targetPagePtr + reqLen),
					(errcode_for_file_access(),
					 errmsg("could not read from WAL segment %s, LSN %X/%08X, offset %u: %m",
							fname, LSN_FORMAT_ARGS(targetPagePtr),
							readOff)));
		}
		else
			ereport(emode_for_corrupt_record(emode, targetPagePtr + reqLen),
					(errcode(ERRCODE_DATA_CORRUPTED),
					 errmsg("could not read from WAL segment %s, LSN %X/%08X, offset %u: read %zd of %zu",
							fname, LSN_FORMAT_ARGS(targetPagePtr),
							readOff, r, (Size) XLOG_BLCKSZ)));
		goto next_record_is_invalid;
	}
	pgstat_report_wait_end();

	pgstat_count_io_op_time(IOOBJECT_WAL, IOCONTEXT_NORMAL, IOOP_READ,
							io_start, 1, r);

	Assert(targetSegNo == readSegNo);
	Assert(targetPageOff == readOff);
	Assert(reqLen <= readLen);

	xlogreader->seg.ws_tli = curFileTLI;

	/*
	 * Check the page header immediately, so that we can retry immediately if
	 * it's not valid. This may seem unnecessary, because ReadPageInternal()
	 * validates the page header anyway, and would propagate the failure up to
	 * ReadRecord(), which would retry. However, there's a corner case with
	 * continuation records, if a record is split across two pages such that
	 * we would need to read the two pages from different sources across two
	 * WAL segments.
	 *
	 * The first page is only available locally, in pg_wal, because it's
	 * already been recycled on the primary. The second page, however, is not
	 * present in pg_wal, and we should stream it from the primary. There is a
	 * recycled WAL segment present in pg_wal, with garbage contents, however.
	 * We would read the first page from the local WAL segment, but when
	 * reading the second page, we would read the bogus, recycled, WAL
	 * segment. If we didn't catch that case here, we would never recover,
	 * because ReadRecord() would retry reading the whole record from the
	 * beginning.
	 *
	 * Of course, this only catches errors in the page header, which is what
	 * happens in the case of a recycled WAL segment. Other kinds of errors or
	 * corruption still has the same problem. But this at least fixes the
	 * common case, which can happen as part of normal operation.
	 *
	 * Validating the page header is cheap enough that doing it twice
	 * shouldn't be a big deal from a performance point of view.
	 *
	 * When not in standby mode, an invalid page header should cause recovery
	 * to end, not retry reading the page, so we don't need to validate the
	 * page header here for the retry. Instead, ReadPageInternal() is
	 * responsible for the validation.
	 */
	if (StandbyMode &&
		(targetPagePtr % wal_segment_size) == 0 &&
		!XLogReaderValidatePageHeader(xlogreader, targetPagePtr, readBuf))
	{
		/*
		 * Emit this error right now then retry this page immediately. Use
		 * errmsg_internal() because the message was already translated.
		 */
		if (xlogreader->errormsg_buf[0])
			ereport(emode_for_corrupt_record(emode, xlogreader->EndRecPtr),
					(errmsg_internal("%s", xlogreader->errormsg_buf)));

		/* reset any error XLogReaderValidatePageHeader() might have set */
		XLogReaderResetError(xlogreader);
		goto next_record_is_invalid;
	}

	return readLen;

next_record_is_invalid:

	/*
	 * If we're reading ahead, give up fast.  Retries and error reporting will
	 * be handled by a later read when recovery catches up to this point.
	 */
	if (xlogreader->nonblocking)
		return XLREAD_WOULDBLOCK;

	lastSourceFailed = true;

	if (readFile >= 0)
		close(readFile);
	readFile = -1;
	readLen = 0;
	readSource = XLOG_FROM_ANY;

	/* In standby-mode, keep trying */
	if (StandbyMode)
		goto retry;
	else
		return XLREAD_FAIL;
}

/*
 * Open the WAL segment containing WAL location 'RecPtr'.
 *
 * The segment can be fetched via restore_command, or via walreceiver having
 * streamed the record, or it can already be present in pg_wal. Checking
 * pg_wal is mainly for crash recovery, but it will be polled in standby mode
 * too, in case someone copies a new segment directly to pg_wal. That is not
 * documented or recommended, though.
 *
 * If 'fetching_ckpt' is true, we're fetching a checkpoint record, and should
 * prepare to read WAL starting from RedoStartLSN after this.
 *
 * 'RecPtr' might not point to the beginning of the record we're interested
 * in, it might also point to the page or segment header. In that case,
 * 'tliRecPtr' is the position of the WAL record we're interested in. It is
 * used to decide which timeline to stream the requested WAL from.
 *
 * 'replayLSN' is the current replay LSN, so that if we scan for new
 * timelines, we can reject a switch to a timeline that branched off before
 * this point.
 *
 * If the record is not immediately available, the function returns XLREAD_FAIL
 * if we're not in standby mode. In standby mode, the function waits for it to
 * become available.
 *
 * When the requested record becomes available, the function opens the file
 * containing it (if not open already), and returns XLREAD_SUCCESS. When end
 * of standby mode is triggered by the user, and there is no more WAL
 * available, returns XLREAD_FAIL.
 *
 * If nonblocking is true, then give up immediately if we can't satisfy the
 * request, returning XLREAD_WOULDBLOCK instead of waiting.
 */
/*
 * 中文注释：
 * 等待并打开包含目标 WAL 位置的段文件，是恢复 WAL 来源状态机的实现。
 *
 * 状态机在归档（XLOG_FROM_ARCHIVE）、本地 pg_wal（XLOG_FROM_PG_WAL）和流复制
 * （XLOG_FROM_STREAM）之间切换：
 *   - 崩溃恢复只读 pg_wal；
 *   - 归档恢复优先归档，再 pg_wal；
 *   - 备库模式在两者都失败后启动/连接 walreceiver，流式等待新 WAL；
 *   - 流失败时关闭 walreceiver，按需重新扫描时间线，然后 sleep
 *     wal_retrieve_retry_interval 后回到归档重试。
 * 每次失败先检查提升触发；一旦触发，仍会尽量把已收到的 WAL 重放完再退出。
 * 非阻塞模式（prefetch readahead）遇到任何需要等待的情况立即返回
 * XLREAD_WOULDBLOCK，由调用者稍后重试。成功打开文件返回 XLREAD_SUCCESS；
 * 非备库且所有来源耗尽返回 XLREAD_FAIL。
 * 函数还负责在 streaming 时设置 XLogReceiptTime、启动 walreceiver 的起始位置
 * （fetching_ckpt 时用 RedoStartLSN）、处理 pendingWalRcvRestart，以及周期性
 * 处理恢复暂停和 startup 进程中断。
 */
static XLogPageReadResult
WaitForWALToBecomeAvailable(XLogRecPtr RecPtr, bool randAccess,
							bool fetching_ckpt, XLogRecPtr tliRecPtr,
							TimeLineID replayTLI, XLogRecPtr replayLSN,
							bool nonblocking)
{
	static TimestampTz last_fail_time = 0;
	TimestampTz now;
	bool		streaming_reply_sent = false;

	/*-------
	 * Standby mode is implemented by a state machine:
	 *
	 * 1. Read from either archive or pg_wal (XLOG_FROM_ARCHIVE), or just
	 *	  pg_wal (XLOG_FROM_PG_WAL)
	 * 2. Check for promotion trigger request
	 * 3. Read from primary server via walreceiver (XLOG_FROM_STREAM)
	 * 4. Rescan timelines
	 * 5. Sleep wal_retrieve_retry_interval milliseconds, and loop back to 1.
	 *
	 * Failure to read from the current source advances the state machine to
	 * the next state.
	 *
	 * 'currentSource' indicates the current state. There are no currentSource
	 * values for "check trigger", "rescan timelines", and "sleep" states,
	 * those actions are taken when reading from the previous source fails, as
	 * part of advancing to the next state.
	 *
	 * If standby mode is turned off while reading WAL from stream, we move
	 * to XLOG_FROM_ARCHIVE and reset lastSourceFailed, to force fetching
	 * the files (which would be required at end of recovery, e.g., timeline
	 * history file) from archive or pg_wal. We don't need to kill WAL receiver
	 * here because it's already stopped when standby mode is turned off at
	 * the end of recovery.
	 *-------
	 */
	if (!InArchiveRecovery)
		currentSource = XLOG_FROM_PG_WAL;
	else if (currentSource == XLOG_FROM_ANY ||
			 (!StandbyMode && currentSource == XLOG_FROM_STREAM))
	{
		lastSourceFailed = false;
		currentSource = XLOG_FROM_ARCHIVE;
	}

	for (;;)
	{
		XLogSource	oldSource = currentSource;
		bool		startWalReceiver = false;

		/*
		 * First check if we failed to read from the current source, and
		 * advance the state machine if so. The failure to read might've
		 * happened outside this function, e.g when a CRC check fails on a
		 * record, or within this loop.
		 */
		if (lastSourceFailed)
		{
			/*
			 * Don't allow any retry loops to occur during nonblocking
			 * readahead.  Let the caller process everything that has been
			 * decoded already first.
			 */
			if (nonblocking)
				return XLREAD_WOULDBLOCK;

			switch (currentSource)
			{
				case XLOG_FROM_ARCHIVE:
				case XLOG_FROM_PG_WAL:

					/*
					 * Check to see if promotion is requested. Note that we do
					 * this only after failure, so when you promote, we still
					 * finish replaying as much as we can from archive and
					 * pg_wal before failover.
					 */
					if (StandbyMode && CheckForStandbyTrigger())
					{
						XLogShutdownWalRcv();
						return XLREAD_FAIL;
					}

					/*
					 * Not in standby mode, and we've now tried the archive
					 * and pg_wal.
					 */
					if (!StandbyMode)
						return XLREAD_FAIL;

					/*
					 * Move to XLOG_FROM_STREAM state, and set to start a
					 * walreceiver if necessary.
					 */
					currentSource = XLOG_FROM_STREAM;
					startWalReceiver = true;
					break;

				case XLOG_FROM_STREAM:

					/*
					 * Failure while streaming. Most likely, we got here
					 * because streaming replication was terminated, or
					 * promotion was triggered. But we also get here if we
					 * find an invalid record in the WAL streamed from the
					 * primary, in which case something is seriously wrong.
					 * There's little chance that the problem will just go
					 * away, but PANIC is not good for availability either,
					 * especially in hot standby mode. So, we treat that the
					 * same as disconnection, and retry from archive/pg_wal
					 * again. The WAL in the archive should be identical to
					 * what was streamed, so it's unlikely that it helps, but
					 * one can hope...
					 */

					/*
					 * We should be able to move to XLOG_FROM_STREAM only in
					 * standby mode.
					 */
					Assert(StandbyMode);

					/*
					 * Before we leave XLOG_FROM_STREAM state, make sure that
					 * walreceiver is not active, so that it won't overwrite
					 * WAL that we restore from archive.
					 *
					 * If walreceiver is actively streaming (or attempting to
					 * connect), we must shut it down. However, if it's
					 * already in WAITING state (e.g., due to timeline
					 * divergence), we only need to reset the install flag to
					 * allow archive restoration.
					 */
					if (WalRcvStreaming())
						XLogShutdownWalRcv();
					else
					{
						/*
						 * WALRCV_STOPPING state is a transient state while
						 * the startup process is in ShutdownWalRcv().  It
						 * should never appear here since we would be waiting
						 * for the walreceiver to reach WALRCV_STOPPED in that
						 * case.
						 */
						Assert(WalRcvGetState() != WALRCV_STOPPING);
						ResetInstallXLogFileSegmentActive();
					}

					/*
					 * Before we sleep, re-scan for possible new timelines if
					 * we were requested to recover to the latest timeline.
					 */
					if (recoveryTargetTimeLineGoal == RECOVERY_TARGET_TIMELINE_LATEST)
					{
						if (rescanLatestTimeLine(replayTLI, replayLSN))
						{
							currentSource = XLOG_FROM_ARCHIVE;
							break;
						}
					}

					/*
					 * XLOG_FROM_STREAM is the last state in our state
					 * machine, so we've exhausted all the options for
					 * obtaining the requested WAL. We're going to loop back
					 * and retry from the archive, but if it hasn't been long
					 * since last attempt, sleep wal_retrieve_retry_interval
					 * milliseconds to avoid busy-waiting.
					 */
					now = GetCurrentTimestamp();
					if (!TimestampDifferenceExceeds(last_fail_time, now,
													wal_retrieve_retry_interval))
					{
						long		wait_time;

						wait_time = wal_retrieve_retry_interval -
							TimestampDifferenceMilliseconds(last_fail_time, now);

						elog(LOG, "waiting for WAL to become available at %X/%08X",
							 LSN_FORMAT_ARGS(RecPtr));

						/* Do background tasks that might benefit us later. */
						KnownAssignedTransactionIdsIdleMaintenance();

						(void) WaitLatch(&XLogRecoveryCtl->recoveryWakeupLatch,
										 WL_LATCH_SET | WL_TIMEOUT |
										 WL_EXIT_ON_PM_DEATH,
										 wait_time,
										 WAIT_EVENT_RECOVERY_RETRIEVE_RETRY_INTERVAL);
						ResetLatch(&XLogRecoveryCtl->recoveryWakeupLatch);
						now = GetCurrentTimestamp();

						/* Handle interrupt signals of startup process */
						ProcessStartupProcInterrupts();
					}
					last_fail_time = now;
					currentSource = XLOG_FROM_ARCHIVE;
					break;

				default:
					elog(ERROR, "unexpected WAL source %d", currentSource);
			}
		}
		else if (currentSource == XLOG_FROM_PG_WAL)
		{
			/*
			 * We just successfully read a file in pg_wal. We prefer files in
			 * the archive over ones in pg_wal, so try the next file again
			 * from the archive first.
			 */
			if (InArchiveRecovery)
				currentSource = XLOG_FROM_ARCHIVE;
		}

		if (currentSource != oldSource)
			elog(DEBUG2, "switched WAL source from %s to %s after %s",
				 xlogSourceNames[oldSource], xlogSourceNames[currentSource],
				 lastSourceFailed ? "failure" : "success");

		/*
		 * We've now handled possible failure. Try to read from the chosen
		 * source.
		 */
		lastSourceFailed = false;

		switch (currentSource)
		{
			case XLOG_FROM_ARCHIVE:
			case XLOG_FROM_PG_WAL:

				/*
				 * WAL receiver must not be running when reading WAL from
				 * archive or pg_wal.
				 */
				Assert(!WalRcvStreaming());

				/* Close any old file we might have open. */
				if (readFile >= 0)
				{
					close(readFile);
					readFile = -1;
				}
				/* Reset curFileTLI if random fetch. */
				if (randAccess)
					curFileTLI = 0;

				/*
				 * Try to restore the file from archive, or read an existing
				 * file from pg_wal.
				 */
				readFile = XLogFileReadAnyTLI(readSegNo,
											  currentSource == XLOG_FROM_ARCHIVE ? XLOG_FROM_ANY :
											  currentSource);
				if (readFile >= 0)
					return XLREAD_SUCCESS;	/* success! */

				/*
				 * Nope, not found in archive or pg_wal.
				 */
				lastSourceFailed = true;
				break;

			case XLOG_FROM_STREAM:
				{
					bool		havedata;

					/*
					 * We should be able to move to XLOG_FROM_STREAM only in
					 * standby mode.
					 */
					Assert(StandbyMode);

					/*
					 * First, shutdown walreceiver if its restart has been
					 * requested -- but no point if we're already slated for
					 * starting it.
					 */
					if (pendingWalRcvRestart && !startWalReceiver)
					{
						XLogShutdownWalRcv();

						/*
						 * Re-scan for possible new timelines if we were
						 * requested to recover to the latest timeline.
						 */
						if (recoveryTargetTimeLineGoal ==
							RECOVERY_TARGET_TIMELINE_LATEST)
							rescanLatestTimeLine(replayTLI, replayLSN);

						startWalReceiver = true;
					}
					pendingWalRcvRestart = false;

					/*
					 * Launch walreceiver if needed.
					 *
					 * If fetching_ckpt is true, RecPtr points to the initial
					 * checkpoint location. In that case, we use RedoStartLSN
					 * as the streaming start position instead of RecPtr, so
					 * that when we later jump backwards to start redo at
					 * RedoStartLSN, we will have the logs streamed already.
					 */
					if (startWalReceiver &&
						PrimaryConnInfo && strcmp(PrimaryConnInfo, "") != 0)
					{
						XLogRecPtr	ptr;
						TimeLineID	tli;

						if (fetching_ckpt)
						{
							ptr = RedoStartLSN;
							tli = RedoStartTLI;
						}
						else
						{
							ptr = RecPtr;

							/*
							 * Use the record begin position to determine the
							 * TLI, rather than the position we're reading.
							 */
							tli = tliOfPointInHistory(tliRecPtr, expectedTLEs);

							if (curFileTLI > 0 && tli < curFileTLI)
								elog(ERROR, "according to history file, WAL location %X/%08X belongs to timeline %u, but previous recovered WAL file came from timeline %u",
									 LSN_FORMAT_ARGS(tliRecPtr),
									 tli, curFileTLI);
						}
						curFileTLI = tli;
						SetInstallXLogFileSegmentActive();
						RequestXLogStreaming(tli, ptr, PrimaryConnInfo,
											 PrimarySlotName,
											 wal_receiver_create_temp_slot);
						flushedUpto = InvalidXLogRecPtr;
					}

					/*
					 * Check if WAL receiver is active or wait to start up.
					 */
					if (!WalRcvStreaming())
					{
						lastSourceFailed = true;
						break;
					}

					/*
					 * Walreceiver is active, so see if new data has arrived.
					 *
					 * We only advance XLogReceiptTime when we obtain fresh
					 * WAL from walreceiver and observe that we had already
					 * processed everything before the most recent "chunk"
					 * that it flushed to disk.  In steady state where we are
					 * keeping up with the incoming data, XLogReceiptTime will
					 * be updated on each cycle. When we are behind,
					 * XLogReceiptTime will not advance, so the grace time
					 * allotted to conflicting queries will decrease.
					 */
					if (RecPtr < flushedUpto)
						havedata = true;
					else
					{
						XLogRecPtr	latestChunkStart;

						flushedUpto = GetWalRcvFlushRecPtr(&latestChunkStart, &receiveTLI);
						if (RecPtr < flushedUpto && receiveTLI == curFileTLI)
						{
							havedata = true;
							if (latestChunkStart <= RecPtr)
							{
								XLogReceiptTime = GetCurrentTimestamp();
								SetCurrentChunkStartTime(XLogReceiptTime);
							}
						}
						else
							havedata = false;
					}
					if (havedata)
					{
						/*
						 * Great, streamed far enough.  Open the file if it's
						 * not open already.  Also read the timeline history
						 * file if we haven't initialized timeline history
						 * yet; it should be streamed over and present in
						 * pg_wal by now.  Use XLOG_FROM_STREAM so that source
						 * info is set correctly and XLogReceiptTime isn't
						 * changed.
						 *
						 * NB: We must set readTimeLineHistory based on
						 * recoveryTargetTLI, not receiveTLI. Normally they'll
						 * be the same, but if recovery_target_timeline is
						 * 'latest' and archiving is configured, then it's
						 * possible that we managed to retrieve one or more
						 * new timeline history files from the archive,
						 * updating recoveryTargetTLI.
						 */
						if (readFile < 0)
						{
							if (!expectedTLEs)
								expectedTLEs = readTimeLineHistory(recoveryTargetTLI);
							readFile = XLogFileRead(readSegNo, receiveTLI,
													XLOG_FROM_STREAM, false);
							Assert(readFile >= 0);
						}
						else
						{
							/* just make sure source info is correct... */
							readSource = XLOG_FROM_STREAM;
							XLogReceiptSource = XLOG_FROM_STREAM;
							return XLREAD_SUCCESS;
						}
						break;
					}

					/* In nonblocking mode, return rather than sleeping. */
					if (nonblocking)
						return XLREAD_WOULDBLOCK;

					/*
					 * Data not here yet. Check for trigger, then wait for
					 * walreceiver to wake us up when new WAL arrives.
					 */
					if (CheckForStandbyTrigger())
					{
						/*
						 * Note that we don't return XLREAD_FAIL immediately
						 * here. After being triggered, we still want to
						 * replay all the WAL that was already streamed. It's
						 * in pg_wal now, so we just treat this as a failure,
						 * and the state machine will move on to replay the
						 * streamed WAL from pg_wal, and then recheck the
						 * trigger and exit replay.
						 */
						lastSourceFailed = true;
						break;
					}

					/*
					 * Since we have replayed everything we have received so
					 * far and are about to start waiting for more WAL, let's
					 * tell the upstream server our replay location now so
					 * that pg_stat_replication doesn't show stale
					 * information.
					 */
					if (!streaming_reply_sent)
					{
						WalRcvRequestApplyReply();
						streaming_reply_sent = true;
					}

					/* Do any background tasks that might benefit us later. */
					KnownAssignedTransactionIdsIdleMaintenance();

					/* Update pg_stat_recovery_prefetch before sleeping. */
					XLogPrefetcherComputeStats(xlogprefetcher);

					/*
					 * Wait for more WAL to arrive, when we will be woken
					 * immediately by the WAL receiver.
					 */
					(void) WaitLatch(&XLogRecoveryCtl->recoveryWakeupLatch,
									 WL_LATCH_SET | WL_EXIT_ON_PM_DEATH,
									 -1L,
									 WAIT_EVENT_RECOVERY_WAL_STREAM);
					ResetLatch(&XLogRecoveryCtl->recoveryWakeupLatch);
					break;
				}

			default:
				elog(ERROR, "unexpected WAL source %d", currentSource);
		}

		/*
		 * Check for recovery pause here so that we can confirm more quickly
		 * that a requested pause has actually taken effect.
		 */
		if (((volatile XLogRecoveryCtlData *) XLogRecoveryCtl)->recoveryPauseState !=
			RECOVERY_NOT_PAUSED)
			recoveryPausesHere(false);

		/*
		 * This possibly-long loop needs to handle interrupts of startup
		 * process.
		 */
		ProcessStartupProcInterrupts();
	}

	return XLREAD_FAIL;			/* not reached */
}


/*
 * Determine what log level should be used to report a corrupt WAL record
 * in the current WAL page, previously read by XLogPageRead().
 *
 * 'emode' is the error mode that would be used to report a file-not-found
 * or legitimate end-of-WAL situation.   Generally, we use it as-is, but if
 * we're retrying the exact same record that we've tried previously, only
 * complain the first time to keep the noise down.  However, we only do when
 * reading from pg_wal, because we don't expect any invalid records in archive
 * or in records streamed from the primary. Files in the archive should be complete,
 * and we should never hit the end of WAL because we stop and wait for more WAL
 * to arrive before replaying it.
 *
 * NOTE: This function remembers the RecPtr value it was last called with,
 * to suppress repeated messages about the same record. Only call this when
 * you are about to ereport(), or you might cause a later message to be
 * erroneously suppressed.
 */
/*
 * 中文注释：
 * 决定损坏 WAL 记录应使用的日志级别，避免对同一位置反复刷屏。
 *
 * 仅当当前来源是 pg_wal 且 emode 为 LOG 时做抑制：若 RecPtr 与上次抱怨的位置
 * 相同，降为 DEBUG1；否则记录该位置并返回原级别。归档和流复制来源不应出现无效
 * 记录，因此不抑制。函数用静态变量保存上次位置，所以只能在即将 ereport 时调用，
 * 否则可能错误地吞掉后续真正需要报告的消息。
 */
static int
emode_for_corrupt_record(int emode, XLogRecPtr RecPtr)
{
	static XLogRecPtr lastComplaint = InvalidXLogRecPtr;

	if (readSource == XLOG_FROM_PG_WAL && emode == LOG)
	{
		if (RecPtr == lastComplaint)
			emode = DEBUG1;
		else
			lastComplaint = RecPtr;
	}
	return emode;
}


/*
 * Subroutine to try to fetch and validate a prior checkpoint record.
 */
/*
 * 中文注释：
 * 读取并验证一个检查点记录，供启动时定位 redo 起点。
 *
 * 先检查 RecPtr 是否落在合法的页内偏移；然后让 prefetcher 从该位置开始读一条
 * 记录（fetching_ckpt=true）。验证：读取成功、rmid 为 RM_XLOG_ID、info 是
 * XLOG_CHECKPOINT_SHUTDOWN 或 ONLINE、记录总长恰好等于
 * XLogRecord + 短数据头 + CheckPoint 结构。任一不满足只记 LOG 并返回 NULL，
 * 由调用者决定 FATAL；成功返回记录指针，CheckPoint 数据可通过
 * XLogRecGetData 取得。
 */
static XLogRecord *
ReadCheckpointRecord(XLogPrefetcher *xlogprefetcher, XLogRecPtr RecPtr,
					 TimeLineID replayTLI)
{
	XLogRecord *record;
	uint8		info;

	Assert(xlogreader != NULL);

	if (!XRecOffIsValid(RecPtr))
	{
		ereport(LOG,
				(errmsg("invalid checkpoint location")));
		return NULL;
	}

	XLogPrefetcherBeginRead(xlogprefetcher, RecPtr);
	record = ReadRecord(xlogprefetcher, LOG, true, replayTLI);

	if (record == NULL)
	{
		ereport(LOG,
				(errmsg("invalid checkpoint record")));
		return NULL;
	}
	if (record->xl_rmid != RM_XLOG_ID)
	{
		ereport(LOG,
				(errmsg("invalid resource manager ID in checkpoint record")));
		return NULL;
	}
	info = record->xl_info & ~XLR_INFO_MASK;
	if (info != XLOG_CHECKPOINT_SHUTDOWN &&
		info != XLOG_CHECKPOINT_ONLINE)
	{
		ereport(LOG,
				(errmsg("invalid xl_info in checkpoint record")));
		return NULL;
	}
	if (record->xl_tot_len != SizeOfXLogRecord + SizeOfXLogRecordDataHeaderShort + sizeof(CheckPoint))
	{
		ereport(LOG,
				(errmsg("invalid length of checkpoint record")));
		return NULL;
	}
	return record;
}

/*
 * Scan for new timelines that might have appeared in the archive since we
 * started recovery.
 *
 * If there are any, the function changes recovery target TLI to the latest
 * one and returns 'true'.
 */
/*
 * 中文注释：
 * 重新扫描归档中是否出现了更新的时间线，用于 recovery_target_timeline=latest。
 *
 * 调用 findNewestTimeLine 找最新 TLI；没有更新直接返回 false。读取新 TLI 的
 * 历史后检查：
 *   - 当前 recoveryTargetTLI 必须出现在新历史中，否则新时间线不是当前系统的
 *     后代，不能切换；
 *   - 分叉点 currentTle->end 不能早于当前重放位置 replayLSN，否则切换后会跳过
 *     尚未重放的历史。
 * 校验通过后更新 recoveryTargetTLI、替换 expectedTLEs、补齐旧目标到新目标之间的
 * 历史文件，并返回 true。replayTLI 用于错误消息，replayLSN 用于分叉点判断。
 */
static bool
rescanLatestTimeLine(TimeLineID replayTLI, XLogRecPtr replayLSN)
{
	List	   *newExpectedTLEs;
	bool		found;
	ListCell   *cell;
	TimeLineID	newtarget;
	TimeLineID	oldtarget = recoveryTargetTLI;
	TimeLineHistoryEntry *currentTle = NULL;

	newtarget = findNewestTimeLine(recoveryTargetTLI);
	if (newtarget == recoveryTargetTLI)
	{
		/* No new timelines found */
		return false;
	}

	/*
	 * Determine the list of expected TLIs for the new TLI
	 */

	newExpectedTLEs = readTimeLineHistory(newtarget);

	/*
	 * If the current timeline is not part of the history of the new timeline,
	 * we cannot proceed to it.
	 */
	found = false;
	foreach(cell, newExpectedTLEs)
	{
		currentTle = (TimeLineHistoryEntry *) lfirst(cell);

		if (currentTle->tli == recoveryTargetTLI)
		{
			found = true;
			break;
		}
	}
	if (!found)
	{
		ereport(LOG,
				(errmsg("new timeline %u is not a child of database system timeline %u",
						newtarget,
						replayTLI)));
		return false;
	}

	/*
	 * The current timeline was found in the history file, but check that the
	 * next timeline was forked off from it *after* the current recovery
	 * location.
	 */
	if (currentTle->end < replayLSN)
	{
		ereport(LOG,
				errmsg("new timeline %u forked off current database system timeline %u before current recovery point %X/%08X",
					   newtarget,
					   replayTLI,
					   LSN_FORMAT_ARGS(replayLSN)));
		return false;
	}

	/* The new timeline history seems valid. Switch target */
	recoveryTargetTLI = newtarget;
	list_free_deep(expectedTLEs);
	expectedTLEs = newExpectedTLEs;

	/*
	 * As in StartupXLOG(), try to ensure we have all the history files
	 * between the old target and new target in pg_wal.
	 */
	restoreTimeLineHistoryFiles(oldtarget + 1, newtarget);

	ereport(LOG,
			(errmsg("new target timeline is %u",
					recoveryTargetTLI)));

	return true;
}


/*
 * Open a logfile segment for reading (during recovery).
 *
 * If source == XLOG_FROM_ARCHIVE, the segment is retrieved from archive.
 * Otherwise, it's assumed to be already available in pg_wal.
 */
/*
 * 中文注释：
 * 打开一个指定段号和时间线的 WAL 段文件用于恢复读取。
 *
 * source 为 XLOG_FROM_ARCHIVE 时调用 RestoreArchivedFile 执行 restore_command，
 * 并写 PS 显示“waiting for ...”；取回后用 KeepFileRestoredFromArchive 原子地
 * 放入 pg_wal，再从新路径打开。source 为 PG_WAL/STREAM 时直接按
 * XLogFilePath 拼路径。
 *
 * 打开成功后更新 curFileTLI、readSource、XLogReceiptSource 和（非流式来源的）
 * XLogReceiptTime，并把 PS 显示改为“recovering ...”。文件不存在且 notfoundOk
 * 时返回 -1；其他错误 PANIC，因为恢复无法安全继续。
 */
static int
XLogFileRead(XLogSegNo segno, TimeLineID tli,
			 XLogSource source, bool notfoundOk)
{
	char		xlogfname[MAXFNAMELEN];
	char		activitymsg[MAXFNAMELEN + 16];
	char		path[MAXPGPATH];
	int			fd;

	XLogFileName(xlogfname, tli, segno, wal_segment_size);

	switch (source)
	{
		case XLOG_FROM_ARCHIVE:
			/* Report recovery progress in PS display */
			snprintf(activitymsg, sizeof(activitymsg), "waiting for %s",
					 xlogfname);
			set_ps_display(activitymsg);

			if (!RestoreArchivedFile(path, xlogfname,
									 "RECOVERYXLOG",
									 wal_segment_size,
									 InRedo))
				return -1;
			break;

		case XLOG_FROM_PG_WAL:
		case XLOG_FROM_STREAM:
			XLogFilePath(path, tli, segno, wal_segment_size);
			break;

		default:
			elog(ERROR, "invalid XLogFileRead source %d", source);
	}

	/*
	 * If the segment was fetched from archival storage, replace the existing
	 * xlog segment (if any) with the archival version.
	 */
	if (source == XLOG_FROM_ARCHIVE)
	{
		Assert(!IsInstallXLogFileSegmentActive());
		KeepFileRestoredFromArchive(path, xlogfname);

		/*
		 * Set path to point at the new file in pg_wal.
		 */
		snprintf(path, MAXPGPATH, XLOGDIR "/%s", xlogfname);
	}

	fd = BasicOpenFile(path, O_RDONLY | PG_BINARY);
	if (fd >= 0)
	{
		/* Success! */
		curFileTLI = tli;

		/* Report recovery progress in PS display */
		snprintf(activitymsg, sizeof(activitymsg), "recovering %s",
				 xlogfname);
		set_ps_display(activitymsg);

		/* Track source of data in assorted state variables */
		readSource = source;
		XLogReceiptSource = source;
		/* In FROM_STREAM case, caller tracks receipt time, not me */
		if (source != XLOG_FROM_STREAM)
			XLogReceiptTime = GetCurrentTimestamp();

		return fd;
	}
	if (errno != ENOENT || !notfoundOk) /* unexpected failure? */
		ereport(PANIC,
				(errcode_for_file_access(),
				 errmsg("could not open file \"%s\": %m", path)));
	return -1;
}

/*
 * Open a logfile segment for reading (during recovery).
 *
 * This version searches for the segment with any TLI listed in expectedTLEs.
 */
/*
 * 中文注释：
 * 在 expectedTLEs 列出的所有时间线中查找并打开指定段号的 WAL 段。
 *
 * 时间线历史按从新到旧遍历；curFileTLI 记录前一个文件的时间线，不允许倒退，
 * 以免父时间线的同名高段号文件覆盖子时间线。若段的起始位置早于某时间线的 begin
 * 段号，说明该段不属于这个时间线，跳过。对每个候选时间线，先按配置尝试归档，
 * 再尝试 pg_wal；找到即返回 fd，并在首次读取历史时把临时列表保存为 expectedTLEs。
 * 全部失败返回 -1，并只对目标时间线路径记 DEBUG2 日志。
 */
static int
XLogFileReadAnyTLI(XLogSegNo segno, XLogSource source)
{
	char		path[MAXPGPATH];
	ListCell   *cell;
	int			fd;
	List	   *tles;

	/*
	 * Loop looking for a suitable timeline ID: we might need to read any of
	 * the timelines listed in expectedTLEs.
	 *
	 * We expect curFileTLI on entry to be the TLI of the preceding file in
	 * sequence, or 0 if there was no predecessor.  We do not allow curFileTLI
	 * to go backwards; this prevents us from picking up the wrong file when a
	 * parent timeline extends to higher segment numbers than the child we
	 * want to read.
	 *
	 * If we haven't read the timeline history file yet, read it now, so that
	 * we know which TLIs to scan.  We don't save the list in expectedTLEs,
	 * however, unless we actually find a valid segment.  That way if there is
	 * neither a timeline history file nor a WAL segment in the archive, and
	 * streaming replication is set up, we'll read the timeline history file
	 * streamed from the primary when we start streaming, instead of
	 * recovering with a dummy history generated here.
	 */
	if (expectedTLEs)
		tles = expectedTLEs;
	else
		tles = readTimeLineHistory(recoveryTargetTLI);

	foreach(cell, tles)
	{
		TimeLineHistoryEntry *hent = (TimeLineHistoryEntry *) lfirst(cell);
		TimeLineID	tli = hent->tli;

		if (tli < curFileTLI)
			break;				/* don't bother looking at too-old TLIs */

		/*
		 * Skip scanning the timeline ID that the logfile segment to read
		 * doesn't belong to
		 */
		if (XLogRecPtrIsValid(hent->begin))
		{
			XLogSegNo	beginseg = 0;

			XLByteToSeg(hent->begin, beginseg, wal_segment_size);

			/*
			 * The logfile segment that doesn't belong to the timeline is
			 * older or newer than the segment that the timeline started or
			 * ended at, respectively. It's sufficient to check only the
			 * starting segment of the timeline here. Since the timelines are
			 * scanned in descending order in this loop, any segments newer
			 * than the ending segment should belong to newer timeline and
			 * have already been read before. So it's not necessary to check
			 * the ending segment of the timeline here.
			 */
			if (segno < beginseg)
				continue;
		}

		if (source == XLOG_FROM_ANY || source == XLOG_FROM_ARCHIVE)
		{
			fd = XLogFileRead(segno, tli, XLOG_FROM_ARCHIVE, true);
			if (fd != -1)
			{
				elog(DEBUG1, "got WAL segment from archive");
				if (!expectedTLEs)
					expectedTLEs = tles;
				return fd;
			}
		}

		if (source == XLOG_FROM_ANY || source == XLOG_FROM_PG_WAL)
		{
			fd = XLogFileRead(segno, tli, XLOG_FROM_PG_WAL, true);
			if (fd != -1)
			{
				if (!expectedTLEs)
					expectedTLEs = tles;
				return fd;
			}
		}
	}

	/* Couldn't find it.  For simplicity, complain about front timeline */
	XLogFilePath(path, recoveryTargetTLI, segno, wal_segment_size);
	errno = ENOENT;
	ereport(DEBUG2,
			(errcode_for_file_access(),
			 errmsg("could not open file \"%s\": %m", path)));
	return -1;
}

/*
 * Set flag to signal the walreceiver to restart.  (The startup process calls
 * this on noticing a relevant configuration change.)
 */
/*
 * 中文注释：
 * 请求重启 walreceiver（例如 primary_conninfo 等配置改变后）。
 *
 * 仅当当前正在从流复制读取且 walreceiver 在运行时设置 pendingWalRcvRestart，
 * 实际关闭/重启由 WaitForWALToBecomeAvailable 在安全点完成；这样不会打断正在
 * 进行的页读取。非流式来源无需处理。
 */
void
StartupRequestWalReceiverRestart(void)
{
	if (currentSource == XLOG_FROM_STREAM && WalRcvRunning())
	{
		ereport(LOG,
				(errmsg("WAL receiver process shutdown requested")));

		pendingWalRcvRestart = true;
	}
}


/*
 * Has a standby promotion already been triggered?
 *
 * Unlike CheckForStandbyTrigger(), this works in any process
 * that's connected to shared memory.
 */
/*
 * 中文注释：
 * 判断是否已经触发备库提升，可在任何连接共享内存的进程中调用。
 *
 * 先用进程本地 LocalPromoteIsTriggered 快速返回；未置位时在 info_lck 下读取共享
 * 的 SharedPromoteIsTriggered 并缓存到本地。提升只能触发一次，因此一旦看到 true
 * 就无需再访问共享内存。
 */
bool
PromoteIsTriggered(void)
{
	/*
	 * We check shared state each time only until a standby promotion is
	 * triggered. We can't trigger a promotion again, so there's no need to
	 * keep checking after the shared variable has once been seen true.
	 */
	if (LocalPromoteIsTriggered)
		return true;

	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	LocalPromoteIsTriggered = XLogRecoveryCtl->SharedPromoteIsTriggered;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	return LocalPromoteIsTriggered;
}

/*
 * 中文注释：
 * 标记提升已触发：在 info_lck 下设置共享标志，调用 SetRecoveryPause(false)
 * 清除暂停状态（否则 pg_get_wal_replay_pause_state 可能在提升过程中仍报告
 * paused），并设置本地缓存。该函数由检测到 promote 信号的 startup 进程调用。
 */
static void
SetPromoteIsTriggered(void)
{
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	XLogRecoveryCtl->SharedPromoteIsTriggered = true;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	/*
	 * Mark the recovery pause state as 'not paused' because the paused state
	 * ends and promotion continues if a promotion is triggered while recovery
	 * is paused. Otherwise pg_get_wal_replay_pause_state() can mistakenly
	 * return 'paused' while a promotion is ongoing.
	 */
	SetRecoveryPause(false);

	LocalPromoteIsTriggered = true;
}

/*
 * Check whether a promote request has arrived.
 */
/*
 * 中文注释：
 * 检查是否收到提升请求，是 startup 进程轮询提升信号的核心。
 *
 * 先看本地标志；否则检查 IsPromoteSignaled（快速共享标志）和
 * CheckPromoteSignal（promote 信号文件是否存在）。两者都满足时记录 LOG、删除
 * 信号文件、清除共享标志、调用 SetPromoteIsTriggered，并返回 true。
 * 该函数在 WAL 读取失败、等待 streaming 数据、恢复暂停循环等多处被调用，确保
 * 用户执行 pg_promote 后能尽快退出恢复。
 */
static bool
CheckForStandbyTrigger(void)
{
	if (LocalPromoteIsTriggered)
		return true;

	if (IsPromoteSignaled() && CheckPromoteSignal())
	{
		ereport(LOG, (errmsg("received promote request")));
		RemovePromoteSignalFiles();
		ResetPromoteSignaled();
		SetPromoteIsTriggered();
		return true;
	}

	return false;
}

/*
 * Remove the files signaling a standby promotion request.
 */
/*
 * 中文注释：
 * 删除 promote 信号文件，表示提升请求已被消费。unlink 失败不检查：文件可能已被
 * 其他路径删除，或稍后由 CheckPromoteSignal 的共享标志阻止重复触发。
 */
void
RemovePromoteSignalFiles(void)
{
	unlink(PROMOTE_SIGNAL_FILE);
}

/*
 * Check to see if a promote request has arrived.
 */
/*
 * 中文注释：
 * 检查 promote 信号文件是否存在。仅做 stat，不读取内容；存在即返回 true。
 * 该文件由 pg_promote 创建，是备库提升的外部触发方式之一。
 */
bool
CheckPromoteSignal(void)
{
	struct stat stat_buf;

	if (stat(PROMOTE_SIGNAL_FILE, &stat_buf) == 0)
		return true;

	return false;
}

/*
 * Wake up startup process to replay newly arrived WAL, or to notice that
 * failover has been requested.
 */
/*
 * 中文注释：
 * 唤醒 startup 进程的恢复闩锁，使其重新检查是否有新 WAL、提升请求或恢复暂停
 * 状态变化。walreceiver 收到新数据、postmaster 处理信号等场景会调用。
 */
void
WakeupRecovery(void)
{
	SetLatch(&XLogRecoveryCtl->recoveryWakeupLatch);
}

/*
 * Schedule a walreceiver wakeup in the main recovery loop.
 */
/*
 * 中文注释：
 * 请求在主恢复循环中让 walreceiver 向上游发送一次已重放位置回复。
 *
 * 只设置 doRequestWalReceiverReply 标志；ApplyWalRecord 在记录重放完成后检查该
 * 标志并调用 WalRcvRequestApplyReply。不能在任意上下文直接唤醒 walreceiver，
 * 因为需要保证 lastReplayedEndRecPtr 已经更新到一致状态。
 */
void
XLogRequestWalReceiverReply(void)
{
	doRequestWalReceiverReply = true;
}

/*
 * Is HotStandby active yet? This is only important in special backends
 * since normal backends won't ever be able to connect until this returns
 * true. Postmaster knows this by way of signal, not via shared memory.
 *
 * Unlike testing standbyState, this works in any process that's connected to
 * shared memory.  (And note that standbyState alone doesn't tell the truth
 * anyway.)
 */
/*
 * 中文注释：
 * 判断热备是否已经激活，可在任何连接共享内存的进程中调用。
 *
 * 先用 LocalHotStandbyActive 快速返回；否则在 info_lck 下读取共享
 * SharedHotStandbyActive 并缓存。热备一旦激活不会撤销，因此本地缓存永远有效。
 * 普通后端在 postmaster 允许连接前不会运行，但特殊进程（如 walsender）需要此
 * 查询来判断能否提供只读查询服务。
 */
bool
HotStandbyActive(void)
{
	/*
	 * We check shared state each time only until Hot Standby is active. We
	 * can't de-activate Hot Standby, so there's no need to keep checking
	 * after the shared variable has once been seen true.
	 */
	if (LocalHotStandbyActive)
		return true;
	else
	{
		/* spinlock is essential on machines with weak memory ordering! */
		SpinLockAcquire(&XLogRecoveryCtl->info_lck);
		LocalHotStandbyActive = XLogRecoveryCtl->SharedHotStandbyActive;
		SpinLockRelease(&XLogRecoveryCtl->info_lck);

		return LocalHotStandbyActive;
	}
}

/*
 * Like HotStandbyActive(), but to be used only in WAL replay code,
 * where we don't need to ask any other process what the state is.
 */
/*
 * 中文注释：
 * 供 WAL 重放代码使用的热备状态查询。
 *
 * 重放代码运行在 startup 进程（或单用户模式）中，直接读本地
 * LocalHotStandbyActive 即可，无需访问共享内存。Assert 用于确保调用上下文正确。
 */
static bool
HotStandbyActiveInReplay(void)
{
	Assert(AmStartupProcess() || !IsPostmasterEnvironment);
	return LocalHotStandbyActive;
}

/*
 * Get latest redo apply position.
 *
 * Exported to allow WALReceiver to read the pointer directly.
 */
/*
 * 中文注释：
 * 返回最后一条已成功重放记录的结束 LSN，可选返回其 TLI。
 *
 * 在 info_lck 下读取 lastReplayedEndRecPtr/lastReplayedTLI，保证两个值一致。
 * 该值表示“已经应用到数据页的 WAL 位置”，供 walreceiver 汇报、检查点判断和
 * 等待 standby replay 的进程使用。若 replayTLI 非 NULL，写入时间线。
 */
XLogRecPtr
GetXLogReplayRecPtr(TimeLineID *replayTLI)
{
	XLogRecPtr	recptr;
	TimeLineID	tli;

	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	recptr = XLogRecoveryCtl->lastReplayedEndRecPtr;
	tli = XLogRecoveryCtl->lastReplayedTLI;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	if (replayTLI)
		*replayTLI = tli;
	return recptr;
}


/*
 * Get position of last applied, or the record being applied.
 *
 * This is different from GetXLogReplayRecPtr() in that if a WAL
 * record is currently being applied, this includes that record.
 */
/*
 * 中文注释：
 * 返回当前正在重放（或最后已重放）记录的结束 LSN，可选返回 TLI。
 *
 * 与 GetXLogReplayRecPtr 的区别：replayEndRecPtr 在记录开始重放前就更新，因此
 * 包含“正在应用”的记录；lastReplayedEndRecPtr 只在成功完成后更新。用于需要
 * 知道恢复已推进到哪条记录的场景，例如 minRecoveryPoint 更新和进度显示。
 */
XLogRecPtr
GetCurrentReplayRecPtr(TimeLineID *replayEndTLI)
{
	XLogRecPtr	recptr;
	TimeLineID	tli;

	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	recptr = XLogRecoveryCtl->replayEndRecPtr;
	tli = XLogRecoveryCtl->replayEndTLI;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	if (replayEndTLI)
		*replayEndTLI = tli;
	return recptr;
}

/*
 * Save timestamp of latest processed commit/abort record.
 *
 * We keep this in XLogRecoveryCtl, not a simple static variable, so that it can be
 * seen by processes other than the startup process.  Note in particular
 * that CreateRestartPoint is executed in the checkpointer.
 */
/*
 * 中文注释：
 * 在 info_lck 下保存最近处理的 commit/abort 记录时间戳到共享
 * recoveryLastXTime。该值供检查点进程（CreateRestartPoint）和其他后端读取，
 * 用于日志中的“最后完成事务时间”以及恢复进度判断。
 */
static void
SetLatestXTime(TimestampTz xtime)
{
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	XLogRecoveryCtl->recoveryLastXTime = xtime;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);
}

/*
 * Fetch timestamp of latest processed commit/abort record.
 */
/*
 * 中文注释：
 * 在 info_lck 下读取最近 commit/abort 记录的时间戳。若尚未处理任何带时间戳的
 * 事务记录，返回 0。恢复结束时用它输出“last completed transaction was at ...”。
 */
TimestampTz
GetLatestXTime(void)
{
	TimestampTz xtime;

	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	xtime = XLogRecoveryCtl->recoveryLastXTime;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	return xtime;
}

/*
 * Save timestamp of the next chunk of WAL records to apply.
 *
 * We keep this in XLogRecoveryCtl, not a simple static variable, so that it can be
 * seen by all backends.
 */
/*
 * 中文注释：
 * 保存当前这批流式 WAL 数据开始到达的时间到共享 currentChunkStartTime。
 *
 * walreceiver 每收到一批新数据时更新，用于计算备库查询的冲突宽限期：如果备库
 * 落后，XLogReceiptTime 不前进，冲突查询获得的额外时间会相应减少。
 */
static void
SetCurrentChunkStartTime(TimestampTz xtime)
{
	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	XLogRecoveryCtl->currentChunkStartTime = xtime;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);
}

/*
 * Fetch timestamp of latest processed commit/abort record.
 * Startup process maintains an accurate local copy in XLogReceiptTime
 */
/*
 * 中文注释：
 * 读取当前这批 WAL 数据开始到达的时间。startup 进程本地另有一份更精确的
 * XLogReceiptTime，此共享值供其他后端使用。
 */
TimestampTz
GetCurrentChunkReplayStartTime(void)
{
	TimestampTz xtime;

	SpinLockAcquire(&XLogRecoveryCtl->info_lck);
	xtime = XLogRecoveryCtl->currentChunkStartTime;
	SpinLockRelease(&XLogRecoveryCtl->info_lck);

	return xtime;
}

/*
 * Returns time of receipt of current chunk of XLOG data, as well as
 * whether it was received from streaming replication or from archives.
 */
/*
 * 中文注释：
 * 返回当前 WAL 数据的接收时间以及来源是否为流复制。
 *
 * 这两个值只保存在 startup 进程的本地变量中（XLogReceiptTime、
 * XLogReceiptSource），因此必须在恢复进程中调用（Assert(InRecovery)）。热备查询
 * 冲突检测用它判断备库落后程度。
 */
void
GetXLogReceiptTime(TimestampTz *rtime, bool *fromStream)
{
	/*
	 * This must be executed in the startup process, since we don't export the
	 * relevant state to shared memory.
	 */
	Assert(InRecovery);

	*rtime = XLogReceiptTime;
	*fromStream = (XLogReceiptSource == XLOG_FROM_STREAM);
}

/*
 * Note that text field supplied is a parameter name and does not require
 * translation
 */
/*
 * 中文注释：
 * 校验备库参数是否不低于主库，避免热备查询因资源不足而出错。
 *
 * currValue 是本地设置，minValue 是主库值。若 currValue < minValue：
 *   - 热备已激活时先 WARNING 并请求暂停，给用户修改配置的机会；暂停循环中若
 *     用户触发提升，则额外 WARNING 说明无法提升，并继续等待 resume；
 *   - 用户 resume 后仍不满足，则 FATAL 终止恢复，提示重启并修改参数。
 * 若热备尚未激活，直接 FATAL。param_name 是 GUC 名，不需要翻译。
 */
void
RecoveryRequiresIntParameter(const char *param_name, int currValue, int minValue)
{
	if (currValue < minValue)
	{
		if (HotStandbyActiveInReplay())
		{
			bool		warned_for_promote = false;

			ereport(WARNING,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("hot standby is not possible because of insufficient parameter settings"),
					 errdetail("%s = %d is a lower setting than on the primary server, where its value was %d.",
							   param_name,
							   currValue,
							   minValue)));

			SetRecoveryPause(true);

			ereport(LOG,
					(errmsg("recovery has paused"),
					 errdetail("If recovery is unpaused, the server will shut down."),
					 errhint("You can then restart the server after making the necessary configuration changes.")));

			while (GetRecoveryPauseState() != RECOVERY_NOT_PAUSED)
			{
				ProcessStartupProcInterrupts();

				if (CheckForStandbyTrigger())
				{
					if (!warned_for_promote)
						ereport(WARNING,
								(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
								 errmsg("promotion is not possible because of insufficient parameter settings"),

						/*
						 * Repeat the detail from above so it's easy to find
						 * in the log.
						 */
								 errdetail("%s = %d is a lower setting than on the primary server, where its value was %d.",
										   param_name,
										   currValue,
										   minValue),
								 errhint("Restart the server after making the necessary configuration changes.")));
					warned_for_promote = true;
				}

				/*
				 * If recovery pause is requested then set it paused.  While
				 * we are in the loop, user might resume and pause again so
				 * set this every time.
				 */
				ConfirmRecoveryPaused();

				/*
				 * We wait on a condition variable that will wake us as soon
				 * as the pause ends, but we use a timeout so we can check the
				 * above conditions periodically too.
				 */
				ConditionVariableTimedSleep(&XLogRecoveryCtl->recoveryNotPausedCV, 1000,
											WAIT_EVENT_RECOVERY_PAUSE);
			}
			ConditionVariableCancelSleep();
		}

		ereport(FATAL,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("recovery aborted because of insufficient parameter settings"),
		/* Repeat the detail from above so it's easy to find in the log. */
				 errdetail("%s = %d is a lower setting than on the primary server, where its value was %d.",
						   param_name,
						   currValue,
						   minValue),
				 errhint("You can restart the server after making the necessary configuration changes.")));
	}
}


/*
 * GUC check_hook for primary_slot_name
 */
/*
 * 中文注释：
 * primary_slot_name GUC 的 check_hook。
 *
 * 空值合法（表示不使用复制槽）。非空时调用
 * ReplicationSlotValidateNameInternal 校验名称长度和字符集；失败时把返回的
 * errcode/errdetail/errhint 转成 GUC 错误并返回 false。
 */
bool
check_primary_slot_name(char **newval, void **extra, GucSource source)
{
	int			err_code;
	char	   *err_msg = NULL;
	char	   *err_hint = NULL;

	if (*newval && strcmp(*newval, "") != 0 &&
		!ReplicationSlotValidateNameInternal(*newval, false, &err_code,
											 &err_msg, &err_hint))
	{
		GUC_check_errcode(err_code);
		GUC_check_errdetail("%s", err_msg);
		if (err_hint != NULL)
			GUC_check_errhint("%s", err_hint);
		return false;
	}

	return true;
}

/*
 * Return the recovery target derived from the recovery_target* settings,
 * raising an error if more than one of them is set.
 */
/*
 * 中文注释：
 * 根据 recovery_target* GUC 推导唯一的恢复目标类型。
 *
 * 通过宏依次检查 recovery_target、recovery_target_lsn/name/time/xid；每发现一个
 * 非空值就计数并记录类型，同时把 GUC 名拼进错误消息。若超过一个目标被设置，
 * FATAL 并列出冲突的参数；否则返回对应类型或 RECOVERY_TARGET_UNSET。
 * 该检查即使未请求恢复也会执行，以便尽早发现配置错误。
 */
static RecoveryTargetType
DetermineRecoveryTargetType(void)
{
	int			ntargets = 0;
	RecoveryTargetType target = RECOVERY_TARGET_UNSET;
	const char *val;
	StringInfoData buf;

	initStringInfo(&buf);

#define ADD_TARGET_IF_SET(gucname, kind) \
	do { \
		val = GetConfigOption(gucname, false, false); \
		if (val[0] != '\0') \
		{ \
			ntargets++; \
			target = (kind); \
			if (buf.len == 0) \
				appendStringInfo(&buf, _("\"%s\""), gucname); \
			else \
				appendStringInfo(&buf, _(", \"%s\""), gucname); \
		} \
	} while (0)

	ADD_TARGET_IF_SET("recovery_target", RECOVERY_TARGET_IMMEDIATE);
	ADD_TARGET_IF_SET("recovery_target_lsn", RECOVERY_TARGET_LSN);
	ADD_TARGET_IF_SET("recovery_target_name", RECOVERY_TARGET_NAME);
	ADD_TARGET_IF_SET("recovery_target_time", RECOVERY_TARGET_TIME);
	ADD_TARGET_IF_SET("recovery_target_xid", RECOVERY_TARGET_XID);
#undef ADD_TARGET_IF_SET

	if (ntargets > 1)
		ereport(FATAL,
				errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				errmsg("cannot specify more than one recovery target"),
				errdetail("Parameters set are: %s.",
						  buf.data));

	pfree(buf.data);

	return target;
}

/*
 * GUC check_hook for recovery_target
 */
/*
 * 中文注释：
 * recovery_target GUC 的 check_hook。
 *
 * 只允许空字符串或 "immediate"：前者表示未设置，后者表示恢复到最早一致点。
 * 其他值返回 false，并通过 GUC_check_errdetail 提示唯一允许值。
 */
bool
check_recovery_target(char **newval, void **extra, GucSource source)
{
	if (strcmp(*newval, "immediate") != 0 && strcmp(*newval, "") != 0)
	{
		GUC_check_errdetail("The only allowed value is \"immediate\".");
		return false;
	}
	return true;
}

/*
 * GUC check_hook for recovery_target_lsn
 */
/*
 * 中文注释：
 * recovery_target_lsn GUC 的 check_hook。
 *
 * 空值合法。非空时用 pg_lsn_in_safe 在“不抛错”模式下解析 LSN；解析失败返回
 * false。成功后用 guc_malloc 分配 XLogRecPtr 作为 extra 数据，供 assign hook
 * 直接取用，避免二次解析。guc_malloc 失败也返回 false。
 */
bool
check_recovery_target_lsn(char **newval, void **extra, GucSource source)
{
	if (strcmp(*newval, "") != 0)
	{
		XLogRecPtr	lsn;
		XLogRecPtr *myextra;
		ErrorSaveContext escontext = {T_ErrorSaveContext};

		lsn = pg_lsn_in_safe(*newval, (Node *) &escontext);
		if (escontext.error_occurred)
			return false;

		myextra = (XLogRecPtr *) guc_malloc(LOG, sizeof(XLogRecPtr));
		if (!myextra)
			return false;
		*myextra = lsn;
		*extra = myextra;
	}
	return true;
}

/*
 * GUC assign_hook for recovery_target_lsn
 */
/*
 * 中文注释：
 * recovery_target_lsn GUC 的 assign_hook。
 *
 * 非空时把 check hook 解析好的 XLogRecPtr 写入全局 recoveryTargetLSN；空值表示
 * 未设置，保持原值（实际不会参与目标判断）。extra 一定非 NULL，因为只有 check
 * 成功才会调用 assign。
 */
void
assign_recovery_target_lsn(const char *newval, void *extra)
{
	if (newval && strcmp(newval, "") != 0)
		recoveryTargetLSN = *((XLogRecPtr *) extra);
}

/*
 * GUC check_hook for recovery_target_name
 */
/*
 * 中文注释：
 * recovery_target_name GUC 的 check_hook。
 *
 * 名称直接使用字符串，只检查长度不超过 MAXFNAMELEN（含结尾 '\\0'）。超长时通过
 * GUC_check_errdetail 报告最大允许字符数并返回 false。restore point 名称最终要
 * 写入时间线历史文件，因此长度限制与文件名一致。
 */
bool
check_recovery_target_name(char **newval, void **extra, GucSource source)
{
	/* Use the value of newval directly */
	if (strlen(*newval) >= MAXFNAMELEN)
	{
		GUC_check_errdetail("\"%s\" is too long (maximum %d characters).",
							"recovery_target_name", MAXFNAMELEN - 1);
		return false;
	}
	return true;
}

/*
 * GUC check_hook for recovery_target_time
 *
 * The interpretation of the recovery_target_time string can depend on the
 * time zone setting, so we need to wait until after all GUC processing is
 * done before we can do the final parsing of the string.  This check function
 * only does a parsing pass to catch syntax errors, but we store the string
 * and parse it again when we need to use it.
 */
/*
 * 中文注释：
 * recovery_target_time GUC 的 check_hook。
 *
 * 此处只做语法校验：拒绝 now/today/tomorrow/yesterday 等相对时间（恢复目标必须
 * 是确定的绝对时间），再用 ParseDateTime/DecodeDateTime/tm2timestamp 解析并检查
 * 范围。真正的最终解析推迟到 validateRecoveryParameters，因为时间解释依赖
 * TimeZone 等 GUC，必须等所有 GUC 处理完成。解析失败返回 false。
 */
bool
check_recovery_target_time(char **newval, void **extra, GucSource source)
{
	if (strcmp(*newval, "") != 0)
	{
		/* reject some special values */
		if (strcmp(*newval, "now") == 0 ||
			strcmp(*newval, "today") == 0 ||
			strcmp(*newval, "tomorrow") == 0 ||
			strcmp(*newval, "yesterday") == 0)
		{
			return false;
		}

		/*
		 * parse timestamp value (see also timestamptz_in())
		 */
		{
			char	   *str = *newval;
			fsec_t		fsec;
			struct pg_tm tt,
					   *tm = &tt;
			int			tz;
			int			dtype;
			int			nf;
			int			dterr;
			char	   *field[MAXDATEFIELDS];
			int			ftype[MAXDATEFIELDS];
			char		workbuf[MAXDATELEN + MAXDATEFIELDS];
			DateTimeErrorExtra dtextra;
			TimestampTz timestamp;

			dterr = ParseDateTime(str, workbuf, sizeof(workbuf),
								  field, ftype, MAXDATEFIELDS, &nf);
			if (dterr == 0)
				dterr = DecodeDateTime(field, ftype, nf,
									   &dtype, tm, &fsec, &tz, &dtextra);
			if (dterr != 0)
				return false;
			if (dtype != DTK_DATE)
				return false;

			if (tm2timestamp(tm, fsec, &tz, &timestamp) != 0)
			{
				GUC_check_errdetail("Timestamp out of range: \"%s\".", str);
				return false;
			}
		}
	}
	return true;
}

/*
 * GUC check_hook for recovery_target_timeline
 */
/*
 * 中文注释：
 * recovery_target_timeline GUC 的 check_hook。
 *
 * "current" 表示使用 pg_control 中的时间线，"latest" 表示沿历史找到最新时间线，
 * 其他值按无符号整数解析为具体时间线号，要求 1..PG_UINT32_MAX。解析结果存入
 * guc_malloc 分配的 extra，供 assign hook 使用。非法数字或越界返回 false。
 */
bool
check_recovery_target_timeline(char **newval, void **extra, GucSource source)
{
	RecoveryTargetTimeLineGoal rttg;
	RecoveryTargetTimeLineGoal *myextra;

	if (strcmp(*newval, "current") == 0)
		rttg = RECOVERY_TARGET_TIMELINE_CONTROLFILE;
	else if (strcmp(*newval, "latest") == 0)
		rttg = RECOVERY_TARGET_TIMELINE_LATEST;
	else
	{
		char	   *endp;
		uint64		timeline;

		rttg = RECOVERY_TARGET_TIMELINE_NUMERIC;

		errno = 0;
		timeline = strtou64(*newval, &endp, 0);

		if (*endp != '\0' || errno == EINVAL || errno == ERANGE)
		{
			GUC_check_errdetail("\"%s\" is not a valid number.",
								"recovery_target_timeline");
			return false;
		}

		if (timeline < 1 || timeline > PG_UINT32_MAX)
		{
			GUC_check_errdetail("\"%s\" must be between %u and %u.",
								"recovery_target_timeline", 1, PG_UINT32_MAX);
			return false;
		}
	}

	myextra = (RecoveryTargetTimeLineGoal *) guc_malloc(LOG, sizeof(RecoveryTargetTimeLineGoal));
	if (!myextra)
		return false;
	*myextra = rttg;
	*extra = myextra;

	return true;
}

/*
 * GUC assign_hook for recovery_target_timeline
 */
/*
 * 中文注释：
 * recovery_target_timeline GUC 的 assign_hook。
 *
 * 把 check hook 计算好的 RecoveryTargetTimeLineGoal 写入全局
 * recoveryTargetTimeLineGoal；若为 numeric 模式，再解析字符串得到
 * recoveryTargetTLIRequested，否则置 0。真正的合法性检查（时间线是否存在）在
 * validateRecoveryParameters 中完成。
 */
void
assign_recovery_target_timeline(const char *newval, void *extra)
{
	recoveryTargetTimeLineGoal = *((RecoveryTargetTimeLineGoal *) extra);
	if (recoveryTargetTimeLineGoal == RECOVERY_TARGET_TIMELINE_NUMERIC)
		recoveryTargetTLIRequested = (TimeLineID) strtoul(newval, NULL, 0);
	else
		recoveryTargetTLIRequested = 0;
}

/*
 * GUC check_hook for recovery_target_xid
 */
/*
 * 中文注释：
 * recovery_target_xid GUC 的 check_hook。
 *
 * 空值合法。非空时先把字符串转成 uint64 再截断为 32 位 TransactionId（允许用户
 * 输入带 epoch 的 FullTransactionId，截断即丢弃 epoch）。校验：没有多余字符、
 * 非负、不是 ERANGE，且结果 >= FirstNormalTransactionId（特殊 XID 不能作为恢复
 * 目标）。成功后用 guc_malloc 保存 TransactionId 到 extra。
 */
bool
check_recovery_target_xid(char **newval, void **extra, GucSource source)
{
	if (strcmp(*newval, "") != 0)
	{
		TransactionId xid;
		TransactionId *myextra;
		char	   *endp;
		char	   *val;

		errno = 0;

		/*
		 * Consume leading whitespace to determine if number is negative
		 */
		val = *newval;

		while (isspace((unsigned char) *val))
			val++;

		/*
		 * This cast will remove the epoch, if any
		 */
		xid = (TransactionId) strtou64(val, &endp, 0);

		if (*endp != '\0' || errno == EINVAL || errno == ERANGE || *val == '-')
		{
			GUC_check_errdetail("\"%s\" is not a valid number.",
								"recovery_target_xid");
			return false;
		}

		if (xid < FirstNormalTransactionId)
		{
			GUC_check_errdetail("\"%s\" without epoch must be greater than or equal to %u.",
								"recovery_target_xid",
								FirstNormalTransactionId);
			return false;
		}

		myextra = (TransactionId *) guc_malloc(LOG, sizeof(TransactionId));
		if (!myextra)
			return false;
		*myextra = xid;
		*extra = myextra;
	}
	return true;
}

/*
 * GUC assign_hook for recovery_target_xid
 */
/*
 * 中文注释：
 * recovery_target_xid GUC 的 assign_hook。
 *
 * 非空时把 check hook 保存的 TransactionId 写入全局 recoveryTargetXid；空值表示
 * 未设置。逻辑复制/PITR 停止判断会在 recoveryStopsBefore/After 中比较该值。
 */
void
assign_recovery_target_xid(const char *newval, void *extra)
{
	if (newval && strcmp(newval, "") != 0)
		recoveryTargetXid = *((TransactionId *) extra);
}
