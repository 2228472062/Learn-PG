/*-------------------------------------------------------------------------
 *
 * bgwriter.c
 *
 * The background writer (bgwriter) is new as of Postgres 8.0.  It attempts
 * to keep regular backends from having to write out dirty shared buffers
 * (which they would only do when needing to free a shared buffer to read in
 * another page).  In the best scenario all writes from shared buffers will
 * be issued by the background writer process.  However, regular backends are
 * still empowered to issue writes if the bgwriter fails to maintain enough
 * clean shared buffers.
 *
 * As of Postgres 9.2 the bgwriter no longer handles checkpoints.
 *
 * Normal termination is by SIGTERM, which instructs the bgwriter to exit(0).
 * Emergency termination is by SIGQUIT; like any backend, the bgwriter will
 * simply abort and exit on SIGQUIT.
 *
 * If the bgwriter exits unexpectedly, the postmaster treats that the same
 * as a backend crash: shared memory may be corrupted, so remaining backends
 * should be killed by SIGQUIT and then a recovery cycle started.
 *
 * 【中文总述】
 * 本文件实现后台写进程（bgwriter，Postgres 8.0 引入）：
 * 它的任务是尽量维持共享缓冲池里有足够的干净缓冲区，
 * 让普通后端进程不必亲自刷脏页（后端只有在自己要腾出缓冲区
 * 读新页、又找不到干净页时才会写盘）。理想情况下，共享缓冲区的
 * 所有写盘动作都应由 bgwriter 发出；但若它没能维持足够的干净页，
 * 普通后端仍被允许自己写盘兜底。
 *
 * 9.2 起 checkpoint 已交给独立的 checkpointer 进程处理，
 * bgwriter 只负责平时的脏页刷盘，不再参与 checkpoint 刷盘。
 * 两者分工：bgwriter 平时勤快地把脏页批量写回磁盘，保证缓冲池
 * 一直有"存货"；checkpointer 只在 checkpoint 时工作，做全量刷盘。
 *
 * 终止方式：SIGTERM 正常退出（exit(0)）；SIGQUIT 紧急退出。
 * 若 bgwriter 意外退出，postmaster 视同后端崩溃处理：
 * 共享内存可能已损坏，先 SIGQUIT 杀掉其余后端，再进入恢复周期。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 *
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/bgwriter.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/xlog.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/auxprocess.h"
#include "postmaster/bgwriter.h"
#include "postmaster/interrupt.h"
#include "storage/aio_subsys.h"
#include "storage/buf_internals.h"
#include "storage/bufmgr.h"
#include "storage/condition_variable.h"
#include "storage/fd.h"
#include "storage/lwlock.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/smgr.h"
#include "storage/standby.h"
#include "utils/memutils.h"
#include "utils/resowner.h"
#include "utils/timestamp.h"
#include "utils/wait_event.h"

/*
 * GUC parameters
 */
/* 【中文】bgwriter 主循环每轮处理完脏页后休眠的毫秒数
 * （GUC 参数 bgwriter_delay，默认 200ms，可配置） */
int			BgWriterDelay = 200;

/*
 * Multiplier to apply to BgWriterDelay when we decide to hibernate.
 * (Perhaps this needs to be configurable?)
 */
/* 【中文】决定进入"冬眠"（hibernation）模式时，把 BgWriterDelay
 * 放大 50 倍再睡（即空闲时一次可睡 200ms × 50 = 10 秒），
 * 减少唤醒次数、降低空闲功耗。*/
#define HIBERNATE_FACTOR			50

/*
 * Interval in which standby snapshots are logged into the WAL stream, in
 * milliseconds.
 */
/* 【中文】周期性把"运行中事务快照"（xl_running_xacts）写入 WAL 的
 * 时间间隔，默认 15 秒一次（见主循环中对应的处理逻辑） */
#define LOG_SNAPSHOT_INTERVAL_MS 15000

/*
 * LSN and timestamp at which we last issued a LogStandbySnapshot(), to avoid
 * doing so too often or repeatedly if there has been no other write activity
 * in the system.
 */
/* 【中文】记录上次 LogStandbySnapshot() 的时间与 LSN，避免系统
 * 没有其它写活动时还反复写快照、白吵醒磁盘。*/
static TimestampTz last_snapshot_ts;
static XLogRecPtr last_snapshot_lsn = InvalidXLogRecPtr;


/*
 * Main entry point for bgwriter process
 *
 * This is invoked from AuxiliaryProcessMain, which has already created the
 * basic execution environment, but not enabled signals yet.
 *
 * 【中文总述】
 * bgwriter 进程的主入口（由 AuxiliaryProcessMain 分发调用，
 * 彼时基本执行环境已就绪，但信号尚未启用）。整体执行阶段：
 *   1. 安装/忽略本进程关心的信号（SIGHUP 重载配置、SIGTERM 请求停机等）
 *   2. 初始化：创建专属内存上下文、初始化写回（writeback）上下文
 *   3. 建立错误恢复现场（sigsetjmp），此后若发生 ERROR 则清理现场重来
 *   4. 进入主循环（for(;;)），每轮做：
 *      a. 处理挂起的信号/中断 → 调用 BgBufferSync() 刷一批脏页
 *      b. 上报统计；若刚完成一次 checkpoint 则销毁所有 smgr 对象
 *      c. 需要时向 WAL 写入 standby 运行事务快照
 *      d. 用 WaitLatch 睡 BgWriterDelay；空闲到一定程度转入
 *         "冬眠"模式（睡得更久，等有后端分配缓冲区时被 latch 唤醒）
 */
void
BackgroundWriterMain(const void *startup_data, size_t startup_data_len)
{
	sigjmp_buf	local_sigjmp_buf;
	MemoryContext bgwriter_context;
	bool		prev_hibernate;
	WritebackContext wb_context;

	Assert(startup_data_len == 0);

	/* 【调用链】AuxiliaryProcessMainCommon()
	 *   → 完成辅助进程的公共初始化：挂接共享内存、初始化 GUC、
	 *     建立 proc 结构（MyProc）、注册到 ProcGlobal 等
	 *   → 相当于"迷你版"后端启动，但不会做连接/事务相关初始化 */
	AuxiliaryProcessMainCommon();

	/*
	 * Properly accept or ignore signals that might be sent to us.
	 * 【中文】逐个设置信号处理方式（本进程的"信号清单"）：
	 * SIGHUP → 重载配置文件；SIGINT/SIGALRM/SIGUSR2 → 忽略；
	 * SIGTERM → 请求停机（置 ShutdownRequestPending）；
	 * SIGUSR1 → procsignal（其它进程发来的请求，如配置重载通知）；
	 * SIGPIPE → 忽略（写管道/套接字出错时不想被杀死）。
	 * SIGQUIT 已在 InitPostmasterChild 里设为立即退出的处理函数。
	 */
	pqsignal(SIGHUP, SignalHandlerForConfigReload);
	pqsignal(SIGINT, PG_SIG_IGN);
	pqsignal(SIGTERM, SignalHandlerForShutdownRequest);
	/* SIGQUIT handler was already set up by InitPostmasterChild */
	pqsignal(SIGALRM, PG_SIG_IGN);
	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, PG_SIG_IGN);

	/*
	 * Reset some signals that are accepted by postmaster but not here
	 * 【中文】SIGCHLD 恢复默认行为：bgwriter 不会 fork 子进程，
	 * 不需要像 postmaster 那样回收子进程，收到 SIGCHLD 直接默认处理。
	 */
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/*
	 * We just started, assume there has been either a shutdown or
	 * end-of-recovery snapshot.
	 * 【中文】刚启动时把"上次快照时间"初始化为当前时刻，
	 * 相当于假设停机/恢复结束时已写过快照，避免启动后立刻重复写。
	 */
	last_snapshot_ts = GetCurrentTimestamp();

	/*
	 * Create a memory context that we will do all our work in.  We do this so
	 * that we can reset the context during error recovery and thereby avoid
	 * possible memory leaks.  Formerly this code just ran in
	 * TopMemoryContext, but resetting that would be a really bad idea.
	 *
	 * 【中文】创建本进程专用的内存上下文 "Background Writer"：
	 * 所有工作都在这里面分配内存，出错恢复时整体 Reset 即可
	 * 清掉泄漏，比直接跑在 TopMemoryContext 上安全得多。
	 */
	bgwriter_context = AllocSetContextCreate(TopMemoryContext,
											 "Background Writer",
											 ALLOCSET_DEFAULT_SIZES);
	MemoryContextSwitchTo(bgwriter_context);

	/* 【调用链】WritebackContextInit()
	 *   → 初始化写回上下文（记录待聚合的 writeback IO 请求，
	 *     攒够 bgwriter_flush_after 页后统一 IssuePendingWritebacks()） */
	WritebackContextInit(&wb_context, &bgwriter_flush_after);

	/*
	 * If an exception is encountered, processing resumes here.
	 *
	 * You might wonder why this isn't coded as an infinite loop around a
	 * PG_TRY construct.  The reason is that this is the bottom of the
	 * exception stack, and so with PG_TRY there would be no exception handler
	 * in force at all during the CATCH part.  By leaving the outermost setjmp
	 * always active, we have at least some chance of recovering from an error
	 * during error recovery.  (If we get into an infinite loop thereby, it
	 * will soon be stopped by overflow of elog.c's internal state stack.)
	 *
	 * Note that we use sigsetjmp(..., 1), so that the prevailing signal mask
	 * (to wit, BlockSig) will be restored when longjmp'ing to here.  Thus,
	 * signals other than SIGQUIT will be blocked until we complete error
	 * recovery.  It might seem that this policy makes the HOLD_INTERRUPTS()
	 * call redundant, but it is not since InterruptPending might be set
	 * already.
	 *
	 * 【中文】这是整个进程最外层的错误恢复点：任何环节抛错
	 * （elog/ereport(ERROR)）都会 longjmp 回到这里。
	 * 不用 PG_TRY 是因为这里是异常栈的最底层，CATCH 期间必须
	 * 保持这个 setjmp 仍然有效，至少还有机会从"错误恢复过程中
	 * 再出错"的情况里二次恢复。
	 */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/* Since not using PG_TRY, must reset error stack by hand */
		/* 【中文】手工重置错误上下文栈（PG_TRY 之外必须自己做） */
		error_context_stack = NULL;

		/* Prevent interrupts while cleaning up */
		/* 【中文】清理期间先屏蔽中断，避免清理到一半被新信号打断 */
		HOLD_INTERRUPTS();

		/* Report the error to the server log */
		/* 【中文】把刚才的错误信息输出到服务器日志 */
		EmitErrorReport();

		/*
		 * These operations are really just a minimal subset of
		 * AbortTransaction().  We don't have very many resources to worry
		 * about in bgwriter, but we do have LWLocks, buffers, and temp files.
		 * 【中文】以下是对 AbortTransaction() 的最小化模拟：
		 * bgwriter 资源少，只需释放 LWLocks、取消条件变量睡眠、
		 * 清理 AIO 缓冲、释放缓冲区和临时文件即可，不必走完整事务回滚。
		 */
		LWLockReleaseAll();
		ConditionVariableCancelSleep();
		pgaio_error_cleanup();
		UnlockBuffers();
		ReleaseAuxProcessResources(false);
		AtEOXact_Buffers(false);
		AtEOXact_SMgr();
		AtEOXact_Files(false);
		AtEOXact_HashTables(false);

		/*
		 * Now return to normal top-level context and clear ErrorContext for
		 * next time.
		 * 【中文】切回专属内存上下文并清空 ErrorContext，
		 * 为下一次错误处理做准备。
		 */
		MemoryContextSwitchTo(bgwriter_context);
		FlushErrorState();

		/* Flush any leaked data in the top-level context */
		/* 【中文】清空专属上下文中泄漏的所有内存（防止累积） */
		MemoryContextReset(bgwriter_context);

		/* re-initialize to avoid repeated errors causing problems */
		/* 【中文】重新初始化写回上下文，避免上次错误留下脏状态 */
		WritebackContextInit(&wb_context, &bgwriter_flush_after);

		/* Now we can allow interrupts again */
		/* 【中文】清理完毕，恢复允许中断 */
		RESUME_INTERRUPTS();

		/*
		 * Sleep at least 1 second after any error.  A write error is likely
		 * to be repeated, and we don't want to be filling the error logs as
		 * fast as we can.
		 * 【中文】出错后至少睡 1 秒再重试：写盘错误往往会连续发生，
		 * 立刻重试只会疯狂刷错误日志。
		 */
		pg_usleep(1000000L);

		/* Report wait end here, when there is no further possibility of wait */
		/* 【中文】确保统计里的等待事件被收尾（不再有可能的等待了） */
		pgstat_report_wait_end();
	}

	/* We can now handle ereport(ERROR) */
	/* 【中文】此后本进程就拥有完整的错误处理能力了 */
	PG_exception_stack = &local_sigjmp_buf;

	/*
	 * Unblock signals (they were blocked when the postmaster forked us)
	 * 【中文】解除信号屏蔽（postmaster fork 我们时信号是屏蔽的，
	 * 现在一切就绪，放开以接收 SIGHUP/SIGTERM 等）
	 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * Reset hibernation state after any error.
	 * 【中文】错误恢复后重置冬眠状态：只有连续两轮都"无事可做"
	 * 才会真正进入冬眠（见主循环中的判断）。
	 */
	prev_hibernate = false;

	/*
	 * Loop forever
	 * 【中文】主循环：每轮刷一批脏页 → 上报统计 → 清理/快照等杂活
	 * → 睡 BgWriterDelay（空闲则加长睡眠进入冬眠），直至收到 SIGTERM。
	 */
	for (;;)
	{
		bool		can_hibernate;
		int			rc;

		/* Clear any already-pending wakeups */
		/* 【中文】清除上次遗留的 latch 唤醒事件，重新开始新一轮等待 */
		ResetLatch(MyLatch);

		/* 【调用链】ProcessMainLoopInterrupts()
		 *   → 处理挂起的信号：SIGHUP 重载配置 / SIGTERM 触发优雅退出
		 *     （proc_exit(0)）等，是"信号异步进来、主循环统一处理"
		 *     模式的处理入口 */
		ProcessMainLoopInterrupts();

		/*
		 * Do one cycle of dirty-buffer writing.
		 * 【中文】本轮的核心工作：批量写出一批脏页。
		 *
		 * 【调用链】BgBufferSync(&wb_context)（storage/buffer/bufmgr.c）
		 *   → 读取 buffer 策略控制块：被"时钟扫描"掠过的位置、
		 *     完成轮数、最近分配数（numBufferAllocs 清零并返回）
		 *   → 结合反馈控制算出本轮要写多少页（bgwriter_lru_maxpages/
		 *     bgwriter_lru_multiplier 动态调节）
		 *   → 环形扫描共享缓冲池，挑脏页 → SyncOneBuffer() 写盘
		 *     （延迟到 writeback 上下文批量下发，减少 IO 次数）
		 *   → 返回 true 表示系统空闲、适合进入冬眠模式
		 */
		can_hibernate = BgBufferSync(&wb_context);

		/* Report pending statistics to the cumulative stats system */
		/* 【中文】向累积统计系统上报本进程的统计（写入页数等）：
		 * pgstat_report_bgwriter() 报 bgwriter 自身，
		 * pgstat_report_wal(true) 顺带上报 WAL 统计 */
		pgstat_report_bgwriter();
		pgstat_report_wal(true);

		if (FirstCallSinceLastCheckpoint())
		{
			/*
			 * After any checkpoint, free all smgr objects.  Otherwise we
			 * would never do so for dropped relations, as the bgwriter does
			 * not process shared invalidation messages or call
			 * AtEOXact_SMgr().
			 */
			/* 【中文】每次 checkpoint 完成后的第一个调用周期里，
			 * 销毁所有 smgr 对象：否则被 DROP 的关系永远得不到
			 * 清理（bgwriter 不处理共享失效消息，也不调用
			 * AtEOXact_SMgr()）。
			 *
			 * 【调用链】FirstCallSinceLastCheckpoint()
			 *   → 检查 CheckpointerShmem->ckpt_done（checkpointer
			 *     每次完成 checkpoint 都会 +1），与本地缓存值比较，
			 *     不等说明刚完成一次 checkpoint（每周期只返回一次 true）
			 *
			 * 【调用链】smgrdestroyall()
			 *   → 遍历 smgr 哈希表，关掉所有仍打开的底层文件
			 *   → 这样被删除关系的数据文件才能被真正删除/回收 */
			smgrdestroyall();
		}

		/*
		 * Log a new xl_running_xacts every now and then so replication can
		 * get into a consistent state faster (think of suboverflowed
		 * snapshots) and clean up resources (locks, KnownXids*) more
		 * frequently. The costs of this are relatively low, so doing it 4
		 * times (LOG_SNAPSHOT_INTERVAL_MS) a minute seems fine.
		 *
		 * We assume the interval for writing xl_running_xacts is
		 * significantly bigger than BgWriterDelay, so we don't complicate the
		 * overall timeout handling but just assume we're going to get called
		 * often enough even if hibernation mode is active. It's not that
		 * important that LOG_SNAPSHOT_INTERVAL_MS is met strictly. To make
		 * sure we're not waking the disk up unnecessarily on an idle system
		 * we check whether there has been any WAL inserted since the last
		 * time we've logged a running xacts.
		 *
		 * We do this logging in the bgwriter as it is the only process that
		 * is run regularly and returns to its mainloop all the time. E.g.
		 * Checkpointer, when active, is barely ever in its mainloop and thus
		 * makes it hard to log regularly.
		 *
		 * 【中文】周期性把 xl_running_xacts 记录写进 WAL：
		 * 好处是复制（逻辑/物理）能更快进入一致状态，也能更频繁地
		 * 清理主库的资源（锁、KnownXids 等）。成本低，默认 4 次/分钟。
		 * 选在 bgwriter 做，因为它是最"守时"、每轮都会回到主循环的进程；
		 * checkpointer 忙的时候几乎不在主循环里，无法规律地写。
		 */
		if (XLogStandbyInfoActive() && !RecoveryInProgress())
		{
			TimestampTz timeout = 0;
			TimestampTz now = GetCurrentTimestamp();

			/* 【中文】下次该写快照的时刻 = 上次写的时刻 + 间隔 */
			timeout = TimestampTzPlusMilliseconds(last_snapshot_ts,
												  LOG_SNAPSHOT_INTERVAL_MS);

			/*
			 * Only log if enough time has passed and interesting records have
			 * been inserted since the last snapshot.  Have to compare with <=
			 * instead of < because GetLastImportantRecPtr() points at the
			 * start of a record, whereas last_snapshot_lsn points just past
			 * the end of the record.
			 *
			 * 【中文】两个条件都满足才写：
			 * 1) 距上次写已超过 LOG_SNAPSHOT_INTERVAL_MS；
			 * 2) 期间有新的"重要"WAL 记录产生（否则快照重复且无意义）。
			 * 注意用 <= 而非 <：GetLastImportantRecPtr() 返回的是
			 * 记录起点，而 last_snapshot_lsn 指向记录末尾之后。
			 */
			if (now >= timeout &&
				last_snapshot_lsn <= GetLastImportantRecPtr())
			{
				/* 【调用链】LogStandbySnapshot()
				 *   → LogCurrentRunningXacts() 把当前运行中事务的快照
				 *     编码成 xl_running_xacts 记录写入 WAL
				 *   → 返回写入后的 LSN，记到静态变量里供下次比较 */
				last_snapshot_lsn = LogStandbySnapshot();
				last_snapshot_ts = now;
			}
		}

		/*
		 * Sleep until we are signaled or BgWriterDelay has elapsed.
		 *
		 * Note: the feedback control loop in BgBufferSync() expects that we
		 * will call it every BgWriterDelay msec.  While it's not critical for
		 * correctness that that be exact, the feedback loop might misbehave
		 * if we stray too far from that.  Hence, avoid loading this process
		 * down with latch events that are likely to happen frequently during
		 * normal operation.
		 *
		 * 【中文】阻塞等待：被信号唤醒（latch 被置位）或
		 * BgWriterDelay 毫秒超时。注意 BgBufferSync() 的反馈控制
		 * 假定我们每 BgWriterDelay 毫秒就被调用一次，所以这里
		 * 不要理会那些日常高频的 latch 事件，避免节奏被打乱。
		 */
		rc = WaitLatch(MyLatch,
					   WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
					   BgWriterDelay /* ms */ , WAIT_EVENT_BGWRITER_MAIN);

		/*
		 * If no latch event and BgBufferSync says nothing's happening, extend
		 * the sleep in "hibernation" mode, where we sleep for much longer
		 * than bgwriter_delay says.  Fewer wakeups save electricity.  When a
		 * backend starts using buffers again, it will wake us up by setting
		 * our latch.  Because the extra sleep will persist only as long as no
		 * buffer allocations happen, this should not distort the behavior of
		 * BgBufferSync's control loop too badly; essentially, it will think
		 * that the system-wide idle interval didn't exist.
		 *
		 * There is a race condition here, in that a backend might allocate a
		 * buffer between the time BgBufferSync saw the alloc count as zero
		 * and the time we call StrategyNotifyBgWriter.  While it's not
		 * critical that we not hibernate anyway, we try to reduce the odds of
		 * that by only hibernating when BgBufferSync says nothing's happening
		 * for two consecutive cycles.  Also, we mitigate any possible
		 * consequences of a missed wakeup by not hibernating forever.
		 *
		 * 【中文】判断是否进入"冬眠"：本轮既没被 latch 唤醒（纯超时）
		 * 且 BgBufferSync 连续两轮都说无事可做，才把睡眠时间
		 * 拉长到 BgWriterDelay × HIBERNATE_FACTOR（约 10 秒），
		 * 减少空闲唤醒次数省电。之后只要某个后端又开始分配缓冲区，
		 * 就会置位我们的 latch 把我们从冬眠中叫醒。
		 * 连睡两轮才冬眠、以及不永久冬眠，都是为了对冲
		 * "刚好在检查后分配缓冲区导致漏唤醒"的竞态。
		 */
		if (rc == WL_TIMEOUT && can_hibernate && prev_hibernate)
		{
			/* Ask for notification at next buffer allocation */
			/* 【中文】登记"下一次分配缓冲区时唤醒我"
			 *
			 * 【调用链】StrategyNotifyBgWriter(MyProcNumber)
			 *   → 把本进程编号写入 StrategyControl->bgwprocno
			 *   → 之后 StrategyGetBuffer()（任何后端分配缓冲区时）
			 *     发现该编号有效，就会 SetLatch() 唤醒我们 */
			StrategyNotifyBgWriter(MyProcNumber);
			/* Sleep ... */
			/* 【中文】长睡（被 latch 唤醒或超时），等待事件记作
			 * BGWRITER_HIBERNATE，便于 pg_stat_activity 观察 */
			(void) WaitLatch(MyLatch,
							 WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
							 BgWriterDelay * HIBERNATE_FACTOR,
							 WAIT_EVENT_BGWRITER_HIBERNATE);
			/* Reset the notification request in case we timed out */
			/* 【中文】睡醒后撤销唤醒登记（超时醒来的情况下，
			 * 不撤的话下次任何后端分配缓冲区都会误唤醒我们） */
			StrategyNotifyBgWriter(-1);
		}

		/* 【中文】记录本轮是否"空闲"，供下一轮判断连续空闲两轮 */
		prev_hibernate = can_hibernate;
	}
}
