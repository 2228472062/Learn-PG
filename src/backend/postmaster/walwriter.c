/*-------------------------------------------------------------------------
 *
 * walwriter.c
 *
 * The WAL writer background process is new as of Postgres 8.3.  It attempts
 * to keep regular backends from having to write out (and fsync) WAL pages.
 * Also, it guarantees that transaction commit records that weren't synced
 * to disk immediately upon commit (ie, were "asynchronously committed")
 * will reach disk within a knowable time --- which, as it happens, is at
 * most three times the wal_writer_delay cycle time.
 *
 * Note that as with the bgwriter for shared buffers, regular backends are
 * still empowered to issue WAL writes and fsyncs when the walwriter doesn't
 * keep up. This means that the WALWriter is not an essential process and
 * can shutdown quickly when requested.
 *
 * Because the walwriter's cycle is directly linked to the maximum delay
 * before async-commit transactions are guaranteed committed, it's probably
 * unwise to load additional functionality onto it.  For instance, if you've
 * got a yen to create xlog segments further in advance, that'd be better done
 * in bgwriter than in walwriter.
 *
 * The walwriter is started by the postmaster as soon as the startup subprocess
 * finishes.  It remains alive until the postmaster commands it to terminate.
 * Normal termination is by SIGTERM, which instructs the walwriter to exit(0).
 * Emergency termination is by SIGQUIT; like any backend, the walwriter will
 * simply abort and exit on SIGQUIT.
 *
 * If the walwriter exits unexpectedly, the postmaster treats that the same
 * as a backend crash: shared memory may be corrupted, so remaining backends
 * should be killed by SIGQUIT and then a recovery cycle started.
 *
 * 【中文总述】
 * 本文件实现 WAL 写进程（walwriter，Postgres 8.3 引入）：
 * 它的任务是替普通后端进程写 WAL 页并 fsync，避免每个后端
 * 都自己刷盘；同时保证"异步提交"（commit 时不立即 fsync）的
 * 事务提交记录，最迟在 3 个 wal_writer_delay 周期内到达磁盘。
 *
 * 与 bgwriter 类似：walwriter 跟不上时，普通后端仍被允许
 * 自己写 WAL、自己 fsync。因此 walwriter 不是必需进程，
 * 收到停机请求可以快速退出。
 *
 * 注意：walwriter 的周期直接决定了异步提交的保证时限，
 * 所以不宜给它加载额外功能（比如预创建 WAL 段这种事
 * 更适合放在 bgwriter 里做）。
 *
 * 生命周期：postmaster 在 startup 子进程结束后就启动它，
 * 一直活到 postmaster 命令它终止。SIGTERM 正常退出（exit(0)），
 * SIGQUIT 紧急退出；意外退出时 postmaster 视同后端崩溃，
 * 会 SIGQUIT 杀掉其余后端并进入恢复周期。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 *
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/walwriter.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>

#include "access/xlog.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/auxprocess.h"
#include "postmaster/interrupt.h"
#include "postmaster/walwriter.h"
#include "storage/aio_subsys.h"
#include "storage/bufmgr.h"
#include "storage/condition_variable.h"
#include "storage/fd.h"
#include "storage/lwlock.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/smgr.h"
#include "utils/hsearch.h"
#include "utils/memutils.h"
#include "utils/resowner.h"
#include "utils/wait_event.h"


/*
 * GUC parameters
 */
/* 【中文】walwriter 主循环每轮处理完 WAL 后休眠的毫秒数
 * （GUC 参数 wal_writer_delay，默认 200ms） */
int			WalWriterDelay = 200;
/* 【中文】WAL 中待刷未刷的块数超过该阈值就立刻 flush
 * （GUC 参数 wal_writer_flush_after，默认取自宏
 * DEFAULT_WAL_WRITER_FLUSH_AFTER），不必等周期到点 */
int			WalWriterFlushAfter = DEFAULT_WAL_WRITER_FLUSH_AFTER;

/*
 * Number of do-nothing loops before lengthening the delay time, and the
 * multiplier to apply to WalWriterDelay when we do decide to hibernate.
 * (Perhaps these need to be configurable?)
 */
/* 【中文】连续 LOOPS_UNTIL_HIBERNATE 轮（50 轮）都没活干时，
 * 把睡眠时间拉长到 WalWriterDelay × HIBERNATE_FACTOR（25 倍，
 * 即 200ms × 25 = 5 秒），降低空闲功耗。
 * LOOPS_UNTIL_HIBERNATE 还兼作"冬眠倒计时"。*/
#define LOOPS_UNTIL_HIBERNATE		50
#define HIBERNATE_FACTOR			25

/*
 * Main entry point for walwriter process
 *
 * This is invoked from AuxiliaryProcessMain, which has already created the
 * basic execution environment, but not enabled signals yet.
 *
 * 【中文总述】
 * walwriter 进程的主入口（由 AuxiliaryProcessMain 分发调用）。
 * 整体执行阶段：
 *   1. 安装/忽略本进程关心的信号（SIGHUP 重载配置、SIGTERM 停机等）
 *   2. 创建专属内存上下文
 *   3. 建立错误恢复现场（sigsetjmp），发生 ERROR 时清理现场重来
 *   4. 进入主循环（for(;;)），每轮做：
 *      a. 提前广播"本轮是否可能冬眠"（供异步提交的后端决定
 *         是否需要在提交时置位 latch 叫醒我们）
 *      b. 处理挂起的信号/中断
 *      c. 调用 XLogBackgroundFlush()：把已积攒的 WAL 写出并
 *         （必要时）fsync —— 这正是异步提交记录落盘的保证
 *      d. 上报统计；按"是否有活干"决定睡眠时长
 *         （正常 200ms；连续 50 轮无事则进入 5 秒长眠）
 *
 * WAL 写盘时机（本进程的两个触发点）：
 *   - 定期 flush：每 wal_writer_delay 毫秒由本循环调用
 *     XLogBackgroundFlush() 兜底刷一次；
 *   - 被请求立即 flush：后端提交异步事务时若发现本进程正在冬眠，
 *     会 SetLatch() 唤醒我们，下一轮循环立刻补刷。
 */
void
WalWriterMain(const void *startup_data, size_t startup_data_len)
{
	sigjmp_buf	local_sigjmp_buf;
	MemoryContext walwriter_context;
	int			left_till_hibernate;
	bool		hibernating;

	Assert(startup_data_len == 0);

	/* 【调用链】AuxiliaryProcessMainCommon()
	 *   → 完成辅助进程的公共初始化：挂接共享内存、初始化 GUC、
	 *     建立 proc 结构（MyProc）、注册到 ProcGlobal 等
	 *   → 相当于"迷你版"后端启动，但不会做连接/事务相关初始化 */
	AuxiliaryProcessMainCommon();

	/*
	 * Properly accept or ignore signals the postmaster might send us
	 * 【中文】信号清单与 bgwriter 基本一致：
	 * SIGHUP → 重载配置；SIGINT → 忽略（没有查询可取消）；
	 * SIGTERM → 请求停机；SIGUSR1 → procsignal 通知；
	 * SIGALRM/SIGPIPE/SIGUSR2 → 忽略。
	 * SIGQUIT 已在 InitPostmasterChild 里设置。
	 */
	pqsignal(SIGHUP, SignalHandlerForConfigReload);
	pqsignal(SIGINT, PG_SIG_IGN);	/* no query to cancel */
	pqsignal(SIGTERM, SignalHandlerForShutdownRequest);
	/* SIGQUIT handler was already set up by InitPostmasterChild */
	pqsignal(SIGALRM, PG_SIG_IGN);
	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, PG_SIG_IGN);	/* not used */

	/*
	 * Reset some signals that are accepted by postmaster but not here
	 * 【中文】SIGCHLD 恢复默认行为：本进程不 fork 子进程，
	 * 不需要像 postmaster 那样回收子进程。
	 */
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/*
	 * Create a memory context that we will do all our work in.  We do this so
	 * that we can reset the context during error recovery and thereby avoid
	 * possible memory leaks.  Formerly this code just ran in
	 * TopMemoryContext, but resetting that would be a really bad idea.
	 *
	 * 【中文】创建本进程专用的内存上下文 "Wal Writer"：
	 * 出错恢复时整体 Reset 即可清掉所有泄漏内存，
	 * 比直接跑在 TopMemoryContext 上安全。
	 */
	walwriter_context = AllocSetContextCreate(TopMemoryContext,
											  "Wal Writer",
											  ALLOCSET_DEFAULT_SIZES);
	MemoryContextSwitchTo(walwriter_context);

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
	 * 【中文】最外层错误恢复点：任何环节抛错都会 longjmp 回到这里。
	 * 不用 PG_TRY 是因为这是异常栈的最底层，CATCH 期间必须保持
	 * 这个 setjmp 仍然有效，才有机会从"错误恢复过程中再出错"恢复。
	 */
	if (sigsetjmp(local_sigjmp_buf, 1) != 0)
	{
		/* Since not using PG_TRY, must reset error stack by hand */
		/* 【中文】手工重置错误上下文栈（PG_TRY 之外必须自己做） */
		error_context_stack = NULL;

		/* Prevent interrupts while cleaning up */
		/* 【中文】清理期间屏蔽中断，防止清理到一半被打断 */
		HOLD_INTERRUPTS();

		/* Report the error to the server log */
		/* 【中文】把错误信息输出到服务器日志 */
		EmitErrorReport();

		/*
		 * These operations are really just a minimal subset of
		 * AbortTransaction().  We don't have very many resources to worry
		 * about in walwriter, but we do have LWLocks, and perhaps buffers?
		 * 【中文】对 AbortTransaction() 的最小化模拟：walwriter 资源少，
		 * 只需释放 LWLocks、取消条件变量睡眠、清理 AIO 与缓冲区即可。
		 */
		LWLockReleaseAll();
		ConditionVariableCancelSleep();
		pgstat_report_wait_end();
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
		 * 【中文】切回专属上下文并清空 ErrorContext，为下次错误做准备。
		 */
		MemoryContextSwitchTo(walwriter_context);
		FlushErrorState();

		/* Flush any leaked data in the top-level context */
		/* 【中文】清空专属上下文中泄漏的所有内存（防止累积） */
		MemoryContextReset(walwriter_context);

		/* Now we can allow interrupts again */
		/* 【中文】清理完毕，恢复允许中断 */
		RESUME_INTERRUPTS();

		/*
		 * Sleep at least 1 second after any error.  A write error is likely
		 * to be repeated, and we don't want to be filling the error logs as
		 * fast as we can.
		 * 【中文】出错后至少睡 1 秒再重试，避免疯狂刷错误日志。
		 */
		pg_usleep(1000000L);
	}

	/* We can now handle ereport(ERROR) */
	/* 【中文】此后本进程就拥有完整的错误处理能力了 */
	PG_exception_stack = &local_sigjmp_buf;

	/*
	 * Unblock signals (they were blocked when the postmaster forked us)
	 * 【中文】解除信号屏蔽（fork 时是屏蔽的），开始接收信号。
	 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * Reset hibernation state after any error.
	 * 【中文】错误恢复后重置冬眠状态：倒计时重新从 50 轮开始，
	 * 并声明本进程当前未在冬眠。
	 */
	left_till_hibernate = LOOPS_UNTIL_HIBERNATE;
	hibernating = false;
	/* 【调用链】SetWalWriterSleeping(false)
	 *   → 加自旋锁更新 XLogCtl->WalWriterSleeping 标志
	 *   → 后端异步提交时会读这个标志：若 walwriter 在冬眠，
	 *     则提交后必须置位 latch 把 walwriter 叫醒补刷 */
	SetWalWriterSleeping(false);

	/*
	 * Loop forever
	 * 【中文】主循环：flush WAL → 上报统计 → 睡眠
	 * （忙时 200ms 一轮，连续 50 轮无事则拉长到 5 秒冬眠），
	 * 直至收到 SIGTERM 停机。
	 */
	for (;;)
	{
		long		cur_timeout;

		/*
		 * Advertise whether we might hibernate in this cycle.  We do this
		 * before resetting the latch to ensure that any async commits will
		 * see the flag set if they might possibly need to wake us up, and
		 * that we won't miss any signal they send us.  (If we discover work
		 * to do in the last cycle before we would hibernate, the global flag
		 * will be set unnecessarily, but little harm is done.)  But avoid
		 * touching the global flag if it doesn't need to change.
		 *
		 * 【中文】先广播"本轮是否可能进入冬眠"（冬眠标志 + 共享
		 * 内存里的 WalWriterSleeping）。必须在 ResetLatch 之前做：
		 * 保证可能在下一轮需要唤醒我们的异步提交，能看到标志
		 * 并提前置位 latch，避免漏掉。若下一轮发现其实有活干，
		 * 也只是标志多设了一轮，无伤大雅。
		 */
		if (hibernating != (left_till_hibernate <= 1))
		{
			hibernating = (left_till_hibernate <= 1);
			SetWalWriterSleeping(hibernating);
		}

		/* Clear any already-pending wakeups */
		/* 【中文】清除上次遗留的 latch 唤醒事件，开始新一轮等待 */
		ResetLatch(MyLatch);

		/* Process any signals received recently */
		/* 【调用链】ProcessMainLoopInterrupts()
		 *   → 处理挂起的信号：SIGHUP 重载配置 / SIGTERM 优雅退出等 */
		ProcessMainLoopInterrupts();

		/*
		 * Do what we're here for; then, if XLogBackgroundFlush() found useful
		 * work to do, reset hibernation counter.
		 * 【中文】干正事：把 WAL 刷到磁盘；若这次确实做了有用功
		 * （有可写的 WAL），就把冬眠倒计时重置回 50，
		 * 否则倒计时减一（减到 0 就进入长眠）。
		 *
		 * 【调用链】XLogBackgroundFlush()（access/transam/xlog.c）
		 *   → 恢复中直接返回 false（不需要刷 WAL）
		 *   → 读取共享内存中的写请求 LSN（LogwrtRqst），回退到
		 *     最后一个完整页边界
		 *   → 若还没刷到那里，则取 asyncXactLSN（最新异步提交的
		 *     事务结束记录位置）继续补齐
		 *   → 确实有内容要写时：调用 XLogWrite() 把 WAL 缓冲写出；
		 *     fsync 只在满足条件时才做——距上次 flush 超过
		 *     wal_writer_delay 毫秒，或积压的未刷块数超过
		 *     wal_writer_flush_after 块（避免高频 fsync 影响并发 IO）
		 *   → 返回 true 表示本轮有活干（即使因节流没实际 fsync）
		 */
		if (XLogBackgroundFlush())
			left_till_hibernate = LOOPS_UNTIL_HIBERNATE;
		else if (left_till_hibernate > 0)
			left_till_hibernate--;

		/* report pending statistics to the cumulative stats system */
		/* 【中文】向累积统计系统上报本进程的统计
		 * （写入/刷新的 WAL 字节数等） */
		pgstat_report_wal(false);

		/*
		 * Sleep until we are signaled or WalWriterDelay has elapsed.  If we
		 * haven't done anything useful for quite some time, lengthen the
		 * sleep time so as to reduce the server's idle power consumption.
		 * 【中文】计算本轮睡眠时长：倒计时没到 0 就按正常
		 * WalWriterDelay（200ms）睡；到 0 说明长期空闲，
		 * 按 WalWriterDelay × HIBERNATE_FACTOR（5 秒）长眠。
		 */
		if (left_till_hibernate > 0)
			cur_timeout = WalWriterDelay;	/* in ms */
		else
			cur_timeout = WalWriterDelay * HIBERNATE_FACTOR;

		/* 【中文】阻塞等待：被 latch 唤醒（如异步提交要我们补刷）、
		 * 超时或 postmaster 死亡。等待事件记作 WAL_WRITER_MAIN */
		(void) WaitLatch(MyLatch,
						 WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
						 cur_timeout,
						 WAIT_EVENT_WAL_WRITER_MAIN);
	}
}
