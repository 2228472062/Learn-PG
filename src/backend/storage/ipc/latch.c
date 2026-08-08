/*-------------------------------------------------------------------------
 *
 * latch.c
 *	  Routines for inter-process latches
 *
 * The latch interface is a reliable replacement for the common pattern of
 * using pg_usleep() or select() to wait until a signal arrives, where the
 * signal handler sets a flag variable.  See latch.h for more information
 * on how to use them.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的 latch(门闩)原语:一种进程内/跨进程的
 * "唤醒"机制,用于可靠地替代"信号处理函数里置个标志位 + pg_usleep()/
 * select() 轮询"这种老式写法(那会丢失"置位与等待之间"到达的信号)。
 *
 * 【核心机制】
 * - Latch 结构(见 latch.h)含 is_set(是否已置位)、maybe_sleeping(是否
 *   可能有人正睡在上面)、owner_pid(持有者,共享 latch 才有意义)等
 *   字段。关键性质:
 *   1) SetLatch() 与 ResetLatch()/等待动作之间用内存屏障(pg_memory_
 *      barrier)保证顺序,置位者必须先落盘自己的状态、等待者必须先
 *      读走别人的状态,绝不错序;
 *   2) SetLatch() 可在信号处理函数或临界区里调用(不抛错、无锁);
 *   3) 唤醒另一个进程通过 SIGUSR1(信号语义与并发容忍度见 SetLatch
 *      注释);同进程自唤醒走"自管道/自信号"。
 * - 等待侧基于 WaitEventSet(见 waiteventset.c,底层是 poll()/epoll(),
 *   Windows 用 WaitForMultipleObjects):WaitLatch() 复用模块级静态
 *   WaitEventSet,WaitLatchOrSocket() 则临时建一个并附加 socket。
 * - 配套的还有 PM death 事件:postmaster 管理的进程等待时,要么请求
 *   "postmaster 死亡则自动退出"(WL_EXIT_ON_PM_DEATH),要么请求把
 *   "postmaster 已死"作为唤醒条件返回(WL_POSTMASTER_DEATH)。
 *
 * 【使用约定】进程私有 latch 用 InitLatch() 初始化即可用;共享 latch
 * 必须由 postmaster 在 fork 前 InitSharedLatch(),子进程再 OwnLatch()
 * 认领。等待方必须"循环底部等待"(wait-at-bottom):先 ResetLatch 再
 * 干活,循环末尾再 WaitLatch,这样"等待之前恰好到达的置位"不会被漏掉。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/latch.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "miscadmin.h"
#include "port/atomics.h"
#include "storage/latch.h"
#include "storage/waiteventset.h"
#include "utils/resowner.h"

/* A common WaitEventSet used to implement WaitLatch() */
/* (中文)实现 WaitLatch() 的公共 WaitEventSet:模块级静态对象,由
 * InitializeLatchWaitSet() 建立,两个槽位分别登记 latch 事件与 PM
 * 死亡事件。复用它避免了每次 WaitLatch 都重建/销毁事件集合的开销。 */
static WaitEventSet *LatchWaitSet;

/* The positions of the latch and PM death events in LatchWaitSet */
/* (中文)LatchWaitSet 里两个事件槽位的固定下标:
 * - LatchWaitSetLatchPos(0)        :latch 事件(每次 WaitLatch 经
 *   ModifyWaitEvent 换成本次要等的 latch);
 * - LatchWaitSetPostmasterDeathPos(1):postmaster 死亡事件(每次按
 *   wakeEvents 修改为 WL_EXIT_ON_PM_DEATH 或 WL_POSTMASTER_DEATH)。 */
#define LatchWaitSetLatchPos 0
#define LatchWaitSetPostmasterDeathPos 1

/*
 * InitializeLatchWaitSet - (中文)建立 WaitLatch() 使用的公共 WaitEventSet
 *
 * 【作用】启动早期调用一次:创建容量为 2 的 WaitEventSet,把 latch 事件
 * 固定在槽位 0;若本进程是 postmaster 的子进程,再注册 postmaster 死亡
 * 事件到槽位 1。
 *
 * 【设计思想】WaitLatch() 每次调用都要支持"等不同 latch / 不同死亡
 * 处理方式",所以用 ModifyWaitEvent 就地修改这两个槽位,而不是重建
 * 集合。槽位下标通过断言与宏保持一致,防止顺序错乱。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
InitializeLatchWaitSet(void)
{
	int			latch_pos PG_USED_FOR_ASSERTS_ONLY;

	Assert(LatchWaitSet == NULL);

	/* Set up the WaitEventSet used by WaitLatch(). */
	LatchWaitSet = CreateWaitEventSet(NULL, 2);
	latch_pos = AddWaitEventToSet(LatchWaitSet, WL_LATCH_SET, PGINVALID_SOCKET,
								  MyLatch, NULL);
	Assert(latch_pos == LatchWaitSetLatchPos);

	/*
	 * WaitLatch will modify this to WL_EXIT_ON_PM_DEATH or
	 * WL_POSTMASTER_DEATH on each call.
	 */
	if (IsUnderPostmaster)
	{
		latch_pos = AddWaitEventToSet(LatchWaitSet, WL_EXIT_ON_PM_DEATH,
									  PGINVALID_SOCKET, NULL, NULL);
		Assert(latch_pos == LatchWaitSetPostmasterDeathPos);
	}
}

/*
 * Initialize a process-local latch.
 */
/*
 * InitLatch - (中文)初始化一个进程私有的 latch
 *
 * 【作用】把 latch 各字段置初值:is_set/maybe_sleeping 清零、owner_pid
 * 设为本进程(私有 latch 天然归属本进程)、is_shared 置 false;Windows
 * 下额外创建内核事件对象(自动复位事件),供 WaitForMultipleObjects 用。
 *
 * 【设计思想】进程私有 latch 不需要跨进程同步,owner_pid 记成本进程
 * 只是为了满足"只有 owner 才能 ResetLatch"的断言。注意 InitLatch
 * 只能在 fork 之后做,私有 latch 不应被其他进程触碰。
 *
 * 【参数】latch —— 待初始化的 Latch 结构(通常在进程私有内存或
 * PGPROC 里)。
 * 【返回值】无。
 */
void
InitLatch(Latch *latch)
{
	latch->is_set = false;
	latch->maybe_sleeping = false;
	latch->owner_pid = MyProcPid;
	latch->is_shared = false;

#ifdef WIN32
	latch->event = CreateEvent(NULL, TRUE, FALSE, NULL);
	if (latch->event == NULL)
		elog(ERROR, "CreateEvent failed: error code %lu", GetLastError());
#endif							/* WIN32 */
}

/*
 * Initialize a shared latch that can be set from other processes. The latch
 * is initially owned by no-one; use OwnLatch to associate it with the
 * current process.
 *
 * InitSharedLatch needs to be called in postmaster before forking child
 * processes, usually right after initializing the shared memory block
 * containing the latch. (The Unix implementation doesn't actually require
 * that, but the Windows one does.) Because of this restriction, we have no
 * concurrency issues to worry about here.
 *
 * Note that other handles created in this module are never marked as
 * inheritable.  Thus we do not need to worry about cleaning up child
 * process references to postmaster-private latches or WaitEventSets.
 */
/*
 * InitSharedLatch - (中文)初始化一个可被其他进程置位的共享 latch
 *
 * 【作用】把 latch 置为"共享"初值:is_set/maybe_sleeping 清零、
 * owner_pid 置 0(尚无人认领)、is_shared 置 true;Windows 下创建
 * 可继承的内核事件对象。
 *
 * 【设计思想】必须在 postmaster fork 任何子进程之前调用(通常紧随共享
 * 内存块初始化之后):Unix 实现其实不强制,但 Windows 实现要求事件句柄
 * 在 fork/exec 前创建以便子进程继承。因此本函数不会遇到并发问题。
 * 初始化后由某个进程(通常是 postmaster 自己)经 OwnLatch() 认领。
 *
 * 【参数】latch —— 位于共享内存中的 Latch 结构。
 * 【返回值】无。
 */
void
InitSharedLatch(Latch *latch)
{
#ifdef WIN32
	SECURITY_ATTRIBUTES sa;

	/*
	 * Set up security attributes to specify that the events are inherited.
	 */
	ZeroMemory(&sa, sizeof(sa));
	sa.nLength = sizeof(sa);
	sa.bInheritHandle = TRUE;

	latch->event = CreateEvent(&sa, TRUE, FALSE, NULL);
	if (latch->event == NULL)
		elog(ERROR, "CreateEvent failed: error code %lu", GetLastError());
#endif

	latch->is_set = false;
	latch->maybe_sleeping = false;
	latch->owner_pid = 0;
	latch->is_shared = true;
}

/*
 * Associate a shared latch with the current process, allowing it to
 * wait on the latch.
 *
 * Although there is a sanity check for latch-already-owned, we don't do
 * any sort of locking here, meaning that we could fail to detect the error
 * if two processes try to own the same latch at about the same time.  If
 * there is any risk of that, caller must provide an interlock to prevent it.
 */
/*
 * OwnLatch - (中文)当前进程认领一个共享 latch
 *
 * 【作用】把共享 latch 的 owner_pid 从 0 改为本进程 PID,此后本进程
 * 才能在其上等待;若已被他人认领(owner_pid != 0)则 PANIC。
 *
 * 【设计思想】认领不做加锁,只有"已认领"的健全性检查:两个进程几乎
 * 同时认领同一个 latch 时可能都通过检查(检查与写入非原子),存在漏检
 * 风险;若调用方有这种并发可能,必须自行提供互斥手段。owner_pid
 * 语义:非零表示有人认领;同时它是 SetLatch 决定"唤醒哪个进程"的依据。
 *
 * 【参数】latch —— 已用 InitSharedLatch 初始化的共享 latch。
 * 【返回值】无。
 */
void
OwnLatch(Latch *latch)
{
	int			owner_pid;

	/* Sanity checks */
	Assert(latch->is_shared);

	owner_pid = latch->owner_pid;
	if (owner_pid != 0)
		elog(PANIC, "latch already owned by PID %d", owner_pid);

	latch->owner_pid = MyProcPid;
}

/*
 * Disown a shared latch currently owned by the current process.
 */
/*
 * DisownLatch - (中文)当前进程放弃对共享 latch 的认领
 *
 * 【作用】把 owner_pid 复位为 0(带断言:必须是本进程认领的),此后
 * 其他进程才能重新认领。
 *
 * 【设计思想】典型的"所有权转移"场景:postmaster 把 latch 交给某个
 * 子进程、或进程退出前归还。断言 owner_pid == MyProcPid 防止误放弃
 * 别人的 latch。
 *
 * 【参数】latch —— 本进程当前认领的共享 latch。
 * 【返回值】无。
 */
void
DisownLatch(Latch *latch)
{
	Assert(latch->is_shared);
	Assert(latch->owner_pid == MyProcPid);

	latch->owner_pid = 0;
}

/*
 * Wait for a given latch to be set, or for postmaster death, or until timeout
 * is exceeded. 'wakeEvents' is a bitmask that specifies which of those events
 * to wait for. If the latch is already set (and WL_LATCH_SET is given), the
 * function returns immediately.
 *
 * The "timeout" is given in milliseconds. It must be >= 0 if WL_TIMEOUT flag
 * is given.  Although it is declared as "long", we don't actually support
 * timeouts longer than INT_MAX milliseconds.  Note that some extra overhead
 * is incurred when WL_TIMEOUT is given, so avoid using a timeout if possible.
 *
 * The latch must be owned by the current process, ie. it must be a
 * process-local latch initialized with InitLatch, or a shared latch
 * associated with the current process by calling OwnLatch.
 *
 * Returns bit mask indicating which condition(s) caused the wake-up. Note
 * that if multiple wake-up conditions are true, there is no guarantee that
 * we return all of them in one call, but we will return at least one.
 */
/*
 * WaitLatch - (中文)等待 latch 被置位 / postmaster 死亡 / 超时(之一)
 *
 * 【作用】复用模块级静态 WaitEventSet 实现等待:按 wakeEvents 就地
 * 修改两个槽位(latch 事件、PM 死亡事件)后调用 WaitEventSetWait()。
 * 若 latch 已置位(WL_LATCH_SET 且在 wakeEvents 中)则立即返回。
 *
 * 【设计思想】等待语义(以位掩码返回唤醒原因,至少返回一种,可能同时
 * 返回多种)由 WaitEventSetWait 提供。使用静态集合并用 ModifyWaitEvent
 * 换参数,避免每次调用重建集合的开销;代价是并发调用 WaitLatch 不受
 * 支持(每个进程同时只能有一个等待者,这是 latch 的设计假设)。断言
 * 要求 postmaster 管理下的调用者必须处理 PM 死亡(二选一)。
 *
 * 【参数】
 *   latch           —— 本进程拥有的 latch(InitLatch 或 OwnLatch 过的);
 *                     若 wakeEvents 不含 WL_LATCH_SET,传 NULL 即可;
 *   wakeEvents      —— 等待哪些事件(WL_LATCH_SET | WL_TIMEOUT |
 *                      WL_EXIT_ON_PM_DEATH | WL_POSTMASTER_DEATH 等);
 *   timeout         —— 超时毫秒数(仅 WL_TIMEOUT 时有效,须 >= 0;实际
 *                      上限 INT_MAX 毫秒,且带超时的等待有额外开销);
 *   wait_event_info —— 等待事件描述(用于 pg_stat_activity 的 wait_event
 *                      列)。
 * 【返回值】位掩码:唤醒条件(WL_TIMEOUT 表示超时;否则为 event.events,
 * 可能含 WL_LATCH_SET / WL_POSTMASTER_DEATH 等)。
 */
int
WaitLatch(Latch *latch, int wakeEvents, long timeout,
		  uint32 wait_event_info)
{
	WaitEvent	event;

	/* Postmaster-managed callers must handle postmaster death somehow. */
	Assert(!IsUnderPostmaster ||
		   (wakeEvents & WL_EXIT_ON_PM_DEATH) ||
		   (wakeEvents & WL_POSTMASTER_DEATH));

	/*
	 * Some callers may have a latch other than MyLatch, or no latch at all,
	 * or want to handle postmaster death differently.  It's cheap to assign
	 * those, so just do it every time.
	 */
	if (!(wakeEvents & WL_LATCH_SET))
		latch = NULL;
	ModifyWaitEvent(LatchWaitSet, LatchWaitSetLatchPos, WL_LATCH_SET, latch);

	if (IsUnderPostmaster)
		ModifyWaitEvent(LatchWaitSet, LatchWaitSetPostmasterDeathPos,
						(wakeEvents & (WL_EXIT_ON_PM_DEATH | WL_POSTMASTER_DEATH)),
						NULL);

	if (WaitEventSetWait(LatchWaitSet,
						 (wakeEvents & WL_TIMEOUT) ? timeout : -1,
						 &event, 1,
						 wait_event_info) == 0)
		return WL_TIMEOUT;
	else
		return event.events;
}

/*
 * Like WaitLatch, but with an extra socket argument for WL_SOCKET_*
 * conditions.
 *
 * When waiting on a socket, EOF and error conditions always cause the socket
 * to be reported as readable/writable/connected, so that the caller can deal
 * with the condition.
 *
 * wakeEvents must include either WL_EXIT_ON_PM_DEATH for automatic exit
 * if the postmaster dies or WL_POSTMASTER_DEATH for a flag set in the
 * return value if the postmaster dies.  The latter is useful for rare cases
 * where some behavior other than immediate exit is needed.
 *
 * NB: These days this is just a wrapper around the WaitEventSet API. When
 * using a latch very frequently, consider creating a longer living
 * WaitEventSet instead; that's more efficient.
 */
/*
 * WaitLatchOrSocket - (中文)等待 latch / socket 事件 / PM 死亡 / 超时(之一)
 *
 * 【作用】WaitLatch 的扩展版本:额外支持 socket 可读/可写/连接事件
 * (WL_SOCKET_*)。实现上临时创建一个容量为 3 的 WaitEventSet(挂在
 * 当前资源所有者下),按需加入 latch 事件、PM 死亡事件与 socket 事件,
 * 等待后回收集合,把唤醒条件翻译成位掩码返回。
 *
 * 【设计思想】socket 上的 EOF/错误条件总是被当作"可读/可写/已连接"
 * 报告,让调用方自己去处理(读取时才会发现错误);因此调用方不需要在
 * 事件集合里显式监听异常。注意:本函数每次调用都新建/销毁 WaitEventSet,
 * 高频使用时应自行持有长生命周期的 WaitEventSet(原注释也建议如此)。
 * 对 PM 死亡,要么 WL_EXIT_ON_PM_DEATH(自动退出),要么
 * WL_POSTMASTER_DEATH(作为返回位返回,由调用方决定行为)。
 *
 * 【参数】
 *   latch           —— 本进程拥有的 latch(可为 NULL,取决于 wakeEvents);
 *   wakeEvents      —— 等待的事件组合(含 WL_SOCKET_READ/WRITE/CONNECT
 *                      及 latch/timeout/PM 死亡事件);
 *   sock            —— 要监听的 socket(仅在含 WL_SOCKET_MASK 时有效);
 *   timeout         —— 超时毫秒数(WL_TIMEOUT 时须 >= 0;否则传任意值,
 *                      内部按"不超时"处理);
 *   wait_event_info —— 等待事件描述(wait_event 统计用)。
 * 【返回值】位掩码:WL_TIMEOUT(超时)、WL_LATCH_SET、WL_POSTMASTER_DEATH、
 * 及 socket 相关事件位。
 */
int
WaitLatchOrSocket(Latch *latch, int wakeEvents, pgsocket sock,
				  long timeout, uint32 wait_event_info)
{
	int			ret = 0;
	int			rc;
	WaitEvent	event;
	WaitEventSet *set = CreateWaitEventSet(CurrentResourceOwner, 3);

	if (wakeEvents & WL_TIMEOUT)
		Assert(timeout >= 0);
	else
		timeout = -1;

	if (wakeEvents & WL_LATCH_SET)
		AddWaitEventToSet(set, WL_LATCH_SET, PGINVALID_SOCKET,
						  latch, NULL);

	/* Postmaster-managed callers must handle postmaster death somehow. */
	Assert(!IsUnderPostmaster ||
		   (wakeEvents & WL_EXIT_ON_PM_DEATH) ||
		   (wakeEvents & WL_POSTMASTER_DEATH));

	if ((wakeEvents & WL_POSTMASTER_DEATH) && IsUnderPostmaster)
		AddWaitEventToSet(set, WL_POSTMASTER_DEATH, PGINVALID_SOCKET,
						  NULL, NULL);

	if ((wakeEvents & WL_EXIT_ON_PM_DEATH) && IsUnderPostmaster)
		AddWaitEventToSet(set, WL_EXIT_ON_PM_DEATH, PGINVALID_SOCKET,
						  NULL, NULL);

	if (wakeEvents & WL_SOCKET_MASK)
	{
		int			ev;

		ev = wakeEvents & WL_SOCKET_MASK;
		AddWaitEventToSet(set, ev, sock, NULL, NULL);
	}

	rc = WaitEventSetWait(set, timeout, &event, 1, wait_event_info);

	if (rc == 0)
		ret |= WL_TIMEOUT;
	else
	{
		ret |= event.events & (WL_LATCH_SET |
							   WL_POSTMASTER_DEATH |
							   WL_SOCKET_MASK);
	}

	FreeWaitEventSet(set);

	return ret;
}

/*
 * Sets a latch and wakes up anyone waiting on it.
 *
 * This is cheap if the latch is already set, otherwise not so much.
 *
 * NB: when calling this in a signal handler, be sure to save and restore
 * errno around it.  (That's standard practice in most signal handlers, of
 * course, but we used to omit it in handlers that only set a flag.)
 *
 * NB: this function is called from critical sections and signal handlers so
 * throwing an error is not a good idea.
 */
/*
 * SetLatch - (中文)置位一个 latch 并唤醒正在其上等待的进程
 *
 * 【作用】把 latch->is_set 置为 true,并唤醒等待者:若本进程可能正睡在
 * 上面(maybe_sleeping)则通过自唤醒机制(WakeupMyProc,自管道/自信号)
 * 打断自己;若是其他进程拥有,则向该进程发 SIGUSR1 唤醒
 * (WakeupOtherProc)。Windows 下改为 SetEvent 内核事件。
 *
 * 【设计思想】这是 latch 机制的"写侧",正确性依赖两个内存屏障:
 * 1) 进入时先做 pg_memory_barrier(),保证本进程在此前修改的"标志变量"
 * 先冲刷到主存,再检查/设置 is_set——否则等待者读不到这些更新;
 * 2) is_set 置位后再做一次屏障,再读 maybe_sleeping。
 * 快速路径:latch 已置位则直接返回(廉价);没人睡觉也直接返回。读
 * owner_pid 只读一次,容忍"认领/放弃正并发进行"的竞态(最坏信号错
 * 进程,而 PG 进程都容忍多余的 SIGUSR1)。还有一个经典竞态:刚检查完
 * 就有人接管了 latch,我们没发信号——这没问题,只要所有
 * ResetLatch/WaitLatch 调用方遵循"循环底部等待"的约定(见文件头)。
 * 错误处理的约定:本函数可能在临界区/信号处理函数里被调用,因此绝不
 * 抛错(Windows 下 SetEvent 失败也静默忽略)。
 *
 * 【参数】latch —— 要置位的 latch。
 * 【返回值】无。
 */
void
SetLatch(Latch *latch)
{
#ifndef WIN32
	pid_t		owner_pid;
#else
	HANDLE		handle;
#endif

	/*
	 * The memory barrier has to be placed here to ensure that any flag
	 * variables possibly changed by this process have been flushed to main
	 * memory, before we check/set is_set.
	 */
	pg_memory_barrier();

	/* Quick exit if already set */
	if (latch->is_set)
		return;

	latch->is_set = true;

	pg_memory_barrier();
	if (!latch->maybe_sleeping)
		return;

#ifndef WIN32

	/*
	 * See if anyone's waiting for the latch. It can be the current process if
	 * we're in a signal handler. We use the self-pipe or SIGURG to ourselves
	 * to wake up WaitEventSetWaitBlock() without races in that case. If it's
	 * another process, send a signal.
	 *
	 * Fetch owner_pid only once, in case the latch is concurrently getting
	 * owned or disowned. XXX: This assumes that pid_t is atomic, which isn't
	 * guaranteed to be true! In practice, the effective range of pid_t fits
	 * in a 32 bit integer, and so should be atomic. In the worst case, we
	 * might end up signaling the wrong process. Even then, you're very
	 * unlucky if a process with that bogus pid exists and belongs to
	 * Postgres; and PG database processes should handle excess SIGUSR1
	 * interrupts without a problem anyhow.
	 *
	 * Another sort of race condition that's possible here is for a new
	 * process to own the latch immediately after we look, so we don't signal
	 * it. This is okay so long as all callers of ResetLatch/WaitLatch follow
	 * the standard coding convention of waiting at the bottom of their loops,
	 * not the top, so that they'll correctly process latch-setting events
	 * that happen before they enter the loop.
	 */
	owner_pid = latch->owner_pid;
	if (owner_pid == 0)
		return;
	else if (owner_pid == MyProcPid)
		WakeupMyProc();
	else
		WakeupOtherProc(owner_pid);

#else

	/*
	 * See if anyone's waiting for the latch. It can be the current process if
	 * we're in a signal handler.
	 *
	 * Use a local variable here just in case somebody changes the event field
	 * concurrently (which really should not happen).
	 */
	handle = latch->event;
	if (handle)
	{
		SetEvent(handle);

		/*
		 * Note that we silently ignore any errors. We might be in a signal
		 * handler or other critical path where it's not safe to call elog().
		 */
	}
#endif
}

/*
 * Clear the latch. Calling WaitLatch after this will sleep, unless
 * the latch is set again before the WaitLatch call.
 */
/*
 * ResetLatch - (中文)清除 latch 的置位状态(等待循环的"读侧")
 *
 * 【作用】把 is_set 清为 false。此后 WaitLatch 会真正睡眠,除非在
 * WaitLatch 调用之前又有一次 SetLatch。
 *
 * 【设计思想】只能由 latch 的 owner(本进程)调用(断言)。清除后再做
 * 一次内存屏障:确保 is_set 的写先于后续对"标志变量"的读冲刷到主存,
 * 否则并发的 SetLatch 会误判"无需唤醒我们",而我们已经漏掉了 SetLatch
 * 本应告知的标志更新。正确的使用模式是"循环底部等待":工作前 Reset、
 * 循环尾 WaitLatch,这样等待之前到达的置位不会被漏。
 *
 * 【参数】latch —— 本进程拥有的 latch。
 * 【返回值】无。
 */
void
ResetLatch(Latch *latch)
{
	/* Only the owner should reset the latch */
	Assert(latch->owner_pid == MyProcPid);
	Assert(latch->maybe_sleeping == false);

	latch->is_set = false;

	/*
	 * Ensure that the write to is_set gets flushed to main memory before we
	 * examine any flag variables.  Otherwise a concurrent SetLatch might
	 * falsely conclude that it needn't signal us, even though we have missed
	 * seeing some flag updates that SetLatch was supposed to inform us of.
	 */
	pg_memory_barrier();
}
