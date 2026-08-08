/*-------------------------------------------------------------------------
 *
 * condition_variable.c
 *	  Implementation of condition variables.  Condition variables provide
 *	  a way for one process to wait until a specific condition occurs,
 *	  without needing to know the specific identity of the process for
 *	  which they are waiting.  Waits for condition variables can be
 *	  interrupted, unlike LWLock waits.  Condition variables are safe
 *	  to use within dynamic shared memory segments.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的条件变量(Condition Variable,简称 CV)。
 * 条件变量是"等待某个特定条件成立"的同步原语:一个进程等待,另一个进程
 * 通过 Signal/Broadcast 唤醒它。与 LWLock 等待相比,条件变量等待是可被
 * 中断的(收到信号/超时/取消时会退出等待),且可安全地用于动态共享内存段
 * (DSM)中,因此被大量用在 parallel query 等场景。
 *
 * 【核心设计思想】
 * - 每个条件变量由两部分组成:一把自旋锁 mutex(保护等待队列)和一个
 *   等待队列 wakeup(proclist,元素是 PGPROC 的 cvWaitLink 链)。
 * - "唤醒"的实现依赖 PGPROC 里的 procLatch:发信号的一方把被唤醒者从
 *   队列里摘下来并 SetLatch,等待方在 WaitLatch 返回后检查自己是否还在
 *   队列中——不在队列里就说明"被信号唤醒了",应返回调用者重新检查条件。
 * - 整个模块都建立在"一个进程同时只能睡在一个条件变量上"这一约定上:
 *   进程的 PGPROC 里只有一条 cvWaitLink,全局静态变量 cv_sleep_target
 *   记录当前"已准备入睡"的目标;换一个 CV 睡之前必须先取消旧睡眠。
 * - 假唤醒(spurious wakeup)是允许的:Sleep 返回不代表条件已成立,调用者
 *   必须用循环"重查条件";并且被唤醒后要立刻把自己重新放回等待队列,
 *   防止在检查条件期间错过别的进程的 Signal(即"丢失唤醒"问题)。
 * - 与 pthread 条件变量最大的不同:PG 版必须显式调用 PrepareToSleep /
 *   CancelSleep 来进出"睡眠状态",这一显式化正是为避免"丢失唤醒"而设计的。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/storage/lmgr/condition_variable.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <limits.h>

#include "miscadmin.h"
#include "portability/instr_time.h"
#include "storage/condition_variable.h"
#include "storage/proc.h"
#include "storage/proclist.h"
#include "storage/spin.h"

/* Initially, we are not prepared to sleep on any condition variable. */
/* 全局静态变量:记录本进程当前"准备入睡"的条件变量(若正处于睡眠等待中,
 * 则记录的是睡眠目标)。因为 PGPROC 中只有一条 cvWaitLink,一个进程同一
 * 时刻只能睡在一个条件变量上,故用这一个静态变量即可跟踪状态;
 * NULL 表示当前没有挂起的睡眠。此变量只被本进程访问,无需加锁。 */
static ConditionVariable *cv_sleep_target = NULL;

/*
 * Initialize a condition variable.
 */
/*
 * ConditionVariableInit
 *      (中文)初始化一个条件变量
 *
 * 【作用】在条件变量首次使用前调用:初始化保护等待队列的自旋锁 mutex,
 * 并把等待队列 wakeup 置空。
 *
 * 【设计思想】条件变量可位于共享内存(如 DSM)或本进程内存中,但无论
 * 位置如何,初始化动作都是一样的;队列采用 proclist(以 PGPROC 的
 * cvWaitLink 为链元素),元素按"入队先后"排序,Signal 时唤醒最老的进程。
 *
 * 【参数】cv —— 待初始化的条件变量指针。
 * 【返回值】无。
 */
void
ConditionVariableInit(ConditionVariable *cv)
{
	SpinLockInit(&cv->mutex);
	proclist_init(&cv->wakeup);
}

/*
 * Prepare to wait on a given condition variable.
 *
 * This can optionally be called before entering a test/sleep loop.
 * Doing so is more efficient if we'll need to sleep at least once.
 * However, if the first test of the exit condition is likely to succeed,
 * it's more efficient to omit the ConditionVariablePrepareToSleep call.
 * See comments in ConditionVariableSleep for more detail.
 *
 * Caution: "before entering the loop" means you *must* test the exit
 * condition between calling ConditionVariablePrepareToSleep and calling
 * ConditionVariableSleep.  If that is inconvenient, omit calling
 * ConditionVariablePrepareToSleep.
 */
/*
 * ConditionVariablePrepareToSleep
 *      (中文)准备在一个条件变量上入睡(把自己加入等待队列)
 *
 * 【作用】进入"测试条件-睡眠"循环之前调用:把本进程挂到指定条件变量的
 * 等待队列尾部,并记录 cv_sleep_target。此后调用 ConditionVariableSleep
 * 才会真正阻塞。
 *
 * 【设计思想】
 * - 是否值得调用本函数取决于条件"大概率立即成立"还是"大概率要等":
 *   若不调用,则 ConditionVariableSleep 第一次调用时会自动准备并立刻
 *   返回,让调用者重查一次条件(相当于把"出队、重查、再入队"推迟);
 *   若先调用 PrepareToSleep,则省去这多余的一次条件测试。文档建议:
 *   预计第一次测试就成功 → 不调用;预计要睡 → 调用。
 * - 注意约定:调用本函数之后、调用 ConditionVariableSleep 之前,
 *   必须先测试一次退出条件!否则可能在条件已经成立的情况下白白睡觉,
 *   甚至永远等不到信号。若不方便这样做,就不要调用本函数。
 * - 若之前已为别的条件变量准备了睡眠,先 ConditionVariableCancelSleep
 *   取消掉(因为 cv_sleep_target 和 PGPROC->cvWaitLink 都只有一份);
 *   这不会丢信号——别的循环下次调用 ConditionVariableSleep 时会重新
 *   建立自己的睡眠。
 *
 * 【参数】cv —— 要入睡的条件变量。
 * 【返回值】无。
 */
void
ConditionVariablePrepareToSleep(ConditionVariable *cv)
{
	int			pgprocno = MyProcNumber;

	/*
	 * If some other sleep is already prepared, cancel it; this is necessary
	 * because we have just one static variable tracking the prepared sleep,
	 * and also only one cvWaitLink in our PGPROC.  It's okay to do this
	 * because whenever control does return to the other test-and-sleep loop,
	 * its ConditionVariableSleep call will just re-establish that sleep as
	 * the prepared one.
	 */
	if (cv_sleep_target != NULL)
		ConditionVariableCancelSleep();

	/* Record the condition variable on which we will sleep. */
	cv_sleep_target = cv;

	/* Add myself to the wait queue. */
	SpinLockAcquire(&cv->mutex);
	proclist_push_tail(&cv->wakeup, pgprocno, cvWaitLink);
	SpinLockRelease(&cv->mutex);
}

/*
 * Wait for the given condition variable to be signaled.
 *
 * This should be called in a predicate loop that tests for a specific exit
 * condition and otherwise sleeps, like so:
 *
 *	 ConditionVariablePrepareToSleep(cv);  // optional
 *	 while (condition for which we are waiting is not true)
 *		 ConditionVariableSleep(cv, wait_event_info);
 *	 ConditionVariableCancelSleep();
 *
 * wait_event_info should be a value from one of the WaitEventXXX enums
 * defined in pgstat.h.  This controls the contents of pg_stat_activity's
 * wait_event_type and wait_event columns while waiting.
 */
/*
 * ConditionVariableSleep
 *      (中文)等待条件变量被发信号(无超时版本)
 *
 * 【作用】阻塞本进程,直到被 ConditionVariableSignal/Broadcast 唤醒。
 * 必须在"测试-睡眠"谓词循环中使用,典型用法:
 *     ConditionVariablePrepareToSleep(cv);   // 可选
 *     while (等待的条件不成立)
 *         ConditionVariableSleep(cv, wait_event_info);
 *     ConditionVariableCancelSleep();
 * 注意:被唤醒不代表条件成立,循环体的条件测试才是真正的判断依据;
 * 退出循环后必须调用 ConditionVariableCancelSleep() 把自己从队列摘下。
 *
 * 【实现】本函数就是 ConditionVariableTimedSleep 的"永不超时"包装
 * (timeout 传 -1)。
 *
 * 【参数】
 *   cv              —— 等待的条件变量;
 *   wait_event_info —— pgstat.h 中 WaitEventXXX 枚举之一,控制等待期间
 *                      pg_stat_activity 的 wait_event_type/wait_event 显示。
 * 【返回值】无(仅在被信号唤醒后返回;等待期间可被中断/取消打断)。
 */
void
ConditionVariableSleep(ConditionVariable *cv, uint32 wait_event_info)
{
	(void) ConditionVariableTimedSleep(cv, -1 /* no timeout */ ,
									   wait_event_info);
}

/*
 * Wait for a condition variable to be signaled or a timeout to be reached.
 *
 * The "timeout" is given in milliseconds.
 *
 * Returns true when timeout expires, otherwise returns false.
 *
 * See ConditionVariableSleep() for general usage.
 */
/*
 * ConditionVariableTimedSleep
 *      (中文)等待条件变量被发信号,或直到超时
 *
 * 【作用】带超时的睡眠版本,timeout 单位为毫秒。超时返回 true;被信号
 * 唤醒(或假唤醒)返回 false。用法与 ConditionVariableSleep 相同,
 * 只是循环退出条件里要同时判断"是否已超时"。
 *
 * 【执行流程与设计思想】
 * 1. 若还没为这个 CV 准备睡眠(cv_sleep_target != cv),则先
 *    ConditionVariablePrepareToSleep 并立刻返回 false——调用者会重查
 *    条件,若仍不成立会再次调用本函数。这保证"退出条件在睡眠前至少被
 *    检查过一次",从根本上杜绝丢失唤醒。
 * 2. 循环等待 MyLatch:
 *    - WaitLatch 返回后先 ResetLatch(清掉 latch,否则会立即再次唤醒);
 *    - 持 cv->mutex 检查自己是否还在等待队列:不在 = 被 Signal 摘下,
 *      但为了不遗漏"检查条件期间到来的新信号",必须立刻把自己重新
 *      放回队列尾部,然后返回;
 *    - CHECK_FOR_INTERRUPTS() 处理挂起的信号:若中断处理器改了
 *      cv_sleep_target(意味着处理器曾等待别的条件变量),本次睡眠算
 *      "假唤醒",返回;
 *    - 有超时参数时用 instr_time 计算已等待的毫秒数,剩余时间不足
 *      即返回 true。
 * 3. 为什么要用"在不在队列里"判断是否被信号唤醒:Signal 的语义就是
 *    "把队首进程摘下来并 SetLatch",所以若醒来后仍在队列里,说明 latch
 *    是别人 Set 的(与本次 CV 无关)或纯属假唤醒,继续睡即可。
 *
 * 【参数】
 *   cv              —— 等待的条件变量;
 *   timeout         —— 超时毫秒数;-1 表示永不超时(等价于
 *                      ConditionVariableSleep);
 *   wait_event_info —— 等待事件的统计信息(见 ConditionVariableSleep)。
 * 【返回值】true = 超时;false = 被信号唤醒或假唤醒(调用者应重查条件)。
 */
bool
ConditionVariableTimedSleep(ConditionVariable *cv, long timeout,
							uint32 wait_event_info)
{
	long		cur_timeout = -1;
	instr_time	start_time;
	instr_time	cur_time;
	int			wait_events;

	/*
	 * If the caller didn't prepare to sleep explicitly, then do so now and
	 * return immediately.  The caller's predicate loop should immediately
	 * call again if its exit condition is not yet met.  This will result in
	 * the exit condition being tested twice before we first sleep.  The extra
	 * test can be prevented by calling ConditionVariablePrepareToSleep(cv)
	 * first.  Whether it's worth doing that depends on whether you expect the
	 * exit condition to be met initially, in which case skipping the prepare
	 * is recommended because it avoids manipulations of the wait list, or not
	 * met initially, in which case preparing first is better because it
	 * avoids one extra test of the exit condition.
	 *
	 * If we are currently prepared to sleep on some other CV, we just cancel
	 * that and prepare this one; see ConditionVariablePrepareToSleep.
	 */
	if (cv_sleep_target != cv)
	{
		ConditionVariablePrepareToSleep(cv);
		return false;
	}

	/*
	 * Record the current time so that we can calculate the remaining timeout
	 * if we are woken up spuriously.
	 */
	if (timeout >= 0)
	{
		INSTR_TIME_SET_CURRENT(start_time);
		Assert(timeout >= 0 && timeout <= INT_MAX);
		cur_timeout = timeout;
		wait_events = WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH;
	}
	else
		wait_events = WL_LATCH_SET | WL_EXIT_ON_PM_DEATH;

	while (true)
	{
		bool		done = false;

		/*
		 * Wait for latch to be set.  (If we're awakened for some other
		 * reason, the code below will cope anyway.)
		 */
		(void) WaitLatch(MyLatch, wait_events, cur_timeout, wait_event_info);

		/* Reset latch before examining the state of the wait list. */
		ResetLatch(MyLatch);

		/*
		 * If this process has been taken out of the wait list, then we know
		 * that it has been signaled by ConditionVariableSignal (or
		 * ConditionVariableBroadcast), so we should return to the caller. But
		 * that doesn't guarantee that the exit condition is met, only that we
		 * ought to check it.  So we must put the process back into the wait
		 * list, to ensure we don't miss any additional wakeup occurring while
		 * the caller checks its exit condition.  We can take ourselves out of
		 * the wait list only when the caller calls
		 * ConditionVariableCancelSleep.
		 *
		 * If we're still in the wait list, then the latch must have been set
		 * by something other than ConditionVariableSignal; though we don't
		 * guarantee not to return spuriously, we'll avoid this obvious case.
		 */
		SpinLockAcquire(&cv->mutex);
		if (!proclist_contains(&cv->wakeup, MyProcNumber, cvWaitLink))
		{
			done = true;
			proclist_push_tail(&cv->wakeup, MyProcNumber, cvWaitLink);
		}
		SpinLockRelease(&cv->mutex);

		/*
		 * Check for interrupts, and return spuriously if that caused the
		 * current sleep target to change (meaning that interrupt handler code
		 * waited for a different condition variable).
		 */
		CHECK_FOR_INTERRUPTS();
		if (cv != cv_sleep_target)
			done = true;

		/* We were signaled, so return */
		if (done)
			return false;

		/* If we're not done, update cur_timeout for next iteration */
		if (timeout >= 0)
		{
			INSTR_TIME_SET_CURRENT(cur_time);
			INSTR_TIME_SUBTRACT(cur_time, start_time);
			cur_timeout = timeout - (long) INSTR_TIME_GET_MILLISEC(cur_time);

			/* Have we crossed the timeout threshold? */
			if (cur_timeout <= 0)
				return true;
		}
	}
}

/*
 * Cancel any pending sleep operation.
 *
 * We just need to remove ourselves from the wait queue of any condition
 * variable for which we have previously prepared a sleep.
 *
 * Do nothing if nothing is pending; this allows this function to be called
 * during transaction abort to clean up any unfinished CV sleep.
 *
 * Return true if we've been signaled.
 */
/*
 * ConditionVariableCancelSleep
 *      (中文)取消任何挂起的睡眠(把自己从等待队列中摘下)
 *
 * 【作用】结束对某条件变量的等待:若本进程还在该 CV 的等待队列里,把
 * 自己摘除;返回"是否曾被信号唤醒"。
 *
 * 【设计思想】
 * - 必须在退出"测试-睡眠"循环后调用,否则本进程会一直留在队列里,
 *   将来该 CV 的任何一次 Signal 都会"唤醒"一个其实已不等待的进程
 *   (浪费一次 SetLatch,并可能造成后续队列语义混乱);
 * - 若当前根本没有挂起的睡眠(cv_sleep_target == NULL),直接返回 false。
 *   这使得本函数可以在事务回滚清理路径上无条件调用,安全无害;
 * - 返回"是否被信号唤醒"的语义:如果摘除时发现自己已不在队列里,
 *   说明之前已被 Signal 摘下(信号已经送达),返回 true。这个返回值
 *   供少数调用者(如 LWLock 释放路径)知道"不用再发信号了"。
 *
 * 【参数】无(作用于全局状态 cv_sleep_target)。
 * 【返回值】true = 在被取消前已经收到过信号;false = 无挂起睡眠或
 * 直接摘除(未收到信号)。
 */
bool
ConditionVariableCancelSleep(void)
{
	ConditionVariable *cv = cv_sleep_target;
	bool		signaled = false;

	if (cv == NULL)
		return false;

	SpinLockAcquire(&cv->mutex);
	if (proclist_contains(&cv->wakeup, MyProcNumber, cvWaitLink))
		proclist_delete(&cv->wakeup, MyProcNumber, cvWaitLink);
	else
		signaled = true;
	SpinLockRelease(&cv->mutex);

	cv_sleep_target = NULL;

	return signaled;
}

/*
 * Wake up the oldest process sleeping on the CV, if there is any.
 *
 * Note: it's difficult to tell whether this has any real effect: we know
 * whether we took an entry off the list, but the entry might only be a
 * sentinel.  Hence, think twice before proposing that this should return
 * a flag telling whether it woke somebody.
 */
/*
 * ConditionVariableSignal
 *      (中文)唤醒一个在指定条件变量上睡觉的进程(队首的、即最老的)
 *
 * 【作用】把 CV 等待队列中"最老"的进程摘下来并 SetLatch,使其从睡眠中
 * 醒来。若队列为空,什么都不做。
 *
 * 【设计思想】队列按入队顺序排列,Signal 总唤醒第一个(最老)等待者,
 * 保证公平;摘除与唤醒分两步:先在 mutex 保护下摘除(此时唤醒权已
 * 转移给被摘除者),再 SetLatch。即使 SetLatch 前该进程已因其他原因
 * 醒来,也只是一次无害的多余唤醒。
 *
 * 【参数】cv —— 要发信号的条件变量。
 * 【返回值】无。
 */
void
ConditionVariableSignal(ConditionVariable *cv)
{
	PGPROC	   *proc = NULL;

	/* Remove the first process from the wakeup queue (if any). */
	SpinLockAcquire(&cv->mutex);
	if (!proclist_is_empty(&cv->wakeup))
		proc = proclist_pop_head_node(&cv->wakeup, cvWaitLink);
	SpinLockRelease(&cv->mutex);

	/* If we found someone sleeping, set their latch to wake them up. */
	if (proc != NULL)
		SetLatch(&proc->procLatch);
}

/*
 * Wake up all processes sleeping on the given CV.
 *
 * This guarantees to wake all processes that were sleeping on the CV
 * at time of call, but processes that add themselves to the list mid-call
 * will typically not get awakened.
 */
/*
 * ConditionVariableBroadcast
 *      (中文)唤醒所有在指定条件变量上睡觉的进程
 *
 * 【作用】把 CV 等待队列里的全部进程(以调用时刻在队列中为准)逐个摘除
 * 并 SetLatch。调用过程中新加入队列的进程通常不会被唤醒。
 *
 * 【设计思想】
 * - 唤醒者可能在醒来后立即重新入队(常见于"唤醒-重查-再睡"循环),
 *   若简单地把队列清空,会与这种进程陷入潜在的无限循环。因此用自己
 *   的 cvWaitLink 作为"哨兵"插入队尾:只要哨兵还在队列里,就继续摘
 *   队首;等哨兵也轮到被摘时,说明调用前在队列里的进程都已处理完。
 * - 若别人恰好也在 Signal 并把我们的哨兵摘走了,则可能多唤醒一个
 *   进程——那是故意的:与其"漏唤醒"(丢掉唤醒信号,可能永远睡死),
 *   不如"多唤醒"(假唤醒,最多浪费几圈循环)。
 * - 插入哨兵前,若自己正挂着别的睡眠(cv_sleep_target != NULL),必须
 *   先取消,否则 cvWaitLink 已在别的队列里,无法复用(见函数内注释)。
 *
 * 【参数】cv —— 要广播的条件变量。
 * 【返回值】无。
 */
void
ConditionVariableBroadcast(ConditionVariable *cv)
{
	int			pgprocno = MyProcNumber;
	PGPROC	   *proc = NULL;
	bool		have_sentinel = false;

	/*
	 * In some use-cases, it is common for awakened processes to immediately
	 * re-queue themselves.  If we just naively try to reduce the wakeup list
	 * to empty, we'll get into a potentially-indefinite loop against such a
	 * process.  The semantics we really want are just to be sure that we have
	 * wakened all processes that were in the list at entry.  We can use our
	 * own cvWaitLink as a sentinel to detect when we've finished.
	 *
	 * A seeming flaw in this approach is that someone else might signal the
	 * CV and in doing so remove our sentinel entry.  But that's fine: since
	 * CV waiters are always added and removed in order, that must mean that
	 * every previous waiter has been wakened, so we're done.  We'll get an
	 * extra "set" on our latch from the someone else's signal, which is
	 * slightly inefficient but harmless.
	 *
	 * We can't insert our cvWaitLink as a sentinel if it's already in use in
	 * some other proclist.  While that's not expected to be true for typical
	 * uses of this function, we can deal with it by simply canceling any
	 * prepared CV sleep.  The next call to ConditionVariableSleep will take
	 * care of re-establishing the lost state.
	 */
	if (cv_sleep_target != NULL)
		ConditionVariableCancelSleep();

	/*
	 * Inspect the state of the queue.  If it's empty, we have nothing to do.
	 * If there's exactly one entry, we need only remove and signal that
	 * entry.  Otherwise, remove the first entry and insert our sentinel.
	 */
	SpinLockAcquire(&cv->mutex);
	/* While we're here, let's assert we're not in the list. */
	Assert(!proclist_contains(&cv->wakeup, pgprocno, cvWaitLink));

	if (!proclist_is_empty(&cv->wakeup))
	{
		proc = proclist_pop_head_node(&cv->wakeup, cvWaitLink);
		if (!proclist_is_empty(&cv->wakeup))
		{
			proclist_push_tail(&cv->wakeup, pgprocno, cvWaitLink);
			have_sentinel = true;
		}
	}
	SpinLockRelease(&cv->mutex);

	/* Awaken first waiter, if there was one. */
	if (proc != NULL)
		SetLatch(&proc->procLatch);

	while (have_sentinel)
	{
		/*
		 * Each time through the loop, remove the first wakeup list entry, and
		 * signal it unless it's our sentinel.  Repeat as long as the sentinel
		 * remains in the list.
		 *
		 * Notice that if someone else removes our sentinel, we will waken one
		 * additional process before exiting.  That's intentional, because if
		 * someone else signals the CV, they may be intending to waken some
		 * third process that added itself to the list after we added the
		 * sentinel.  Better to give a spurious wakeup (which should be
		 * harmless beyond wasting some cycles) than to lose a wakeup.
		 */
		proc = NULL;
		SpinLockAcquire(&cv->mutex);
		if (!proclist_is_empty(&cv->wakeup))
			proc = proclist_pop_head_node(&cv->wakeup, cvWaitLink);
		have_sentinel = proclist_contains(&cv->wakeup, pgprocno, cvWaitLink);
		SpinLockRelease(&cv->mutex);

		if (proc != NULL && proc != MyProc)
			SetLatch(&proc->procLatch);
	}
}
