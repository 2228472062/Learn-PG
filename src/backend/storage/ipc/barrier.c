/*-------------------------------------------------------------------------
 *
 * barrier.c
 *	  Barriers for synchronizing cooperating processes.
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * From Wikipedia[1]: "In parallel computing, a barrier is a type of
 * synchronization method.  A barrier for a group of threads or processes in
 * the source code means any thread/process must stop at this point and cannot
 * proceed until all other threads/processes reach this barrier."
 *
 * This implementation of barriers allows for static sets of participants
 * known up front, or dynamic sets of participants which processes can join or
 * leave at any time.  In the dynamic case, a phase number can be used to
 * track progress through a parallel algorithm, and may be necessary to
 * synchronize with the current phase of a multi-phase algorithm when a new
 * participant joins.  In the static case, the phase number is used
 * internally, but it isn't strictly necessary for client code to access it
 * because the phase can only advance when the declared number of participants
 * reaches the barrier, so client code should be in no doubt about the current
 * phase of computation at all times.
 *
 * Consider a parallel algorithm that involves separate phases of computation
 * A, B and C where the output of each phase is needed before the next phase
 * can begin.
 *
 * In the case of a static barrier initialized with 4 participants, each
 * participant works on phase A, then calls BarrierArriveAndWait to wait until
 * all 4 participants have reached that point.  When BarrierArriveAndWait
 * returns control, each participant can work on B, and so on.  Because the
 * barrier knows how many participants to expect, the phases of computation
 * don't need labels or numbers, since each process's program counter implies
 * the current phase.  Even if some of the processes are slow to start up and
 * begin running phase A, the other participants are expecting them and will
 * patiently wait at the barrier.  The code could be written as follows:
 *
 *     perform_a();
 *     BarrierArriveAndWait(&barrier, ...);
 *     perform_b();
 *     BarrierArriveAndWait(&barrier, ...);
 *     perform_c();
 *     BarrierArriveAndWait(&barrier, ...);
 *
 * If the number of participants is not known up front, then a dynamic barrier
 * is needed and the number should be set to zero at initialization.  New
 * complications arise because the number necessarily changes over time as
 * participants attach and detach, and therefore phases B, C or even the end
 * of processing may be reached before any given participant has started
 * running and attached.  Therefore the client code must perform an initial
 * test of the phase number after attaching, because it needs to find out
 * which phase of the algorithm has been reached by any participants that are
 * already attached in order to synchronize with that work.  Once the program
 * counter or some other representation of current progress is synchronized
 * with the barrier's phase, normal control flow can be used just as in the
 * static case.  Our example could be written using a switch statement with
 * cases that fall-through, as follows:
 *
 *     phase = BarrierAttach(&barrier);
 *     switch (phase)
 *     {
 *     case PHASE_A:
 *         perform_a();
 *         BarrierArriveAndWait(&barrier, ...);
 *     case PHASE_B:
 *         perform_b();
 *         BarrierArriveAndWait(&barrier, ...);
 *     case PHASE_C:
 *         perform_c();
 *         BarrierArriveAndWait(&barrier, ...);
 *     }
 *     BarrierDetach(&barrier);
 *
 * Static barriers behave similarly to POSIX's pthread_barrier_t.  Dynamic
 * barriers behave similarly to Java's java.util.concurrent.Phaser.
 *
 * [1] https://en.wikipedia.org/wiki/Barrier_(computer_science)
 *
 * 【模块总览(中文)】
 * 本文件实现"屏障"(Barrier):一组协作进程必须全部到达同步点后才能继续
 * 执行的同步原语,是并行执行中"阶段同步"的基石。典型场景:并行查询的各
 * worker 分别完成阶段 A 后,必须等所有人都完成才能安全进入阶段 B——因为
 * 阶段 B 可能消费阶段 A 的全部输出。
 *
 * 【静态 / 动态两种参与方模式】
 * - 静态屏障:BarrierInit 时给定 participants > 0,人数全程不变,客户代码
 *   用程序计数器即可推断当前阶段,不必读 phase;
 * - 动态屏障:BarrierInit 时给 0,进程用 BarrierAttach / BarrierDetach /
 *   BarrierArriveAndDetach 随时加入或退出;此时 phase 号码是客户代码同步
 *   进度的唯一依据(attach 后必须先读 phase 判断算法已进行到哪一步)。
 *
 * 【实现要点】
 * - 共享内存中的 Barrier 结构由自旋锁 mutex 保护,配合 ConditionVariable
 *   (条件变量)实现睡眠/唤醒:最后一个到达者负责递增 phase 并广播唤醒;
 * - 每个 phase 恰好"选出"一个参与者(BarrierArriveAndWait 返回 true),
 *   由它执行需要串行化的那部分工作,其余进程返回 false;
 * - "脱离"(detach)必须能推进 phase:若等待者只差这一个进程,它的退出
 *   等价于"到达",广播唤醒后由某个被唤醒者补选 elected 并返回 true;
 * - BarrierPhase 免锁读取:读方自己仍处于 attached 状态,而 phase 没有
 *   读方参与就不可能变化,配合 attach / 参与变更时的内存屏障即安全。
 *
 * 本实现语义上等价于 POSIX 的 pthread_barrier_t(静态)与 Java 的
 * java.util.concurrent.Phaser(动态)。
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/barrier.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"
#include "storage/barrier.h"

/* BarrierDetachImpl 的前置声明,权威注释见其定义处。 */
static inline bool BarrierDetachImpl(Barrier *barrier, bool arrive);

/*
 * Initialize this barrier.  To use a static party size, provide the number of
 * participants to wait for at each phase indicating that that number of
 * backends is implicitly attached.  To use a dynamic party size, specify zero
 * here and then use BarrierAttach() and
 * BarrierDetach()/BarrierArriveAndDetach() to register and deregister
 * participants explicitly.
 */
/*
 * BarrierInit - (中文)初始化一个屏障
 *
 * 【作用】把 Barrier 结构置初值:自旋锁、参与方数、已到达数、阶段号、
 * 当选者、条件变量。必须在共享内存中、且在任何进程使用该屏障之前调用。
 *
 * 【设计思想】participants > 0 表示"静态屏障":人数隐含固定,Attach/Detach
 * 系列接口被禁止(断言 static_party);participants = 0 表示"动态屏障",
 * 之后用 BarrierAttach 显式注册/注销参与者。
 *
 * 【参数】
 *   barrier      —— 待初始化的 Barrier(通常位于共享内存);
 *   participants —— 静态屏障的参与方总数;0 表示动态屏障。
 * 【返回值】无。
 */
void
BarrierInit(Barrier *barrier, int participants)
{
	SpinLockInit(&barrier->mutex);
	barrier->participants = participants;
	barrier->arrived = 0;
	barrier->phase = 0;
	barrier->elected = 0;
	barrier->static_party = participants > 0;
	ConditionVariableInit(&barrier->condition_variable);
}

/*
 * Arrive at this barrier, wait for all other attached participants to arrive
 * too and then return.  Increments the current phase.  The caller must be
 * attached.
 *
 * While waiting, pg_stat_activity shows a wait_event_type and wait_event
 * controlled by the wait_event_info passed in, which should be a value from
 * one of the WaitEventXXX enums defined in pgstat.h.
 *
 * Return true in one arbitrarily chosen participant.  Return false in all
 * others.  The return code can be used to elect one participant to execute a
 * phase of work that must be done serially while other participants wait.
 */
/*
 * BarrierArriveAndWait - (中文)到达屏障,等所有人到齐后进入下一阶段
 *
 * 【作用】调用者(必须已 attach)到达本阶段屏障:若自己是最后一个到达者,
 * 递增 phase 并唤醒所有等待者、返回 true(被"选举"执行串行工作);否则
 * 睡眠等待直到 phase 推进(最后一个到达者或某个等待者脱离都会推进)。
 * 等待期间以 wait_event_info 登记 pg_stat_activity 的等待事件。
 *
 * 【设计思想】
 * - "最后一个到达者立即返回并负责广播",利用了它"还持有 CPU 时间片"
 *   的优势,避免一次不必要的调度切换;
 * - 睡眠循环的正确性依赖一个不变量:本进程仍 attach 着,所以 phase 只能
 *   从 start_phase 推进到 start_phase + 1,不可能跳得更远(循环内有
 *   断言覆盖);
 * - elected 字段的竞态处理:若 phase 是"因某人脱离"而推进的,推进者
 *   已经离开,此时需要由某个被唤醒者认领 elected 再返回 true;
 * - 使用条件变量的 PrepareToSleep / Sleep 两段式协议:先持锁修改
 *   arrived 再准备睡眠,防止"到达与等待之间 phase 已推进"造成永久睡眠。
 *
 * 【参数】
 *   barrier         —— 屏障;
 *   wait_event_info —— 等待事件的标识(WaitEventXXX 枚举,见 pgstat.h),
 *                      用于 pg_stat_activity 展示。
 * 【返回值】true:本进程被选为"串行工作执行者";false:普通参与者。
 */
bool
BarrierArriveAndWait(Barrier *barrier, uint32 wait_event_info)
{
	bool		release = false;
	bool		elected;
	int			start_phase;
	int			next_phase;

	SpinLockAcquire(&barrier->mutex);
	start_phase = barrier->phase;
	next_phase = start_phase + 1;
	++barrier->arrived;
	if (barrier->arrived == barrier->participants)
	{
		release = true;
		barrier->arrived = 0;
		barrier->phase = next_phase;
		barrier->elected = next_phase;
	}
	SpinLockRelease(&barrier->mutex);

	/*
	 * If we were the last expected participant to arrive, we can release our
	 * peers and return true to indicate that this backend has been elected to
	 * perform any serial work.
	 */
	if (release)
	{
		ConditionVariableBroadcast(&barrier->condition_variable);

		return true;
	}

	/*
	 * Otherwise we have to wait for the last participant to arrive and
	 * advance the phase.
	 */
	elected = false;
	ConditionVariablePrepareToSleep(&barrier->condition_variable);
	for (;;)
	{
		/*
		 * We know that phase must either be start_phase, indicating that we
		 * need to keep waiting, or next_phase, indicating that the last
		 * participant that we were waiting for has either arrived or detached
		 * so that the next phase has begun.  The phase cannot advance any
		 * further than that without this backend's participation, because
		 * this backend is attached.
		 */
		SpinLockAcquire(&barrier->mutex);
		Assert(barrier->phase == start_phase || barrier->phase == next_phase);
		release = barrier->phase == next_phase;
		if (release && barrier->elected != next_phase)
		{
			/*
			 * Usually the backend that arrives last and releases the other
			 * backends is elected to return true (see above), so that it can
			 * begin processing serial work while it has a CPU timeslice.
			 * However, if the barrier advanced because someone detached, then
			 * one of the backends that is awoken will need to be elected.
			 */
			barrier->elected = barrier->phase;
			elected = true;
		}
		SpinLockRelease(&barrier->mutex);
		if (release)
			break;
		ConditionVariableSleep(&barrier->condition_variable, wait_event_info);
	}
	ConditionVariableCancelSleep();

	return elected;
}

/*
 * Arrive at this barrier, but detach rather than waiting.  Returns true if
 * the caller was the last to detach.
 */
/*
 * BarrierArriveAndDetach - (中文)到达屏障后立即脱离(不等待)
 *
 * 【作用】参与者"到达 + 退出"的合并操作:表示本进程完成了当前阶段的
 * 工作,并且不再参与后续阶段。若自己是最后一个参与者,返回 true。
 *
 * 【设计思想】把"到达"与"脱离"合并成一次持锁操作,避免两个动作之间被
 * 其他进程插入(否则可能出现"已到达、但 phase 推进后才退出"造成的状态
 * 错乱)。具体语义见 BarrierDetachImpl 的 arrive 参数说明。
 *
 * 【参数】barrier —— 屏障。
 * 【返回值】true 表示调用者是最后一个脱离的参与者。
 */
bool
BarrierArriveAndDetach(Barrier *barrier)
{
	return BarrierDetachImpl(barrier, true);
}

/*
 * Arrive at a barrier, and detach all but the last to arrive.  Returns true if
 * the caller was the last to arrive, and is therefore still attached.
 */
/*
 * BarrierArriveAndDetachExceptLast - (中文)到达后让除最后一个之外的所有
 * 参与者脱离
 *
 * 【作用】动态并行算法收尾的惯用法:每个完成工作的参与者调用本函数,只有
 * 最后一个到达者被保留在参与者名单里并返回 true。例如"聚合多个 worker
 * 结果"的模式:前 N-1 个 worker 到达即退出,最后一个 worker(通常是
 * leader 或最后完成的 worker)继续承担收尾工作。
 *
 * 【设计思想】不修改 arrived(调用者此前都已各自处理过"到达"),只递减
 * participants;当自己是最后一个(participants == 1)时递增 phase 表示
 * 本阶段结束并返回 true。因为返回 true 者仍 attach 着,由它直接递增
 * phase 是安全的(不会被并发推进)。
 *
 * 【参数】barrier —— 屏障。
 * 【返回值】true:调用者是最后一个到达者,仍保持 attach;false:已脱离。
 */
bool
BarrierArriveAndDetachExceptLast(Barrier *barrier)
{
	SpinLockAcquire(&barrier->mutex);
	if (barrier->participants > 1)
	{
		--barrier->participants;
		SpinLockRelease(&barrier->mutex);

		return false;
	}
	Assert(barrier->participants == 1);
	++barrier->phase;
	SpinLockRelease(&barrier->mutex);

	return true;
}

/*
 * Attach to a barrier.  All waiting participants will now wait for this
 * participant to call BarrierArriveAndWait(), BarrierDetach() or
 * BarrierArriveAndDetach().  Return the current phase.
 */
/*
 * BarrierAttach - (中文)注册一个动态参与者并返回当前阶段号
 *
 * 【作用】动态屏障专用:调用者加入参与方集合,所有正在等待的进程此后都会
 * 等到它 arrive/detach 才会放行;返回的 phase 供调用者判断算法进行到
 * 哪一步(典型用法见文件头注释的 switch 示例)。
 *
 * 【设计思想】参与者数 +1 与读取 phase 在同一临界区内完成,保证调用者
 * 看到的是"自己加入之后"的一致阶段;若先读 phase 再加人数,可能读到
 * 加入前的旧阶段,造成进度误判。
 *
 * 【参数】barrier —— 屏障。
 * 【返回值】当前阶段号(调用者加入时的 phase)。
 */
int
BarrierAttach(Barrier *barrier)
{
	int			phase;

	Assert(!barrier->static_party);

	SpinLockAcquire(&barrier->mutex);
	++barrier->participants;
	phase = barrier->phase;
	SpinLockRelease(&barrier->mutex);

	return phase;
}

/*
 * Detach from a barrier.  This may release other waiters from
 * BarrierArriveAndWait() and advance the phase if they were only waiting for
 * this backend.  Return true if this participant was the last to detach.
 */
/*
 * BarrierDetach - (中文)从屏障脱离(不产生"到达")
 *
 * 【作用】动态屏障专用:调用者直接退出参与方集合。若当前等待者恰好只差
 * 这一个参与者,则推进 phase 并释放它们。返回 true 表示自己是最后一个
 * 脱离者。
 *
 * 【设计思想】与 BarrierArriveAndDetach 的唯一区别是"不递增 arrived,
 * 且当已是最后一个参与者时不推进 phase"(见 BarrierDetachImpl 的
 * arrive 参数语义)。调用者必须已经完成自己阶段的工作,且不再参与后续
 * 阶段。
 *
 * 【参数】barrier —— 屏障。
 * 【返回值】true:最后一个脱离者;false:还有其他参与者。
 */
bool
BarrierDetach(Barrier *barrier)
{
	return BarrierDetachImpl(barrier, false);
}

/*
 * Return the current phase of a barrier.  The caller must be attached.
 */
/*
 * BarrierPhase - (中文)返回屏障当前阶段号
 *
 * 【作用】查询当前 phase。静态屏障下几乎用不到(程序计数器即可推断
 * 阶段);动态屏障下,新参与者 attach 后用它与已有工作同步进度。
 *
 * 【设计思想】免锁直接读 phase:调用者已 attach,而 phase 的推进必然
 * 包含调用者本人(要么是它自己推的,要么它正在等待/参与),加之 attach
 * 或上次参与变更时执行过内存屏障,读到的值不会陈旧到危险。
 *
 * 【参数】barrier —— 屏障。
 * 【返回值】当前阶段号。
 */
int
BarrierPhase(Barrier *barrier)
{
	/*
	 * It is OK to read barrier->phase without locking, because it can't
	 * change without us (we are attached to it), and we executed a memory
	 * barrier when we either attached or participated in changing it last
	 * time.
	 */
	return barrier->phase;
}

/*
 * Return an instantaneous snapshot of the number of participants currently
 * attached to this barrier.  For debugging purposes only.
 */
/*
 * BarrierParticipants - (中文)返回当前参与方数量的瞬时快照
 *
 * 【作用】仅用于调试(如打印屏障状态):读取当前 participants。
 *
 * 【设计思想】持自旋锁读取以获得一致值;但不保证稳定(其他进程随时可能
 * attach/detach),所以只适合观察性用途,不能用于流程控制。
 *
 * 【参数】barrier —— 屏障。
 * 【返回值】当前参与者个数。
 */
int
BarrierParticipants(Barrier *barrier)
{
	int			participants;

	SpinLockAcquire(&barrier->mutex);
	participants = barrier->participants;
	SpinLockRelease(&barrier->mutex);

	return participants;
}

/*
 * Detach from a barrier.  If 'arrive' is true then also increment the phase
 * if there are no other participants.  If there are other participants
 * waiting, then the phase will be advanced and they'll be released if they
 * were only waiting for the caller.  Return true if this participant was the
 * last to detach.
 */
/*
 * BarrierDetachImpl - (中文)脱离屏障的通用实现(BarrierDetach 与
 * BarrierArriveAndDetach 共用)
 *
 * 【作用】把调用者从参与方集合移除;若"还有其他参与者正在等待,且本进程
 * 正是他们缺的那一个",则推进 phase 并广播唤醒他们;若 arrive 为 true
 * 且自己是最后参与者,同样推进 phase(相当于"最后一人到达即完成本阶段")。
 *
 * 【设计思想】两个接口的差异全部由 arrive 参数表达:
 * - arrive = false(BarrierDetach):仅退出,只有当"还有其他参与者正等着
 *   自己"时才推进 phase 释放他们;自己已是最后一个时不再推进(没人需要
 *   被释放);
 * - arrive = true(BarrierArriveAndDetach):除了上述释放逻辑,还要处理
 *   "自己是最后一人"的情形——此时本阶段到此结束,phase 应递增。
 * 条件 `(arrive || participants > 0) && arrived == participants` 精确
 * 表达了这两种语义。释放条件是"已到达数 == 剩余参与人数",即在等待者
 * 眼中,本进程的"到达 + 退出"等价于一次到达。
 *
 * 【参数】
 *   barrier —— 屏障;
 *   arrive  —— true 表示这是 BarrierArriveAndDetach(需要时推进 phase)。
 * 【返回值】true 表示调用者是最后一个脱离者。
 */
static inline bool
BarrierDetachImpl(Barrier *barrier, bool arrive)
{
	bool		release;
	bool		last;

	Assert(!barrier->static_party);

	SpinLockAcquire(&barrier->mutex);
	Assert(barrier->participants > 0);
	--barrier->participants;

	/*
	 * If any other participants are waiting and we were the last participant
	 * waited for, release them.  If no other participants are waiting, but
	 * this is a BarrierArriveAndDetach() call, then advance the phase too.
	 */
	if ((arrive || barrier->participants > 0) &&
		barrier->arrived == barrier->participants)
	{
		release = true;
		barrier->arrived = 0;
		++barrier->phase;
	}
	else
		release = false;

	last = barrier->participants == 0;
	SpinLockRelease(&barrier->mutex);

	if (release)
		ConditionVariableBroadcast(&barrier->condition_variable);

	return last;
}
