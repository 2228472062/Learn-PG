/*-------------------------------------------------------------------------
 *
 * s_lock.c
 *	   Implementation of spinlocks.
 *
 * When waiting for a contended spinlock we loop tightly for awhile, then
 * delay using pg_usleep() and try again.  Preferably, "awhile" should be a
 * small multiple of the maximum time we expect a spinlock to be held.  100
 * iterations seems about right as an initial guess.  However, on a
 * uniprocessor the loop is a waste of cycles, while in a multi-CPU scenario
 * it's usually better to spin a bit longer than to call the kernel, so we try
 * to adapt the spin loop count depending on whether we seem to be in a
 * uniprocessor or multiprocessor.
 *
 * Note: you might think MIN_SPINS_PER_DELAY should be just 1, but you'd
 * be wrong; there are platforms where that can result in a "stuck
 * spinlock" failure.  This has been seen particularly on Alphas; it seems
 * that the first TAS after returning from kernel space will always fail
 * on that hardware.
 *
 * Once we do decide to block, we use randomly increasing pg_usleep()
 * delays. The first delay is 1 msec, then the delay randomly increases to
 * about one second, after which we reset to 1 msec and start again.  The
 * idea here is that in the presence of heavy contention we need to
 * increase the delay, else the spinlock holder may never get to run and
 * release the lock.  (Consider situation where spinlock holder has been
 * nice'd down in priority by the scheduler --- it will not get scheduled
 * until all would-be acquirers are sleeping, so if we always use a 1-msec
 * sleep, there is a real possibility of starvation.)  But we can't just
 * clamp the delay to an upper bound, else it would take a long time to
 * make a reasonable number of tries.
 *
 * We time out and declare error after NUM_DELAYS delays (thus, exactly
 * that many tries).  With the given settings, this will usually take 2 or
 * so minutes.  It seems better to fix the total number of tries (and thus
 * the probability of unintended failure) than to fix the total time
 * spent.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 自旋锁(spinlock)中"与平台无关"的那一部分逻辑。
 *
 * 自旋锁是最底层的锁原语,常被用来保护更高级别的结构:例如 LWLock
 * 的头部、锁管理器(LOCK 表)的分区元数据、缓冲区的头部等。在支持的
 * 平台上,锁变量 slock_t 的获取由一条原子指令完成——TAS(Test-And-Set,
 * 在 x86 上是 lock xchg,在 ARM 上是 swp/ldrex 等),这些架构相关代码
 * 位于 s_lock.h 及 src/include/port/atomics 系列头文件中。
 *
 * 本文件承担三部分职责:
 * 1) 自旋等待的"策略":当 TAS 拿不到锁时,先紧循环自旋(spin),自旋
 *    若干次后改为 pg_usleep() 休眠,而且休眠时长按随机指数退避增长;
 *    超过 NUM_DELAYS 次仍拿不到就判定"锁卡死"并报 PANIC。详见上方
 *    原有英文注释中对策略动机的阐述(单 CPU 与多 CPU 的取舍、防止
 *    持锁进程被调度器饿死的随机退避等)。
 * 2) 动态调整 spins_per_delay:根据"最近一次拿锁是否经历了延迟"来
 *    自适应地调大/调小本进程紧循环自旋的次数(单 CPU 上自旋纯属浪费,
 *    多 CPU 上则值得多自旋)。每进程维护一个本地副本,进程退出时把
 *    观测结果以指数移动平均的方式汇入共享变量,再在下次后端启动时
 *    取回,使"自旋多久"能跨进程收敛到一个合理值。
 * 3) 可选的 s_unlock 默认实现,以及 S_LOCK_TEST 独立测试程序(验证
 *    某个移植平台的 TAS/S_LOCK 语义是否正确)。
 *
 * 关系说明:本文件不直接服务于锁管理器 lock.c —— 锁管理器之上还有
 * 一层 LWLock(lwlock.c),而 LWLock 的内部状态正是用本文件的自旋锁
 * (即 S_LOCK/TAS 系列宏)来保护的;锁管理器使用 LWLock 作为分区锁。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/s_lock.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <time.h>
#include <unistd.h>

#include "common/pg_prng.h"
#include "storage/s_lock.h"
#include "utils/wait_event.h"

#define MIN_SPINS_PER_DELAY 10
#define MAX_SPINS_PER_DELAY 1000
#define NUM_DELAYS			1000
#define MIN_DELAY_USEC		1000L
#define MAX_DELAY_USEC		1000000L

/* 以上五个宏是自旋等待策略的全部参数:
 * - MIN_SPINS_PER_DELAY / MAX_SPINS_PER_DELAY : 每轮"紧循环自旋"次数的
 *   上下限(即 spins_per_delay 的取值范围)。下限取 10 而非 1 是经验教训:
 *   在部分平台(尤其 Alpha)上,从内核态返回后的第一次 TAS 必然失败,
 *   若自旋次数为 1,会被误判为"锁卡死"(见文件头注释);
 * - NUM_DELAYS     : 最大延迟(休眠)次数,超过即判死锁并报错;
 * - MIN_DELAY_USEC / MAX_DELAY_USEC : 单次休眠时长的上下限,1 毫秒到
 *   1 秒,每次翻 1~2 倍随机递增,超过上限后折回最小值重新开始。 */

#ifdef S_LOCK_TEST
/*
 * These are needed by pgstat_report_wait_start in the standalone compile of
 * s_lock_test.
 */
static uint32 local_my_wait_event_info;
uint32	   *my_wait_event_info = &local_my_wait_event_info;
#endif

static int	spins_per_delay = DEFAULT_SPINS_PER_DELAY;
/* 本进程的自旋策略参数:每轮"紧循环自旋"的次数(之后转休眠)。
 * 启动时从共享变量取回初值(见 set_spins_per_delay),此后由
 * finish_spin_delay 依据每次拿锁的实际体验动态调整,进程退出时经
 * update_spins_per_delay 汇入共享估计值。static 表明它是进程私有的。 */

/*
 * s_lock_stuck() - complain about a stuck spinlock
 */
/*
 * s_lock_stuck
 *      (中文)报告"自旋锁卡死"
 *
 * 【作用】在自旋了 NUM_DELAYS 次(约几分钟)仍拿不到锁时被调用:
 * - 独立测试程序(S_LOCK_TEST)下:向 stderr 打印位置信息后 exit(1);
 * - 正常运行时:elog(PANIC) 终止整个 postmaster(自旋锁被持住不放
 *   几乎肯定是程序 bug,如中断路径上忘记释放,带病继续只会更糟)。
 *
 * 【参数】
 *   file —— 发起自旋的源文件名;
 *   line —— 所在行号;
 *   func —— 所在函数名(可为 NULL,此时显示 "(unknown)")。
 * 【返回值】无(正常路径不返回;测试程序直接退出)。
 */
static void
s_lock_stuck(const char *file, int line, const char *func)
{
	if (!func)
		func = "(unknown)";
#if defined(S_LOCK_TEST)
	fprintf(stderr,
			"\nStuck spinlock detected at %s, %s:%d.\n",
			func, file, line);
	exit(1);
#else
	elog(PANIC, "stuck spinlock detected at %s, %s:%d",
		 func, file, line);
#endif
}

/*
 * s_lock(lock) - platform-independent portion of waiting for a spinlock.
 */
/*
 * s_lock
 *      (中文)自旋锁的"平台无关"等待主循环(真正拿锁的 TAS 是平台相关宏)
 *
 * 【作用】反复尝试 TAS_SPIN(lock) 获取自旋锁,拿不到就调用
 * perform_spin_delay 自旋/休眠退避,直到成功;成功后执行
 * finish_spin_delay 调整后续的自旋参数,并返回本次经历的延迟次数。
 *
 * 【设计思想】TAS 指令的具体形式(内联汇编/内建函数)随架构在
 * s_lock.h 中定义,本函数只负责"循环 + 退避策略",因此可以在所有
 * 平台复用同一份等待逻辑。调用方通常不是直接使用本函数,而是通过
 * S_LOCK() 宏展开为 "s_lock(lock, __FILE__, __LINE__, __func__)",
 * 这样一旦卡死,报告里能精确指出调用位置。
 *
 * 【参数】
 *   lock —— 指向自旋锁变量(slock_t,volatile)的指针;
 *   file/line/func —— 调用处的文件名、行号、函数名,用于卡死报告。
 * 【返回值】本次等待经历的休眠次数(status->delays),仅供调试/统计用。
 */
int
s_lock(volatile slock_t *lock, const char *file, int line, const char *func)
{
	SpinDelayStatus delayStatus;

	init_spin_delay(&delayStatus, file, line, func);

	while (TAS_SPIN(lock))
	{
		perform_spin_delay(&delayStatus);
	}

	finish_spin_delay(&delayStatus);

	return delayStatus.delays;
}

#ifdef USE_DEFAULT_S_UNLOCK
void
s_unlock(volatile slock_t *lock)
{
	*lock = 0;
}
#endif

/* (中文)若平台未提供更优的解锁方式(USE_DEFAULT_S_UNLOCK),就用这个
 * 默认实现:直接把锁变量清零。自旋锁的约定是"0 = 空闲,非 0 = 被持",
 * 由 TAS 指令负责把 0 原子地写成 1,所以解锁只需要一次普通(但须是
 * volatile)写入;写屏障由架构相关的 TAS 宏或编译器内存屏障保证。 */

/*
 * Wait while spinning on a contended spinlock.
 */
/*
 * perform_spin_delay
 *      (中文)执行一轮"自旋退避":CPU 级延迟 + 周期性的休眠退避
 *
 * 【作用】每次 TAS 失败后被调用。先执行架构相关的 SPIN_DELAY()
 * (通常是一条 pause / yield 指令,降低自旋对 CPU 流水线和缓存带宽的
 * 压力);每 spins_per_delay 次自旋后进入休眠阶段:pg_usleep 当前延迟
 * 时长,并把下一次延迟随机放大 1~2 倍,超过上限则折回 1 毫秒重新开始。
 * 休眠总次数超过 NUM_DELAYS 时判定锁卡死(s_lock_stuck)。
 *
 * 【设计思想】
 * - 紧循环自旋阶段不调用内核,切换开销为零,适合锁被短暂持有的情况;
 * - 休眠阶段让出 CPU 给持锁者(防止持锁进程因优先级被压低而饿死),
 *   而"随机指数退避"避免了众多等待者同时醒来、再次同时争锁的
 *   "惊群式"自旋;延迟必须从 1 毫秒逐渐增长,而不是直接睡很久,
 *   否则拿不到几次锁就会触发卡死判定(总尝试次数是固定的);
 * - 进入休眠时通过 pgstat_report_wait_start/end 上报 WAIT_EVENT_SPIN_DELAY,
 *   便于在 pg_stat_activity 中观察到进程正卡在自旋锁上。
 *
 * 【参数】status —— SpinDelayStatus,记录自旋/延迟计数与调用位置。
 * 【返回值】无(可能经 s_lock_stuck 不返回)。
 */
void
perform_spin_delay(SpinDelayStatus *status)
{
	/* CPU-specific delay each time through the loop */
	SPIN_DELAY();

	/* Block the process every spins_per_delay tries */
	if (++(status->spins) >= spins_per_delay)
	{
		if (++(status->delays) > NUM_DELAYS)
			s_lock_stuck(status->file, status->line, status->func);

		if (status->cur_delay == 0) /* first time to delay? */
			status->cur_delay = MIN_DELAY_USEC;

		/*
		 * Once we start sleeping, the overhead of reporting a wait event is
		 * justified. Actively spinning easily stands out in profilers, but
		 * sleeping with an exponential backoff is harder to spot...
		 *
		 * We might want to report something more granular at some point, but
		 * this is better than nothing.
		 */
		pgstat_report_wait_start(WAIT_EVENT_SPIN_DELAY);
		pg_usleep(status->cur_delay);
		pgstat_report_wait_end();

#if defined(S_LOCK_TEST)
		fprintf(stdout, "*");
		fflush(stdout);
#endif

		/* increase delay by a random fraction between 1X and 2X */
		status->cur_delay += (int) (status->cur_delay *
									pg_prng_double(&pg_global_prng_state) + 0.5);
		/* wrap back to minimum delay when max is exceeded */
		if (status->cur_delay > MAX_DELAY_USEC)
			status->cur_delay = MIN_DELAY_USEC;

		status->spins = 0;
	}
}

/*
 * After acquiring a spinlock, update estimates about how long to loop.
 *
 * If we were able to acquire the lock without delaying, it's a good
 * indication we are in a multiprocessor.  If we had to delay, it's a sign
 * (but not a sure thing) that we are in a uniprocessor. Hence, we
 * decrement spins_per_delay slowly when we had to delay, and increase it
 * rapidly when we didn't.  It's expected that spins_per_delay will
 * converge to the minimum value on a uniprocessor and to the maximum
 * value on a multiprocessor.
 *
 * Note: spins_per_delay is local within our current process. We want to
 * average these observations across multiple backends, since it's
 * relatively rare for this function to even get entered, and so a single
 * backend might not live long enough to converge on a good value.  That
 * is handled by the two routines below.
 */
/*
 * finish_spin_delay
 *      (中文)拿到自旋锁后,根据本次等待体验调整自旋次数估计
 *
 * 【作用】在 s_lock 成功拿到锁后调用一次,更新进程私有的 spins_per_delay:
 * - 本次完全没经历延迟(cur_delay == 0):说明自旋很快就拿到了锁,这是
 *   多 CPU 环境的典型表现,把 spins_per_delay 快速上调(每次 +100,
 *   封顶 MAX_SPINS_PER_DELAY);
 * - 本次经历了休眠:多半是单 CPU(或严重争用),缓慢下调(每次 -1,
 *   下限 MIN_SPINS_PER_DELAY)。
 *
 * 【设计思想】调整不对称(快升慢降)是为了让估值向"当前环境"快速靠拢:
 * 多 CPU 下自旋有收益,应尽快增大自旋预算;单 CPU 下自旋浪费 CPU,
 * 只需缓慢收缩。注意这里的观测是进程私有的,跨进程的统计收敛由
 * set_spins_per_delay / update_spins_per_delay 两个函数完成
 * (见函数注释)。
 *
 * 【参数】status —— 本次拿锁的 SpinDelayStatus(已由 s_lock 填好)。
 * 【返回值】无。
 */
void
finish_spin_delay(SpinDelayStatus *status)
{
	if (status->cur_delay == 0)
	{
		/* we never had to delay */
		if (spins_per_delay < MAX_SPINS_PER_DELAY)
			spins_per_delay = Min(spins_per_delay + 100, MAX_SPINS_PER_DELAY);
	}
	else
	{
		if (spins_per_delay > MIN_SPINS_PER_DELAY)
			spins_per_delay = Max(spins_per_delay - 1, MIN_SPINS_PER_DELAY);
	}
}

/*
 * Set local copy of spins_per_delay during backend startup.
 *
 * NB: this has to be pretty fast as it is called while holding a spinlock
 */
/* (中文)后端启动时把共享的 spins_per_delay 估计值拷入本进程私有变量。
 * 注意:它是在持有某把自旋锁的情况下被调用的(见 spin.c 的共享内存
 * 初始化),因此实现必须极快——这里只是一个普通赋值。 */
void
set_spins_per_delay(int shared_spins_per_delay)
{
	spins_per_delay = shared_spins_per_delay;
}


/*
 * Update shared estimate of spins_per_delay during backend exit.
 *
 * NB: this has to be pretty fast as it is called while holding a spinlock
 */
/*
 * update_spins_per_delay
 *      (中文)后端退出时,把本进程的观测值汇入共享的自旋参数估计
 *
 * 【作用】返回一个合并后的新共享值:new = (old * 15 + local) / 16。
 * 调用者(spin.c)把它写回共享内存,供下一个启动的后端用
 * set_spins_per_delay 取走,实现"每进程观测、跨进程收敛"。
 *
 * 【设计思想】
 * - 指数移动平均(15:1 权重)让单个进程的噪声不会过分扰动全局值,
 *   同时使全局值能缓慢跟踪机器负载/CPU 数量的长期变化;
 * - 故意用截断而非四舍五入:让单次的小调整也能最终影响共享估计
 *   (配合 finish_spin_delay 的"快升慢降"非对称规则);
 * - 与 set_spins_per_delay 一样,本函数可能在持有自旋锁时被调用,
 *   必须极快(只有一次乘法与加法)。
 *
 * 【参数】shared_spins_per_delay —— 当前共享估计值。
 * 【返回值】合并后的新估计值(供调用者写回共享内存)。
 */
int
update_spins_per_delay(int shared_spins_per_delay)
{
	/*
	 * We use an exponential moving average with a relatively slow adaption
	 * rate, so that noise in any one backend's result won't affect the shared
	 * value too much.  As long as both inputs are within the allowed range,
	 * the result must be too, so we need not worry about clamping the result.
	 *
	 * We deliberately truncate rather than rounding; this is so that single
	 * adjustments inside a backend can affect the shared estimate (see the
	 * asymmetric adjustment rules above).
	 */
	return (shared_spins_per_delay * 15 + spins_per_delay) / 16;
}


/*****************************************************************************/
#if defined(S_LOCK_TEST)

/*
 * test program for verifying a port's spinlock support.
 */
/* (中文)独立测试程序(以 S_LOCK_TEST 宏单独编译 s_lock_test 时进入,
 * 通常由 port 移植者运行):
 * - test_lock_struct 在 slock_t 两侧各放一个 0x44 哨兵字节,用来验证
 *   S_INIT_LOCK/S_LOCK/S_UNLOCK 不会越界写坏相邻内存(若 slock_t 的
 *   声明大小与架构实际不符,哨兵就会被改写);
 * - 依次执行初始化→加锁→解锁→再加锁,每步都检查哨兵是否完好;
 * - 最后故意在已持锁的情况下再次 s_lock() 同一把锁,期望自旋足够多次
 *   后触发"stuck spinlock"判定并以退出码 1 结束;若没被卡住(说明
 *   TAS 语义不对,锁根本没锁上),则打印失败信息并返回 1。测试期间
 *   每休眠一次打印一个 '*' 星号,便于观察退避过程。 */
struct test_lock_struct
{
	char		pad1;
	slock_t		lock;
	char		pad2;
};

volatile struct test_lock_struct test_lock;

/* (中文)自旋锁支持的自检程序入口:见上方 test_lock_struct 的中文注释。
 * 逻辑要点:1) 用随机种子初始化 PRNG(供退避延迟的随机倍数使用);
 * 2) 哨兵检查;3) 拿锁→放锁→再拿锁,验证 S_LOCK/S_UNLOCK 成对可用;
 * 4) 对已持锁的锁再次 s_lock(),期望触发 "stuck spinlock" 报告并退出。 */
int
main()
{
	pg_prng_seed(&pg_global_prng_state, (uint64) time(NULL));

	test_lock.pad1 = test_lock.pad2 = 0x44;

	S_INIT_LOCK(&test_lock.lock);

	if (test_lock.pad1 != 0x44 || test_lock.pad2 != 0x44)
	{
		printf("S_LOCK_TEST: failed, declared datatype is wrong size\n");
		return 1;
	}

	S_LOCK(&test_lock.lock);

	if (test_lock.pad1 != 0x44 || test_lock.pad2 != 0x44)
	{
		printf("S_LOCK_TEST: failed, declared datatype is wrong size\n");
		return 1;
	}

	S_UNLOCK(&test_lock.lock);

	if (test_lock.pad1 != 0x44 || test_lock.pad2 != 0x44)
	{
		printf("S_LOCK_TEST: failed, declared datatype is wrong size\n");
		return 1;
	}

	S_LOCK(&test_lock.lock);

	if (test_lock.pad1 != 0x44 || test_lock.pad2 != 0x44)
	{
		printf("S_LOCK_TEST: failed, declared datatype is wrong size\n");
		return 1;
	}

	printf("S_LOCK_TEST: this will print %d stars and then\n", NUM_DELAYS);
	printf("             exit with a 'stuck spinlock' message\n");
	printf("             if S_LOCK() and TAS() are working.\n");
	fflush(stdout);

	s_lock(&test_lock.lock, __FILE__, __LINE__, __func__);

	printf("S_LOCK_TEST: failed, lock not locked\n");
	return 1;
}

#endif							/* S_LOCK_TEST */
