/*-------------------------------------------------------------------------
 *
 * waiteventset.c
 *	  ppoll()/pselect() like abstraction
 *
 * WaitEvents are an abstraction for waiting for one or more events at a time.
 * The waiting can be done in a race free fashion, similar ppoll() or
 * pselect() (as opposed to plain poll()/select()).
 *
 * You can wait for:
 * - a latch being set from another process or from signal handler in the same
 *   process (WL_LATCH_SET)
 * - data to become readable or writeable on a socket (WL_SOCKET_*)
 * - postmaster death (WL_POSTMASTER_DEATH or WL_EXIT_ON_PM_DEATH)
 * - timeout (WL_TIMEOUT)
 *
 * Implementation
 * --------------
 *
 * The poll() implementation uses the so-called self-pipe trick to overcome the
 * race condition involved with poll() and setting a global flag in the signal
 * handler. When a latch is set and the current process is waiting for it, the
 * signal handler wakes up the poll() in WaitLatch by writing a byte to a pipe.
 * A signal by itself doesn't interrupt poll() on all platforms, and even on
 * platforms where it does, a signal that arrives just before the poll() call
 * does not prevent poll() from entering sleep. An incoming byte on a pipe
 * however reliably interrupts the sleep, and causes poll() to return
 * immediately even if the signal arrives before poll() begins.
 *
 * The epoll() implementation overcomes the race with a different technique: it
 * keeps SIGURG blocked and consumes from a signalfd() descriptor instead.  We
 * don't need to register a signal handler or create our own self-pipe.  We
 * assume that any system that has Linux epoll() also has Linux signalfd().
 *
 * The kqueue() implementation waits for SIGURG with EVFILT_SIGNAL.
 *
 * The Windows implementation uses Windows events that are inherited by all
 * postmaster child processes. There's no need for the self-pipe trick there.
 *
 * 【模块总览(中文)】
 * 本文件实现"等待事件集合"(WaitEventSet):把若干事件(latch 置位、socket
 * 可读/可写/对端关闭、postmaster 死亡、超时)组织进一个集合,用一次系统
 * 调用同时等待。这是 latch.c 的底层支撑:WaitLatch / WaitLatchOrSocket
 * 最终都落到本模块。语义上等价于 ppoll()/pselect() 的"无竞态"版本:
 * 信号在进入睡眠之前到达也不会丢失。
 *
 * 【支持的等待对象】
 * - WL_LATCH_SET:等待本进程拥有的 latch 被置位(SetLatch 可来自其他进程
 *   或本进程的信号处理器);
 * - WL_SOCKET_* :socket 可读 / 可写 / 建立连接 / 可 accept / 对端关闭;
 * - WL_POSTMASTER_DEATH / WL_EXIT_ON_PM_DEATH:postmaster 死亡(后者在
 *   检测到时直接 proc_exit 退出,而不是把事件返回给调用者);
 * - WL_TIMEOUT:超时。
 *
 * 【四种内核后端与"唤醒竞态"】
 * 编译期按平台选择 poll / epoll / kqueue / Win32 之一(可用 WAIT_USE_*
 * 宏手工指定以便测试)。核心难题是"信号处理器置位 latch"的竞态:信号本身
 * 不保证打断 poll() 的睡眠,且信号若在 poll() 之前到达,poll() 照样会睡
 * 过去。三种解决思路:
 * - self-pipe 技巧(poll):信号处理器往管道写一个字节,管道里有数据必然
 *   使 poll 立即返回(写端非阻塞,满了也无害);
 * - signalfd(epoll + Linux):阻塞 SIGURG,由内核把它转成文件描述符上的
 *   可读事件,直接加入 epoll 集合;
 * - kqueue:用 EVFILT_SIGNAL 过滤器直接等待 SIGURG 信号事件。
 * Windows 用继承的事件对象 + WaitForMultipleObjects。
 *
 * 【其他要点】
 * - WaitEventSet 与 ResourceOwner 挂钩,事务 / 会话结束自动释放;
 * - epoll 的 ADD / MOD / DEL 三种内核操作由 WaitEventAdjustEpoll 统一
 *   封装,内核事件位与 WL_* 位在此映射;
 * - latch 的 maybe_sleeping 标志 + 内存屏障用于"置位者"与"即将睡眠者"
 *   的握手,细节见 latch.c。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/waiteventset.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <unistd.h>
#ifdef HAVE_SYS_EPOLL_H
#include <sys/epoll.h>
#endif
#ifdef HAVE_SYS_EVENT_H
#include <sys/event.h>
#endif
#ifdef HAVE_SYS_SIGNALFD_H
#include <sys/signalfd.h>
#endif
#ifdef HAVE_POLL_H
#include <poll.h>
#endif

#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "port/atomics.h"
#include "portability/instr_time.h"
#include "postmaster/postmaster.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/pmsignal.h"
#include "storage/latch.h"
#include "storage/waiteventset.h"
#include "utils/memutils.h"
#include "utils/resowner.h"
#include "utils/wait_event.h"

/*
 * Select the fd readiness primitive to use. Normally the "most modern"
 * primitive supported by the OS will be used, but for testing it can be
 * useful to manually specify the used primitive.  If desired, just add a
 * define somewhere before this block.
 */
/* 选择底层就绪检测原语:默认取系统支持的最"现代"的
 * (epoll > kqueue > poll > Win32 事件),允许在编译期用 WAIT_USE_*
 * 宏手工覆盖,便于分别测试各实现。 */
#if defined(WAIT_USE_EPOLL) || defined(WAIT_USE_POLL) || \
	defined(WAIT_USE_KQUEUE) || defined(WAIT_USE_WIN32)
/* don't overwrite manual choice */
#elif defined(HAVE_SYS_EPOLL_H)
#define WAIT_USE_EPOLL
#elif defined(HAVE_KQUEUE)
#define WAIT_USE_KQUEUE
#elif defined(HAVE_POLL)
#define WAIT_USE_POLL
#elif WIN32
#define WAIT_USE_WIN32
#else
#error "no wait set implementation available"
#endif

/*
 * By default, we use a self-pipe with poll() and a signalfd with epoll(), if
 * available.  For testing the choice can also be manually specified.
 */
/* 在 poll / epoll 后端里,再选择"如何把 SIGURG 变成 fd 可读":Linux 上
 * 优先用 signalfd,其余平台用 self-pipe(管道字节)。同样允许手工指定,
 * 以测不同路径。 */
#if defined(WAIT_USE_POLL) || defined(WAIT_USE_EPOLL)
#if defined(WAIT_USE_SELF_PIPE) || defined(WAIT_USE_SIGNALFD)
/* don't overwrite manual choice */
#elif defined(WAIT_USE_EPOLL) && defined(HAVE_SYS_SIGNALFD_H)
#define WAIT_USE_SIGNALFD
#else
#define WAIT_USE_SELF_PIPE
#endif
#endif

/* typedef in waiteventset.h */
/* 等待事件集合本体(进程私有内存):
 * - owner            : 登记本集合的 ResourceOwner(NULL 表示会话级生命期);
 * - nevents          : 已注册的事件数;
 * - nevents_space    : 集合容量(创建时指定,不可再扩);
 * - events[]         : 事件定义数组(长度为 nevents_space,含 pos / fd /
 *                       events / user_data 等字段,见 waiteventset.h);
 * - latch / latch_pos: 若集合含 WL_LATCH_SET 事件,这里记录 latch 指针与
 *                      对应事件在数组中的下标;等待前先检查 latch 状态可
 *                      省去系统调用;
 * - exit_on_postmaster_death: WL_EXIT_ON_PM_DEATH 会先把事件转成
 *                      WL_POSTMASTER_DEATH 并置此标志,检测到 postmaster
 *                      死亡时直接 proc_exit(1) 而非返回事件;
 * - 各后端专用字段:
 *   - epoll_fd / epoll_ret_events : epoll 描述符与一次性分配的结果数组;
 *   - kqueue_fd / kqueue_ret_events / report_postmaster_not_running :
 *     同上;后者记录"postmaster 已退出但需推迟上报"的状态(kqueue 对同一
 *     进程退出事件只报告一次,靠它维持电平语义);
 *   - pollfds                      : poll() 每次调用都要传完整事件数组,
 *                                    预先准备一份;
 *   - handles                      : Win32 事件句柄数组(元素 0 恒为
 *                                    pgwin32_signal_event,其余按下标 +1)。 */
struct WaitEventSet
{
	ResourceOwner owner;

	int			nevents;		/* number of registered events */
	int			nevents_space;	/* maximum number of events in this set */

	/*
	 * Array, of nevents_space length, storing the definition of events this
	 * set is waiting for.
	 */
	WaitEvent  *events;

	/*
	 * If WL_LATCH_SET is specified in any wait event, latch is a pointer to
	 * said latch, and latch_pos the offset in the ->events array. This is
	 * useful because we check the state of the latch before performing doing
	 * syscalls related to waiting.
	 */
	Latch	   *latch;
	int			latch_pos;

	/*
	 * WL_EXIT_ON_PM_DEATH is converted to WL_POSTMASTER_DEATH, but this flag
	 * is set so that we'll exit immediately if postmaster death is detected,
	 * instead of returning.
	 */
	bool		exit_on_postmaster_death;

#if defined(WAIT_USE_EPOLL)
	int			epoll_fd;
	/* epoll_wait returns events in a user provided arrays, allocate once */
	struct epoll_event *epoll_ret_events;
#elif defined(WAIT_USE_KQUEUE)
	int			kqueue_fd;
	/* kevent returns events in a user provided arrays, allocate once */
	struct kevent *kqueue_ret_events;
	bool		report_postmaster_not_running;
#elif defined(WAIT_USE_POLL)
	/* poll expects events to be waited on every poll() call, prepare once */
	struct pollfd *pollfds;
#elif defined(WAIT_USE_WIN32)

	/*
	 * Array of windows events. The first element always contains
	 * pgwin32_signal_event, so the remaining elements are offset by one (i.e.
	 * event->pos + 1).
	 */
	HANDLE	   *handles;
#endif
};

#ifndef WIN32
/* Are we currently in WaitLatch? The signal handler would like to know. */
/* 本进程当前是否正阻塞在等待循环里(信号处理器想知道的):
 * latch_sigurg_handler 仅在 waiting 时写 self-pipe,避免没人在等时白白
 * 灌满管道。 */
static volatile sig_atomic_t waiting = false;
#endif

#ifdef WAIT_USE_SIGNALFD
/* On Linux, we'll receive SIGURG via a signalfd file descriptor. */
/* Linux:接收 SIGURG 的 signalfd 描述符(初始化后不变) */
static int	signal_fd = -1;
#endif

#ifdef WAIT_USE_SELF_PIPE
/* Read and write ends of the self-pipe */
/* self-pipe 的读端 / 写端描述符,以及所属进程 PID:
 * fork 后子进程要关闭继承的管道、创建自己的(见
 * InitializeWaitEventSupport);owner_pid 用于识别"这份管道归谁"。 */
static int	selfpipe_readfd = -1;
static int	selfpipe_writefd = -1;

/* Process owning the self-pipe --- needed for checking purposes */
static int	selfpipe_owner_pid = 0;

/* Private function prototypes */
/* 内部函数前置声明,权威注释见各定义处。 */
static void latch_sigurg_handler(SIGNAL_ARGS);
static void sendSelfPipeByte(void);
#endif

#if defined(WAIT_USE_SELF_PIPE) || defined(WAIT_USE_SIGNALFD)
static void drain(void);
#endif

#if defined(WAIT_USE_EPOLL)
static void WaitEventAdjustEpoll(WaitEventSet *set, WaitEvent *event, int action);
#elif defined(WAIT_USE_KQUEUE)
static void WaitEventAdjustKqueue(WaitEventSet *set, WaitEvent *event, int old_events);
#elif defined(WAIT_USE_POLL)
static void WaitEventAdjustPoll(WaitEventSet *set, WaitEvent *event);
#elif defined(WAIT_USE_WIN32)
static void WaitEventAdjustWin32(WaitEventSet *set, WaitEvent *event);
#endif

static inline int WaitEventSetWaitBlock(WaitEventSet *set, int cur_timeout,
										WaitEvent *occurred_events, int nevents);

/* ResourceOwner support to hold WaitEventSets */
static void ResOwnerReleaseWaitEventSet(Datum res);

/* WaitEventSet 的资源所有者描述符:在"锁之后"的阶段
 * (RESOURCE_RELEASE_AFTER_LOCKS)释放,优先级 RELEASE_PRIO_WAITEVENTSETS,
 * 保证锁被释放后、会话收尾时才回收事件集,避免使用中的集合被提前销毁。 */
static const ResourceOwnerDesc wait_event_set_resowner_desc =
{
	.name = "WaitEventSet",
	.release_phase = RESOURCE_RELEASE_AFTER_LOCKS,
	.release_priority = RELEASE_PRIO_WAITEVENTSETS,
	.ReleaseResource = ResOwnerReleaseWaitEventSet,
	.DebugPrint = NULL
};

/* Convenience wrappers over ResourceOwnerRemember/Forget */
/* 把 WaitEventSet 登记到 / 从 ResourceOwner 解除的便捷包装 */
static inline void
ResourceOwnerRememberWaitEventSet(ResourceOwner owner, WaitEventSet *set)
{
	ResourceOwnerRemember(owner, PointerGetDatum(set), &wait_event_set_resowner_desc);
}
static inline void
ResourceOwnerForgetWaitEventSet(ResourceOwner owner, WaitEventSet *set)
{
	ResourceOwnerForget(owner, PointerGetDatum(set), &wait_event_set_resowner_desc);
}


/*
 * Initialize the process-local wait event infrastructure.
 *
 * This must be called once during startup of any process that can wait on
 * latches, before it issues any InitLatch() or OwnLatch() calls.
 */
/*
 * InitializeWaitEventSupport - (中文)初始化进程级等待基础设施
 *
 * 【作用】任何要等待 latch 的进程,在使用 latch(InitLatch / OwnLatch)
 * 之前必须调用一次:创建 self-pipe(或 signalfd)并挂接 SIGURG 相关处理。
 *
 * 【设计思想】postmaster 先建好管道,子进程 fork 时会继承 fd;子进程必须
 * 关闭继承的管道、创建自己的(否则多进程共享一个管道会互相误唤醒),这
 * 是"隔离等待者"的关键(EXEC_BACKEND 下靠 FD_CLOEXEC 自动关闭)。管道
 * 两端都设 O_NONBLOCK 与 FD_CLOEXEC:写端非阻塞保证 SetLatch 在管道满
 * 时不卡死,读端非阻塞方便 drain 清空;CLOEXEC 防止 exec 后的程序乱碰。
 * Linux 分支还把 SIGURG 加进 UnBlockSig(使信号被阻塞、由内核转成
 * signalfd 可读事件)并创建 signalfd;两个长活 fd 都要向 fd.c 记账
 * (ReserveExternalFD)。
 *
 * 【参数】无。
 * 【返回值】无(失败 FATAL)。
 */
void
InitializeWaitEventSupport(void)
{
#if defined(WAIT_USE_SELF_PIPE)
	int			pipefd[2];

	if (IsUnderPostmaster)
	{
		/*
		 * We might have inherited connections to a self-pipe created by the
		 * postmaster.  It's critical that child processes create their own
		 * self-pipes, of course, and we really want them to close the
		 * inherited FDs for safety's sake.
		 */
		if (selfpipe_owner_pid != 0)
		{
			/* Assert we go through here but once in a child process */
			Assert(selfpipe_owner_pid != MyProcPid);
			/* Release postmaster's pipe FDs; ignore any error */
			(void) close(selfpipe_readfd);
			(void) close(selfpipe_writefd);
			/* Clean up, just for safety's sake; we'll set these below */
			selfpipe_readfd = selfpipe_writefd = -1;
			selfpipe_owner_pid = 0;
			/* Keep fd.c's accounting straight */
			ReleaseExternalFD();
			ReleaseExternalFD();
		}
		else
		{
			/*
			 * Postmaster didn't create a self-pipe ... or else we're in an
			 * EXEC_BACKEND build, in which case it doesn't matter since the
			 * postmaster's pipe FDs were closed by the action of FD_CLOEXEC.
			 * fd.c won't have state to clean up, either.
			 */
			Assert(selfpipe_readfd == -1);
		}
	}
	else
	{
		/* In postmaster or standalone backend, assert we do this but once */
		Assert(selfpipe_readfd == -1);
		Assert(selfpipe_owner_pid == 0);
	}

	/*
	 * Set up the self-pipe that allows a signal handler to wake up the
	 * poll()/epoll_wait() in WaitLatch. Make the write-end non-blocking, so
	 * that SetLatch won't block if the event has already been set many times
	 * filling the kernel buffer. Make the read-end non-blocking too, so that
	 * we can easily clear the pipe by reading until EAGAIN or EWOULDBLOCK.
	 * Also, make both FDs close-on-exec, since we surely do not want any
	 * child processes messing with them.
	 */
	if (pipe(pipefd) < 0)
		elog(FATAL, "pipe() failed: %m");
	if (fcntl(pipefd[0], F_SETFL, O_NONBLOCK) == -1)
		elog(FATAL, "fcntl(F_SETFL) failed on read-end of self-pipe: %m");
	if (fcntl(pipefd[1], F_SETFL, O_NONBLOCK) == -1)
		elog(FATAL, "fcntl(F_SETFL) failed on write-end of self-pipe: %m");
	if (fcntl(pipefd[0], F_SETFD, FD_CLOEXEC) == -1)
		elog(FATAL, "fcntl(F_SETFD) failed on read-end of self-pipe: %m");
	if (fcntl(pipefd[1], F_SETFD, FD_CLOEXEC) == -1)
		elog(FATAL, "fcntl(F_SETFD) failed on write-end of self-pipe: %m");

	selfpipe_readfd = pipefd[0];
	selfpipe_writefd = pipefd[1];
	selfpipe_owner_pid = MyProcPid;

	/* Tell fd.c about these two long-lived FDs */
	ReserveExternalFD();
	ReserveExternalFD();

	pqsignal(SIGURG, latch_sigurg_handler);
#endif

#ifdef WAIT_USE_SIGNALFD
	sigset_t	signalfd_mask;

	if (IsUnderPostmaster)
	{
		/*
		 * It would probably be safe to re-use the inherited signalfd since
		 * signalfds only see the current process's pending signals, but it
		 * seems less surprising to close it and create our own.
		 */
		if (signal_fd != -1)
		{
			/* Release postmaster's signal FD; ignore any error */
			(void) close(signal_fd);
			signal_fd = -1;
			ReleaseExternalFD();
		}
	}

	/* Block SIGURG, because we'll receive it through a signalfd. */
	sigaddset(&UnBlockSig, SIGURG);

	/* Set up the signalfd to receive SIGURG notifications. */
	sigemptyset(&signalfd_mask);
	sigaddset(&signalfd_mask, SIGURG);
	signal_fd = signalfd(-1, &signalfd_mask, SFD_NONBLOCK | SFD_CLOEXEC);
	if (signal_fd < 0)
		elog(FATAL, "signalfd() failed");
	ReserveExternalFD();
#endif

#ifdef WAIT_USE_KQUEUE
	/* Ignore SIGURG, because we'll receive it via kqueue. */
	pqsignal(SIGURG, PG_SIG_IGN);
#endif
}

/*
 * Create a WaitEventSet with space for nevents different events to wait for.
 *
 * These events can then be efficiently waited upon together, using
 * WaitEventSetWait().
 *
 * The WaitEventSet is tracked by the given 'resowner'.  Use NULL for session
 * lifetime.
 */
/*
 * CreateWaitEventSet - (中文)创建能容纳 nevents 个事件的等待集合
 *
 * 【作用】分配并初始化 WaitEventSet:在一块 MAXALIGN 对齐的连续内存里
 * 装下"结构体 + 事件数组 + 内核后端所需数组"(epoll_event / pollfd /
 * kevent / HANDLE),并创建 epoll / kqueue 句柄。之后用
 * AddWaitEventToSet 往里加事件,用 WaitEventSetWait 统一等待。
 *
 * 【设计思想】一次性分配避免多次 malloc 与指针管理;MAXALIGN 对齐保证
 * 后面的 epoll_event 等结构满足平台对齐要求(纯 sizeof 累加可能破坏
 * 对齐);集合受 resowner 管理(NULL 则活到进程结束);fd 创建走
 * AcquireExternalFD 记账,防止超出进程 fd 限额。
 *
 * 【参数】
 *   resowner —— 归属的资源所有者(NULL = 会话级);
 *   nevents  —— 计划注册的最大事件数。
 * 【返回值】新集合;不再使用须 FreeWaitEventSet。
 */
WaitEventSet *
CreateWaitEventSet(ResourceOwner resowner, int nevents)
{
	WaitEventSet *set;
	char	   *data;
	Size		sz = 0;

	/*
	 * Use MAXALIGN size/alignment to guarantee that later uses of memory are
	 * aligned correctly. E.g. epoll_event might need 8 byte alignment on some
	 * platforms, but earlier allocations like WaitEventSet and WaitEvent
	 * might not be sized to guarantee that when purely using sizeof().
	 */
	sz += MAXALIGN(sizeof(WaitEventSet));
	sz += MAXALIGN(sizeof(WaitEvent) * nevents);

#if defined(WAIT_USE_EPOLL)
	sz += MAXALIGN(sizeof(struct epoll_event) * nevents);
#elif defined(WAIT_USE_KQUEUE)
	sz += MAXALIGN(sizeof(struct kevent) * nevents);
#elif defined(WAIT_USE_POLL)
	sz += MAXALIGN(sizeof(struct pollfd) * nevents);
#elif defined(WAIT_USE_WIN32)
	/* need space for the pgwin32_signal_event */
	sz += MAXALIGN(sizeof(HANDLE) * (nevents + 1));
#endif

	if (resowner != NULL)
		ResourceOwnerEnlarge(resowner);

	data = (char *) MemoryContextAllocZero(TopMemoryContext, sz);

	set = (WaitEventSet *) data;
	data += MAXALIGN(sizeof(WaitEventSet));

	set->events = (WaitEvent *) data;
	data += MAXALIGN(sizeof(WaitEvent) * nevents);

#if defined(WAIT_USE_EPOLL)
	set->epoll_ret_events = (struct epoll_event *) data;
	data += MAXALIGN(sizeof(struct epoll_event) * nevents);
#elif defined(WAIT_USE_KQUEUE)
	set->kqueue_ret_events = (struct kevent *) data;
	data += MAXALIGN(sizeof(struct kevent) * nevents);
#elif defined(WAIT_USE_POLL)
	set->pollfds = (struct pollfd *) data;
	data += MAXALIGN(sizeof(struct pollfd) * nevents);
#elif defined(WAIT_USE_WIN32)
	set->handles = (HANDLE) data;
	data += MAXALIGN(sizeof(HANDLE) * nevents);
#endif

	set->latch = NULL;
	set->nevents_space = nevents;
	set->exit_on_postmaster_death = false;

	if (resowner != NULL)
	{
		ResourceOwnerRememberWaitEventSet(resowner, set);
		set->owner = resowner;
	}

#if defined(WAIT_USE_EPOLL)
	if (!AcquireExternalFD())
		elog(ERROR, "AcquireExternalFD, for epoll_create1, failed: %m");
	set->epoll_fd = epoll_create1(EPOLL_CLOEXEC);
	if (set->epoll_fd < 0)
	{
		ReleaseExternalFD();
		elog(ERROR, "epoll_create1 failed: %m");
	}
#elif defined(WAIT_USE_KQUEUE)
	if (!AcquireExternalFD())
		elog(ERROR, "AcquireExternalFD, for kqueue, failed: %m");
	set->kqueue_fd = kqueue();
	if (set->kqueue_fd < 0)
	{
		ReleaseExternalFD();
		elog(ERROR, "kqueue failed: %m");
	}
	if (fcntl(set->kqueue_fd, F_SETFD, FD_CLOEXEC) == -1)
	{
		int			save_errno = errno;

		close(set->kqueue_fd);
		ReleaseExternalFD();
		errno = save_errno;
		elog(ERROR, "fcntl(F_SETFD) failed on kqueue descriptor: %m");
	}
	set->report_postmaster_not_running = false;
#elif defined(WAIT_USE_WIN32)

	/*
	 * To handle signals while waiting, we need to add a win32 specific event.
	 * We accounted for the additional event at the top of this routine. See
	 * port/win32/signal.c for more details.
	 *
	 * Note: pgwin32_signal_event should be first to ensure that it will be
	 * reported when multiple events are set.  We want to guarantee that
	 * pending signals are serviced.
	 */
	set->handles[0] = pgwin32_signal_event;
#endif

	return set;
}

/*
 * Free a previously created WaitEventSet.
 *
 * Note: preferably, this shouldn't have to free any resources that could be
 * inherited across an exec().  If it did, we'd likely leak those resources in
 * many scenarios.  For the epoll case, we ensure that by setting EPOLL_CLOEXEC
 * when the FD is created.  For the Windows case, we assume that the handles
 * involved are non-inheritable.
 */
/*
 * FreeWaitEventSet - (中文)释放等待事件集合
 *
 * 【作用】解下 ResourceOwner、关闭内核句柄(epoll / kqueue)、按平台清理
 * Win32 事件对象,最后释放内存。
 *
 * 【设计思想】所有 fd 在创建时都带 CLOEXEC(epoll 用 EPOLL_CLOEXEC,
 * Win32 句柄不可继承),所以本函数不担心"资源被 exec 继承"的泄漏问题,
 * 可以放心释放。
 *
 * 【参数】set —— 待释放的集合。
 * 【返回值】无。
 */
void
FreeWaitEventSet(WaitEventSet *set)
{
	if (set->owner)
	{
		ResourceOwnerForgetWaitEventSet(set->owner, set);
		set->owner = NULL;
	}

#if defined(WAIT_USE_EPOLL)
	close(set->epoll_fd);
	ReleaseExternalFD();
#elif defined(WAIT_USE_KQUEUE)
	close(set->kqueue_fd);
	ReleaseExternalFD();
#elif defined(WAIT_USE_WIN32)
	for (WaitEvent *cur_event = set->events;
		 cur_event < (set->events + set->nevents);
		 cur_event++)
	{
		if (cur_event->events & WL_LATCH_SET)
		{
			/* uses the latch's HANDLE */
		}
		else if (cur_event->events & WL_POSTMASTER_DEATH)
		{
			/* uses PostmasterHandle */
		}
		else
		{
			/* Clean up the event object we created for the socket */
			WSAEventSelect(cur_event->fd, NULL, 0);
			WSACloseEvent(set->handles[cur_event->pos + 1]);
		}
	}
#endif

	pfree(set);
}

/*
 * Free a previously created WaitEventSet in a child process after a fork().
 */
/*
 * FreeWaitEventSetAfterFork - (中文)fork 之后在子进程里释放集合
 *
 * 【作用】子进程 fork 后调用:关闭从父进程继承的 epoll / kqueue 描述符
 * 并释放内存(kqueue 本身不会被子进程继承,只需还掉 fd 记账)。
 *
 * 【设计思想】子进程继承了父进程的内存镜像与 fd;epoll fd 是进程相关的
 * 内核对象,子进程里继续持有它没有意义,必须关闭并释放对应记账,避免
 * fd 泄漏。
 *
 * 【参数】set —— 待释放的集合。
 * 【返回值】无。
 */
void
FreeWaitEventSetAfterFork(WaitEventSet *set)
{
#if defined(WAIT_USE_EPOLL)
	close(set->epoll_fd);
	ReleaseExternalFD();
#elif defined(WAIT_USE_KQUEUE)
	/* kqueues are not normally inherited by child processes */
	ReleaseExternalFD();
#endif

	pfree(set);
}

/* ---
 * Add an event to the set. Possible events are:
 * - WL_LATCH_SET: Wait for the latch to be set
 * - WL_POSTMASTER_DEATH: Wait for postmaster to die
 * - WL_SOCKET_READABLE: Wait for socket to become readable,
 *	 can be combined in one event with other WL_SOCKET_* events
 * - WL_SOCKET_WRITEABLE: Wait for socket to become writeable,
 *	 can be combined with other WL_SOCKET_* events
 * - WL_SOCKET_CONNECTED: Wait for socket connection to be established,
 *	 can be combined with other WL_SOCKET_* events (on non-Windows
 *	 platforms, this is the same as WL_SOCKET_WRITEABLE)
 * - WL_SOCKET_ACCEPT: Wait for new connection to a server socket,
 *	 can be combined with other WL_SOCKET_* events (on non-Windows
 *	 platforms, this is the same as WL_SOCKET_READABLE)
 * - WL_SOCKET_CLOSED: Wait for socket to be closed by remote peer.
 * - WL_EXIT_ON_PM_DEATH: Exit immediately if the postmaster dies
 *
 * Returns the offset in WaitEventSet->events (starting from 0), which can be
 * used to modify previously added wait events using ModifyWaitEvent().
 *
 * In the WL_LATCH_SET case the latch must be owned by the current process,
 * i.e. it must be a process-local latch initialized with InitLatch, or a
 * shared latch associated with the current process by calling OwnLatch.
 *
 * In the WL_SOCKET_READABLE/WRITEABLE/CONNECTED/ACCEPT cases, EOF and error
 * conditions cause the socket to be reported as readable/writable/connected,
 * so that the caller can deal with the condition.
 *
 * The user_data pointer specified here will be set for the events returned
 * by WaitEventSetWait(), allowing to easily associate additional data with
 * events.
 */
/*
 * AddWaitEventToSet - (中文)向集合注册一个等待事件
 *
 * 【作用】把"等待什么"登记进集合:事件类型(位掩码)、fd、latch、用户数据。
 * 返回事件在集合内的下标 pos,供 ModifyWaitEvent 后续修改。
 *
 * 【设计思想】
 * - WL_EXIT_ON_PM_DEATH 立即折算成 WL_POSTMASTER_DEATH + 集合级标志
 *   exit_on_postmaster_death;
 * - latch 必须是本进程拥有(owner_pid 校验),且整个集合最多一个 latch,
 *   事件类型必须恰好是 WL_LATCH_SET;等待 socket 事件必须有 fd;
 * - latch 事件在 Unix 后端复用 self-pipe / signalfd 的读端作为 fd——所有
 *   latch 共用这一个 fd,内核只监听它,具体是哪个 latch 由用户态检查
 *   is_set 区分;postmaster 死亡事件监听 postmaster_alive_fds 的读端
 *   (postmaster 崩溃时写端被关闭,读端出现可读/挂断);
 * - 最后调用平台专用的 WaitEventAdjust* 把事件登记进内核。
 *
 * 【参数】
 *   set       —— 集合;
 *   events    —— 事件位掩码(WL_*);
 *   fd        —— socket 事件对应的 fd;
 *   latch     —— latch 事件对应的 latch;
 *   user_data —— 事件发生时随事件返回给调用者的指针。
 * 【返回值】事件在集合中的下标(从 0 起)。
 */
int
AddWaitEventToSet(WaitEventSet *set, uint32 events, pgsocket fd, Latch *latch,
				  void *user_data)
{
	WaitEvent  *event;

	/* not enough space */
	Assert(set->nevents < set->nevents_space);

	if (events == WL_EXIT_ON_PM_DEATH)
	{
		events = WL_POSTMASTER_DEATH;
		set->exit_on_postmaster_death = true;
	}

	if (latch)
	{
		if (latch->owner_pid != MyProcPid)
			elog(ERROR, "cannot wait on a latch owned by another process");
		if (set->latch)
			elog(ERROR, "cannot wait on more than one latch");
		if ((events & WL_LATCH_SET) != WL_LATCH_SET)
			elog(ERROR, "latch events only support being set");
	}
	else
	{
		if (events & WL_LATCH_SET)
			elog(ERROR, "cannot wait on latch without a specified latch");
	}

	/* waiting for socket readiness without a socket indicates a bug */
	if (fd == PGINVALID_SOCKET && (events & WL_SOCKET_MASK))
		elog(ERROR, "cannot wait on socket event without a socket");

	event = &set->events[set->nevents];
	event->pos = set->nevents++;
	event->fd = fd;
	event->events = events;
	event->user_data = user_data;
#ifdef WIN32
	event->reset = false;
#endif

	if (events == WL_LATCH_SET)
	{
		set->latch = latch;
		set->latch_pos = event->pos;
#if defined(WAIT_USE_SELF_PIPE)
		event->fd = selfpipe_readfd;
#elif defined(WAIT_USE_SIGNALFD)
		event->fd = signal_fd;
#else
		event->fd = PGINVALID_SOCKET;
#ifdef WAIT_USE_EPOLL
		return event->pos;
#endif
#endif
	}
	else if (events == WL_POSTMASTER_DEATH)
	{
#ifndef WIN32
		event->fd = postmaster_alive_fds[POSTMASTER_FD_WATCH];
#endif
	}

	/* perform wait primitive specific initialization, if needed */
#if defined(WAIT_USE_EPOLL)
	WaitEventAdjustEpoll(set, event, EPOLL_CTL_ADD);
#elif defined(WAIT_USE_KQUEUE)
	WaitEventAdjustKqueue(set, event, 0);
#elif defined(WAIT_USE_POLL)
	WaitEventAdjustPoll(set, event);
#elif defined(WAIT_USE_WIN32)
	WaitEventAdjustWin32(set, event);
#endif

	return event->pos;
}

/*
 * Change the event mask and, in the WL_LATCH_SET case, the latch associated
 * with the WaitEvent.  The latch may be changed to NULL to disable the latch
 * temporarily, and then set back to a latch later.
 *
 * 'pos' is the id returned by AddWaitEventToSet.
 */
/*
 * ModifyWaitEvent - (中文)修改已注册事件的掩码(及 latch 事件对象)
 *
 * 【作用】按 AddWaitEventToSet 返回的 pos 修改事件:常见于同一个 socket
 * 在"等可读"与"等可写"之间切换。latch 事件可临时改成 NULL(禁用)再改回。
 *
 * 【设计思想】
 * - 只允许在 WL_POSTMASTER_DEATH 与 WL_EXIT_ON_PM_DEATH 之间切换,不
 *   允许移除(集合级标志随之更新),因此该分支要在"事件没变就提前返回"
 *   的快路径之前判断;
 * - 事件与 latch 都没变时直接返回——这是重要优化:libpq 等 socket 层
 *   经常以高频调用本函数切换读写等待,应避免不必要的系统调用;
 * - latch 事件本身不允许改类型(只许换 latch 对象);Unix 后端所有 latch
 *   共用同一个 self-pipe / signalfd,内核对象无需改动,直接返回即可;
 *   只有 Win32 需要更新句柄数组(旧句柄留着,容忍失效事件的虚假唤醒);
 * - 其余情况把新掩码下推到平台专用 Adjust 例程(epoll 走 EPOLL_CTL_MOD,
 *   kqueue 要按旧掩码算差集)。
 *
 * 【参数】
 *   set    —— 集合;
 *   pos    —— 目标事件下标;
 *   events —— 新的事件掩码;
 *   latch  —— 新的 latch(仅 latch 事件有意义,可为 NULL 禁用)。
 * 【返回值】无。
 */
void
ModifyWaitEvent(WaitEventSet *set, int pos, uint32 events, Latch *latch)
{
	WaitEvent  *event;
#if defined(WAIT_USE_KQUEUE)
	int			old_events;
#endif

	Assert(pos < set->nevents);

	event = &set->events[pos];
#if defined(WAIT_USE_KQUEUE)
	old_events = event->events;
#endif

	/*
	 * Allow switching between WL_POSTMASTER_DEATH and WL_EXIT_ON_PM_DEATH.
	 *
	 * Note that because WL_EXIT_ON_PM_DEATH is mapped to WL_POSTMASTER_DEATH
	 * in AddWaitEventToSet(), this needs to be checked before the fast-path
	 * below that checks if 'events' has changed.
	 */
	if (event->events == WL_POSTMASTER_DEATH)
	{
		if (events != WL_POSTMASTER_DEATH && events != WL_EXIT_ON_PM_DEATH)
			elog(ERROR, "cannot remove postmaster death event");
		set->exit_on_postmaster_death = ((events & WL_EXIT_ON_PM_DEATH) != 0);
		return;
	}

	/*
	 * If neither the event mask nor the associated latch changes, return
	 * early. That's an important optimization for some sockets, where
	 * ModifyWaitEvent is frequently used to switch from waiting for reads to
	 * waiting on writes.
	 */
	if (events == event->events &&
		(!(event->events & WL_LATCH_SET) || set->latch == latch))
		return;

	if (event->events & WL_LATCH_SET && events != event->events)
		elog(ERROR, "cannot modify latch event");

	/* FIXME: validate event mask */
	event->events = events;

	if (events == WL_LATCH_SET)
	{
		if (latch && latch->owner_pid != MyProcPid)
			elog(ERROR, "cannot wait on a latch owned by another process");
		set->latch = latch;

		/*
		 * On Unix, we don't need to modify the kernel object because the
		 * underlying pipe (if there is one) is the same for all latches so we
		 * can return immediately.  On Windows, we need to update our array of
		 * handles, but we leave the old one in place and tolerate spurious
		 * wakeups if the latch is disabled.
		 */
#if defined(WAIT_USE_WIN32)
		if (!latch)
			return;
#else
		return;
#endif
	}

#if defined(WAIT_USE_EPOLL)
	WaitEventAdjustEpoll(set, event, EPOLL_CTL_MOD);
#elif defined(WAIT_USE_KQUEUE)
	WaitEventAdjustKqueue(set, event, old_events);
#elif defined(WAIT_USE_POLL)
	WaitEventAdjustPoll(set, event);
#elif defined(WAIT_USE_WIN32)
	WaitEventAdjustWin32(set, event);
#endif
}

#if defined(WAIT_USE_EPOLL)
/*
 * action can be one of EPOLL_CTL_ADD | EPOLL_CTL_MOD | EPOLL_CTL_DEL
 */
/*
 * WaitEventAdjustEpoll - (中文)把事件注册 / 修改 / 删除到 epoll 集合
 *
 * 【作用】action 为 EPOLL_CTL_ADD / EPOLL_CTL_MOD / EPOLL_CTL_DEL,把
 * event 的 fd 与感兴趣的事件位登记到 set->epoll_fd。epoll_event.data.ptr
 * 存 WaitEvent 指针,这样 epoll_wait 返回时能直接拿回对应事件。
 *
 * 【设计思想】内核位与 WL_* 位的映射:WL_LATCH_SET → EPOLLIN
 * (self-pipe / signalfd 可读),WL_POSTMASTER_DEATH → EPOLLIN(死亡管道
 * 可读),socket 事件:READABLE → EPOLLIN,WRITEABLE → EPOLLOUT,
 * CLOSED → EPOLLRDHUP;恒加 EPOLLERR | EPOLLHUP,保证错误 / 挂断也
 * 会上报。ADD / DEL 都传同一个 epoll_event 参数(历史上 epoll 有个要求
 * 如此的旧 bug,带上也无害)。
 *
 * 【参数】
 *   set    —— 集合;
 *   event  —— 目标事件;
 *   action —— EPOLL_CTL_ADD / EPOLL_CTL_MOD / EPOLL_CTL_DEL。
 * 【返回值】无(失败 ERROR)。
 */
static void
WaitEventAdjustEpoll(WaitEventSet *set, WaitEvent *event, int action)
{
	struct epoll_event epoll_ev;
	int			rc;

	/* pointer to our event, returned by epoll_wait */
	epoll_ev.data.ptr = event;
	/* always wait for errors */
	epoll_ev.events = EPOLLERR | EPOLLHUP;

	/* prepare pollfd entry once */
	if (event->events == WL_LATCH_SET)
	{
		Assert(set->latch != NULL);
		epoll_ev.events |= EPOLLIN;
	}
	else if (event->events == WL_POSTMASTER_DEATH)
	{
		epoll_ev.events |= EPOLLIN;
	}
	else
	{
		Assert(event->fd != PGINVALID_SOCKET);
		Assert(event->events & (WL_SOCKET_READABLE |
								WL_SOCKET_WRITEABLE |
								WL_SOCKET_CLOSED));

		if (event->events & WL_SOCKET_READABLE)
			epoll_ev.events |= EPOLLIN;
		if (event->events & WL_SOCKET_WRITEABLE)
			epoll_ev.events |= EPOLLOUT;
		if (event->events & WL_SOCKET_CLOSED)
			epoll_ev.events |= EPOLLRDHUP;
	}

	/*
	 * Even though unused, we also pass epoll_ev as the data argument if
	 * EPOLL_CTL_DEL is passed as action.  There used to be an epoll bug
	 * requiring that, and actually it makes the code simpler...
	 */
	rc = epoll_ctl(set->epoll_fd, action, event->fd, &epoll_ev);

	if (rc < 0)
		ereport(ERROR,
				(errcode_for_socket_access(),
				 errmsg("%s() failed: %m",
						"epoll_ctl")));
}
#endif

#if defined(WAIT_USE_POLL)
/*
 * WaitEventAdjustPoll - (中文)把事件同步到 poll() 的 pollfd 数组
 *
 * 【作用】把 event 的 fd 与事件位翻译成 pollfd 填入 set->pollfds[event->pos]
 * (poll() 每次调用都要传完整数组,所以"准备一次、反复使用")。
 *
 * 【设计思想】映射:WL_LATCH_SET → POLLIN;WL_POSTMASTER_DEATH → POLLIN;
 * socket:READABLE → POLLIN,WRITEABLE → POLLOUT,CLOSED → POLLRDHUP
 * (平台不支持 POLLRDHUP 时省略,调用方可用 WaitEventSetCanReportClosed
 * 查询)。每次先清 revents(内核的输出字段)。
 *
 * 【参数】
 *   set   —— 集合;
 *   event —— 目标事件。
 * 【返回值】无。
 */
static void
WaitEventAdjustPoll(WaitEventSet *set, WaitEvent *event)
{
	struct pollfd *pollfd = &set->pollfds[event->pos];

	pollfd->revents = 0;
	pollfd->fd = event->fd;

	/* prepare pollfd entry once */
	if (event->events == WL_LATCH_SET)
	{
		Assert(set->latch != NULL);
		pollfd->events = POLLIN;
	}
	else if (event->events == WL_POSTMASTER_DEATH)
	{
		pollfd->events = POLLIN;
	}
	else
	{
		Assert(event->events & (WL_SOCKET_READABLE |
								WL_SOCKET_WRITEABLE |
								WL_SOCKET_CLOSED));
		pollfd->events = 0;
		if (event->events & WL_SOCKET_READABLE)
			pollfd->events |= POLLIN;
		if (event->events & WL_SOCKET_WRITEABLE)
			pollfd->events |= POLLOUT;
#ifdef POLLRDHUP
		if (event->events & WL_SOCKET_CLOSED)
			pollfd->events |= POLLRDHUP;
#endif
	}

	Assert(event->fd != PGINVALID_SOCKET);
}
#endif

#if defined(WAIT_USE_KQUEUE)

/*
 * On most BSD family systems, the udata member of struct kevent is of type
 * void *, so we could directly convert to/from WaitEvent *.  Unfortunately,
 * NetBSD has it as intptr_t, so here we wallpaper over that difference with
 * an lvalue cast.
 */
#define AccessWaitEvent(k_ev) (*((WaitEvent **)(&(k_ev)->udata)))

/* 构造一个通用 kevent 的小工具:ident = fd,filter / flags 由调用方给出,
 * udata 记录 WaitEvent 指针(经 AccessWaitEvent 宏解决各 BSD 系统
 * udata 成员类型不同的差异)。 */
static inline void
WaitEventAdjustKqueueAdd(struct kevent *k_ev, int filter, int action,
						 WaitEvent *event)
{
	k_ev->ident = event->fd;
	k_ev->filter = filter;
	k_ev->flags = action;
	k_ev->fflags = 0;
	k_ev->data = 0;
	AccessWaitEvent(k_ev) = event;
}

/* 构造"postmaster 退出"事件的 kevent:监听 PostmasterPid 的进程退出
 * (EVFILT_PROC + NOTE_EXIT)。kqueue 对同一进程的退出只报告一次,因此
 * 之后要靠 report_postmaster_not_running 维持"电平"语义。 */
static inline void
WaitEventAdjustKqueueAddPostmaster(struct kevent *k_ev, WaitEvent *event)
{
	/* For now postmaster death can only be added, not removed. */
	k_ev->ident = PostmasterPid;
	k_ev->filter = EVFILT_PROC;
	k_ev->flags = EV_ADD;
	k_ev->fflags = NOTE_EXIT;
	k_ev->data = 0;
	AccessWaitEvent(k_ev) = event;
}

/* 构造"latch 置位"事件的 kevent:监听 SIGURG(EVFILT_SIGNAL)。SIGURG
 * 已被设为忽略,进程不会真的收到信号,只是由 kqueue 捕获通知。 */
static inline void
WaitEventAdjustKqueueAddLatch(struct kevent *k_ev, WaitEvent *event)
{
	/* For now latch can only be added, not removed. */
	k_ev->ident = SIGURG;
	k_ev->filter = EVFILT_SIGNAL;
	k_ev->flags = EV_ADD;
	k_ev->fflags = 0;
	k_ev->data = 0;
	AccessWaitEvent(k_ev) = event;
}

/*
 * old_events is the previous event mask, used to compute what has changed.
 */
/*
 * WaitEventAdjustKqueue - (中文)把事件掩码变化同步到 kqueue
 *
 * 【作用】对比 old_events 与新掩码,计算需要 ADD / DELETE 的 kevent 并
 * 用一次 kevent() 提交。kqueue 把"可读 / 可写"看成两个独立事件,因此
 * 要做差集运算;latch 与 postmaster 死亡事件只加不删。
 *
 * 【设计思想】postmaster 事件登记时若失败(ESRCH / EACCES,说明进程已
 * 不存在)或检测到 PostmasterPid != getppid() 且 PostmasterIsAlive()
 * 为假,就置 report_postmaster_not_running,由下一次
 * WaitEventSetWaitBlock 上报——因为 postmaster 可能已死甚至 PID 已被
 * 复用,此刻不能当成普通事件立即返回。
 *
 * 【参数】
 *   set        —— 集合;
 *   event      —— 目标事件;
 *   old_events —— 修改前的事件掩码。
 * 【返回值】无(kevent 调用失败 ERROR)。
 */
static void
WaitEventAdjustKqueue(WaitEventSet *set, WaitEvent *event, int old_events)
{
	int			rc;
	struct kevent k_ev[2];
	int			count = 0;
	bool		new_filt_read = false;
	bool		old_filt_read = false;
	bool		new_filt_write = false;
	bool		old_filt_write = false;

	if (old_events == event->events)
		return;

	Assert(event->events != WL_LATCH_SET || set->latch != NULL);
	Assert(event->events == WL_LATCH_SET ||
		   event->events == WL_POSTMASTER_DEATH ||
		   (event->events & (WL_SOCKET_READABLE |
							 WL_SOCKET_WRITEABLE |
							 WL_SOCKET_CLOSED)));

	if (event->events == WL_POSTMASTER_DEATH)
	{
		/*
		 * Unlike all the other implementations, we detect postmaster death
		 * using process notification instead of waiting on the postmaster
		 * alive pipe.
		 */
		WaitEventAdjustKqueueAddPostmaster(&k_ev[count++], event);
	}
	else if (event->events == WL_LATCH_SET)
	{
		/* We detect latch wakeup using a signal event. */
		WaitEventAdjustKqueueAddLatch(&k_ev[count++], event);
	}
	else
	{
		/*
		 * We need to compute the adds and deletes required to get from the
		 * old event mask to the new event mask, since kevent treats readable
		 * and writable as separate events.
		 */
		if (old_events & (WL_SOCKET_READABLE | WL_SOCKET_CLOSED))
			old_filt_read = true;
		if (event->events & (WL_SOCKET_READABLE | WL_SOCKET_CLOSED))
			new_filt_read = true;
		if (old_events & WL_SOCKET_WRITEABLE)
			old_filt_write = true;
		if (event->events & WL_SOCKET_WRITEABLE)
			new_filt_write = true;
		if (old_filt_read && !new_filt_read)
			WaitEventAdjustKqueueAdd(&k_ev[count++], EVFILT_READ, EV_DELETE,
									 event);
		else if (!old_filt_read && new_filt_read)
			WaitEventAdjustKqueueAdd(&k_ev[count++], EVFILT_READ, EV_ADD,
									 event);
		if (old_filt_write && !new_filt_write)
			WaitEventAdjustKqueueAdd(&k_ev[count++], EVFILT_WRITE, EV_DELETE,
									 event);
		else if (!old_filt_write && new_filt_write)
			WaitEventAdjustKqueueAdd(&k_ev[count++], EVFILT_WRITE, EV_ADD,
									 event);
	}

	/* For WL_SOCKET_READ -> WL_SOCKET_CLOSED, no change needed. */
	if (count == 0)
		return;

	Assert(count <= 2);

	rc = kevent(set->kqueue_fd, &k_ev[0], count, NULL, 0, NULL);

	/*
	 * When adding the postmaster's pid, we have to consider that it might
	 * already have exited and perhaps even been replaced by another process
	 * with the same pid.  If so, we have to defer reporting this as an event
	 * until the next call to WaitEventSetWaitBlock().
	 */

	if (rc < 0)
	{
		if (event->events == WL_POSTMASTER_DEATH &&
			(errno == ESRCH || errno == EACCES))
			set->report_postmaster_not_running = true;
		else
			ereport(ERROR,
					(errcode_for_socket_access(),
					 errmsg("%s() failed: %m",
							"kevent")));
	}
	else if (event->events == WL_POSTMASTER_DEATH &&
			 PostmasterPid != getppid() &&
			 !PostmasterIsAlive())
	{
		/*
		 * The extra PostmasterIsAliveInternal() check prevents false alarms
		 * on systems that give a different value for getppid() while being
		 * traced by a debugger.
		 */
		set->report_postmaster_not_running = true;
	}
}

#endif

#if defined(WAIT_USE_WIN32)
StaticAssertDecl(WSA_INVALID_EVENT == NULL, "");

/*
 * WaitEventAdjustWin32 - (中文)把事件同步到 Win32 句柄数组
 *
 * 【作用】按事件类型把 set->handles[event->pos + 1] 填成对应句柄:
 * latch → latch 的 Win32 event;postmaster 死亡 → PostmasterHandle;
 * socket → 用 WSAEventSelect 把 fd 与新建 / 复用的 WSA event 关联,
 * 掩码恒含 FD_CLOSE(错误 / EOF 总是上报)。
 *
 * 【设计思想】socket 的 WSA event 按需惰性创建;每次调整都用
 * WSAEventSelect 重设通知掩码,使"读 / 写 / 连接"的切换生效。
 *
 * 【参数】
 *   set   —— 集合;
 *   event —— 目标事件。
 * 【返回值】无(失败 ERROR)。
 */
static void
WaitEventAdjustWin32(WaitEventSet *set, WaitEvent *event)
{
	HANDLE	   *handle = &set->handles[event->pos + 1];

	if (event->events == WL_LATCH_SET)
	{
		Assert(set->latch != NULL);
		*handle = set->latch->event;
	}
	else if (event->events == WL_POSTMASTER_DEATH)
	{
		*handle = PostmasterHandle;
	}
	else
	{
		int			flags = FD_CLOSE;	/* always check for errors/EOF */

		if (event->events & WL_SOCKET_READABLE)
			flags |= FD_READ;
		if (event->events & WL_SOCKET_WRITEABLE)
			flags |= FD_WRITE;
		if (event->events & WL_SOCKET_CONNECTED)
			flags |= FD_CONNECT;
		if (event->events & WL_SOCKET_ACCEPT)
			flags |= FD_ACCEPT;

		if (*handle == WSA_INVALID_EVENT)
		{
			*handle = WSACreateEvent();
			if (*handle == WSA_INVALID_EVENT)
				elog(ERROR, "failed to create event for socket: error code %d",
					 WSAGetLastError());
		}
		if (WSAEventSelect(event->fd, *handle, flags) != 0)
			elog(ERROR, "failed to set up event for socket: error code %d",
				 WSAGetLastError());

		Assert(event->fd != PGINVALID_SOCKET);
	}
}
#endif

/*
 * Wait for events added to the set to happen, or until the timeout is
 * reached.  At most nevents occurred events are returned.
 *
 * If timeout = -1, block until an event occurs; if 0, check sockets for
 * readiness, but don't block; if > 0, block for at most timeout milliseconds.
 *
 * Returns the number of events occurred, or 0 if the timeout was reached.
 *
 * Returned events will have the fd, pos, user_data fields set to the
 * values associated with the registered event.
 */
/*
 * WaitEventSetWait - (中文)等待集合中的事件发生(顶层循环)
 *
 * 【作用】阻塞直到至少一个注册事件发生或超时;把发生的事件(最多 nevents
 * 个)填入 occurred_events 数组,返回个数。timeout = -1 无限等待,
 * = 0 只查不睡,> 0 最多等那么多毫秒。
 *
 * 【设计思想】
 * - 先检查 latch 是否已置位:是则不必进内核睡眠,直接返回;若还没置位,
 *   置 maybe_sleeping 并内存屏障再复查,与 SetLatch 侧的屏障配对,堵住
 *   "检查-睡眠"间隙里信号到达的竞态;
 * - latch 已置位时仍以 0 超时做一次内核轮询,尽量在同一批返回里带上
 *   其他非 latch 事件(满足调用方"一次等多样"的语义);
 * - 返回 0(被 EINTR 打断等)时重算剩余超时再循环,保证总等待时长不变;
 * - 等待期间通过 pgstat_report_wait_start / End 登记等待事件,用于
 *   pg_stat_activity;Unix 侧维护 waiting 标志供信号处理器判断是否
 *   要写 self-pipe(Win32 侧则先派发排队的信号)。
 *
 * 【参数】
 *   set              —— 集合;
 *   timeout          —— 毫秒(-1 无限,0 不阻塞,>0 上限);
 *   occurred_events  —— 输出:发生的事件数组(由调用方分配);
 *   nevents          —— 输出数组容量(至少 1);
 *   wait_event_info  —— 等待事件标识(供 pg_stat_activity)。
 * 【返回值】发生的事件数;超时返回 0。事件的 fd / pos / user_data 均
 *          来自注册时的值。
 */
int
WaitEventSetWait(WaitEventSet *set, long timeout,
				 WaitEvent *occurred_events, int nevents,
				 uint32 wait_event_info)
{
	int			returned_events = 0;
	instr_time	start_time;
	instr_time	cur_time;
	long		cur_timeout = -1;

	Assert(nevents > 0);

	/*
	 * Initialize timeout if requested.  We must record the current time so
	 * that we can determine the remaining timeout if interrupted.
	 */
	if (timeout >= 0)
	{
		INSTR_TIME_SET_CURRENT(start_time);
		Assert(timeout >= 0 && timeout <= INT_MAX);
		cur_timeout = timeout;
	}
	else
		INSTR_TIME_SET_ZERO(start_time);

	pgstat_report_wait_start(wait_event_info);

#ifndef WIN32
	waiting = true;
#else
	/* Ensure that signals are serviced even if latch is already set */
	pgwin32_dispatch_queued_signals();
#endif
	while (returned_events == 0)
	{
		int			rc;

		/*
		 * Check if the latch is set already first.  If so, we either exit
		 * immediately or ask the kernel for further events available right
		 * now without waiting, depending on how many events the caller wants.
		 *
		 * If someone sets the latch between this and the
		 * WaitEventSetWaitBlock() below, the setter will write a byte to the
		 * pipe (or signal us and the signal handler will do that), and the
		 * readiness routine will return immediately.
		 *
		 * On unix, If there's a pending byte in the self pipe, we'll notice
		 * whenever blocking. Only clearing the pipe in that case avoids
		 * having to drain it every time WaitLatchOrSocket() is used. Should
		 * the pipe-buffer fill up we're still ok, because the pipe is in
		 * nonblocking mode. It's unlikely for that to happen, because the
		 * self pipe isn't filled unless we're blocking (waiting = true), or
		 * from inside a signal handler in latch_sigurg_handler().
		 *
		 * On windows, we'll also notice if there's a pending event for the
		 * latch when blocking, but there's no danger of anything filling up,
		 * as "Setting an event that is already set has no effect.".
		 *
		 * Note: we assume that the kernel calls involved in latch management
		 * will provide adequate synchronization on machines with weak memory
		 * ordering, so that we cannot miss seeing is_set if a notification
		 * has already been queued.
		 */
		if (set->latch && !set->latch->is_set)
		{
			/* about to sleep on a latch */
			set->latch->maybe_sleeping = true;
			pg_memory_barrier();
			/* and recheck */
		}

		if (set->latch && set->latch->is_set)
		{
			occurred_events->fd = PGINVALID_SOCKET;
			occurred_events->pos = set->latch_pos;
			occurred_events->user_data =
				set->events[set->latch_pos].user_data;
			occurred_events->events = WL_LATCH_SET;
			occurred_events++;
			returned_events++;

			/* could have been set above */
			set->latch->maybe_sleeping = false;

			if (returned_events == nevents)
				break;			/* output buffer full already */

			/*
			 * Even though we already have an event, we'll poll just once with
			 * zero timeout to see what non-latch events we can fit into the
			 * output buffer at the same time.
			 */
			cur_timeout = 0;
			timeout = 0;
		}

		/*
		 * Wait for events using the readiness primitive chosen at the top of
		 * this file. If -1 is returned, a timeout has occurred, if 0 we have
		 * to retry, everything >= 1 is the number of returned events.
		 */
		rc = WaitEventSetWaitBlock(set, cur_timeout,
								   occurred_events, nevents - returned_events);

		if (set->latch &&
			set->latch->maybe_sleeping)
			set->latch->maybe_sleeping = false;

		if (rc == -1)
			break;				/* timeout occurred */
		else
			returned_events += rc;

		/* If we're not done, update cur_timeout for next iteration */
		if (returned_events == 0 && timeout >= 0)
		{
			INSTR_TIME_SET_CURRENT(cur_time);
			INSTR_TIME_SUBTRACT(cur_time, start_time);
			cur_timeout = timeout - (long) INSTR_TIME_GET_MILLISEC(cur_time);
			if (cur_timeout <= 0)
				break;
		}
	}
#ifndef WIN32
	waiting = false;
#endif

	pgstat_report_wait_end();

	return returned_events;
}


#if defined(WAIT_USE_EPOLL)

/*
 * Wait using linux's epoll_wait(2).
 *
 * This is the preferable wait method, as several readiness notifications are
 * delivered, without having to iterate through all of set->events. The return
 * epoll_event struct contain a pointer to our events, making association
 * easy.
 */
/*
 * WaitEventSetWaitBlock - (中文)epoll 内核睡眠与事件翻译(单次)
 *
 * 【作用】执行一次 epoll_wait,把返回的 epoll 事件翻译成 WaitEvent 填进
 * 输出数组。返回 -1 表示超时,0 表示被 EINTR 打断需重试,>0 为事件数。
 *
 * 【设计思想】epoll 的 data.ptr 直接指向 WaitEvent,免去逐一扫描全部
 * 事件的代价(相比 poll 后端的主要优势);对每个 epoll 事件:
 * - latch 事件:先 drain() 排空 self-pipe / signalfd,再校验
 *   maybe_sleeping && is_set 才上报 WL_LATCH_SET(防止"管道里有旧字节
 *   但 latch 未置位"的误报);
 * - postmaster 死亡:EPOLLIN / EPOLLERR / EPOLLHUP 都算候选,但必须
 *   PostmasterIsAliveInternal() 复核(警惕旧平台的虚假事件;PID 可能被
 *   复用),确认后按 exit_on_postmaster_death 决定 proc_exit 或上报;
 * - socket 事件:EPOLLIN / EPOLLOUT / EPOLLRDHUP 与请求的掩码取交集,
 *   错误位(EPOLLERR / EPOLLHUP)也按可读 / 可写 / 关闭上报,让调用方
 *   自己处理 EOF 条件。
 *
 * 【参数】
 *   set              —— 集合;
 *   cur_timeout      —— 本次睡眠毫秒数;
 *   occurred_events  —— 输出数组;
 *   nevents          —— 本次最多返回的事件数。
 * 【返回值】-1 超时;0 重试;>=1 事件数。
 */
static inline int
WaitEventSetWaitBlock(WaitEventSet *set, int cur_timeout,
					  WaitEvent *occurred_events, int nevents)
{
	int			returned_events = 0;
	int			rc;
	WaitEvent  *cur_event;
	struct epoll_event *cur_epoll_event;

	/* Sleep */
	rc = epoll_wait(set->epoll_fd, set->epoll_ret_events,
					Min(nevents, set->nevents_space), cur_timeout);

	/* Check return code */
	if (rc < 0)
	{
		/* EINTR is okay, otherwise complain */
		if (errno != EINTR)
		{
			waiting = false;
			ereport(ERROR,
					(errcode_for_socket_access(),
					 errmsg("%s() failed: %m",
							"epoll_wait")));
		}
		return 0;
	}
	else if (rc == 0)
	{
		/* timeout exceeded */
		return -1;
	}

	/*
	 * At least one event occurred, iterate over the returned epoll events
	 * until they're either all processed, or we've returned all the events
	 * the caller desired.
	 */
	for (cur_epoll_event = set->epoll_ret_events;
		 cur_epoll_event < (set->epoll_ret_events + rc) &&
		 returned_events < nevents;
		 cur_epoll_event++)
	{
		/* epoll's data pointer is set to the associated WaitEvent */
		cur_event = (WaitEvent *) cur_epoll_event->data.ptr;

		occurred_events->pos = cur_event->pos;
		occurred_events->user_data = cur_event->user_data;
		occurred_events->events = 0;

		if (cur_event->events == WL_LATCH_SET &&
			cur_epoll_event->events & (EPOLLIN | EPOLLERR | EPOLLHUP))
		{
			/* Drain the signalfd. */
			drain();

			if (set->latch && set->latch->maybe_sleeping && set->latch->is_set)
			{
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_LATCH_SET;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events == WL_POSTMASTER_DEATH &&
				 cur_epoll_event->events & (EPOLLIN | EPOLLERR | EPOLLHUP))
		{
			/*
			 * We expect an EPOLLHUP when the remote end is closed, but
			 * because we don't expect the pipe to become readable or to have
			 * any errors either, treat those cases as postmaster death, too.
			 *
			 * Be paranoid about a spurious event signaling the postmaster as
			 * being dead.  There have been reports about that happening with
			 * older primitives (select(2) to be specific), and a spurious
			 * WL_POSTMASTER_DEATH event would be painful. Re-checking doesn't
			 * cost much.
			 */
			if (!PostmasterIsAliveInternal())
			{
				if (set->exit_on_postmaster_death)
					proc_exit(1);
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_POSTMASTER_DEATH;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events & (WL_SOCKET_READABLE |
									  WL_SOCKET_WRITEABLE |
									  WL_SOCKET_CLOSED))
		{
			Assert(cur_event->fd != PGINVALID_SOCKET);

			if ((cur_event->events & WL_SOCKET_READABLE) &&
				(cur_epoll_event->events & (EPOLLIN | EPOLLERR | EPOLLHUP)))
			{
				/* data available in socket, or EOF */
				occurred_events->events |= WL_SOCKET_READABLE;
			}

			if ((cur_event->events & WL_SOCKET_WRITEABLE) &&
				(cur_epoll_event->events & (EPOLLOUT | EPOLLERR | EPOLLHUP)))
			{
				/* writable, or EOF */
				occurred_events->events |= WL_SOCKET_WRITEABLE;
			}

			if ((cur_event->events & WL_SOCKET_CLOSED) &&
				(cur_epoll_event->events & (EPOLLRDHUP | EPOLLERR | EPOLLHUP)))
			{
				/* remote peer shut down, or error */
				occurred_events->events |= WL_SOCKET_CLOSED;
			}

			if (occurred_events->events != 0)
			{
				occurred_events->fd = cur_event->fd;
				occurred_events++;
				returned_events++;
			}
		}
	}

	return returned_events;
}

#elif defined(WAIT_USE_KQUEUE)

/*
 * Wait using kevent(2) on BSD-family systems and macOS.
 *
 * For now this mirrors the epoll code, but in future it could modify the fd
 * set in the same call to kevent as it uses for waiting instead of doing that
 * with separate system calls.
 */
/*
 * WaitEventSetWaitBlock - (中文)kqueue 内核睡眠与事件翻译(单次,BSD 系)
 *
 * 【作用】执行一次 kevent 等待,把返回的事件翻译成 WaitEvent。返回 -1
 * 表示超时,0 表示被 EINTR 打断需重试,>0 为事件数。
 *
 * 【设计思想】超时毫秒换算成 timespec;先处理此前登记时发现的上报挂起
 * 的 postmaster 死亡(report_postmaster_not_running);事件翻译:
 * - latch 事件(EVFILT_SIGNAL):同样校验 maybe_sleeping && is_set;
 * - postmaster 死亡(EVFILT_PROC + NOTE_EXIT):内核只通知一次,因此
 *   置 report_postmaster_not_running 记录,维持"电平"语义供后续调用
 *   持续上报,并按 exit_on_postmaster_death 决定退出还是返回;
 * - socket:EVFILT_READ 对应可读与对端关闭(EV_EOF 才报 CLOSED),
 *   EVFILT_WRITE 对应可写。
 *
 * 【参数】
 *   set              —— 集合;
 *   cur_timeout      —— 本次睡眠毫秒数;
 *   occurred_events  —— 输出数组;
 *   nevents          —— 本次最多返回的事件数。
 * 【返回值】-1 超时;0 重试;>=1 事件数。
 */
static int
WaitEventSetWaitBlock(WaitEventSet *set, int cur_timeout,
					  WaitEvent *occurred_events, int nevents)
{
	int			returned_events = 0;
	int			rc;
	WaitEvent  *cur_event;
	struct kevent *cur_kqueue_event;
	struct timespec timeout;
	struct timespec *timeout_p;

	if (cur_timeout < 0)
		timeout_p = NULL;
	else
	{
		timeout.tv_sec = cur_timeout / 1000;
		timeout.tv_nsec = (cur_timeout % 1000) * 1000000;
		timeout_p = &timeout;
	}

	/*
	 * Report postmaster events discovered by WaitEventAdjustKqueue() or an
	 * earlier call to WaitEventSetWait().
	 */
	if (unlikely(set->report_postmaster_not_running))
	{
		if (set->exit_on_postmaster_death)
			proc_exit(1);
		occurred_events->fd = PGINVALID_SOCKET;
		occurred_events->events = WL_POSTMASTER_DEATH;
		return 1;
	}

	/* Sleep */
	rc = kevent(set->kqueue_fd, NULL, 0,
				set->kqueue_ret_events,
				Min(nevents, set->nevents_space),
				timeout_p);

	/* Check return code */
	if (rc < 0)
	{
		/* EINTR is okay, otherwise complain */
		if (errno != EINTR)
		{
			waiting = false;
			ereport(ERROR,
					(errcode_for_socket_access(),
					 errmsg("%s() failed: %m",
							"kevent")));
		}
		return 0;
	}
	else if (rc == 0)
	{
		/* timeout exceeded */
		return -1;
	}

	/*
	 * At least one event occurred, iterate over the returned kqueue events
	 * until they're either all processed, or we've returned all the events
	 * the caller desired.
	 */
	for (cur_kqueue_event = set->kqueue_ret_events;
		 cur_kqueue_event < (set->kqueue_ret_events + rc) &&
		 returned_events < nevents;
		 cur_kqueue_event++)
	{
		/* kevent's udata points to the associated WaitEvent */
		cur_event = AccessWaitEvent(cur_kqueue_event);

		occurred_events->pos = cur_event->pos;
		occurred_events->user_data = cur_event->user_data;
		occurred_events->events = 0;

		if (cur_event->events == WL_LATCH_SET &&
			cur_kqueue_event->filter == EVFILT_SIGNAL)
		{
			if (set->latch && set->latch->maybe_sleeping && set->latch->is_set)
			{
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_LATCH_SET;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events == WL_POSTMASTER_DEATH &&
				 cur_kqueue_event->filter == EVFILT_PROC &&
				 (cur_kqueue_event->fflags & NOTE_EXIT) != 0)
		{
			/*
			 * The kernel will tell this kqueue object only once about the
			 * exit of the postmaster, so let's remember that for next time so
			 * that we provide level-triggered semantics.
			 */
			set->report_postmaster_not_running = true;

			if (set->exit_on_postmaster_death)
				proc_exit(1);
			occurred_events->fd = PGINVALID_SOCKET;
			occurred_events->events = WL_POSTMASTER_DEATH;
			occurred_events++;
			returned_events++;
		}
		else if (cur_event->events & (WL_SOCKET_READABLE |
									  WL_SOCKET_WRITEABLE |
									  WL_SOCKET_CLOSED))
		{
			Assert(cur_event->fd >= 0);

			if ((cur_event->events & WL_SOCKET_READABLE) &&
				(cur_kqueue_event->filter == EVFILT_READ))
			{
				/* readable, or EOF */
				occurred_events->events |= WL_SOCKET_READABLE;
			}

			if ((cur_event->events & WL_SOCKET_CLOSED) &&
				(cur_kqueue_event->filter == EVFILT_READ) &&
				(cur_kqueue_event->flags & EV_EOF))
			{
				/* the remote peer has shut down */
				occurred_events->events |= WL_SOCKET_CLOSED;
			}

			if ((cur_event->events & WL_SOCKET_WRITEABLE) &&
				(cur_kqueue_event->filter == EVFILT_WRITE))
			{
				/* writable, or EOF */
				occurred_events->events |= WL_SOCKET_WRITEABLE;
			}

			if (occurred_events->events != 0)
			{
				occurred_events->fd = cur_event->fd;
				occurred_events++;
				returned_events++;
			}
		}
	}

	return returned_events;
}

#elif defined(WAIT_USE_POLL)

/*
 * Wait using poll(2).
 *
 * This allows to receive readiness notifications for several events at once,
 * but requires iterating through all of set->pollfds.
 */
/*
 * WaitEventSetWaitBlock - (中文)poll 内核睡眠与事件翻译(单次)
 *
 * 【作用】执行一次 poll() 并遍历全部 pollfds 的 revents,把就绪事件翻译
 * 成 WaitEvent。返回 -1 表示超时,0 表示被 EINTR 打断需重试,>0 为事件数。
 *
 * 【设计思想】poll 后端需要"全量扫描 + 全量翻内核位",且无法直接拿到
 * 事件指针,只能按数组下标对应 set->events;错误位组合
 * (POLLHUP | POLLERR | POLLNVAL) 统一按可读 / 可写 / 关闭上报;latch
 * 与 postmaster 死亡事件的处理同 epoll 后端(先 drain / 先复核存活)。
 *
 * 【参数】
 *   set              —— 集合;
 *   cur_timeout      —— 本次睡眠毫秒数;
 *   occurred_events  —— 输出数组;
 *   nevents          —— 本次最多返回的事件数。
 * 【返回值】-1 超时;0 重试;>=1 事件数。
 */
static inline int
WaitEventSetWaitBlock(WaitEventSet *set, int cur_timeout,
					  WaitEvent *occurred_events, int nevents)
{
	int			returned_events = 0;
	int			rc;
	WaitEvent  *cur_event;
	struct pollfd *cur_pollfd;

	/* Sleep */
	rc = poll(set->pollfds, set->nevents, cur_timeout);

	/* Check return code */
	if (rc < 0)
	{
		/* EINTR is okay, otherwise complain */
		if (errno != EINTR)
		{
			waiting = false;
			ereport(ERROR,
					(errcode_for_socket_access(),
					 errmsg("%s() failed: %m",
							"poll")));
		}
		return 0;
	}
	else if (rc == 0)
	{
		/* timeout exceeded */
		return -1;
	}

	for (cur_event = set->events, cur_pollfd = set->pollfds;
		 cur_event < (set->events + set->nevents) &&
		 returned_events < nevents;
		 cur_event++, cur_pollfd++)
	{
		/* no activity on this FD, skip */
		if (cur_pollfd->revents == 0)
			continue;

		occurred_events->pos = cur_event->pos;
		occurred_events->user_data = cur_event->user_data;
		occurred_events->events = 0;

		if (cur_event->events == WL_LATCH_SET &&
			(cur_pollfd->revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL)))
		{
			/* There's data in the self-pipe, clear it. */
			drain();

			if (set->latch && set->latch->maybe_sleeping && set->latch->is_set)
			{
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_LATCH_SET;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events == WL_POSTMASTER_DEATH &&
				 (cur_pollfd->revents & (POLLIN | POLLHUP | POLLERR | POLLNVAL)))
		{
			/*
			 * We expect a POLLHUP when the remote end is closed, but because
			 * we don't expect the pipe to become readable or to have any
			 * errors either, treat those cases as postmaster death, too.
			 *
			 * Be paranoid about a spurious event signaling the postmaster as
			 * being dead.  There have been reports about that happening with
			 * older primitives (select(2) to be specific), and a spurious
			 * WL_POSTMASTER_DEATH event would be painful.  Re-checking
			 * doesn't cost much.
			 */
			if (!PostmasterIsAliveInternal())
			{
				if (set->exit_on_postmaster_death)
					proc_exit(1);
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_POSTMASTER_DEATH;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events & (WL_SOCKET_READABLE |
									  WL_SOCKET_WRITEABLE |
									  WL_SOCKET_CLOSED))
		{
			int			errflags = POLLHUP | POLLERR | POLLNVAL;

			Assert(cur_event->fd >= PGINVALID_SOCKET);

			if ((cur_event->events & WL_SOCKET_READABLE) &&
				(cur_pollfd->revents & (POLLIN | errflags)))
			{
				/* data available in socket, or EOF */
				occurred_events->events |= WL_SOCKET_READABLE;
			}

			if ((cur_event->events & WL_SOCKET_WRITEABLE) &&
				(cur_pollfd->revents & (POLLOUT | errflags)))
			{
				/* writeable, or EOF */
				occurred_events->events |= WL_SOCKET_WRITEABLE;
			}

#ifdef POLLRDHUP
			if ((cur_event->events & WL_SOCKET_CLOSED) &&
				(cur_pollfd->revents & (POLLRDHUP | errflags)))
			{
				/* remote peer closed, or error */
				occurred_events->events |= WL_SOCKET_CLOSED;
			}
#endif

			if (occurred_events->events != 0)
			{
				occurred_events->fd = cur_event->fd;
				occurred_events++;
				returned_events++;
			}
		}
	}
	return returned_events;
}

#elif defined(WAIT_USE_WIN32)

/*
 * Wait using Windows' WaitForMultipleObjects().  Each call only "consumes" one
 * event, so we keep calling until we've filled up our output buffer to match
 * the behavior of the other implementations.
 *
 * https://blogs.msdn.microsoft.com/oldnewthing/20150409-00/?p=44273
 */
/*
 * WaitEventSetWaitBlock - (中文)Win32 等待与事件翻译(单次)
 *
 * 【作用】用 WaitForMultipleObjects 等待句柄数组(元素 0 恒为信号事件),
 * 把命中的事件翻译成 WaitEvent;一次只"消费"一个句柄,所以用零超时的
 * 第二轮轮询尽量把多个就绪事件凑进同一次返回,与其他后端行为对齐。
 *
 * 【设计思想】
 * - 睡眠前先处理标记为需要重置的事件,并对每个 socket 做"预检":用
 *   WSARecv(MSG_PEEK) 探测可读(补 FD_READ 通知可能已丢的竞态)、用
 *   零字节 WSASend 探测可写(Windows 不会自动报 FD_WRITE 除非上次发送
 *   失败过 WSAEWOULDBLOCK);
 * - WAIT_OBJECT_0 表示信号事件,派发排队信号后返回 0 重试;
 * - latch 事件需 ResetEvent 手动重置;postmaster 死亡同样复核
 *   PostmasterIsAliveInternal;socket 事件用 WSAEnumNetworkEvents 取
 *   FD_READ / FD_WRITE / FD_CONNECT / FD_ACCEPT / FD_CLOSE 位,
 *   FD_CLOSE 会把所有请求的 socket 位都置上(EOF / 错误),并置
 *   cur_event->reset 以便下次等待前重设,避免可读事件丢失造成永久挂起;
 * - 处理完一个事件后,继续用零超时轮询剩余句柄,直到输出缓冲满或扫完。
 *
 * 【参数】
 *   set              —— 集合;
 *   cur_timeout      —— 本次睡眠毫秒数;
 *   occurred_events  —— 输出数组;
 *   nevents          —— 本次最多返回的事件数。
 * 【返回值】-1 超时;0 重试;>=1 事件数。
 */
static inline int
WaitEventSetWaitBlock(WaitEventSet *set, int cur_timeout,
					  WaitEvent *occurred_events, int nevents)
{
	int			returned_events = 0;
	DWORD		rc;
	WaitEvent  *cur_event;

	/* Reset any wait events that need it */
	for (cur_event = set->events;
		 cur_event < (set->events + set->nevents);
		 cur_event++)
	{
		if (cur_event->reset)
		{
			WaitEventAdjustWin32(set, cur_event);
			cur_event->reset = false;
		}

		/*
		 * We associate the socket with a new event handle for each
		 * WaitEventSet.  FD_CLOSE is only generated once if the other end
		 * closes gracefully.  Therefore we might miss the FD_CLOSE
		 * notification, if it was delivered to another event after we stopped
		 * waiting for it.  Close that race by peeking for EOF after setting
		 * up this handle to receive notifications, and before entering the
		 * sleep.
		 *
		 * XXX If we had one event handle for the lifetime of a socket, we
		 * wouldn't need this.
		 */
		if (cur_event->events & WL_SOCKET_READABLE)
		{
			char		c;
			WSABUF		buf;
			DWORD		received;
			DWORD		flags;

			buf.buf = &c;
			buf.len = 1;
			flags = MSG_PEEK;
			if (WSARecv(cur_event->fd, &buf, 1, &received, &flags, NULL, NULL) == 0)
			{
				occurred_events->pos = cur_event->pos;
				occurred_events->user_data = cur_event->user_data;
				occurred_events->events = WL_SOCKET_READABLE;
				occurred_events->fd = cur_event->fd;
				return 1;
			}
		}

		/*
		 * Windows does not guarantee to log an FD_WRITE network event
		 * indicating that more data can be sent unless the previous send()
		 * failed with WSAEWOULDBLOCK.  While our caller might well have made
		 * such a call, we cannot assume that here.  Therefore, if waiting for
		 * write-ready, force the issue by doing a dummy send().  If the dummy
		 * send() succeeds, assume that the socket is in fact write-ready, and
		 * return immediately.  Also, if it fails with something other than
		 * WSAEWOULDBLOCK, return a write-ready indication to let our caller
		 * deal with the error condition.
		 */
		if (cur_event->events & WL_SOCKET_WRITEABLE)
		{
			char		c;
			WSABUF		buf;
			DWORD		sent;
			int			r;

			buf.buf = &c;
			buf.len = 0;

			r = WSASend(cur_event->fd, &buf, 1, &sent, 0, NULL, NULL);
			if (r == 0 || WSAGetLastError() != WSAEWOULDBLOCK)
			{
				occurred_events->pos = cur_event->pos;
				occurred_events->user_data = cur_event->user_data;
				occurred_events->events = WL_SOCKET_WRITEABLE;
				occurred_events->fd = cur_event->fd;
				return 1;
			}
		}
	}

	/*
	 * Sleep.
	 *
	 * Need to wait for ->nevents + 1, because signal handle is in [0].
	 */
	rc = WaitForMultipleObjects(set->nevents + 1, set->handles, FALSE,
								cur_timeout);

	/* Check return code */
	if (rc == WAIT_FAILED)
		elog(ERROR, "WaitForMultipleObjects() failed: error code %lu",
			 GetLastError());
	else if (rc == WAIT_TIMEOUT)
	{
		/* timeout exceeded */
		return -1;
	}

	if (rc == WAIT_OBJECT_0)
	{
		/* Service newly-arrived signals */
		pgwin32_dispatch_queued_signals();
		return 0;				/* retry */
	}

	/*
	 * With an offset of one, due to the always present pgwin32_signal_event,
	 * the handle offset directly corresponds to a wait event.
	 */
	cur_event = (WaitEvent *) &set->events[rc - WAIT_OBJECT_0 - 1];

	for (;;)
	{
		int			next_pos;
		int			count;

		occurred_events->pos = cur_event->pos;
		occurred_events->user_data = cur_event->user_data;
		occurred_events->events = 0;

		if (cur_event->events == WL_LATCH_SET)
		{
			/*
			 * We cannot use set->latch->event to reset the fired event if we
			 * aren't waiting on this latch now.
			 */
			if (!ResetEvent(set->handles[cur_event->pos + 1]))
				elog(ERROR, "ResetEvent failed: error code %lu", GetLastError());

			if (set->latch && set->latch->maybe_sleeping && set->latch->is_set)
			{
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_LATCH_SET;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events == WL_POSTMASTER_DEATH)
		{
			/*
			 * Postmaster apparently died.  Since the consequences of falsely
			 * returning WL_POSTMASTER_DEATH could be pretty unpleasant, we
			 * take the trouble to positively verify this with
			 * PostmasterIsAlive(), even though there is no known reason to
			 * think that the event could be falsely set on Windows.
			 */
			if (!PostmasterIsAliveInternal())
			{
				if (set->exit_on_postmaster_death)
					proc_exit(1);
				occurred_events->fd = PGINVALID_SOCKET;
				occurred_events->events = WL_POSTMASTER_DEATH;
				occurred_events++;
				returned_events++;
			}
		}
		else if (cur_event->events & WL_SOCKET_MASK)
		{
			WSANETWORKEVENTS resEvents;
			HANDLE		handle = set->handles[cur_event->pos + 1];

			Assert(cur_event->fd);

			occurred_events->fd = cur_event->fd;

			ZeroMemory(&resEvents, sizeof(resEvents));
			if (WSAEnumNetworkEvents(cur_event->fd, handle, &resEvents) != 0)
				elog(ERROR, "failed to enumerate network events: error code %d",
					 WSAGetLastError());
			if ((cur_event->events & WL_SOCKET_READABLE) &&
				(resEvents.lNetworkEvents & FD_READ))
			{
				/* data available in socket */
				occurred_events->events |= WL_SOCKET_READABLE;

				/*------
				 * WaitForMultipleObjects doesn't guarantee that a read event
				 * will be returned if the latch is set at the same time.  Even
				 * if it did, the caller might drop that event expecting it to
				 * reoccur on next call.  So, we must force the event to be
				 * reset if this WaitEventSet is used again in order to avoid
				 * an indefinite hang.
				 *
				 * Refer
				 * https://msdn.microsoft.com/en-us/library/windows/desktop/ms741576(v=vs.85).aspx
				 * for the behavior of socket events.
				 *------
				 */
				cur_event->reset = true;
			}
			if ((cur_event->events & WL_SOCKET_WRITEABLE) &&
				(resEvents.lNetworkEvents & FD_WRITE))
			{
				/* writeable */
				occurred_events->events |= WL_SOCKET_WRITEABLE;
			}
			if ((cur_event->events & WL_SOCKET_CONNECTED) &&
				(resEvents.lNetworkEvents & FD_CONNECT))
			{
				/* connected */
				occurred_events->events |= WL_SOCKET_CONNECTED;
			}
			if ((cur_event->events & WL_SOCKET_ACCEPT) &&
				(resEvents.lNetworkEvents & FD_ACCEPT))
			{
				/* incoming connection could be accepted */
				occurred_events->events |= WL_SOCKET_ACCEPT;
			}
			if (resEvents.lNetworkEvents & FD_CLOSE)
			{
				/* EOF/error, so signal all caller-requested socket flags */
				occurred_events->events |= (cur_event->events & WL_SOCKET_MASK);
			}

			if (occurred_events->events != 0)
			{
				occurred_events++;
				returned_events++;
			}
		}

		/* Is the output buffer full? */
		if (returned_events == nevents)
			break;

		/* Have we run out of possible events? */
		next_pos = cur_event->pos + 1;
		if (next_pos == set->nevents)
			break;

		/*
		 * Poll the rest of the event handles in the array starting at
		 * next_pos being careful to skip over the initial signal handle too.
		 * This time we use a zero timeout.
		 */
		count = set->nevents - next_pos;
		rc = WaitForMultipleObjects(count,
									set->handles + 1 + next_pos,
									false,
									0);

		/*
		 * We don't distinguish between errors and WAIT_TIMEOUT here because
		 * we already have events to report.
		 */
		if (rc < WAIT_OBJECT_0 || rc >= WAIT_OBJECT_0 + count)
			break;

		/* We have another event to decode. */
		cur_event = &set->events[next_pos + (rc - WAIT_OBJECT_0)];
	}

	return returned_events;
}
#endif

/*
 * Return whether the current build options can report WL_SOCKET_CLOSED.
 */
/*
 * WaitEventSetCanReportClosed - (中文)查询当前编译配置能否报告
 * WL_SOCKET_CLOSED
 *
 * 【作用】构建期查询:WL_SOCKET_CLOSED 依赖 poll 的 POLLRDHUP(或 epoll /
 * kqueue 原生支持)。调用方(如 libpq)据此决定能否依赖该事件。
 *
 * 【参数】无。
 * 【返回值】true 可报告;false 不可(等待该事件将永远不触发)。
 */
bool
WaitEventSetCanReportClosed(void)
{
#if (defined(WAIT_USE_POLL) && defined(POLLRDHUP)) || \
	defined(WAIT_USE_EPOLL) || \
	defined(WAIT_USE_KQUEUE)
	return true;
#else
	return false;
#endif
}

/*
 * Get the number of wait events registered in a given WaitEventSet.
 */
/*
 * GetNumRegisteredWaitEvents - (中文)返回集合中已注册的事件个数
 *
 * 【作用】查询 set->nevents,供调用方遍历或判断集合使用状态。
 *
 * 【参数】set —— 集合。
 * 【返回值】已注册的事件个数。
 */
int
GetNumRegisteredWaitEvents(WaitEventSet *set)
{
	return set->nevents;
}

#if defined(WAIT_USE_SELF_PIPE)

/*
 * SetLatch uses SIGURG to wake up the process waiting on the latch.
 *
 * Wake up WaitLatch, if we're waiting.
 */
/*
 * latch_sigurg_handler - (中文)SIGURG 信号处理器:唤醒正在等待的 WaitLatch
 *
 * 【作用】SetLatch 通过发送 SIGURG 唤醒等待者(self-pipe 路径):若本进程
 * 正在等待(waiting == true),往 self-pipe 写一个字节,使 poll / epoll
 * 立即返回。
 *
 * 【设计思想】只在 waiting 时写管道:没人在等时写入只会灌满管道(写端
 * 非阻塞,满时的写入会被丢弃,无害)。在信号上下文里只能做 async-signal-
 * safe 的操作,所以调用 sendSelfPipeByte 而非任何日志 / 报错设施。
 *
 * 【参数】SIGNAL_ARGS(标准信号参数,未使用)。
 * 【返回值】无。
 */
static void
latch_sigurg_handler(SIGNAL_ARGS)
{
	if (waiting)
		sendSelfPipeByte();
}

/* Send one byte to the self-pipe, to wake up WaitLatch */
/*
 * sendSelfPipeByte - (中文)向 self-pipe 写入一个字节以唤醒等待者
 *
 * 【作用】写端是非阻塞的:写成功即说明 poll 侧将有数据可读;EAGAIN 表示
 * 管道已满(里面已有字节,足够唤醒)直接返回;EINTR 重试;其他错误只能
 * 静默忽略——本函数可能在信号上下文里被调用,不能 elog。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
sendSelfPipeByte(void)
{
	ssize_t		rc;
	char		dummy = 0;

retry:
	rc = write(selfpipe_writefd, &dummy, 1);
	if (rc < 0)
	{
		/* If interrupted by signal, just retry */
		if (errno == EINTR)
			goto retry;

		/*
		 * If the pipe is full, we don't need to retry, the data that's there
		 * already is enough to wake up WaitLatch.
		 */
		if (errno == EAGAIN || errno == EWOULDBLOCK)
			return;

		/*
		 * Oops, the write() failed for some other reason. We might be in a
		 * signal handler, so it's not safe to elog(). We have no choice but
		 * silently ignore the error.
		 */
		return;
	}
}

#endif

#if defined(WAIT_USE_SELF_PIPE) || defined(WAIT_USE_SIGNALFD)

/*
 * Read all available data from self-pipe or signalfd.
 *
 * Note: this is only called when waiting = true.  If it fails and doesn't
 * return, it must reset that flag first (though ideally, this will never
 * happen).
 */
/*
 * drain - (中文)排空 self-pipe / signalfd 中所有待读数据
 *
 * 【作用】latch 事件被报告后调用:循环读直到 EAGAIN,保证下次等待不会
 * 因为"残留字节"立刻返回(把"电平"清成"边沿")。
 *
 * 【设计思想】仅当 waiting = true 时才会被调用;出错时先复位 waiting
 * 再 elog(此时已在正常上下文,可以报错)。一次读不满 1024 字节即说明
 * 管道已空(管道写入是整字节流,单次可读量小于缓冲即意味着没有更多
 * 数据),无需再读。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
drain(void)
{
	char		buf[1024];
	ssize_t		rc;
	int			fd;

#ifdef WAIT_USE_SELF_PIPE
	fd = selfpipe_readfd;
#else
	fd = signal_fd;
#endif

	for (;;)
	{
		rc = read(fd, buf, sizeof(buf));
		if (rc < 0)
		{
			if (errno == EAGAIN || errno == EWOULDBLOCK)
				break;			/* the descriptor is empty */
			else if (errno == EINTR)
				continue;		/* retry */
			else
			{
				waiting = false;
#ifdef WAIT_USE_SELF_PIPE
				elog(ERROR, "read() on self-pipe failed: %m");
#else
				elog(ERROR, "read() on signalfd failed: %m");
#endif
			}
		}
		else if (rc == 0)
		{
			waiting = false;
#ifdef WAIT_USE_SELF_PIPE
			elog(ERROR, "unexpected EOF on self-pipe");
#else
			elog(ERROR, "unexpected EOF on signalfd");
#endif
		}
		else if (rc < sizeof(buf))
		{
			/* we successfully drained the pipe; no need to read() again */
			break;
		}
		/* else buffer wasn't big enough, so read again */
	}
}

#endif

/* 资源所有者释放回调:解下 owner 引用并释放集合。清 owner 是为了防止
 * FreeWaitEventSet 里对"已被释放流程解下"的 owner 二次 Forget。 */
static void
ResOwnerReleaseWaitEventSet(Datum res)
{
	WaitEventSet *set = (WaitEventSet *) DatumGetPointer(res);

	Assert(set->owner != NULL);
	set->owner = NULL;
	FreeWaitEventSet(set);
}

#ifndef WIN32
/*
 * Wake up my process if it's currently sleeping in WaitEventSetWaitBlock()
 *
 * NB: be sure to save and restore errno around it.  (That's standard practice
 * in most signal handlers, of course, but we used to omit it in handlers that
 * only set a flag.) XXX
 *
 * NB: this function is called from critical sections and signal handlers so
 * throwing an error is not a good idea.
 *
 * On Windows, Latch uses SetEvent directly and this is not used.
 */
/*
 * WakeupMyProc - (中文)唤醒本进程自己(若正睡在等待循环里)
 *
 * 【作用】供临界区 / 信号处理器等"不方便持锁"的路径调用:本进程正在等待
 * 时,写 self-pipe(或对 kqueue 后端发 SIGURG)打断睡眠。注意原注释
 * (XXX)指出:未保存 / 恢复 errno,这是一个已知的小缺陷,大多数调用
 * 场景无影响。
 *
 * 【设计思想】与 latch_sigurg_handler 同源:等待时唤醒机制是"信号或管道
 * 字节";本函数允许普通代码(非信号上下文)主动触发同样的唤醒。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
WakeupMyProc(void)
{
#if defined(WAIT_USE_SELF_PIPE)
	if (waiting)
		sendSelfPipeByte();
#else
	if (waiting)
		kill(MyProcPid, SIGURG);
#endif
}

/* Similar to WakeupMyProc, but wake up another process */
/*
 * WakeupOtherProc - (中文)唤醒另一个进程
 *
 * 【作用】向 pid 发 SIGURG,使目标进程的等待循环被打断(目标须已初始化
 * latch 基础设施)。kqueue 后端由 EVFILT_SIGNAL 上报,self-pipe / 
 * signalfd 后端由信号处理器写管道。
 *
 * 【参数】pid —— 目标进程 PID。
 * 【返回值】无。
 */
void
WakeupOtherProc(int pid)
{
	kill(pid, SIGURG);
}
#endif
