/*-------------------------------------------------------------------------
 *
 * startup.c
 *
 * The Startup process initialises the server and performs any recovery
 * actions that have been specified. Notice that there is no "main loop"
 * since the Startup process ends as soon as initialisation is complete.
 * (in standby mode, one can think of the replay loop as a main loop,
 * though.)
 *
 * 【中文总述】
 * 本文件是 startup 进程（启动/恢复进程）的实现，由 postmaster 在启动阶段
 * fork 出来，负责两件大事：
 *   1. 初始化服务器共享内存等基础设施（通过 StartupXLOG() 开头部分）
 *   2. 执行崩溃恢复 / WAL 重放（redo）：把 WAL 日志一条条重放到数据页上，
 *      使数据库恢复到崩溃前的一致状态；若配置了恢复目标（recovery_target）
 *      或处于备库（standby）模式，则持续从 WAL 中重放日志。
 * 注意：该进程没有传统意义上的"主循环"——普通启动时它做完恢复就退出；
 * 只有 standby 模式下，WAL 重放循环才相当于它的主循环（但主循环体在
 * xlogrecovery.c 的 StartupXLOG() 内部，而不是本文件）。
 * 进程间协作关系：postmaster 通过信号（SIGHUP/SIGTERM/SIGUSR2）向本进程
 * 传达配置重读、关闭、提升（promote）等请求，本文件把这些信号转成标志位
 * 与 Latch 唤醒（WakeupRecovery），由重放循环在安全时机统一处理。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 *
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/startup.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/xlog.h"
#include "access/xlogrecovery.h"
#include "access/xlogutils.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "postmaster/auxprocess.h"
#include "postmaster/startup.h"
#include "storage/ipc.h"
#include "storage/pmsignal.h"
#include "storage/procsignal.h"
#include "storage/standby.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/timeout.h"


#ifndef USE_POSTMASTER_DEATH_SIGNAL
/*
 * On systems that need to make a system call to find out if the postmaster has
 * gone away, we'll do so only every Nth call to ProcessStartupProcInterrupts().
 * This only affects how long it takes us to detect the condition while we're
 * busy replaying WAL.  Latch waits and similar which should react immediately
 * through the usual techniques.
 * 【中文】在无法用信号直接感知 postmaster 死亡的平台上（没有
 * USE_POSTMASTER_DEATH_SIGNAL），检查"postmaster 是否还活着"需要做系统调用
 * （kill(pid, 0)），代价不小。因此不必每次循环都查，而是每调用
 * ProcessStartupProcInterrupts() 1024 次才查一次，避免频繁系统调用拖慢
 * WAL 重放；靠 Latch 等待的场景则用常规方式即时响应，不受此限流影响。
 */
#define POSTMASTER_POLL_RATE_LIMIT 1024
#endif

/*
 * Flags set by interrupt handlers for later service in the redo loop.
 * 【中文】以下标志位由信号处理函数（handler）置位，重放循环（redo loop）
 * 在安全时机统一检查并处理——这是 PG 常见的"信号只置位、主循环处理"模式：
 *  - got_SIGHUP：收到 SIGHUP，请求重读配置文件
 *  - shutdown_requested：收到 SIGTERM，请求放弃恢复、立即退出
 *  - promote_signaled：收到 SIGUSR2，请求结束恢复并把备库提升为主库
 */
static volatile sig_atomic_t got_SIGHUP = false;
static volatile sig_atomic_t shutdown_requested = false;
static volatile sig_atomic_t promote_signaled = false;

/*
 * Flag set when executing a restore command, to tell SIGTERM signal handler
 * that it's safe to just proc_exit.
 * 【中文】执行 restore_command（从归档拉取 WAL 文件的命令，如
 * pg_archivecleanup 或用户自定义脚本）期间置位。此时进程正阻塞在外部
 * 命令上、处于安全点，收到 SIGTERM 可以直接 proc_exit 退出，
 * 不用走"先收尾再退出"的复杂路径。
 */
static volatile sig_atomic_t in_restore_command = false;

/*
 * Time at which the most recent startup operation started.
 * 【中文】当前（最接近的一次）启动阶段耗时操作（如恢复进度、restore 等）
 * 的开始时间戳，用于计算进度报告里的"本阶段已耗时"。
 */
static TimestampTz startup_progress_phase_start_time;

/*
 * Indicates whether the startup progress interval mentioned by the user is
 * elapsed or not. TRUE if timeout occurred, FALSE otherwise.
 * 【中文】由 startup_progress_timeout_handler() 置位：标志用户配置的
 * 进度上报间隔（log_startup_progress_interval）是否已经到期，
 * 供重放循环判断"要不要打一条进度日志"。
 */
static volatile sig_atomic_t startup_progress_timer_expired = false;

/*
 * Time between progress updates for long-running startup operations.
 * 【中文】GUC 参数 log_startup_progress_interval 的底层变量：长耗时启动
 * 操作每隔多少毫秒上报一次进度（0 表示禁用进度上报，默认 10 秒）。
 */
int			log_startup_progress_interval = 10000;	/* 10 sec */

/* Signal handlers */
static void StartupProcTriggerHandler(SIGNAL_ARGS);
static void StartupProcSigHupHandler(SIGNAL_ARGS);

/* Callbacks */
static void StartupProcExit(int code, Datum arg);


/* --------------------------------
 *		signal handler routines
 * --------------------------------
 */

/* SIGUSR2: set flag to finish recovery */
/* 【中文】SIGUSR2 = 提升（promote）请求：postmaster 在收到
 * pg_ctl promote / 主库崩溃信号等场景下发出。
 * 处理：置 promote_signaled 标志，并唤醒重放循环立即去处理，
 * 而不是等它自然醒来——因为 standby 可能正阻塞在等新 WAL 的 Latch 上。
 *
 * 【调用链】WakeupRecovery() → SetLatch(MyLatch)
 *   → 唤醒在 WaitLatch() 上等待的 WAL 重放循环
 *   → 重放循环随后调用 IsPromoteSignaled() 看到标志，结束恢复进入提升流程 */
static void
StartupProcTriggerHandler(SIGNAL_ARGS)
{
	promote_signaled = true;
	WakeupRecovery();
}

/* SIGHUP: set flag to re-read config file at next convenient time */
/* 【中文】SIGHUP = 配置重读请求：postmaster 收到 SIGHUP（如 pg_reload_conf）
 * 后给所有子进程广播 SIGHUP。这里只置 got_SIGHUP 标志并唤醒重放循环，
 * 真正的重读（StartupRereadConfig）由 ProcessStartupProcInterrupts()
 * 在重放循环的安全时机执行。 */
static void
StartupProcSigHupHandler(SIGNAL_ARGS)
{
	got_SIGHUP = true;
	WakeupRecovery();
}

/* SIGTERM: set flag to abort redo and exit */
/* 【中文】SIGTERM = 关闭请求（postmaster 正在关闭，通常是
 * fast 关闭或 shutdown 流程进入停止阶段）。
 * 分支逻辑：
 *  - 若正卡在 restore_command 外部命令上（in_restore_command 为真）：
 *    这里就是安全点，直接 proc_exit(1) 立即退出；
 *  - 否则置 shutdown_requested 标志，等重放循环在
 *    ProcessStartupProcInterrupts() 里检查后再退出，
 *    避免在重放中途的任意位置打断（那会破坏恢复一致性）。
 * 两种情况都要 WakeupRecovery() 唤醒循环，防止它睡死在 Latch 上。 */
static void
StartupProcShutdownHandler(SIGNAL_ARGS)
{
	if (in_restore_command)
		proc_exit(1);
	else
		shutdown_requested = true;
	WakeupRecovery();
}

/*
 * Re-read the config file.
 *
 * If one of the critical walreceiver options has changed, request the startup
 * process to restart the walreceiver.
 * 【中文】重读配置文件（SIGHUP 触发）。
 * 先拷贝当前 walreceiver 相关参数的旧值做对比，重读后再比较：
 * 若 primary_conninfo / primary_slot_name / wal_receiver_create_temp_slot
 * 发生了变化，就通知 StartupXLOG() 里的恢复循环去重启 walreceiver
 * （否则新配置永远不会被备机接收进程使用）。
 *
 * 【调用链】StartupRereadConfig()
 *   → ProcessConfigFile(PGC_SIGHUP)：解析 postgresql.conf，更新 GUC 变量
 *   → strcmp 逐个比较旧值/新值，有变化则 StartupRequestWalReceiverRestart()
 *     → 设置重启 walreceiver 的标志 + WakeupRecovery() 唤醒恢复循环
 */
static void
StartupRereadConfig(void)
{
	/* 先用 pstrdup 快照旧值，因为 ProcessConfigFile 会直接改写 GUC 变量 */
	char	   *conninfo = pstrdup(PrimaryConnInfo);
	char	   *slotname = pstrdup(PrimarySlotName);
	bool		tempSlot = wal_receiver_create_temp_slot;
	bool		conninfoChanged;
	bool		slotnameChanged;
	bool		tempSlotChanged = false;

	/* 重新读取并应用配置文件（参数级别 PGC_SIGHUP，即 SIGHUP 可重载项） */
	ProcessConfigFile(PGC_SIGHUP);

	/* 与旧值对比，判断连接串 / 复制槽名是否被修改 */
	conninfoChanged = strcmp(conninfo, PrimaryConnInfo) != 0;
	slotnameChanged = strcmp(slotname, PrimarySlotName) != 0;

	/*
	 * wal_receiver_create_temp_slot is used only when we have no slot
	 * configured.  We do not need to track this change if it has no effect.
	 * 【中文】临时复制槽开关只有在"未配置 slot"时才有意义：
	 * 若本来就有 slot，这个开关变化与否都不影响行为，不用跟踪。
	 */
	if (!slotnameChanged && strcmp(PrimarySlotName, "") == 0)
		tempSlotChanged = tempSlot != wal_receiver_create_temp_slot;
	/* 旧值快照用完即释放 */
	pfree(conninfo);
	pfree(slotname);

	/* 任何一个关键参数变了，都请求重启 walreceiver 以应用新配置 */
	if (conninfoChanged || slotnameChanged || tempSlotChanged)
		StartupRequestWalReceiverRestart();
}

/* Process various signals that might be sent to the startup process */
/* 【中文总述】启动进程的中断处理入口：WAL 重放循环在每处理完一批记录
 * （或每次 Latch 被唤醒）后调用本函数，把信号处理函数置位的标志
 * 在这里统一"兑现"：
 *   1. SIGHUP → StartupRereadConfig() 重读配置文件
 *   2. SIGTERM → proc_exit(1) 放弃恢复立即退出
 *   3. postmaster 死亡检测 → exit(1) 紧急退出（避免留下孤儿子进程）
 *   4. 进程信号屏障事件 → ProcessProcSignalBarrier()
 *   5. 内存上下文日志请求 → ProcessLogMemoryContextInterrupt()
 * 设计要点：信号处理函数里绝不调用可能阻塞或分配内存的代码，
 * 只置标志；真正有风险的工作全部推迟到这个安全时机来做。
 *
 * 【调用链】由 StartupXLOG() 中的重放主循环调用
 *   → StartupRereadConfig() → ProcessConfigFile()（见上文）
 *   → proc_exit(1)：注册的 on_shmem_exit 回调 StartupProcExit 会先执行
 *   → PostmasterIsAlive()：kill(MyProcPid 之父 PID, 0) 探测 postmaster
 *   → ProcessProcSignalBarrier() → 执行排队的全局 barrier 动作
 *   → ProcessLogMemoryContextInterrupt() → 打印本进程内存上下文统计 */
void
ProcessStartupProcInterrupts(void)
{
#ifdef POSTMASTER_POLL_RATE_LIMIT
	/* 限流计数器：静态变量，跨调用保存"第几次进入本函数" */
	static uint32 postmaster_poll_count = 0;
#endif

	/*
	 * Process any requests or signals received recently.
	 * 【中文】处理 SIGHUP：先清除标志再重读配置。
	 * 注意"先清后做"的顺序——重读期间若又来一个 SIGHUP，
	 * 标志会被重新置位，下次循环还会再重读一次，信号不会丢失。
	 */
	if (got_SIGHUP)
	{
		got_SIGHUP = false;
		StartupRereadConfig();
	}

	/*
	 * Check if we were requested to exit without finishing recovery.
	 * 【中文】处理 SIGTERM 关闭请求：不等待恢复完成，直接 proc_exit(1)。
	 * 退出码 1 会让 postmaster 明白"恢复未完成"（区别于正常完成的 0）。
	 */
	if (shutdown_requested)
		proc_exit(1);

	/*
	 * Emergency bailout if postmaster has died.  This is to avoid the
	 * necessity for manual cleanup of all postmaster children.  Do this less
	 * frequently on systems for which we don't have signals to make that
	 * cheap.
	 * 【中文】应急退路：postmaster 已死（崩溃或被杀）时，它没机会清理
	 * 子进程，本进程必须自行退出避免成孤儿。有 USE_POSTMASTER_DEATH_SIGNAL
	 * 的平台（信号量开销小）每次检查；没有的按上面的限流频率检查。
	 *
	 * 【调用链】PostmasterIsAlive()
	 *   → 有死亡信号平台：读 postmaster_alive_fds 管道，父进程死则 EOF
	 *   → 其它平台：kill(PostmasterPid, 0) 返回值判断是否存活
	 */
	if (IsUnderPostmaster &&
#ifdef POSTMASTER_POLL_RATE_LIMIT
		postmaster_poll_count++ % POSTMASTER_POLL_RATE_LIMIT == 0 &&
#endif
		!PostmasterIsAlive())
		exit(1);

	/* Process barrier events */
	/* 【中文】处理 ProcSignalBarrier：后台工作者等进程可能通过
	 * 进程间信号机制投递的全局 barrier 请求（如 procsignal 队列里的
	 * 某些需要在安全点执行的动作），在这里统一执行。 */
	if (ProcSignalBarrierPending)
		ProcessProcSignalBarrier();

	/* Perform logging of memory contexts of this process */
	/* 【中文】处理内存上下文日志请求：某个进程（如 postmaster）通过
	 * 信号要求本进程打印内存上下文统计（用于排查内存泄漏），
	 * 在此调用 ProcessLogMemoryContextInterrupt() 实际输出。 */
	if (LogMemoryContextPending)
		ProcessLogMemoryContextInterrupt();
}


/* --------------------------------
 *		signal handler routines
 * --------------------------------
 */
static void
StartupProcExit(int code, Datum arg)
{
	/* Shutdown the recovery environment */
	/* 【中文】进程退出前的清理回调（通过 on_shmem_exit 注册，
	 * proc_exit() 时自动调用）：若曾进入 standby 恢复环境（Hot Standby
	 * 的锁/事务环境已初始化），则必须在这里安全拆除——
	 * 否则共享内存里的恢复状态残留，重启恢复时会出错。
	 *
	 * 【调用链】proc_exit() → on_shmem_exit 回调（本函数）
	 *   → ShutdownRecoveryTransactionEnvironment()
	 *     → 结束 standby 事务环境（释放锁、清空事务状态、恢复原时钟等） */
	if (standbyState != STANDBY_DISABLED)
		ShutdownRecoveryTransactionEnvironment();
}


/* ----------------------------------
 *	Startup Process main entry point
 * ----------------------------------
 * 【中文总述】startup 进程的主入口（由 postmaster fork 后调用，
 * EXEC_BACKEND 平台则经由 SubPostmasterMain 分发到这里）。执行阶段：
 *   1. 断言参数为空：startup 进程不需要 postmaster 传额外数据
 *      （其它子进程可能有，见 AuxiliaryProcessMainCommon 的启动数据参数）
 *   2. AuxiliaryProcessMainCommon()：辅助进程公共初始化
 *      （读共享内存指针、注册 GUC、初始化进程类型等）
 *   3. on_shmem_exit() 注册退出清理回调 StartupProcExit
 *   4. 安装/忽略信号：为后续长时间运行正确设定信号处理函数
 *   5. 注册 standby 模式需要的三种超时（死锁/超时/锁等待）
 *   6. 解除信号屏蔽（postmaster fork 时是屏蔽的）
 *   7. StartupXLOG()：真正干活的函数——读 pg_control、做崩溃恢复/
 *      WAL 重放（本文件没有主循环，重放循环就在它内部）
 *   8. proc_exit(0)：恢复成功，以退出码 0 告诉 postmaster"可以开门营业"
 */
void
StartupProcessMain(const void *startup_data, size_t startup_data_len)
{
	/* startup 进程不需要 postmaster 传任何启动数据 */
	Assert(startup_data_len == 0);

	/* 辅助进程公共初始化（共享内存挂接、进程类型登记、GUC 加载等） */
	/* 【调用链】AuxiliaryProcessMainCommon()
	 *   → InitProcessGlobals() 设置进程名/角色
	 *   → PGSharedMemoryReAttach() 重新挂接共享内存
	 *   → InitializeGUCOptions() 载入 GUC 默认值
	 *   → MyAuxProcType = B_STARTUP 登记本进程类型
	 *   → InitAuxiliaryProcess() 初始化（含 MyProc 登记）
	 *   → BaseInit() 基础初始化（文件描述符、临时文件、信号等） */
	AuxiliaryProcessMainCommon();

	/* Arrange to clean up at startup process exit */
	/* 【中文】注册退出清理回调：进程退出时（无论正常/异常路径）
	 * 都会先执行 StartupProcExit 清理恢复环境（见该函数注释）。 */
	on_shmem_exit(StartupProcExit, 0);

	/*
	 * Properly accept or ignore signals the postmaster might send us.
	 * 【中文】逐个设置信号处理策略。原则：postmaster 会发来的信号
	 * 都挂上自己的处理函数；与本进程无关的信号一律忽略（SIG_IGN），
	 * 避免误伤（例如后端进程的查询取消 SIGINT 与本进程无关）。
	 */
	pqsignal(SIGHUP, StartupProcSigHupHandler); /* reload config file */
	pqsignal(SIGINT, PG_SIG_IGN);	/* ignore query cancel */
	pqsignal(SIGTERM, StartupProcShutdownHandler);	/* request shutdown */
	/* SIGQUIT handler was already set up by InitPostmasterChild */
	/* 【中文】SIGQUIT（立即自杀信号）处理函数由 InitPostmasterChild()
	 * 在 fork 时已设置好，这里不用重复安装。 */
	InitializeTimeouts();		/* establishes SIGALRM handler */
	pqsignal(SIGPIPE, PG_SIG_IGN);
	pqsignal(SIGUSR1, procsignal_sigusr1_handler);
	pqsignal(SIGUSR2, StartupProcTriggerHandler);

	/*
	 * Reset some signals that are accepted by postmaster but not here
	 * 【中文】SIGCHLD 恢复默认行为：postmaster 要收割子进程所以自定义了
	 * SIGCHLD；startup 进程没有子进程需要管理，恢复 SIG_DFL 即可
	 * （子进程终止不影响本进程，也省掉无谓的信号处理开销）。
	 */
	pqsignal(SIGCHLD, PG_SIG_DFL);

	/*
	 * Register timeouts needed for standby mode
	 * 【中文】注册 standby（Hot Standby）模式下重放需要的三种超时，
	 * 供 xlogrecovery.c 的重放循环使用（RegisterTimeout 只是登记，
	 * 实际启用由 enable_timeout_after 等调用触发）：
	 *  - STANDBY_DEADLOCK_TIMEOUT：检测重放与并发查询的死锁
	 *  - STANDBY_TIMEOUT：重放等待（锁等待）的总体超时
	 *  - STANDBY_LOCK_TIMEOUT：单条锁等待超时，避免重放永久卡死
	 */
	RegisterTimeout(STANDBY_DEADLOCK_TIMEOUT, StandbyDeadLockHandler);
	RegisterTimeout(STANDBY_TIMEOUT, StandbyTimeoutHandler);
	RegisterTimeout(STANDBY_LOCK_TIMEOUT, StandbyLockTimeoutHandler);

	/*
	 * Unblock signals (they were blocked when the postmaster forked us)
	 * 【中文】解除信号屏蔽：postmaster fork 子进程时先屏蔽全部信号
	 * （防止初始化中途被信号打断），现在准备完毕，恢复默认屏蔽集
	 * UnBlockSig，此后上面的信号处理函数才能真正生效。
	 */
	sigprocmask(SIG_SETMASK, &UnBlockSig, NULL);

	/*
	 * Do what we came for.
	 * 【中文】核心工作：进入 StartupXLOG()。它会读取 pg_control、
	 * 决定需要哪种恢复（冷启动/崩溃恢复/归档恢复/standby 恢复），
	 * 然后执行 WAL 重放。该函数不返回，直到恢复完成
	 * （standby 模式下可能一直重放到被提升或关闭）。
	 *
	 * 【调用链】StartupXLOG()
	 *   → ControlFileLock 加锁 → ReadControlFile() 读 pg_control
	 *   → StartupXLOG 内部根据状态决定恢复模式
	 *   → 崩溃恢复：ReplayStartupPacketHeader/重放各 XLogRecord
	 *     → recovery_apply_delay() 应用延迟 → XLogReadRecord() 读下一条
	 *     → 空闲时 ProcessStartupProcInterrupts()（回到本文件）
	 *     → 恢复到一致点后，若 standby：在 CheckForStandbyIdle() 中
	 *       WaitLatch 睡眠，等新 WAL（promote/SIGTERM 会唤醒它）
	 *   → 恢复完成 → RecoveryRestartPoint() 等收尾 → 返回本函数
	 */
	StartupXLOG();

	/*
	 * Exit normally. Exit code 0 tells postmaster that we completed recovery
	 * successfully.
	 * 【中文】正常退出。退出码 0 对 postmaster 的含义：
	 * "恢复已成功完成"，随后 postmaster 把服务状态切到 PM_RUN
	 * （备库则是 PM_HOT_STANDBY），开始接受连接（见 postmaster.c
	 * 中 reaper 对 startup 进程退出码的处理）。
	 * 注意：若是 recovery_target 恢复（EXIT_STATUS_3）或提升/关闭场景，
	 * 根本不会走到这里，而是从 StartupXLOG() 内部直接退出。
	 */
	proc_exit(0);
}

/* 【中文】进入 restore_command 执行阶段前的钩子（由 xlogrecovery.c
 * 在 fork 外部命令前调用）：告诉 SIGTERM 处理函数"现在处于安全点"。
 * 若在进入之前 SIGTERM 就已经到达（shutdown_requested 已被置位），
 * 说明关闭请求正在等我们，那就别再执行 restore 命令了，直接退出。
 */
void
PreRestoreCommand(void)
{
	/*
	 * Set in_restore_command to tell the signal handler that we should exit
	 * right away on SIGTERM. We know that we're at a safe point to do that.
	 * Check if we had already received the signal, so that we don't miss a
	 * shutdown request received just before this.
	 * 【中文】置 in_restore_command = true：此刻进程将要阻塞在外部
	 * 命令上，SIGTERM 无法走"等重放循环处理"的路径，所以让信号
	 * 处理函数看到这个标志后直接 proc_exit(1)。
	 * 同时补查一次 shutdown_requested，防止"信号刚好在置位前到达"
	 * 的窗口期把关闭请求漏掉。
	 */
	in_restore_command = true;
	if (shutdown_requested)
		proc_exit(1);
}

/* 【中文】restore_command 执行完毕后的钩子：恢复 in_restore_command
 * 标志，此后 SIGTERM 又回到"置标志、由重放循环处理"的正常路径。 */
void
PostRestoreCommand(void)
{
	in_restore_command = false;
}

/* 【中文】查询"提升请求是否已到达"（供 StartupXLOG() 的恢复循环
 * 和提升流程使用）。promote_signaled 由 StartupProcTriggerHandler
 * 置位，处理完后由 ResetPromoteSignaled() 复位。 */
bool
IsPromoteSignaled(void)
{
	return promote_signaled;
}

/* 【中文】复位提升标志：提升流程开始处理后调用，避免同一信号被
 * 处理两次（比如提升流程内部又回到重放循环）。 */
void
ResetPromoteSignaled(void)
{
	promote_signaled = false;
}

/*
 * Set a flag indicating that it's time to log a progress report.
 * 【中文】STARTUP_PROGRESS_TIMEOUT 超时处理函数：超时到点后仅置
 * startup_progress_timer_expired 标志，真正打日志由重放循环在安全时机
 * 调用 has_startup_progress_timeout_expired() 完成（同样的
 * "信号/超时只置标志、主流程统一处理"模式）。
 */
void
startup_progress_timeout_handler(void)
{
	startup_progress_timer_expired = true;
}

/* 【中文】禁用启动进度超时：log_startup_progress_interval == 0 表示
 * 用户关闭了进度上报功能（"Feature is disabled"），直接返回。
 * 否则取消 STARTUP_PROGRESS_TIMEOUT 并清掉到期标志。
 *
 * 【调用链】disable_timeout() → 从超时机制中移除该项，
 *   同时杀掉等待进程的 SIGALRM 提醒位 */
void
disable_startup_progress_timeout(void)
{
	/* Feature is disabled. */
	if (log_startup_progress_interval == 0)
		return;

	disable_timeout(STARTUP_PROGRESS_TIMEOUT, false);
	startup_progress_timer_expired = false;
}

/*
 * Set the start timestamp of the current operation and enable the timeout.
 * 【中文】开启启动进度超时：记录当前操作开始的时间戳，
 * 并启用"周期性"超时——首次在 fin_time 到期，之后每隔
 * log_startup_progress_interval 毫秒再触发一次
 * （enable_timeout_every 的 every 语义），期间进程可
 * 反复收到超时事件来打进度日志。
 */
void
enable_startup_progress_timeout(void)
{
	TimestampTz fin_time;

	/* Feature is disabled. */
	if (log_startup_progress_interval == 0)
		return;

	/* 记录本阶段开始时间，作为进度日志中"耗时"的起点 */
	startup_progress_phase_start_time = GetCurrentTimestamp();
	fin_time = TimestampTzPlusMilliseconds(startup_progress_phase_start_time,
										   log_startup_progress_interval);
	enable_timeout_every(STARTUP_PROGRESS_TIMEOUT, fin_time,
						 log_startup_progress_interval);
}

/*
 * A thin wrapper to first disable and then enable the startup progress
 * timeout.
 * 【中文】便捷封装：先关后开。用于"开始一个新阶段"——把上一阶段
 * 残留的超时取消（并清掉未处理的到期标志），再以当前时刻为起点
 * 重新计算首次到期时间，避免旧阶段的定时器污染新阶段的节奏。
 */
void
begin_startup_progress_phase(void)
{
	/* Feature is disabled. */
	if (log_startup_progress_interval == 0)
		return;

	disable_startup_progress_timeout();
	enable_startup_progress_timeout();
}

/*
 * Report whether startup progress timeout has occurred. Reset the timer flag
 * if it did, set the elapsed time to the out parameters and return true,
 * otherwise return false.
 * 【中文】查询进度超时是否已到期（重放循环每处理完一批记录后调用）：
 *  - 未到期：返回 false，继续干活；
 *  - 已到期：把"本阶段已耗时"填入 *secs/*usecs 输出参数、
 *    清掉到期标志（防止下轮重复报告）并返回 true，
 *    调用方据此打一条进度日志并（如果需要）更新自己的节奏。
 */
bool
has_startup_progress_timeout_expired(long *secs, int *usecs)
{
	long		seconds;
	int			useconds;
	TimestampTz now;

	/* No timeout has occurred. */
	if (!startup_progress_timer_expired)
		return false;

	/* Calculate the elapsed time. */
	/* 【调用链】GetCurrentTimestamp() → gettimeofday()
	 *   → TimestampDifference() 计算与阶段开始时间的差
	 *   → 拆成秒 + 微秒两部分 */
	now = GetCurrentTimestamp();
	TimestampDifference(startup_progress_phase_start_time, now, &seconds, &useconds);

	*secs = seconds;
	*usecs = useconds;
	startup_progress_timer_expired = false;

	return true;
}
