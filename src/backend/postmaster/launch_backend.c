/*-------------------------------------------------------------------------
 *
 * launch_backend.c
 *	  Functions for launching backends and other postmaster child
 *	  processes.
 *
 * On Unix systems, a new child process is launched with fork().  It inherits
 * all the global variables and data structures that had been initialized in
 * the postmaster.  After forking, the child process closes the file
 * descriptors that are not needed in the child process, and sets up the
 * mechanism to detect death of the parent postmaster process, etc.  After
 * that, it calls the right Main function depending on the kind of child
 * process.
 *
 * In EXEC_BACKEND mode, which is used on Windows but can be enabled on other
 * platforms for testing, the child process is launched by fork() + exec() (or
 * CreateProcess() on Windows).  It does not inherit the state from the
 * postmaster, so it needs to re-attach to the shared memory, re-initialize
 * global variables, reload the config file etc. to get the process to the
 * same state as after fork() on a Unix system.
 *
 * 【中文总述】
 * 本文件是"postmaster 生娃"的场所：postmaster 启动任何一种子进程
 * （客户端后端、autovacuum、bgwriter、walwriter、syslogger 等）
 * 都经由这里统一的入口 postmaster_child_launch()：
 *   1. 普通平台（Unix）：fork_process() 直接 fork，
 *      子进程天然继承 postmaster 的全部内存状态，
 *      只需关闭多余的 fd、与 postmaster 脱钩、按需分离共享内存，
 *      然后进入各自类型的 Main 函数（如 BackendMain）
 *   2. EXEC_BACKEND 平台（Windows 默认，Unix 可开 --enable-... 测试）：
 *      fork + exec 模拟：postmaster 把全部关键全局变量打包进
 *      BackendParameters（写临时文件 / 内存映射），子进程 exec 后从
 *      SubPostmasterMain() 重新加载变量、重挂共享内存、重读配置文件，
 *      把状态恢复得和 fork 出来一模一样
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/postmaster/launch_backend.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <unistd.h>

#include "libpq/libpq-be.h"
#include "miscadmin.h"
#include "postmaster/autovacuum.h"
#include "postmaster/bgworker_internals.h"
#include "postmaster/bgwriter.h"
#include "postmaster/fork_process.h"
#include "postmaster/pgarch.h"
#include "postmaster/postmaster.h"
#include "postmaster/startup.h"
#include "postmaster/syslogger.h"
#include "postmaster/walsummarizer.h"
#include "postmaster/walwriter.h"
#include "replication/slotsync.h"
#include "replication/walreceiver.h"
#include "storage/dsm.h"
#include "storage/io_worker.h"
#include "storage/ipc.h"
#include "storage/pg_shmem.h"
#include "storage/shmem_internal.h"
#include "tcop/backend_startup.h"
#include "utils/memutils.h"

#ifdef EXEC_BACKEND
#include "nodes/queryjumble.h"
#include "portability/instr_time.h"
#include "storage/pg_shmem.h"
#include "storage/spin.h"
#endif


#ifdef EXEC_BACKEND

#include "common/file_utils.h"
#include "storage/fd.h"
#include "storage/lwlock.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "tcop/tcopprot.h"
#include "utils/injection_point.h"

/* Type for a socket that can be inherited to a client process */
/* 【中文】EXEC_BACKEND 下需要"传给子进程"的 socket 类型：
 * Unix 上就是普通 int（fork 继承）；Windows 上必须用
 * WSAPROTOCOL_INFO 才能把 socket 复制给别的进程。 */
#ifdef WIN32
typedef struct
{
	SOCKET		origsocket;		/* Original socket value, or PGINVALID_SOCKET
								 * if not a socket */
	WSAPROTOCOL_INFO wsainfo;
} InheritableSocket;
#else
typedef int InheritableSocket;
#endif

/*
 * Structure contains all variables passed to exec:ed backends
 *
 * 【中文】EXEC_BACKEND 模式下"父进程 → 子进程"传递的全部全局变量快照。
 * exec 出来的子进程不继承 postmaster 的内存，所以要把子进程恢复状态
 * 所需的每一项全局量都装进这个结构（save_backend_variables() 打包，
 * restore_backend_variables() 拆包还原）。字段按功能分组：
 *   - 客户端 socket（连接型子进程才需要）
 *   - 数据目录 / 槽位号 / 共享内存指针 / 进程信号等共享结构指针
 *   - postmaster 身份（PID、启动时间、重载时间）与日志管道
 *   - 进程全局（max_safe_fds、MaxBackends、计时频率等）
 *   - startup_data：可变长度的附加数据（如 BackendStartupData，
 *     由调用方按子进程类型自由定义）
 */
typedef struct
{
	char		DataDir[MAXPGPATH];
#ifndef WIN32
	unsigned long UsedShmemSegID;
#else
	void	   *ShmemProtectiveRegion;
	HANDLE		UsedShmemSegID;
#endif
	void	   *UsedShmemSegAddr;
#ifdef USE_INJECTION_POINTS
	struct InjectionPointsCtl *ActiveInjectionPoints;
#endif
	PROC_HDR   *ProcGlobal;
	PGPROC	   *AuxiliaryProcs;
	PGPROC	   *PreparedXactProcs;
	volatile PMSignalData *PMSignalState;
	ProcSignalHeader *ProcSignal;
	pid_t		PostmasterPid;
	TimestampTz PgStartTime;
	TimestampTz PgReloadTime;
	pg_time_t	first_syslogger_file_time;
	bool		redirection_done;
	bool		IsBinaryUpgrade;
	bool		query_id_enabled;
	int			max_safe_fds;
	int			MaxBackends;
	int			num_pmchild_slots;
#ifdef WIN32
	HANDLE		PostmasterHandle;
	HANDLE		initial_signal_pipe;
	HANDLE		syslogPipe[2];
#else
	int			postmaster_alive_fds[2];
	int			syslogPipe[2];
#endif
	char		my_exec_path[MAXPGPATH];
	char		pkglib_path[MAXPGPATH];

	int			MyPMChildSlot;

	int32		timing_tsc_frequency_khz;

	/*
	 * These are only used by backend processes, but are here because passing
	 * a socket needs some special handling on Windows. 'client_sock' is an
	 * explicit argument to postmaster_child_launch, but is stored in
	 * MyClientSocket in the child process.
	 * 【中文】仅供连接型子进程（后端/walsender）使用：
	 * client_sock 是父进程侧的原结构，inh_sock 是传给子进程的 socket 副本。
	 */
	ClientSocket client_sock;
	InheritableSocket inh_sock;

	/*
	 * Extra startup data, content depends on the child process.
	 * 【中文】附加启动数据：内容由子进程类型决定
	 * （连接型后端就是 BackendStartupData：accept 时间、可否接受连接等）。
	 */
	size_t		startup_data_len;
	char		startup_data[FLEXIBLE_ARRAY_MEMBER];
} BackendParameters;

/* 【中文】结构体总大小 = 固定部分 + 可变长的 startup_data */
#define SizeOfBackendParameters(startup_data_len) (offsetof(BackendParameters, startup_data) + startup_data_len)

static void read_backend_variables(char *id, void **startup_data, size_t *startup_data_len);
static void restore_backend_variables(BackendParameters *param);

static bool save_backend_variables(BackendParameters *param, int child_slot,
								   const ClientSocket *client_sock,
#ifdef WIN32
								   HANDLE childProcess, pid_t childPid,
#endif
								   const void *startup_data, size_t startup_data_len);

static pid_t internal_forkexec(BackendType child_kind, int child_slot,
							   const void *startup_data, size_t startup_data_len,
							   const ClientSocket *client_sock);

#endif							/* EXEC_BACKEND */

/*
 * Information needed to launch different kinds of child processes.
 *
 * 【中文】描述"每种 postmaster 子进程"的元信息，三个字段分别为：
 *   - name：类型名称（日志/ps 显示用）
 *   - main_fn：该类型子进程的入口 Main 函数（fork 之后调用，永不返回）
 *   - shmem_attach：该类型是否需要挂载共享内存
 *     （false 的类型如 syslogger，fork 后直接 PGSharedMemoryDetach）
 */
typedef struct
{
	const char *name;
	void		(*main_fn) (const void *startup_data, size_t startup_data_len);
	bool		shmem_attach;
} child_process_kind;

/* 【中文】按 BackendType 枚举下标索引的元信息表：
 * 具体内容由 proctypelist.h 展开（宏定义一行生成一个数组元素）。 */
static child_process_kind child_process_kinds[] = {
#define PG_PROCTYPE(bktype, bkcategory, description, main_func, shmem_attach) \
	[bktype] = {description, main_func, shmem_attach},
#include "postmaster/proctypelist.h"
#undef PG_PROCTYPE
};

/* 【中文】根据 BackendType 查出类型名称（gettext 描述串），
 * 供日志和 ps 显示（如 "client backend" / "autovacuum worker"）。 */
const char *
PostmasterChildName(BackendType child_type)
{
	return child_process_kinds[child_type].name;
}

/*
 * Start a new postmaster child process.
 *
 * The child process will be restored to roughly the same state whether
 * EXEC_BACKEND is used or not: it will be attached to shared memory if
 * appropriate, and fds and other resources that we've inherited from
 * postmaster that are not needed in a child process have been closed.
 *
 * 'child_slot' is the PMChildFlags array index reserved for the child
 * process.  'startup_data' is an optional contiguous chunk of data that is
 * passed to the child process.
 *
 * 【中文总述】postmaster 创建任何子进程的统一入口。
 * 调用方（如 postmaster.c 的 BackendStartup、StartBackgroundWorker）
 * 已预先分配好子进程槽位（child_slot），本函数负责真正"生"出子进程：
 *   1. （连接型子进程）记录 postmaster 发起 fork 的时刻
 *   2. EXEC_BACKEND 平台：internal_forkexec() 打包全局变量后 fork+exec，
 *      子进程从 SubPostmasterMain() 重新加载状态（见该函数注释）
 *   3. 普通平台：fork_process() 直接 fork，子进程在本函数体内
 *      继续执行以下收尾步骤：
 *       a. 记录 MyBackendType，传递连接建立计时信息
 *       b. ClosePostmasterPorts() 关闭从 postmaster 继承的监听 socket
 *       c. InitPostmasterChild() 与 postmaster 脱钩（信号、退出回调等）
 *       d. 不需要共享内存的子进程类型则 detach 共享内存
 *       e. 切到 TopMemoryContext，拷贝 ClientSocket，保存槽位号
 *       f. 调用该类型对应的 Main 函数（永不返回，最后 pg_unreachable）
 *   4. 父进程侧拿到子进程 PID 后原样返回
 */
pid_t
postmaster_child_launch(BackendType child_type, int child_slot,
						void *startup_data, size_t startup_data_len,
						const ClientSocket *client_sock)
{
	pid_t		pid;

	Assert(IsPostmasterEnvironment && !IsUnderPostmaster);

	/* Capture time Postmaster initiates process creation for logging */
	/* 【中文】记录"发起创建进程"的时间戳，与 accept 时间、fork 完成时间
	 * 一起构成 log_connections 里的连接建立耗时统计。 */
	if (IsExternalConnectionBackend(child_type))
		((BackendStartupData *) startup_data)->fork_started = GetCurrentTimestamp();

#ifdef EXEC_BACKEND
	/* 【中文】EXEC_BACKEND 路径：打包变量 → fork + exec；
	 * 子进程不会走到下面的子进程代码块，而是从 SubPostmasterMain 进入。 */
	pid = internal_forkexec(child_type, child_slot,
							startup_data, startup_data_len, client_sock);
	/* the child process will arrive in SubPostmasterMain */
#else							/* !EXEC_BACKEND */
	/* 【中文】普通路径：fork_process() 封装了 fork 系统调用及失败处理。
	 * 返回 0 进入子进程分支（下方代码块），返回 >0 是父进程。 */
	pid = fork_process();
	if (pid == 0)				/* child */
	{
		MyBackendType = child_type;

		/* Capture and transfer timings that may be needed for logging */
		/* 【中文】把 postmaster 侧记录的 accept/fork 发起时间带进子进程，
		 * 并补上 fork 完成时刻（这些供 log_connections 的耗时统计使用）。 */
		if (IsExternalConnectionBackend(child_type))
		{
			conn_timing.socket_create =
				((BackendStartupData *) startup_data)->socket_created;
			conn_timing.fork_start =
				((BackendStartupData *) startup_data)->fork_started;
			conn_timing.fork_end = GetCurrentTimestamp();
		}

		/* Close the postmaster's sockets */
		/* 【中文】关闭 postmaster 的监听/子进程通知 socket 等 fd
		 * （syslogger 例外，需要保留输出重定向管道）。 */
		ClosePostmasterPorts(child_type == B_LOGGER);

		/* Detangle from postmaster */
		/* 【中文】与 postmaster 脱钩：清理 postmaster 注册的 proc_exit 回调、
		 * 初始化本进程的 wait event/latch 等（见 miscinit.c）。 */
		InitPostmasterChild();

		/* Detach shared memory if not needed. */
		/* 【中文】该类型的子进程不需要共享内存（如 syslogger）时，
		 * 立即 detach 掉，避免占用 shmem 也不受其影响。 */
		if (!child_process_kinds[child_type].shmem_attach)
		{
			dsm_detach_all();
			PGSharedMemoryDetach();
		}

		/*
		 * Enter the Main function with TopMemoryContext.  The startup data is
		 * allocated in PostmasterContext, so we cannot release it here yet.
		 * The Main function will do it after it's done handling the startup
		 * data.
		 * 【中文】在 TopMemoryContext 下进入 Main 函数。
		 * startup_data 还活在 PostmasterContext 里，这里不能释放，
		 * 要等 Main 函数用完再处理。
		 */
		MemoryContextSwitchTo(TopMemoryContext);

		MyPMChildSlot = child_slot;
		if (client_sock)
		{
			/* 【中文】连接型子进程把客户端 socket 结构拷贝一份到自己的内存，
			 * 之后 MyClientSocket 就独立于父进程了。 */
			MyClientSocket = palloc_object(ClientSocket);
			memcpy(MyClientSocket, client_sock, sizeof(ClientSocket));
		}

		/*
		 * Run the appropriate Main function
		 * 【中文】分派到本类型子进程的入口：后端是 BackendMain()、
		 * syslogger 是 SysLoggerMain() 等；Main 函数永不返回。
		 */
		child_process_kinds[child_type].main_fn(startup_data, startup_data_len);
		pg_unreachable();		/* main_fn never returns */
	}
#endif							/* EXEC_BACKEND */
	/* 【中文】父进程路径：返回子进程 PID（fork 失败时为 -1）。 */
	return pid;
}

#ifdef EXEC_BACKEND
#ifndef WIN32

/*
 * internal_forkexec non-win32 implementation
 *
 * - writes out backend variables to the parameter file
 * - fork():s, and then exec():s the child process
 *
 * 【中文总述】EXEC_BACKEND 模式（Unix 平台用于测试）的 fork+exec 实现：
 *   1. save_backend_variables() 把 postmaster 的全部关键全局变量
 *      打包进 BackendParameters 结构
 *   2. 把结构体整块写入临时文件（PG_TEMP_FILES_DIR/backend_var.<pid>.<序号>）
 *   3. fork 子进程，子进程内立即 execv 重新加载 postgres 镜像，
 *      参数为 "--forkchild=<类型> <临时文件>"
 *   4. exec 后的子进程从 SubPostmasterMain() 开始：读回变量文件、
 *      恢复全局状态后进入 Main 函数
 *   5. 父进程直接返回子进程 PID（或 -1）
 */
static pid_t
internal_forkexec(BackendType child_kind, int child_slot,
				  const void *startup_data, size_t startup_data_len, const ClientSocket *client_sock)
{
	static unsigned long tmpBackendFileNum = 0;
	pid_t		pid;
	char		tmpfilename[MAXPGPATH];
	size_t		paramsz;
	BackendParameters *param;
	FILE	   *fp;
	char	   *argv[4];
	char		forkav[MAXPGPATH];

	/*
	 * Use palloc0 to make sure padding bytes are initialized, to prevent
	 * Valgrind from complaining about writing uninitialized bytes to the
	 * file.  This isn't performance critical, and the win32 implementation
	 * initializes the padding bytes to zeros, so do it even when not using
	 * Valgrind.
	 * 【中文】palloc0 清零：结构体的对齐填充字节在写入文件时必须是
	 * 确定的初始值，否则 Valgrind 会告警未初始化字节写入。
	 */
	paramsz = SizeOfBackendParameters(startup_data_len);
	param = palloc0(paramsz);
	if (!save_backend_variables(param, child_slot, client_sock, startup_data, startup_data_len))
	{
		/* 【中文】变量打包失败：子进程还没创建，清理内存后返回 -1
		 * （错误日志已由 save_backend_variables 输出）。 */
		pfree(param);
		return -1;				/* log made by save_backend_variables */
	}

	/* Calculate name for temp file */
	/* 【中文】构造临时文件名：数据目录的临时文件子目录下，
	 * 用 postmaster PID + 自增序号保证唯一。 */
	snprintf(tmpfilename, MAXPGPATH, "%s/%s.backend_var.%d.%lu",
			 PG_TEMP_FILES_DIR, PG_TEMP_FILE_PREFIX,
			 MyProcPid, ++tmpBackendFileNum);

	/* Open file */
	/* 【中文】打开临时文件；若目录不存在，先尝试创建再重试
	 * （与 OpenTemporaryFileInTablespace 的容错策略一致）。 */
	fp = AllocateFile(tmpfilename, PG_BINARY_W);
	if (!fp)
	{
		/*
		 * As in OpenTemporaryFileInTablespace, try to make the temp-file
		 * directory, ignoring errors.
		 */
		(void) MakePGDirectory(PG_TEMP_FILES_DIR);

		fp = AllocateFile(tmpfilename, PG_BINARY_W);
		if (!fp)
		{
			ereport(LOG,
					(errcode_for_file_access(),
					 errmsg("could not create file \"%s\": %m",
							tmpfilename)));
			pfree(param);
			return -1;
		}
	}

	/* 【中文】把整个 BackendParameters 结构（含 startup_data）一次性写入文件。 */
	if (fwrite(param, paramsz, 1, fp) != 1)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not write to file \"%s\": %m", tmpfilename)));
		FreeFile(fp);
		pfree(param);
		return -1;
	}
	pfree(param);

	/* Release file */
	if (FreeFile(fp))
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not write to file \"%s\": %m", tmpfilename)));
		return -1;
	}

	/* set up argv properly */
	/* 【中文】构造 execv 参数：argv[1] 是 "--forkchild=<类型>"，
	 * argv[2] 是变量文件路径（子进程据此恢复状态）。 */
	argv[0] = "postgres";
	snprintf(forkav, MAXPGPATH, "--forkchild=%d", (int) child_kind);
	argv[1] = forkav;
	/* Insert temp file name after --forkchild argument */
	argv[2] = tmpfilename;
	argv[3] = NULL;

	/* Fire off execv in child */
	/* 【中文】fork 后在子进程里立即 execv 换成新的 postgres 镜像；
	 * execv 一旦失败（镜像路径不对等），子进程已无法返回，
	 * 只能记录日志后 exit(1)。 */
	if ((pid = fork_process()) == 0)
	{
		if (execv(postgres_exec_path, argv) < 0)
		{
			ereport(LOG,
					(errmsg("could not execute server process \"%s\": %m",
							postgres_exec_path)));
			/* We're already in the child process here, can't return */
			exit(1);
		}
	}

	/* 【中文】父进程返回子进程 PID（fork 失败时 fork_process 返回 -1）。 */
	return pid;					/* Parent returns pid, or -1 on fork failure */
}
#else							/* WIN32 */

/*
 * internal_forkexec win32 implementation
 *
 * - starts backend using CreateProcess(), in suspended state
 * - writes out backend variables to the parameter file
 *	- during this, duplicates handles and sockets required for
 *	  inheritance into the new process
 * - resumes execution of the new process once the backend parameter
 *	 file is complete.
 *
 * 【中文总述】Windows 版：用"文件映射共享内存 + CreateProcess"模拟 fork：
 *   1. CreateFileMapping + MapViewOfFile 创建一块共享内存当参数通道
 *      （Windows 进程间不共享地址空间，必须显式传数据）
 *   2. CreateProcess 以 CREATE_SUSPENDED（挂起）状态启动子进程
 *   3. save_backend_variables() 把全局变量 + 需要继承的句柄/socket
 *      写进参数共享内存（这一步会做句柄/socket 复制）
 *   4. 在子进程里预留与 postmaster 相同的共享内存地址区；
 *      ASLR 干扰导致失败时终止进程并重试（最多 100 次）
 *   5. ResumeThread 让子进程跑起来，注册"子进程死亡"回调，
 *      父进程返回子进程 PID
 */
static pid_t
internal_forkexec(BackendType child_kind, int child_slot,
				  const void *startup_data, size_t startup_data_len, const ClientSocket *client_sock)
{
	int			retry_count = 0;
	STARTUPINFO si;
	PROCESS_INFORMATION pi;
	char		cmdLine[MAXPGPATH * 2];
	HANDLE		paramHandle;
	BackendParameters *param;
	SECURITY_ATTRIBUTES sa;
	size_t		paramsz;
	char		paramHandleStr[32];
	int			l;

	paramsz = SizeOfBackendParameters(startup_data_len);

	/* Resume here if we need to retry */
	/* 【中文】ASLR 导致共享内存地址预留失败时，终止子进程后跳回这里重试。 */
retry:

	/* Set up shared memory for parameter passing */
	/* 【中文】创建文件映射对象：相当于 Unix 的"参数文件"，
	 * 父子进程都能通过它读写 BackendParameters。 */
	ZeroMemory(&sa, sizeof(sa));
	sa.nLength = sizeof(sa);
	sa.bInheritHandle = TRUE;
	paramHandle = CreateFileMapping(INVALID_HANDLE_VALUE,
									&sa,
									PAGE_READWRITE,
									0,
									paramsz,
									NULL);
	if (paramHandle == INVALID_HANDLE_VALUE)
	{
		ereport(LOG,
				(errmsg("could not create backend parameter file mapping: error code %lu",
						GetLastError())));
		return -1;
	}
	/* 【中文】把映射对象映射到本进程地址空间，之后往里写参数。 */
	param = MapViewOfFile(paramHandle, FILE_MAP_WRITE, 0, 0, paramsz);
	if (!param)
	{
		ereport(LOG,
				(errmsg("could not map backend parameter memory: error code %lu",
						GetLastError())));
		CloseHandle(paramHandle);
		return -1;
	}

	/* Format the cmd line */
	/* 【中文】构造命令行：postgres --forkchild=<类型> <句柄值>，
	 * 子进程用句柄值定位参数共享内存。 */
#ifdef _WIN64
	sprintf(paramHandleStr, "%llu", (LONG_PTR) paramHandle);
#else
	sprintf(paramHandleStr, "%lu", (DWORD) paramHandle);
#endif
	l = snprintf(cmdLine, sizeof(cmdLine) - 1, "\"%s\" --forkchild=%d %s",
				 postgres_exec_path, (int) child_kind, paramHandleStr);
	if (l >= sizeof(cmdLine))
	{
		ereport(LOG,
				(errmsg("subprocess command line too long")));
		UnmapViewOfFile(param);
		CloseHandle(paramHandle);
		return -1;
	}

	memset(&pi, 0, sizeof(pi));
	memset(&si, 0, sizeof(si));
	si.cb = sizeof(si);

	/*
	 * Create the subprocess in a suspended state. This will be resumed later,
	 * once we have written out the parameter file.
	 * 【中文】挂起状态启动子进程：趁它还没跑，先把参数写好；
	 * 全部就绪后再 ResumeThread 让它开始执行。
	 */
	if (!CreateProcess(NULL, cmdLine, NULL, NULL, TRUE, CREATE_SUSPENDED,
					   NULL, NULL, &si, &pi))
	{
		ereport(LOG,
				(errmsg("CreateProcess() call failed: %m (error code %lu)",
						GetLastError())));
		UnmapViewOfFile(param);
		CloseHandle(paramHandle);
		return -1;
	}

	if (!save_backend_variables(param, child_slot, client_sock,
								pi.hProcess, pi.dwProcessId,
								startup_data, startup_data_len))
	{
		/*
		 * log made by save_backend_variables, but we have to clean up the
		 * mess with the half-started process
		 * 【中文】参数写入失败：这个只挂起未运行的子进程没用了，
		 * 终止并释放全部句柄（错误日志已由 save_backend_variables 输出）。
		 */
		if (!TerminateProcess(pi.hProcess, 255))
			ereport(LOG,
					(errmsg_internal("could not terminate unstarted process: error code %lu",
									 GetLastError())));
		CloseHandle(pi.hProcess);
		CloseHandle(pi.hThread);
		UnmapViewOfFile(param);
		CloseHandle(paramHandle);
		return -1;				/* log made by save_backend_variables */
	}

	/* Drop the parameter shared memory that is now inherited to the backend */
	/* 【中文】参数共享内存已被子进程继承（句柄是 bInheritHandle），
	 * 父进程解除映射并关闭句柄即可。 */
	if (!UnmapViewOfFile(param))
		ereport(LOG,
				(errmsg("could not unmap view of backend parameter file: error code %lu",
						GetLastError())));
	if (!CloseHandle(paramHandle))
		ereport(LOG,
				(errmsg("could not close handle to backend parameter file: error code %lu",
						GetLastError())));

	/*
	 * Reserve the memory region used by our main shared memory segment before
	 * we resume the child process.  Normally this should succeed, but if ASLR
	 * is active then it might sometimes fail due to the stack or heap having
	 * gotten mapped into that range.  In that case, just terminate the
	 * process and retry.
	 * 【中文】恢复运行前先占用共享内存段要用的地址区：保证子进程能
	 * attach 到和 postmaster 一样的地址（共享内存指针才能直接用）。
	 * ASLR 可能已把栈/堆映射进该区间导致失败，那就终止重来。
	 */
	if (!pgwin32_ReserveSharedMemoryRegion(pi.hProcess))
	{
		/* pgwin32_ReserveSharedMemoryRegion already made a log entry */
		if (!TerminateProcess(pi.hProcess, 255))
			ereport(LOG,
					(errmsg_internal("could not terminate process that failed to reserve memory: error code %lu",
									 GetLastError())));
		CloseHandle(pi.hProcess);
		CloseHandle(pi.hThread);
		/* 【中文】ASLR 冲突属于运气问题：杀进程后最多重试 100 次，
		 * 仍不行就放弃（可能被杀软等干扰）。 */
		if (++retry_count < 100)
			goto retry;
		ereport(LOG,
				(errmsg("giving up after too many tries to reserve shared memory"),
				 errhint("This might be caused by ASLR or antivirus software.")));
		return -1;
	}

	/*
	 * Now that the backend variables are written out, we start the child
	 * thread so it can start initializing while we set up the rest of the
	 * parent state.
	 * 【中文】一切就绪：恢复子进程运行，让它从 SubPostmasterMain
	 * 开始并行初始化，父进程继续收拾剩余状态。
	 */
	if (ResumeThread(pi.hThread) == -1)
	{
		if (!TerminateProcess(pi.hProcess, 255))
		{
			ereport(LOG,
					(errmsg_internal("could not terminate unstartable process: error code %lu",
									 GetLastError())));
			CloseHandle(pi.hProcess);
			CloseHandle(pi.hThread);
			return -1;
		}
		CloseHandle(pi.hProcess);
		CloseHandle(pi.hThread);
		ereport(LOG,
				(errmsg_internal("could not resume thread of unstarted process: error code %lu",
								 GetLastError())));
		return -1;
	}

	/* Set up notification when the child process dies */
	/* 【中文】注册"子进程死亡"回调：Windows 没有 SIGCHLD，
	 * postmaster 靠它得知子进程退出（等价于 Unix 的 waitpid 通知）。 */
	pgwin32_register_deadchild_callback(pi.hProcess, pi.dwProcessId);

	/* Don't close pi.hProcess, it's owned by the deadchild callback now */

	CloseHandle(pi.hThread);

	return pi.dwProcessId;
}
#endif							/* WIN32 */

/*
 * SubPostmasterMain -- Get the fork/exec'd process into a state equivalent
 *			to what it would be if we'd simply forked on Unix, and then
 *			dispatch to the appropriate place.
 *
 * The first two command line arguments are expected to be "--forkchild=<kind>",
 * where <kind> indicates which process type we are to become, and
 * the name of a variables file that we can read to load data that would
 * have been inherited by fork() on Unix.
 *
 * 【中文总述】EXEC_BACKEND 下 exec 出来的子进程的新"main"：
 * 对应普通平台"fork 子进程从 postmaster_child_launch 内部继续"的那段路径，
 * 这里要手动把所有继承不到的东西重建出来：
 *   1. 初始化 GUC 框架，解析 "--forkchild=<类型>" 确定自己是什么子进程
 *   2. read_backend_variables() 读回 postmaster 打包的全局变量
 *      （Unix 上是读临时文件；Windows 上是读内存映射）
 *   3. 关闭 postmaster 的 socket、InitPostmasterChild() 与父进程脱钩
 *   4. 需要共享内存的类型重新 attach（必须与 postmaster 同一地址）；
 *      不需要的调用 PGSharedMemoryNoReAttach 做清理
 *   5. 恢复非默认 GUC、连接计时信息，校验数据目录、重读控制文件、
 *      重新加载 preload 库、重建共享内存指针
 *   6. 调用本类型对应的 Main 函数（永不返回）
 */
void
SubPostmasterMain(int argc, char *argv[])
{
	void	   *startup_data;
	size_t		startup_data_len;
	char	   *child_kind;
	BackendType child_type;
	TimestampTz fork_end;

	/* In EXEC_BACKEND case we will not have inherited these settings */
	/* 【中文】exec 出来的进程不继承 postmaster 的这些全局设置，
	 * 先手动设好，保证 elog 等基础设施一开始就行为正确。 */
	IsPostmasterEnvironment = true;
	whereToSendOutput = DestNone;

	/*
	 * Capture the end of process creation for logging. We don't include the
	 * time spent copying data from shared memory and setting up the backend.
	 * 【中文】记录进程创建完成的时刻（日志统计 fork 耗时用，
	 * 不含拷贝共享内存和初始化后端的时间）。
	 */
	fork_end = GetCurrentTimestamp();

	/* Setup essential subsystems (to ensure elog() behaves sanely) */
	/* 【中文】初始化 GUC 框架（读入内置默认值），让 elog/ereport 能正常工作。 */
	InitializeGUCOptions();

	/* Check we got appropriate args */
	/* 【中文】参数必须是恰好两个："--forkchild=<类型>" 和变量文件路径。 */
	if (argc != 3)
		elog(FATAL, "invalid subpostmaster invocation");

	/*
	 * Parse the --forkchild argument to find our process type.  We rely with
	 * malice aforethought on atoi returning 0 (B_INVALID) on error.
	 * 【中文】解析 "--forkchild=<类型>"：atoi 解析失败时返回 0
	 * （即 B_INVALID），交给下面的范围检查兜底报错。
	 */
	if (strncmp(argv[1], "--forkchild=", 12) != 0)
		elog(FATAL, "invalid subpostmaster invocation (--forkchild argument missing)");
	child_kind = argv[1] + 12;
	child_type = (BackendType) atoi(child_kind);
	if (child_type <= B_INVALID || child_type > BACKEND_NUM_TYPES - 1)
		elog(ERROR, "unknown child kind %s", child_kind);
	MyBackendType = child_type;

	/* Read in the variables file */
	/* 【中文】从变量文件（或 Windows 的内存映射）读回父进程打包的全部
	 * 全局变量，并恢复（read_backend_variables → restore_backend_variables）。 */
	read_backend_variables(argv[2], &startup_data, &startup_data_len);

	/* Close the postmaster's sockets (as soon as we know them) */
	/* 【中文】与 fork 路径一样：尽早关掉 postmaster 的 socket，
	 * 避免误报父进程存活（见 ClosePostmasterPorts）。 */
	ClosePostmasterPorts(child_type == B_LOGGER);

	/* Setup as postmaster child */
	/* 【中文】与 postmaster 脱钩（信号掩码、退出回调、latch 初始化等）。 */
	InitPostmasterChild();

	/*
	 * If appropriate, physically re-attach to shared memory segment. We want
	 * to do this before going any further to ensure that we can attach at the
	 * same address the postmaster used.  On the other hand, if we choose not
	 * to re-attach, we may have other cleanup to do.
	 *
	 * If testing EXEC_BACKEND on Linux, you should run this as root before
	 * starting the postmaster:
	 *
	 * sysctl -w kernel.randomize_va_space=0
	 *
	 * This prevents using randomized stack and code addresses that cause the
	 * child process's memory map to be different from the parent's, making it
	 * sometimes impossible to attach to shared memory at the desired address.
	 * Return the setting to its old value (usually '1' or '2') when finished.
	 *
	 * 【中文】重新挂载共享内存：必须在做任何别的事之前，
	 * 才能抢到与 postmaster 相同的地址（共享内存指针才能直接用）。
	 * Linux 上测试 EXEC_BACKEND 若 attach 失败，可先
	 * "sysctl -w kernel.randomize_va_space=0" 关闭 ASLR 再启动 postmaster。
	 */
	if (child_process_kinds[child_type].shmem_attach)
		PGSharedMemoryReAttach();
	else
		PGSharedMemoryNoReAttach();

	/* Read in remaining GUC variables */
	/* 【中文】恢复 postmaster 写出的非默认 GUC（postgresql.auto.conf 等），
	 * 因为 exec 后没有继承任何 GUC 设置。 */
	read_nondefault_variables();

	/* Capture and transfer timings that may be needed for log_connections */
	/* 【中文】把打包时存的 accept/fork 时间与刚记录的 fork_end 一起
	 * 填进 conn_timing（log_connections 显示连接建立各阶段耗时）。 */
	if (IsExternalConnectionBackend(child_type))
	{
		conn_timing.socket_create =
			((BackendStartupData *) startup_data)->socket_created;
		conn_timing.fork_start =
			((BackendStartupData *) startup_data)->fork_started;
		conn_timing.fork_end = fork_end;
	}

	/*
	 * Check that the data directory looks valid, which will also check the
	 * privileges on the data directory and update our umask and file/group
	 * variables for creating files later.  Note: this should really be done
	 * before we create any files or directories.
	 * 【中文】校验数据目录（权限、PG_VERSION 等），同时设置本进程的
	 * umask 与文件属组变量——exec 后这些都没继承到。
	 */
	checkDataDir();

	/*
	 * (re-)read control file, as it contains config. The postmaster will
	 * already have read this, but this process doesn't know about that.
	 * 【中文】重新读取 pg_control：里面含有配置信息，
	 * 本进程（exec 出来的）不知道 postmaster 已读过它。
	 */
	LocalProcessControlFile(false);

	/* 【中文】重新注册内置的共享内存初始化回调
	 * （exec 后本进程的内存里没有这些注册信息）。 */
	RegisterBuiltinShmemCallbacks();

	/*
	 * Reload any libraries that were preloaded by the postmaster.  Since we
	 * exec'd this process, those libraries didn't come along with us; but we
	 * should load them into all child processes to be consistent with the
	 * non-EXEC_BACKEND behavior.
	 * 【中文】重新加载 postmaster 的 preload 库（shared_preload_libraries）：
	 * exec 时它们没跟过来，但所有子进程的行为应当保持一致。
	 */
	process_shared_preload_libraries();

	/* Restore basic shared memory pointers */
	/* 【中文】重建共享内存分配器指针，并执行注册过的
	 * 共享内存初始化回调（让本进程的 shmem 状态可用）。 */
	if (UsedShmemSegAddr != NULL)
	{
		InitShmemAllocator(UsedShmemSegAddr);
		ShmemCallRequestCallbacks();
	}

	/*
	 * Run the appropriate Main function
	 * 【中文】状态重建完毕，进入本类型对应的 Main 函数（永不返回）。
	 */
	child_process_kinds[child_type].main_fn(startup_data, startup_data_len);
	pg_unreachable();			/* main_fn never returns */
}

/* 【中文】"可继承 socket"的读写抽象：
 * Unix 上 fork 天然继承 fd，宏就是普通赋值/取值；
 * Windows 上必须通过 WSADuplicateSocket 显式复制（见下面三个函数）。 */
#ifndef WIN32
#define write_inheritable_socket(dest, src, childpid) ((*(dest) = (src)), true)
#define read_inheritable_socket(dest, src) (*(dest) = *(src))
#else
static bool write_duplicated_handle(HANDLE *dest, HANDLE src, HANDLE child);
static bool write_inheritable_socket(InheritableSocket *dest, SOCKET src,
									 pid_t childPid);
static void read_inheritable_socket(SOCKET *dest, InheritableSocket *src);
#endif


/* Save critical backend variables into the BackendParameters struct */
/* 【中文总述】把 postmaster 的关键全局变量逐项填入 BackendParameters，
 * 供 exec 出的子进程恢复（restore_backend_variables() 是其逆操作）。
 * 只拷贝"子进程必须知道"的量：socket、数据目录、槽位号、共享内存指针、
 * 信号结构指针、postmaster 身份、日志管道、计时频率、附加启动数据等。
 * 某些量随平台不同而不同（Windows 复制句柄，Unix 直接拷贝 fd）。 */
static bool
save_backend_variables(BackendParameters *param,
					   int child_slot, const ClientSocket *client_sock,
#ifdef WIN32
					   HANDLE childProcess, pid_t childPid,
#endif
					   const void *startup_data, size_t startup_data_len)
{
	/* 【中文】客户端 socket：连接型子进程原样拷贝，其余置空；
	 * 再准备一份"可继承"的 socket 副本（Windows 需复制 socket）。 */
	if (client_sock)
		memcpy(&param->client_sock, client_sock, sizeof(ClientSocket));
	else
		memset(&param->client_sock, 0, sizeof(ClientSocket));
	if (!write_inheritable_socket(&param->inh_sock,
								  client_sock ? client_sock->sock : PGINVALID_SOCKET,
								  childPid))
		return false;

	strlcpy(param->DataDir, DataDir, MAXPGPATH);

	param->MyPMChildSlot = child_slot;

#ifdef WIN32
	param->ShmemProtectiveRegion = ShmemProtectiveRegion;
#endif
	param->UsedShmemSegID = UsedShmemSegID;
	param->UsedShmemSegAddr = UsedShmemSegAddr;

#ifdef USE_INJECTION_POINTS
	param->ActiveInjectionPoints = ActiveInjectionPoints;
#endif

	/* 【中文】共享内存中的关键结构指针（ProcGlobal、PGPROC 数组、
	 * PMSignal 状态、ProcSignal 表等）：子进程恢复后直接按地址使用。 */
	param->ProcGlobal = ProcGlobal;
	param->AuxiliaryProcs = AuxiliaryProcs;
	param->PreparedXactProcs = PreparedXactProcs;
	param->PMSignalState = PMSignalState;
	param->ProcSignal = ProcSignal;

	/* 【中文】postmaster 身份信息：PID、启动时间、配置重载时间、
	 * syslogger 首个日志文件时间（子进程据此判断是否切新日志文件）。 */
	param->PostmasterPid = PostmasterPid;
	param->PgStartTime = PgStartTime;
	param->PgReloadTime = PgReloadTime;
	param->first_syslogger_file_time = first_syslogger_file_time;

	/* 【中文】各种进程级开关与 fd 上限（fd.c 的外部 fd 管理依赖它）。 */
	param->redirection_done = redirection_done;
	param->IsBinaryUpgrade = IsBinaryUpgrade;
	param->query_id_enabled = query_id_enabled;
	param->max_safe_fds = max_safe_fds;

	param->MaxBackends = MaxBackends;
	param->num_pmchild_slots = num_pmchild_slots;

	param->timing_tsc_frequency_khz = timing_tsc_frequency_khz;

#ifdef WIN32
	param->PostmasterHandle = PostmasterHandle;
	if (!write_duplicated_handle(&param->initial_signal_pipe,
								 pgwin32_create_signal_listener(childPid),
								 childProcess))
		return false;
#else
	/* 【中文】"postmaster 存活检测"管道：子进程持有读端，
	 * postmaster 死亡时管道关闭，子进程通过它感知父进程退出。 */
	memcpy(&param->postmaster_alive_fds, &postmaster_alive_fds,
		   sizeof(postmaster_alive_fds));
#endif

	/* 【中文】stderr 重定向管道：转发日志给 syslogger 用。 */
	memcpy(&param->syslogPipe, &syslogPipe, sizeof(syslogPipe));

	strlcpy(param->my_exec_path, my_exec_path, MAXPGPATH);

	strlcpy(param->pkglib_path, pkglib_path, MAXPGPATH);

	/* 【中文】可变长的附加启动数据（如 BackendStartupData）原样复制。 */
	param->startup_data_len = startup_data_len;
	if (startup_data_len > 0)
		memcpy(param->startup_data, startup_data, startup_data_len);

	return true;
}

#ifdef WIN32
/*
 * Duplicate a handle for usage in a child process, and write the child
 * process instance of the handle to the parameter file.
 * 【中文】把句柄复制成"子进程可用"的副本并写入参数结构：
 * DUPLICATE_CLOSE_SOURCE 关闭源句柄，DUPLICATE_SAME_ACCESS 保持访问权限。
 */
static bool
write_duplicated_handle(HANDLE *dest, HANDLE src, HANDLE childProcess)
{
	HANDLE		hChild = INVALID_HANDLE_VALUE;

	/* 【中文】DuplicateHandle 到子进程的句柄空间（句柄本身不可直接跨进程用）。 */
	if (!DuplicateHandle(GetCurrentProcess(),
						 src,
						 childProcess,
						 &hChild,
						 0,
						 TRUE,
						 DUPLICATE_CLOSE_SOURCE | DUPLICATE_SAME_ACCESS))
	{
		ereport(LOG,
				(errmsg_internal("could not duplicate handle to be written to backend parameter file: error code %lu",
								 GetLastError())));
		return false;
	}

	*dest = hChild;
	return true;
}

/*
 * Duplicate a socket for usage in a child process, and write the resulting
 * structure to the parameter file.
 * This is required because a number of LSPs (Layered Service Providers) very
 * common on Windows (antivirus, firewalls, download managers etc) break
 * straight socket inheritance.
 *
 * 【中文】Windows 上 socket 不能像句柄那样直接复制给子进程：
 * 必须 WSADuplicateSocket 生成 WSAPROTOCOL_INFO 结构（LSP——杀软、
 * 防火墙等中间层——会破坏直接的 socket 继承，所以要绕道协议信息）。
 */
static bool
write_inheritable_socket(InheritableSocket *dest, SOCKET src, pid_t childpid)
{
	dest->origsocket = src;
	if (src != 0 && src != PGINVALID_SOCKET)
	{
		/* Actual socket */
		/* 【中文】真正的 socket：生成一份可由子进程重建的协议信息。 */
		if (WSADuplicateSocket(src, childpid, &dest->wsainfo) != 0)
		{
			ereport(LOG,
					(errmsg("could not duplicate socket %d for use in backend: error code %d",
							(int) src, WSAGetLastError())));
			return false;
		}
	}
	return true;
}

/*
 * Read a duplicate socket structure back, and get the socket descriptor.
 * 【中文】读回流程（read_backend_variables 时调用）：
 * 用 WSASocket(FROM_PROTOCOL_INFO) 从 wsainfo 重建出本进程的 socket
 * 描述符，并关闭原 socket 防止同一 socket 出现两个引用。
 */
static void
read_inheritable_socket(SOCKET *dest, InheritableSocket *src)
{
	SOCKET		s;

	if (src->origsocket == PGINVALID_SOCKET || src->origsocket == 0)
	{
		/* Not a real socket! */
		/* 【中文】本来就没有 socket（非连接型子进程）：原样带回。 */
		*dest = src->origsocket;
	}
	else
	{
		/* Actual socket, so create from structure */
		/* 【中文】按协议信息重建 socket 描述符。 */
		s = WSASocket(FROM_PROTOCOL_INFO,
					  FROM_PROTOCOL_INFO,
					  FROM_PROTOCOL_INFO,
					  &src->wsainfo,
					  0,
					  0);
		if (s == INVALID_SOCKET)
		{
			write_stderr("could not create inherited socket: error code %d\n",
						 WSAGetLastError());
			exit(1);
		}
		*dest = s;

		/*
		 * To make sure we don't get two references to the same socket, close
		 * the original one. (This would happen when inheritance actually
		 * works..
		 * 【中文】关闭父进程侧的原始 socket，避免同一 socket 被引用两次
		 * （如果继承真的生效了的话……）。
		 */
		closesocket(src->origsocket);
	}
}
#endif

/* 【中文总述】子进程侧读回父进程打包的后端变量（save_backend_variables
 * 的逆操作）：Unix 上从临时文件读（读完即删），Windows 上从内存映射读；
 * 读完统一调用 restore_backend_variables() 恢复到全局变量中。 */
static void
read_backend_variables(char *id, void **startup_data, size_t *startup_data_len)
{
	BackendParameters param;

#ifndef WIN32
	/* Non-win32 implementation reads from file */
	FILE	   *fp;

	/* Open file */
	/* 【中文】打开 postmaster 写好的变量临时文件。 */
	fp = AllocateFile(id, PG_BINARY_R);
	if (!fp)
	{
		write_stderr("could not open backend variables file \"%s\": %m\n", id);
		exit(1);
	}

	/* 【中文】读出 BackendParameters 主体（固定部分）。 */
	if (fread(&param, sizeof(param), 1, fp) != 1)
	{
		write_stderr("could not read from backend variables file \"%s\": %m\n", id);
		exit(1);
	}

	/* read startup data */
	/* 【中文】再读可变长的 startup_data（长度记录在结构里），
	 * 单独 palloc 出来由上层（Main 函数）使用。 */
	*startup_data_len = param.startup_data_len;
	if (param.startup_data_len > 0)
	{
		*startup_data = palloc(*startup_data_len);
		if (fread(*startup_data, *startup_data_len, 1, fp) != 1)
		{
			write_stderr("could not read startup data from backend variables file \"%s\": %m\n",
						 id);
			exit(1);
		}
	}
	else
		*startup_data = NULL;

	/* Release file */
	/* 【中文】读完后立即删除临时文件（一次性交接媒介，不留垃圾）。 */
	FreeFile(fp);
	if (unlink(id) != 0)
	{
		write_stderr("could not remove file \"%s\": %m\n", id);
		exit(1);
	}
#else
	/* Win32 version uses mapped file */
	/* 【中文】Windows 版：id 是父进程传进来的映射句柄，
	 * 直接把父进程写的内存映射拷回本地结构。 */
	HANDLE		paramHandle;
	BackendParameters *paramp;

#ifdef _WIN64
	paramHandle = (HANDLE) _atoi64(id);
#else
	paramHandle = (HANDLE) atol(id);
#endif
	paramp = MapViewOfFile(paramHandle, FILE_MAP_READ, 0, 0, 0);
	if (!paramp)
	{
		write_stderr("could not map view of backend variables: error code %lu\n",
					 GetLastError());
		exit(1);
	}

	memcpy(&param, paramp, sizeof(BackendParameters));

	/* read startup data */
	/* 【中文】同样把 startup_data 单独拷出来。 */
	*startup_data_len = param.startup_data_len;
	if (param.startup_data_len > 0)
	{
		*startup_data = palloc(paramp->startup_data_len);
		memcpy(*startup_data, paramp->startup_data, param.startup_data_len);
	}
	else
		*startup_data = NULL;

	if (!UnmapViewOfFile(paramp))
	{
		write_stderr("could not unmap view of backend variables: error code %lu\n",
					 GetLastError());
		exit(1);
	}

	if (!CloseHandle(paramHandle))
	{
		write_stderr("could not close handle to backend parameter variables: error code %lu\n",
					 GetLastError());
		exit(1);
	}
#endif

	/* 【中文】把读回的 BackendParameters 逐项写回进程全局变量。 */
	restore_backend_variables(&param);
}

/* Restore critical backend variables from the BackendParameters struct */
/* 【中文总述】save_backend_variables() 的逆操作：把 exec 出的子进程的
 * 全局变量恢复成 postmaster 打包时的值（数据目录、共享内存指针、
 * 信号结构、日志管道、计时频率等），让子进程状态与 fork 出来等价。 */
static void
restore_backend_variables(BackendParameters *param)
{
	/* 【中文】恢复客户端 socket：连接型子进程重建描述符
	 * （Windows 用 WSASocket 从 wsainfo 重建并关闭原 socket）。 */
	if (param->client_sock.sock != PGINVALID_SOCKET)
	{
		MyClientSocket = MemoryContextAlloc(TopMemoryContext, sizeof(ClientSocket));
		memcpy(MyClientSocket, &param->client_sock, sizeof(ClientSocket));
		read_inheritable_socket(&MyClientSocket->sock, &param->inh_sock);
	}

	SetDataDir(param->DataDir);

	MyPMChildSlot = param->MyPMChildSlot;

#ifdef WIN32
	ShmemProtectiveRegion = param->ShmemProtectiveRegion;
#endif
	UsedShmemSegID = param->UsedShmemSegID;
	UsedShmemSegAddr = param->UsedShmemSegAddr;

#ifdef USE_INJECTION_POINTS
	ActiveInjectionPoints = param->ActiveInjectionPoints;
#endif

	/* 【中文】共享内存结构指针恢复后，即可直接访问（需已重新 attach）。 */
	ProcGlobal = param->ProcGlobal;
	AuxiliaryProcs = param->AuxiliaryProcs;
	PreparedXactProcs = param->PreparedXactProcs;
	PMSignalState = param->PMSignalState;
	ProcSignal = param->ProcSignal;

	PostmasterPid = param->PostmasterPid;
	PgStartTime = param->PgStartTime;
	PgReloadTime = param->PgReloadTime;
	first_syslogger_file_time = param->first_syslogger_file_time;

	redirection_done = param->redirection_done;
	IsBinaryUpgrade = param->IsBinaryUpgrade;
	query_id_enabled = param->query_id_enabled;
	max_safe_fds = param->max_safe_fds;

	MaxBackends = param->MaxBackends;
	num_pmchild_slots = param->num_pmchild_slots;

	timing_tsc_frequency_khz = param->timing_tsc_frequency_khz;

	/* Re-run logic usually done by assign_timing_clock_source */
	/* 【中文】重新初始化计时时钟源——相当于重跑一遍
	 * assign_timing_clock_source 的赋值逻辑（TSC 频率已恢复）。 */
	pg_initialize_timing();
	pg_set_timing_clock_source(timing_clock_source);

#ifdef WIN32
	PostmasterHandle = param->PostmasterHandle;
	pgwin32_initial_signal_pipe = param->initial_signal_pipe;
#else
	/* 【中文】恢复"postmaster 存活检测"管道读端（父进程死亡时被通知）。 */
	memcpy(&postmaster_alive_fds, &param->postmaster_alive_fds,
		   sizeof(postmaster_alive_fds));
#endif

	memcpy(&syslogPipe, &param->syslogPipe, sizeof(syslogPipe));

	strlcpy(my_exec_path, param->my_exec_path, MAXPGPATH);

	strlcpy(pkglib_path, param->pkglib_path, MAXPGPATH);

	/*
	 * We need to restore fd.c's counts of externally-opened FDs; to avoid
	 * confusion, be sure to do this after restoring max_safe_fds.  (Note:
	 * BackendInitialize will handle this for (*client_sock)->sock.)
	 * 【中文】把两个存活检测管道的 fd 计入 fd.c 的"外部 fd 计数"，
	 * 防止 fd.c 误把它们当作自己的文件管理（须在恢复 max_safe_fds 之后）。
	 */
#ifndef WIN32
	if (postmaster_alive_fds[0] >= 0)
		ReserveExternalFD();
	if (postmaster_alive_fds[1] >= 0)
		ReserveExternalFD();
#endif
}

#endif							/* EXEC_BACKEND */
