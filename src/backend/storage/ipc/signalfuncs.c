/*-------------------------------------------------------------------------
 *
 * signalfuncs.c
 *	  Functions for signaling backends
 *
 * 【模块总览(中文)】
 * 本文件实现向 SQL 层暴露的"信号函数":pg_cancel_backend(取消查询)、
 * pg_terminate_backend(终止后端)、pg_reload_conf(重载配置)、
 * pg_rotate_logfile(轮转日志)。它们把"对另一个后端进程发信号"这件内核
 * 操作封装成 SQL 可见的函数。
 *
 * 【权限模型】
 * 信号是否允许发送由 pg_signal_backend() 集中检查,规则是:
 * - 目标后端若属于超级用户(或未登记角色,视同超管),则只有超级用户
 *   (或拥有 pg_signal_autovacuum_worker 角色权限者,对 autovacuum
 *   worker)可以信号它;
 * - 其余情况,调用者须拥有目标后端所属角色的权限(has_privs_of_role),
 *   或拥有 pg_signal_backend 角色的权限。
 * 检查结果用编码数字返回,由各 SQL 函数翻译成对应的 errdetail 错误信息。
 *
 * 【实现机制】
 * - BackendPidGetProc()(procarray.c)把 PID 翻译成 PGPROC,进而获得
 *   目标进程的角色信息并校验其身份;校验与 kill() 之间存在 TOCTOU
 *   竞态窗口,但在顺序 PID 分配 + 回绕的模型下风险可忽略;
 * - 信号实际通过 kill(-pid, sig) 发送(系统支持 setsid() 时对整个
 *   进程组),确保目标及其子进程(如并行 worker)一起收到;
 * - pg_terminate_backend 的可选 timeout 由 pg_wait_until_termination()
 *   实现轮询等待:每隔一小段时间用 kill(pid, 0) 探测目标是否已消失。
 * - pg_reload_conf / pg_rotate_logfile 不经过上述权限检查,它们的权限
 *   完全交给 SQL 的 GRANT 系统管理。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/signalfuncs.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>

#include "catalog/pg_authid.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/syslogger.h"
#include "storage/pmsignal.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "utils/acl.h"
#include "utils/fmgrprotos.h"
#include "utils/wait_event.h"


/*
 * Send a signal to another backend.
 *
 * The signal is delivered if the user is either a superuser or the same
 * role as the backend being signaled. For "dangerous" signals, an explicit
 * check for superuser needs to be done prior to calling this function.
 *
 * Returns 0 on success, 1 on general failure, 2 on normal permission error,
 * 3 if the caller needs to be a superuser, and 4 if the caller needs to have
 * privileges of pg_signal_autovacuum_worker.
 *
 * In the event of a general failure (return code 1), a warning message will
 * be emitted. For permission errors, doing that is the responsibility of
 * the caller.
 */
/* pg_signal_backend() 的返回码:
 * SIGNAL_BACKEND_SUCCESS      —— 发送成功;
 * SIGNAL_BACKEND_ERROR        —— 一般性失败(目标不是 PG 后端进程、或
 *                                 kill 系统调用失败),已记录 WARNING;
 * SIGNAL_BACKEND_NOPERMISSION —— 普通权限不足(调用者不属于目标角色,
 *                                 也没有 pg_signal_backend 角色权限);
 * SIGNAL_BACKEND_NOSUPERUSER  —— 目标是超级用户拥有的后端,而调用者
 *                                 不是超级用户;
 * SIGNAL_BACKEND_NOAUTOVAC    —— 目标是 autovacuum worker,而调用者
 *                                 没有 pg_signal_autovacuum_worker
 *                                 角色权限。 */
#define SIGNAL_BACKEND_SUCCESS 0
#define SIGNAL_BACKEND_ERROR 1
#define SIGNAL_BACKEND_NOPERMISSION 2
#define SIGNAL_BACKEND_NOSUPERUSER 3
#define SIGNAL_BACKEND_NOAUTOVAC 4
/*
 * pg_signal_backend - (中文)向另一个后端进程发送信号的公共"检查 + 发送"
 * 例程
 *
 * 【作用】被 pg_cancel_backend / pg_terminate_backend 调用:先把 PID 翻译
 * 成 PGPROC,校验权限,再真正执行 kill()。是所有"跨进程信号"SQL 函数的
 * 公共底层。
 *
 * 【设计思想】
 * - BackendPidGetProc 找不到 PID 时只发 WARNING 并返回错误码,而不是
 *   ERROR:调用方常常在结果集里循环,若某个后端恰好在循环中途自己退出,
 *   循环不应被打断;
 * - 权限校验的对象是目标 PGPROC 的 roleId(不是调用者的):超管后端只有
 *   超管能信号;非超管后端要求"调用者有目标角色权限,或有
 *   pg_signal_backend 角色权限"。未登记角色(roleId 无效,如 autovacuum
 *   worker)的后端按"重要性等同超管后端"处理,但专门为
 *   pg_signal_autovacuum_worker 角色开了口子;
 * - 校验与 kill 之间的 PID 复用竞态被视为可忽略:顺序 PID 分配 + 回绕
 *   使"刚校验过的进程恰好退出、PID 又被复用"几乎不可能;
 * - 有 setsid() 的平台上对 -pid 发信号,整个进程组一起收到——并行 worker
 *   是目标后端的子进程,组信号保证它们也被取消/终止。
 *
 * 【参数】
 *   pid —— 目标后端进程的 PID;
 *   sig —— 要发送的信号(SIGINT 取消查询 / SIGTERM 终止)。
 * 【返回值】SIGNAL_BACKEND_* 编码,见上方宏定义注释;一般性失败时已记录
 *           WARNING,权限类错误由调用方负责报错。
 */
static int
pg_signal_backend(int pid, int sig)
{
	PGPROC	   *proc = BackendPidGetProc(pid);

	/*
	 * BackendPidGetProc returns NULL if the pid isn't valid; but by the time
	 * we reach kill(), a process for which we get a valid proc here might
	 * have terminated on its own.  There's no way to acquire a lock on an
	 * arbitrary process to prevent that. But since so far all the callers of
	 * this mechanism involve some request for ending the process anyway, that
	 * it might end on its own first is not a problem.
	 *
	 * Note that proc will also be NULL if the pid refers to an auxiliary
	 * process or the postmaster (neither of which can be signaled via
	 * pg_signal_backend()).
	 */
	if (proc == NULL)
	{
		/*
		 * This is just a warning so a loop-through-resultset will not abort
		 * if one backend terminated on its own during the run.
		 */
		ereport(WARNING,
				(errmsg("PID %d is not a PostgreSQL backend process", pid)));

		return SIGNAL_BACKEND_ERROR;
	}

	/*
	 * Only allow superusers to signal superuser-owned backends.  Any process
	 * not advertising a role might have the importance of a superuser-owned
	 * backend, so treat it that way.  As an exception, we allow roles with
	 * privileges of pg_signal_autovacuum_worker to signal autovacuum workers
	 * (which do not advertise a role).
	 *
	 * Otherwise, users can signal backends for roles they have privileges of.
	 */
	if (!OidIsValid(proc->roleId) || superuser_arg(proc->roleId))
	{
		if (proc->backendType == B_AUTOVAC_WORKER)
		{
			if (!has_privs_of_role(GetUserId(), ROLE_PG_SIGNAL_AUTOVACUUM_WORKER))
				return SIGNAL_BACKEND_NOAUTOVAC;
		}
		else if (!superuser())
			return SIGNAL_BACKEND_NOSUPERUSER;
	}
	else if (!has_privs_of_role(GetUserId(), proc->roleId) &&
			 !has_privs_of_role(GetUserId(), ROLE_PG_SIGNAL_BACKEND))
		return SIGNAL_BACKEND_NOPERMISSION;

	/*
	 * Can the process we just validated above end, followed by the pid being
	 * recycled for a new process, before reaching here?  Then we'd be trying
	 * to kill the wrong thing.  Seems near impossible when sequential pid
	 * assignment and wraparound is used.  Perhaps it could happen on a system
	 * where pid re-use is randomized.  That race condition possibility seems
	 * too unlikely to worry about.
	 */

	/* If we have setsid(), signal the backend's whole process group */
#ifdef HAVE_SETSID
	if (kill(-pid, sig))
#else
	if (kill(pid, sig))
#endif
	{
		/* Again, just a warning to allow loops */
		ereport(WARNING,
				(errmsg("could not send signal to process %d: %m", pid)));
		return SIGNAL_BACKEND_ERROR;
	}
	return SIGNAL_BACKEND_SUCCESS;
}

/*
 * Signal to cancel a backend process.  This is allowed if you are a member of
 * the role whose process is being canceled.
 *
 * Note that only superusers can signal superuser-owned processes.
 */
/*
 * pg_cancel_backend - (中文)SQL 函数:取消指定后端的当前查询
 *
 * 【作用】向目标后端发送 SIGINT(查询取消中断)。SQL 语义:参数为要取消
 * 的进程 PID,返回 boolean(成功返回 true;失败返回 false 并附 WARNING,
 * 权限不足则报错)。
 *
 * 【设计思想】把 pg_signal_backend 的三个权限返回码翻译成带 errdetail 的
 * 权限拒绝错误,让用户明确知道"差在哪"(目标是超管后端 / autovacuum
 * worker / 普通角色)。SIGINT 使目标进程在下一个安全点检查到取消中断并
 * 中止当前查询。与 pg_terminate_backend 的区别仅在于信号与错误文案:
 * 取消是可恢复的(SIGINT),终止是不可恢复的(SIGTERM)。
 *
 * 【参数】PG_FUNCTION_ARGS 的第一个参数:目标后端 PID。
 * 【返回值】true 表示信号已成功发送。
 */
Datum
pg_cancel_backend(PG_FUNCTION_ARGS)
{
	int			r = pg_signal_backend(PG_GETARG_INT32(0), SIGINT);

	if (r == SIGNAL_BACKEND_NOSUPERUSER)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to cancel query"),
				 errdetail("Only roles with the %s attribute may cancel queries of roles with the %s attribute.",
						   "SUPERUSER", "SUPERUSER")));

	if (r == SIGNAL_BACKEND_NOAUTOVAC)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to cancel query"),
				 errdetail("Only roles with privileges of the \"%s\" role may cancel autovacuum workers.",
						   "pg_signal_autovacuum_worker")));

	if (r == SIGNAL_BACKEND_NOPERMISSION)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to cancel query"),
				 errdetail("Only roles with privileges of the role whose query is being canceled or with privileges of the \"%s\" role may cancel this query.",
						   "pg_signal_backend")));

	PG_RETURN_BOOL(r == SIGNAL_BACKEND_SUCCESS);
}

/*
 * Wait until there is no backend process with the given PID and return true.
 * On timeout, a warning is emitted and false is returned.
 */
/*
 * pg_wait_until_termination - (中文)轮询等待指定 PID 的进程消失
 *
 * 【作用】pg_terminate_backend 的等待逻辑:每隔最多 100ms 用 kill(pid, 0)
 * 探测目标是否还存在(ESRCH 表示已不存在),直到进程消失、超时或出现
 * 待处理中断。返回 true 表示在超时前目标已消失。
 *
 * 【设计思想】
 * - 用 kill(pid, 0) 只探测存在性、不发信号;ESRCH 之外的错误说明系统
 *   调用本身有问题,直接 ERROR;
 * - 每次探测前 CHECK_FOR_INTERRUPTS() 处理挂起的取消中断——否则用户
 *   已取消本查询,循环还会傻等;
 * - 用 WaitLatch(100ms 超时 + 闩锁 + postmaster 死亡即退出)睡眠而非
 *   忙等:既让出 CPU,又能被 latch 随时打断;
 * - 超时后只发 WARNING 并返回 false,保持"函数不抛错"的 SQL 行为。
 *
 * 【参数】
 *   pid     —— 要等待消失的目标 PID;
 *   timeout —— 总超时毫秒数。
 * 【返回值】true:目标已消失;false:超时(已发 WARNING)。
 */
static bool
pg_wait_until_termination(int pid, int64 timeout)
{
	/*
	 * Wait in steps of waittime milliseconds until this function exits or
	 * timeout.
	 */
	int64		waittime = 100;

	/*
	 * Initially remaining time is the entire timeout specified by the user.
	 */
	int64		remainingtime = timeout;

	/*
	 * Check existence of the backend. If the backend still exists, then wait
	 * for waittime milliseconds, again check for the existence. Repeat this
	 * until timeout or an error occurs or a pending interrupt such as query
	 * cancel gets processed.
	 */
	do
	{
		if (remainingtime < waittime)
			waittime = remainingtime;

		if (kill(pid, 0) == -1)
		{
			if (errno == ESRCH)
				return true;
			else
				ereport(ERROR,
						(errcode(ERRCODE_INTERNAL_ERROR),
						 errmsg("could not check the existence of the backend with PID %d: %m",
								pid)));
		}

		/* Process interrupts, if any, before waiting */
		CHECK_FOR_INTERRUPTS();

		(void) WaitLatch(MyLatch,
						 WL_LATCH_SET | WL_TIMEOUT | WL_EXIT_ON_PM_DEATH,
						 waittime,
						 WAIT_EVENT_BACKEND_TERMINATION);

		ResetLatch(MyLatch);

		remainingtime -= waittime;
	} while (remainingtime > 0);

	ereport(WARNING,
			(errmsg_plural("backend with PID %d did not terminate within %" PRId64 " millisecond",
						   "backend with PID %d did not terminate within %" PRId64 " milliseconds",
						   timeout,
						   pid, timeout)));

	return false;
}

/*
 * Send a signal to terminate a backend process. This is allowed if you are a
 * member of the role whose process is being terminated. If the timeout input
 * argument is 0, then this function just signals the backend and returns
 * true.  If timeout is nonzero, then it waits until no process has the given
 * PID; if the process ends within the timeout, true is returned, and if the
 * timeout is exceeded, a warning is emitted and false is returned.
 *
 * Note that only superusers can signal superuser-owned processes.
 */
/*
 * pg_terminate_backend - (中文)SQL 函数:终止指定后端进程
 *
 * 【作用】向目标后端发送 SIGTERM(正常终止)。可选 timeout(毫秒)参数:
 * 为 0 时只发信号立即返回 true;为正数时等待目标进程真正消失,超时发
 * WARNING 并返回 false。
 *
 * 【设计思想】权限检查与 pg_cancel_backend 相同(超管后端只能由超管
 * 终止,普通后端需要角色权限或 pg_signal_backend 权限);timeout 为负
 * 直接报 ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE。等待仅在"信号发送成功
 * 且 timeout > 0"时才进行——发送失败时没有理由等待。返回 true 只承诺
 * "信号已发出或进程已消失",不等于目标一定被杀掉(目标可能在收信号前
 * 自己退出)。
 *
 * 【参数】PG_FUNCTION_ARGS:第一个参数为目标 PID;第二个参数为等待毫秒数。
 * 【返回值】boolean;true 表示信号已发送(或按 timeout 等到了进程消失)。
 */
Datum
pg_terminate_backend(PG_FUNCTION_ARGS)
{
	int			pid;
	int			r;
	int			timeout;		/* milliseconds */

	pid = PG_GETARG_INT32(0);
	timeout = PG_GETARG_INT64(1);

	if (timeout < 0)
		ereport(ERROR,
				(errcode(ERRCODE_NUMERIC_VALUE_OUT_OF_RANGE),
				 errmsg("\"timeout\" must not be negative")));

	r = pg_signal_backend(pid, SIGTERM);

	if (r == SIGNAL_BACKEND_NOSUPERUSER)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to terminate process"),
				 errdetail("Only roles with the %s attribute may terminate processes of roles with the %s attribute.",
						   "SUPERUSER", "SUPERUSER")));

	if (r == SIGNAL_BACKEND_NOAUTOVAC)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to terminate process"),
				 errdetail("Only roles with privileges of the \"%s\" role may terminate autovacuum workers.",
						   "pg_signal_autovacuum_worker")));

	if (r == SIGNAL_BACKEND_NOPERMISSION)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to terminate process"),
				 errdetail("Only roles with privileges of the role whose process is being terminated or with privileges of the \"%s\" role may terminate this process.",
						   "pg_signal_backend")));

	/* Wait only on success and if actually requested */
	if (r == SIGNAL_BACKEND_SUCCESS && timeout > 0)
		PG_RETURN_BOOL(pg_wait_until_termination(pid, timeout));
	else
		PG_RETURN_BOOL(r == SIGNAL_BACKEND_SUCCESS);
}

/*
 * Signal to reload the database configuration
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * pg_reload_conf - (中文)SQL 函数:通知 postmaster 重载配置文件
 *
 * 【作用】向 postmaster 进程发送 SIGHUP,使其重新读取 postgresql.conf
 * 等配置,并把重载事件广播给所有子进程。
 *
 * 【设计思想】权限完全交给 SQL 的 GRANT 系统管理(函数本身不做额外
 * 检查,是否可执行由系统目录的权限项决定)。直接用 PostmasterPid 发
 * 信号,失败(如 postmaster 恰好不在)时发 WARNING 返回 false,不抛错。
 *
 * 【参数】无。
 * 【返回值】true 表示 SIGHUP 已成功发出。
 */
Datum
pg_reload_conf(PG_FUNCTION_ARGS)
{
	if (kill(PostmasterPid, SIGHUP))
	{
		ereport(WARNING,
				(errmsg("failed to send signal to postmaster: %m")));
		PG_RETURN_BOOL(false);
	}

	PG_RETURN_BOOL(true);
}


/*
 * Rotate log file
 *
 * Permission checking for this function is managed through the normal
 * GRANT system.
 */
/*
 * pg_rotate_logfile - (中文)SQL 函数:请求轮转服务器日志文件
 *
 * 【作用】通过 SendPostmasterSignal(PMSIGNAL_ROTATE_LOGFILE) 请求
 * postmaster 指示 syslogger 轮转日志(把当前日志重命名为带时间戳的文件
 * 并开始新文件)。
 *
 * 【设计思想】仅当 logging_collector = on(日志收集模式)时才可能轮转,
 * 否则发 WARNING 返回 false;权限同样交给 GRANT 系统管理。注意本函数
 * 只是提出请求,轮转由 syslogger 异步完成,返回 true 不代表日志文件
 * 此刻已切换。
 *
 * 【参数】无。
 * 【返回值】true 表示轮转请求已受理。
 */
Datum
pg_rotate_logfile(PG_FUNCTION_ARGS)
{
	if (!Logging_collector)
	{
		ereport(WARNING,
				(errmsg("rotation not possible because log collection not active")));
		PG_RETURN_BOOL(false);
	}

	SendPostmasterSignal(PMSIGNAL_ROTATE_LOGFILE);
	PG_RETURN_BOOL(true);
}
