/*-------------------------------------------------------------------------
 *
 * dsm_impl.c
 *	  manage dynamic shared memory segments
 *
 * This file provides low-level APIs for creating and destroying shared
 * memory segments using several different possible techniques.  We refer
 * to these segments as dynamic because they can be created, altered, and
 * destroyed at any point during the server life cycle.  This is unlike
 * the main shared memory segment, of which there is always exactly one
 * and which is always mapped at a fixed address in every PostgreSQL
 * background process.
 *
 * Because not all systems provide the same primitives in this area, nor
 * do all primitives behave the same way on all systems, we provide
 * several implementations of this facility.  Many systems implement
 * POSIX shared memory (shm_open etc.), which is well-suited to our needs
 * in this area, with the exception that shared memory identifiers live
 * in a flat system-wide namespace, raising the uncomfortable prospect of
 * name collisions with other processes (including other copies of
 * PostgreSQL) running on the same system.  Some systems only support
 * the older System V shared memory interface (shmget etc.) which is
 * also usable; however, the default allocation limits are often quite
 * small, and the namespace is even more restricted.
 *
 * We also provide an mmap-based shared memory implementation.  This may
 * be useful on systems that provide shared memory via a special-purpose
 * filesystem; by opting for this implementation, the user can even
 * control precisely where their shared memory segments are placed.  It
 * can also be used as a fallback for systems where shm_open and shmget
 * are not available or can't be used for some reason.  Of course,
 * mapping a file residing on an actual spinning disk is a fairly poor
 * approximation for shared memory because writeback may hurt performance
 * substantially, but there should be few systems where we must make do
 * with such poor tools.
 *
 * As ever, Windows requires its own implementation.
 *
 * 【模块总览(中文)】
 * 本文件是"动态共享内存(DSM)"的平台层实现:它只负责最原始的系统
 * 调用,不管理引用计数、不自动清理(那是 dsm.c 的事)。它提供四种
 * 实现,由 GUC dynamic_shared_memory_type 在启动时选定一种:
 *
 * 1. POSIX(USE_DSM_POSIX,通常默认):shm_open()/shm_unlink() 创建与
 *    删除段,其余操作把段当文件处理(ftruncate/fstat/mmap)。命名空间
 *    是系统级平坦命名空间(/PostgreSQL.<handle>),可能与其他进程
 *    (包括别的 PG 实例)冲突,create 时靠 O_EXCL 检测重名并静默返回
 *    失败让上层换句柄重试。
 * 2. System V(USE_DSM_SYSV):shmget()/shmat()/shmdt()/shmctl()。
 *    命名空间更受限(key_t),默认分配上限通常很小;把 dsm_handle 直接
 *    当 key 用,并避开 IPC_PRIVATE 特殊值。
 * 3. mmap(USE_DSM_MMAP):在 PG_DYNSHMEM_DIR(默认为 $PGDATA/pg_dynshmem)
 *    里创建"pg_dynshmem.<handle>"普通文件再 mmap。可用于内存文件系统
 *    (如 /dev/shm)或作为无 shm_open/shmget 平台的回退;缺点是若放在
 *    磁盘上,写回会损害性能。创建时逐块写零(而非 ftruncate 留洞),
 *    确保文件空间真实分配,避免日后访问映射时 SIGBUS。
 * 4. Windows(USE_DSM_WINDOWS):CreateFileMapping/OpenFileMapping 基于
 *    系统页文件的映射对象;Windows 在"无引用时自动销毁对象",因此
 *    DETACH 与 DESTROY 等价。
 *
 * 【统一接口】所有实现都实现同一套原语(DSM_OP_CREATE/ATTACH/DETACH/
 * DESTROY),由 dsm_impl_op() 按类型分派。错误码映射统一由
 * errcode_for_dynamic_shared_memory() 完成(EFBIG/ENOMEM 归为
 * OUT_OF_MEMORY,其余按文件访问错误)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/dsm_impl.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <fcntl.h>
#include <signal.h>
#include <unistd.h>
#ifndef WIN32
#include <sys/mman.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/stat.h>
#endif

#include "common/file_perm.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "portability/mem.h"
#include "postmaster/postmaster.h"
#include "storage/dsm_impl.h"
#include "storage/fd.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

#ifdef USE_DSM_POSIX
static bool dsm_impl_posix(dsm_op op, dsm_handle handle, Size request_size,
						   void **impl_private, void **mapped_address,
						   Size *mapped_size, int elevel);
static int	dsm_impl_posix_resize(int fd, off_t size);
#endif
#ifdef USE_DSM_SYSV
static bool dsm_impl_sysv(dsm_op op, dsm_handle handle, Size request_size,
						  void **impl_private, void **mapped_address,
						  Size *mapped_size, int elevel);
#endif
#ifdef USE_DSM_WINDOWS
static bool dsm_impl_windows(dsm_op op, dsm_handle handle, Size request_size,
							 void **impl_private, void **mapped_address,
							 Size *mapped_size, int elevel);
#endif
#ifdef USE_DSM_MMAP
static bool dsm_impl_mmap(dsm_op op, dsm_handle handle, Size request_size,
						  void **impl_private, void **mapped_address,
						  Size *mapped_size, int elevel);
#endif
static int	errcode_for_dynamic_shared_memory(void);

const struct config_enum_entry dynamic_shared_memory_options[] = {
#ifdef USE_DSM_POSIX
	{"posix", DSM_IMPL_POSIX, false},
#endif
#ifdef USE_DSM_SYSV
	{"sysv", DSM_IMPL_SYSV, false},
#endif
#ifdef USE_DSM_WINDOWS
	{"windows", DSM_IMPL_WINDOWS, false},
#endif
#ifdef USE_DSM_MMAP
	{"mmap", DSM_IMPL_MMAP, false},
#endif
	{NULL, 0, false}
};

/* Implementation selector. */
/* (中文)当前使用的 DSM 实现类型(DSM_IMPL_POSIX/SYSV/WINDOWS/MMAP,
 * GUC dynamic_shared_memory_type)。 */
int			dynamic_shared_memory_type = DEFAULT_DYNAMIC_SHARED_MEMORY_TYPE;

/* Amount of space reserved for DSM segments in the main area. */
/* (中文)主共享内存区为 DSM 预留的空间大小(MB,GUC
 * min_dynamic_shared_memory):0 表示不预留。dsm.c 的
 * dsm_main_space_request 用它换算字节数。 */
int			min_dynamic_shared_memory;

/* Size of buffer to be used for zero-filling. */
/* (中文)零填充缓冲大小:mmap 实现创建段时,按这个块大小分块写零。 */
#define ZBUFFER_SIZE				8192

/* (中文)Windows 段名统一前缀("Global/PostgreSQL"),与主共享内存的
 * 命名方式保持一致(见 GetSharedMemName 的相关说明)。 */
#define SEGMENT_NAME_PREFIX			"Global/PostgreSQL"

/*------
 * Perform a low-level shared memory operation in a platform-specific way,
 * as dictated by the selected implementation.  Each implementation is
 * required to implement the following primitives.
 *
 * DSM_OP_CREATE.  Create a segment whose size is the request_size and
 * map it.
 *
 * DSM_OP_ATTACH.  Map the segment, whose size must be the request_size.
 *
 * DSM_OP_DETACH.  Unmap the segment.
 *
 * DSM_OP_DESTROY.  Unmap the segment, if it is mapped.  Destroy the
 * segment.
 *
 * Arguments:
 *	 op: The operation to be performed.
 *	 handle: The handle of an existing object, or for DSM_OP_CREATE, the
 *	   identifier for the new handle the caller wants created.
 *	 request_size: For DSM_OP_CREATE, the requested size.  Otherwise, 0.
 *	 impl_private: Private, implementation-specific data.  Will be a pointer
 *	   to NULL for the first operation on a shared memory segment within this
 *	   backend; thereafter, it will point to the value to which it was set
 *	   on the previous call.
 *	 mapped_address: Pointer to start of current mapping; pointer to NULL
 *	   if none.  Updated with new mapping address.
 *	 mapped_size: Pointer to size of current mapping; pointer to 0 if none.
 *	   Updated with new mapped size.
 *	 elevel: Level at which to log errors.
 *
 * Return value: true on success, false on failure.  When false is returned,
 * a message should first be logged at the specified elevel, except in the
 * case where DSM_OP_CREATE experiences a name collision, which should
 * silently return false.
 *-----
 */
/*
 * dsm_impl_op - (中文)平台层 DSM 操作的统一入口(按实现类型分派)
 *
 * 【作用】把"创建/附着/拆除/销毁"四个操作按
 * dynamic_shared_memory_type 分派给对应的平台实现,统一参数与返回
 * 约定。
 *
 * 【设计思想】dsm.c 只面向本函数编程,不感知平台差异;各平台实现
 * 共享同一套 (op, handle, request_size, impl_private, mapped_address,
 * mapped_size, elevel) 接口,使上层代码完全可移植。参数断言先做
 * 一致性校验。
 *
 * 【参数】含义见上方原注释(operation 定义):
 *   op             —— DSM_OP_CREATE/ATTACH/DETACH/DESTROY;
 *   handle         —— 段句柄(CREATE 时是期望的新句柄);
 *   request_size   —— 仅 CREATE 有意义:段大小;其余传 0;
 *   impl_private   —— 平台私有数据(跨调用保持,首次为 NULL);
 *   mapped_address —— 当前映射地址(无则为 NULL),成功后更新;
 *   mapped_size    —— 当前映射大小(无则为 0),成功后更新;
 *   elevel         —— 错误日志级别。
 * 【返回值】true 成功;false 失败(调用方应先按 elevel 记录了消息;
 * CREATE 撞名时静默返回 false,由上层换句柄重试)。
 */
bool
dsm_impl_op(dsm_op op, dsm_handle handle, Size request_size,
			void **impl_private, void **mapped_address, Size *mapped_size,
			int elevel)
{
	Assert(op == DSM_OP_CREATE || request_size == 0);
	Assert((op != DSM_OP_CREATE && op != DSM_OP_ATTACH) ||
		   (*mapped_address == NULL && *mapped_size == 0));

	switch (dynamic_shared_memory_type)
	{
#ifdef USE_DSM_POSIX
		case DSM_IMPL_POSIX:
			return dsm_impl_posix(op, handle, request_size, impl_private,
								  mapped_address, mapped_size, elevel);
#endif
#ifdef USE_DSM_SYSV
		case DSM_IMPL_SYSV:
			return dsm_impl_sysv(op, handle, request_size, impl_private,
								 mapped_address, mapped_size, elevel);
#endif
#ifdef USE_DSM_WINDOWS
		case DSM_IMPL_WINDOWS:
			return dsm_impl_windows(op, handle, request_size, impl_private,
									mapped_address, mapped_size, elevel);
#endif
#ifdef USE_DSM_MMAP
		case DSM_IMPL_MMAP:
			return dsm_impl_mmap(op, handle, request_size, impl_private,
								 mapped_address, mapped_size, elevel);
#endif
		default:
			elog(ERROR, "unexpected dynamic shared memory type: %d",
				 dynamic_shared_memory_type);
			return false;
	}
}

#ifdef USE_DSM_POSIX
/*
 * Operating system primitives to support POSIX shared memory.
 *
 * POSIX shared memory segments are created and attached using shm_open()
 * and shm_unlink(); other operations, such as sizing or mapping the
 * segment, are performed as if the shared memory segments were files.
 *
 * Indeed, on some platforms, they may be implemented that way.  While
 * POSIX shared memory segments seem intended to exist in a flat namespace,
 * some operating systems may implement them as files, even going so far
 * to treat a request for /xyz as a request to create a file by that name
 * in the root directory.  Users of such broken platforms should select
 * a different shared memory implementation.
 */
/*
 * dsm_impl_posix - (中文)POSIX 共享内存实现(shm_open 系列)
 *
 * 【作用】实现四个 DSM 操作:
 * - DETACH/DESTROY:先 munmap(若有映射),DESTROY 再 shm_unlink 删除段;
 * - CREATE/ATTACH:先 ReserveExternalFD 登记 FD 占用(防 EMFILE,短暂
 *   持有所以用 Reserve 而非 Acquire),shm_open 打开(CREATE 加
 *   O_CREAT|O_EXCL,撞名即 EEXIST 静默失败,让上层重试新句柄);
 *   段名 "/PostgreSQL.<handle>";ATTACH 用 fstat 取现有大小,CREATE
 *   用 dsm_impl_posix_resize 把段扩到请求大小;最后 mmap 映射。
 * 每个失败路径都做已做工作的回退(close/ReleaseExternalFD/必要时
 * shm_unlink)再报错。
 *
 * 【设计思想】POSIX 段名位于系统级平坦命名空间,撞名只可能是"别的
 * 进程(含别的 PG 实例)用过该句柄",因此 CREATE 撞名必须静默返回
 * false 而非报错——上层会换句柄重试。映射用 MAP_SHARED|MAP_HASSEMAPHORE
 * |MAP_NOSYNC(Berkeley 系标志,其他平台忽略)。
 *
 * 【参数】同 dsm_impl_op。
 * 【返回值】true 成功;false 失败(消息已按 elevel 记录;CREATE 撞名
 * 静默)。
 */
static bool
dsm_impl_posix(dsm_op op, dsm_handle handle, Size request_size,
			   void **impl_private, void **mapped_address, Size *mapped_size,
			   int elevel)
{
	char		name[64];
	int			flags;
	int			fd;
	char	   *address;

	snprintf(name, 64, "/PostgreSQL.%u", handle);

	/* Handle teardown cases. */
	if (op == DSM_OP_DETACH || op == DSM_OP_DESTROY)
	{
		if (*mapped_address != NULL
			&& munmap(*mapped_address, *mapped_size) != 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not unmap shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		*mapped_address = NULL;
		*mapped_size = 0;
		if (op == DSM_OP_DESTROY && shm_unlink(name) != 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not remove shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		return true;
	}

	/*
	 * Create new segment or open an existing one for attach.
	 *
	 * Even though we will close the FD before returning, it seems desirable
	 * to use Reserve/ReleaseExternalFD, to reduce the probability of EMFILE
	 * failure.  The fact that we won't hold the FD open long justifies using
	 * ReserveExternalFD rather than AcquireExternalFD, though.
	 */
	ReserveExternalFD();

	flags = O_RDWR | (op == DSM_OP_CREATE ? O_CREAT | O_EXCL : 0);
	if ((fd = shm_open(name, flags, PG_FILE_MODE_OWNER)) == -1)
	{
		ReleaseExternalFD();
		if (op == DSM_OP_ATTACH || errno != EEXIST)
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not open shared memory segment \"%s\": %m",
							name)));
		return false;
	}

	/*
	 * If we're attaching the segment, determine the current size; if we are
	 * creating the segment, set the size to the requested value.
	 */
	if (op == DSM_OP_ATTACH)
	{
		struct stat st;

		if (fstat(fd, &st) != 0)
		{
			int			save_errno;

			/* Back out what's already been done. */
			save_errno = errno;
			close(fd);
			ReleaseExternalFD();
			errno = save_errno;

			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not stat shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		request_size = st.st_size;
	}
	else if (dsm_impl_posix_resize(fd, request_size) != 0)
	{
		int			save_errno;

		/* Back out what's already been done. */
		save_errno = errno;
		close(fd);
		ReleaseExternalFD();
		shm_unlink(name);
		errno = save_errno;

		ereport(elevel,
				(errcode_for_dynamic_shared_memory(),
				 errmsg("could not resize shared memory segment \"%s\" to %zu bytes: %m",
						name, request_size)));
		return false;
	}

	/* Map it. */
	address = mmap(NULL, request_size, PROT_READ | PROT_WRITE,
				   MAP_SHARED | MAP_HASSEMAPHORE | MAP_NOSYNC, fd, 0);
	if (address == MAP_FAILED)
	{
		int			save_errno;

		/* Back out what's already been done. */
		save_errno = errno;
		close(fd);
		ReleaseExternalFD();
		if (op == DSM_OP_CREATE)
			shm_unlink(name);
		errno = save_errno;

		ereport(elevel,
				(errcode_for_dynamic_shared_memory(),
				 errmsg("could not map shared memory segment \"%s\": %m",
						name)));
		return false;
	}
	*mapped_address = address;
	*mapped_size = request_size;
	close(fd);
	ReleaseExternalFD();

	return true;
}

/*
 * Set the size of a virtual memory region associated with a file descriptor.
 * If necessary, also ensure that virtual memory is actually allocated by the
 * operating system, to avoid nasty surprises later.
 *
 * Returns non-zero if either truncation or allocation fails, and sets errno.
 */
/*
 * dsm_impl_posix_resize - (中文)调整 POSIX 段的尺寸并确保空间真实分配
 *
 * 【作用】把 fd 对应的段扩展到 size 字节:Linux 上用 posix_fallocate
 * (在 tmpfs 上实际分配页,见下方设计思想),其他平台用 ftruncate。
 * 两者都带 EINTR 重试循环。
 *
 * 【设计思想】Linux 下 shm_open 的 fd 背后是 tmpfs 文件:若只用
 * ftruncate 会在文件里留下"洞",访问洞时 tmpfs 才现场分配页,空间
 * 不够会直接 SIGBUS 崩溃;因此用 posix_fallocate 现在就分配好,
 * 失败时优雅地报 ENOSPC。调用期间屏蔽除 SIGQUIT 外的全部信号
 * (posix_fallocate 可能耗时很长且是全有或全无操作,反复被 SIGUSR1
 * 打断可能永远无法成功);EINTR 重试循环保留,以应对调试器/作业
 * 控制(SIGCONT)。
 *
 * 【参数】
 *   fd   —— 段的文件描述符;
 *   size —— 目标大小。
 * 【返回值】0 成功;非 0 失败(同时设置 errno;posix_fallocate 的
 * 返回值被赋给 errno 供调用方读取)。
 */
static int
dsm_impl_posix_resize(int fd, off_t size)
{
	int			rc;
	int			save_errno;
	sigset_t	save_sigmask;

	/*
	 * Block all blockable signals, except SIGQUIT.  posix_fallocate() can run
	 * for quite a long time, and is an all-or-nothing operation.  If we
	 * allowed SIGUSR1 to interrupt us repeatedly (for example, due to
	 * recovery conflicts), the retry loop might never succeed.
	 */
	if (IsUnderPostmaster)
		sigprocmask(SIG_SETMASK, &BlockSig, &save_sigmask);

	pgstat_report_wait_start(WAIT_EVENT_DSM_ALLOCATE);
#if defined(HAVE_POSIX_FALLOCATE) && defined(__linux__)

	/*
	 * On Linux, a shm_open fd is backed by a tmpfs file.  If we were to use
	 * ftruncate, the file would contain a hole.  Accessing memory backed by a
	 * hole causes tmpfs to allocate pages, which fails with SIGBUS if there
	 * is no more tmpfs space available.  So we ask tmpfs to allocate pages
	 * here, so we can fail gracefully with ENOSPC now rather than risking
	 * SIGBUS later.
	 *
	 * We still use a traditional EINTR retry loop to handle SIGCONT.
	 * posix_fallocate() doesn't restart automatically, and we don't want this
	 * to fail if you attach a debugger.
	 */
	do
	{
		rc = posix_fallocate(fd, 0, size);
	} while (rc == EINTR);

	/*
	 * The caller expects errno to be set, but posix_fallocate() doesn't set
	 * it.  Instead it returns error numbers directly.  So set errno, even
	 * though we'll also return rc to indicate success or failure.
	 */
	errno = rc;
#else
	/* Extend the file to the requested size. */
	do
	{
		rc = ftruncate(fd, size);
	} while (rc < 0 && errno == EINTR);
#endif
	pgstat_report_wait_end();

	if (IsUnderPostmaster)
	{
		save_errno = errno;
		sigprocmask(SIG_SETMASK, &save_sigmask, NULL);
		errno = save_errno;
	}

	return rc;
}

#endif							/* USE_DSM_POSIX */

#ifdef USE_DSM_SYSV
/*
 * Operating system primitives to support System V shared memory.
 *
 * System V shared memory segments are manipulated using shmget(), shmat(),
 * shmdt(), and shmctl().  As the default allocation limits for System V
 * shared memory are usually quite low, the POSIX facilities may be
 * preferable; but those are not supported everywhere.
 */
/*
 * dsm_impl_sysv - (中文)System V 共享内存实现(shmget 系列)
 *
 * 【作用】实现四个 DSM 操作:用 dsm_handle 作 key(shmget 的键),
 * 注意三点:1) key 取负修正(负 key 不可移植),2) 撞上 IPC_PRIVATE
 * 特殊值时模拟 EEXIST 失败,让 CREATE 重试;3) shmget 查找已存在段
 * 时 size 必须传 0(传非零且偏大会 EINVAL)。把 shmid(段标识)缓存
 * 在 impl_private(TopMemoryContext 里 palloc 的 int,避免反复查找,
 * 分配先于资源获取以防内存失败时泄漏资源)。
 * - CREATE:flags 加 IPC_CREAT|IPC_EXCL,shmget 创建;
 * - ATTACH:shmget 查标识,shmctl(IPC_STAT) 取实际大小;
 * - DETACH/DESTROY:shmdt 解除映射,DESTROY 再 shmctl(IPC_RMID) 删除,
 *   并释放 impl_private 缓存。
 *
 * 【设计思想】System V 命名空间窄(key_t 整数),把 handle 强制转换
 * 截断/扩宽的行为是"每次一致"的,因此跨进程仍能对上同一个段;
 * IPC_PRIVATE 只能由 shmget 自己生成,永远不该被我们用作 handle,
 * 撞上就按"重名"处理。
 *
 * 【参数】同 dsm_impl_op。
 * 【返回值】true 成功;false 失败(消息已按 elevel 记录;CREATE 撞名
 * 静默)。
 */
static bool
dsm_impl_sysv(dsm_op op, dsm_handle handle, Size request_size,
			  void **impl_private, void **mapped_address, Size *mapped_size,
			  int elevel)
{
	key_t		key;
	int			ident;
	char	   *address;
	char		name[64];
	int		   *ident_cache;

	/*
	 * POSIX shared memory and mmap-based shared memory identify segments with
	 * names.  To avoid needless error message variation, we use the handle as
	 * the name.
	 */
	snprintf(name, 64, "%u", handle);

	/*
	 * The System V shared memory namespace is very restricted; names are of
	 * type key_t, which is expected to be some sort of integer data type, but
	 * not necessarily the same one as dsm_handle.  Since we use dsm_handle to
	 * identify shared memory segments across processes, this might seem like
	 * a problem, but it's really not.  If dsm_handle is bigger than key_t,
	 * the cast below might truncate away some bits from the handle the
	 * user-provided, but it'll truncate exactly the same bits away in exactly
	 * the same fashion every time we use that handle, which is all that
	 * really matters.  Conversely, if dsm_handle is smaller than key_t, we
	 * won't use the full range of available key space, but that's no big deal
	 * either.
	 *
	 * We do make sure that the key isn't negative, because that might not be
	 * portable.
	 */
	key = (key_t) handle;
	if (key < 1)				/* avoid compiler warning if type is unsigned */
		key = -key;

	/*
	 * There's one special key, IPC_PRIVATE, which can't be used.  If we end
	 * up with that value by chance during a create operation, just pretend it
	 * already exists, so that caller will retry.  If we run into it anywhere
	 * else, the caller has passed a handle that doesn't correspond to
	 * anything we ever created, which should not happen.
	 */
	if (key == IPC_PRIVATE)
	{
		if (op != DSM_OP_CREATE)
			elog(DEBUG4, "System V shared memory key may not be IPC_PRIVATE");
		errno = EEXIST;
		return false;
	}

	/*
	 * Before we can do anything with a shared memory segment, we have to map
	 * the shared memory key to a shared memory identifier using shmget(). To
	 * avoid repeated lookups, we store the key using impl_private.
	 */
	if (*impl_private != NULL)
	{
		ident_cache = *impl_private;
		ident = *ident_cache;
	}
	else
	{
		int			flags = IPCProtection;
		size_t		segsize;

		/*
		 * Allocate the memory BEFORE acquiring the resource, so that we don't
		 * leak the resource if memory allocation fails.
		 */
		ident_cache = MemoryContextAlloc(TopMemoryContext, sizeof(int));

		/*
		 * When using shmget to find an existing segment, we must pass the
		 * size as 0.  Passing a non-zero size which is greater than the
		 * actual size will result in EINVAL.
		 */
		segsize = 0;

		if (op == DSM_OP_CREATE)
		{
			flags |= IPC_CREAT | IPC_EXCL;
			segsize = request_size;
		}

		if ((ident = shmget(key, segsize, flags)) == -1)
		{
			if (op == DSM_OP_ATTACH || errno != EEXIST)
			{
				int			save_errno = errno;

				pfree(ident_cache);
				errno = save_errno;
				ereport(elevel,
						(errcode_for_dynamic_shared_memory(),
						 errmsg("could not get shared memory segment: %m")));
			}
			return false;
		}

		*ident_cache = ident;
		*impl_private = ident_cache;
	}

	/* Handle teardown cases. */
	if (op == DSM_OP_DETACH || op == DSM_OP_DESTROY)
	{
		pfree(ident_cache);
		*impl_private = NULL;
		if (*mapped_address != NULL && shmdt(*mapped_address) != 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not unmap shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		*mapped_address = NULL;
		*mapped_size = 0;
		if (op == DSM_OP_DESTROY && shmctl(ident, IPC_RMID, NULL) < 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not remove shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		return true;
	}

	/* If we're attaching it, we must use IPC_STAT to determine the size. */
	if (op == DSM_OP_ATTACH)
	{
		struct shmid_ds shm;

		if (shmctl(ident, IPC_STAT, &shm) != 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not stat shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		request_size = shm.shm_segsz;
	}

	/* Map it. */
	address = shmat(ident, NULL, PG_SHMAT_FLAGS);
	if (address == (void *) -1)
	{
		int			save_errno;

		/* Back out what's already been done. */
		save_errno = errno;
		if (op == DSM_OP_CREATE)
			shmctl(ident, IPC_RMID, NULL);
		errno = save_errno;

		ereport(elevel,
				(errcode_for_dynamic_shared_memory(),
				 errmsg("could not map shared memory segment \"%s\": %m",
						name)));
		return false;
	}
	*mapped_address = address;
	*mapped_size = request_size;

	return true;
}
#endif

#ifdef USE_DSM_WINDOWS
/*
 * Operating system primitives to support Windows shared memory.
 *
 * Windows shared memory implementation is done using file mapping
 * which can be backed by either physical file or system paging file.
 * Current implementation uses system paging file as other effects
 * like performance are not clear for physical file and it is used in similar
 * way for main shared memory in windows.
 *
 * A memory mapping object is a kernel object - they always get deleted when
 * the last reference to them goes away, either explicitly via a CloseHandle or
 * when the process containing the reference exits.
 */
/*
 * dsm_impl_windows - (中文)Windows 共享内存实现(CreateFileMapping/OpenFileMapping)
 *
 * 【作用】实现四个 DSM 操作:段名为 "Global/PostgreSQL.<handle>" 的
 * 文件映射对象(基于系统页文件,非物理文件):
 * - CREATE:CreateFileMapping(INVALID_HANDLE_VALUE = 用页文件)创建,
 *   返回 ERROR_ALREADY_EXISTS 或 ERROR_ACCESS_DENIED(已有同名对象,
 *   后者是服务创建的)时关闭句柄并静默失败;
 * - ATTACH:OpenFileMapping 打开;
 * - DETACH/DESTROY:UnmapViewOfFile 解除映射 + CloseHandle 关闭句柄;
 *   Windows 对象在最后引用消失时自动销毁,因此两者等价;
 * - 映射后一律用 VirtualQuery 取实际区域大小(页粒度 4K 取整),使
 *   CREATE 与 ATTACH 的 mapped_size 口径一致。映射句柄存进
 *   impl_private。
 *
 * 【设计思想】Global\ 命名空间让任何会话的进程都可能访问对象
 * (依赖访问权限);命名沿用主共享内存的约定。Windows 没有
 * shm_unlink 概念——"删除"就是让所有引用消失,所以 pin 机制
 * (dsm_impl_pin_segment)专门为它复制句柄到 postmaster 保住引用。
 *
 * 【参数】同 dsm_impl_op。
 * 【返回值】true 成功;false 失败(消息已按 elevel 记录;CREATE 撞名
 * 静默)。
 */
static bool
dsm_impl_windows(dsm_op op, dsm_handle handle, Size request_size,
				 void **impl_private, void **mapped_address,
				 Size *mapped_size, int elevel)
{
	char	   *address;
	HANDLE		hmap;
	char		name[64];
	MEMORY_BASIC_INFORMATION info;

	/*
	 * Storing the shared memory segment in the Global\ namespace, can allow
	 * any process running in any session to access that file mapping object
	 * provided that the caller has the required access rights. But to avoid
	 * issues faced in main shared memory, we are using the naming convention
	 * similar to main shared memory. We can change here once issue mentioned
	 * in GetSharedMemName is resolved.
	 */
	snprintf(name, 64, "%s.%u", SEGMENT_NAME_PREFIX, handle);

	/*
	 * Handle teardown cases.  Since Windows automatically destroys the object
	 * when no references remain, we can treat it the same as detach.
	 */
	if (op == DSM_OP_DETACH || op == DSM_OP_DESTROY)
	{
		if (*mapped_address != NULL
			&& UnmapViewOfFile(*mapped_address) == 0)
		{
			_dosmaperr(GetLastError());
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not unmap shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		if (*impl_private != NULL
			&& CloseHandle(*impl_private) == 0)
		{
			_dosmaperr(GetLastError());
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not remove shared memory segment \"%s\": %m",
							name)));
			return false;
		}

		*impl_private = NULL;
		*mapped_address = NULL;
		*mapped_size = 0;
		return true;
	}

	/* Create new segment or open an existing one for attach. */
	if (op == DSM_OP_CREATE)
	{
		DWORD		size_high;
		DWORD		size_low;
		DWORD		errcode;

		/* Shifts >= the width of the type are undefined. */
#ifdef _WIN64
		size_high = request_size >> 32;
#else
		size_high = 0;
#endif
		size_low = (DWORD) request_size;

		/* CreateFileMapping might not clear the error code on success */
		SetLastError(0);

		hmap = CreateFileMapping(INVALID_HANDLE_VALUE,	/* Use the pagefile */
								 NULL,	/* Default security attrs */
								 PAGE_READWRITE,	/* Memory is read/write */
								 size_high, /* Upper 32 bits of size */
								 size_low,	/* Lower 32 bits of size */
								 name);

		errcode = GetLastError();
		if (errcode == ERROR_ALREADY_EXISTS || errcode == ERROR_ACCESS_DENIED)
		{
			/*
			 * On Windows, when the segment already exists, a handle for the
			 * existing segment is returned.  We must close it before
			 * returning.  However, if the existing segment is created by a
			 * service, then it returns ERROR_ACCESS_DENIED. We don't do
			 * _dosmaperr here, so errno won't be modified.
			 */
			if (hmap)
				CloseHandle(hmap);
			return false;
		}

		if (!hmap)
		{
			_dosmaperr(errcode);
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not create shared memory segment \"%s\": %m",
							name)));
			return false;
		}
	}
	else
	{
		hmap = OpenFileMapping(FILE_MAP_WRITE | FILE_MAP_READ,
							   FALSE,	/* do not inherit the name */
							   name);	/* name of mapping object */
		if (!hmap)
		{
			_dosmaperr(GetLastError());
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not open shared memory segment \"%s\": %m",
							name)));
			return false;
		}
	}

	/* Map it. */
	address = MapViewOfFile(hmap, FILE_MAP_WRITE | FILE_MAP_READ,
							0, 0, 0);
	if (!address)
	{
		int			save_errno;

		_dosmaperr(GetLastError());
		/* Back out what's already been done. */
		save_errno = errno;
		CloseHandle(hmap);
		errno = save_errno;

		ereport(elevel,
				(errcode_for_dynamic_shared_memory(),
				 errmsg("could not map shared memory segment \"%s\": %m",
						name)));
		return false;
	}

	/*
	 * VirtualQuery gives size in page_size units, which is 4K for Windows. We
	 * need size only when we are attaching, but it's better to get the size
	 * when creating new segment to keep size consistent both for
	 * DSM_OP_CREATE and DSM_OP_ATTACH.
	 */
	if (VirtualQuery(address, &info, sizeof(info)) == 0)
	{
		int			save_errno;

		_dosmaperr(GetLastError());
		/* Back out what's already been done. */
		save_errno = errno;
		UnmapViewOfFile(address);
		CloseHandle(hmap);
		errno = save_errno;

		ereport(elevel,
				(errcode_for_dynamic_shared_memory(),
				 errmsg("could not stat shared memory segment \"%s\": %m",
						name)));
		return false;
	}

	*mapped_address = address;
	*mapped_size = info.RegionSize;
	*impl_private = hmap;

	return true;
}
#endif

#ifdef USE_DSM_MMAP
/*
 * Operating system primitives to support mmap-based shared memory.
 *
 * Calling this "shared memory" is somewhat of a misnomer, because what
 * we're really doing is creating a bunch of files and mapping them into
 * our address space.  The operating system may feel obliged to
 * synchronize the contents to disk even if nothing is being paged out,
 * which will not serve us well.  The user can relocate the pg_dynshmem
 * directory to a ramdisk to avoid this problem, if available.
 */
/*
 * dsm_impl_mmap - (中文)mmap 文件实现(把"共享内存"做成普通文件再映射)
 *
 * 【作用】实现四个 DSM 操作:文件名为
 * "PG_DYNSHMEM_DIR/pg_dynshmem.<handle>":
 * - DETACH/DESTROY:munmap(若有映射),DESTROY 再 unlink 删文件;
 * - CREATE/ATTACH:OpenTransientFile 打开(CREATE 加 O_CREAT|O_EXCL,
 *   撞名静默失败);ATTACH 用 fstat 取现有大小;CREATE 则分块写零
 *   (见设计思想);最后 mmap 映射并关闭 fd。
 *
 * 【设计思想】把文件扩展成"带洞"的文件(仅 ftruncate)会让映射后的
 * 页面在首次访问时才真正分配,空间不足会 SIGBUS 崩溃;所以创建时
 * 用 8KB 缓冲逐块 write 把文件空间实打实写出来(代价较大,但换来源
 * 码注释所称的可靠性)。文件放在磁盘上时,OS 可能把内容写回磁盘,
 * 性能差;用户可把 PG_DYNSHMEM_DIR 指到内存文件系统(如 /dev/shm)。
 *
 * 【参数】同 dsm_impl_op。
 * 【返回值】true 成功;false 失败(消息已按 elevel 记录;CREATE 撞名
 * 静默)。
 */
static bool
dsm_impl_mmap(dsm_op op, dsm_handle handle, Size request_size,
			  void **impl_private, void **mapped_address, Size *mapped_size,
			  int elevel)
{
	char		name[64];
	int			flags;
	int			fd;
	char	   *address;

	snprintf(name, 64, PG_DYNSHMEM_DIR "/" PG_DYNSHMEM_MMAP_FILE_PREFIX "%u",
			 handle);

	/* Handle teardown cases. */
	if (op == DSM_OP_DETACH || op == DSM_OP_DESTROY)
	{
		if (*mapped_address != NULL
			&& munmap(*mapped_address, *mapped_size) != 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not unmap shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		*mapped_address = NULL;
		*mapped_size = 0;
		if (op == DSM_OP_DESTROY && unlink(name) != 0)
		{
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not remove shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		return true;
	}

	/* Create new segment or open an existing one for attach. */
	flags = O_RDWR | (op == DSM_OP_CREATE ? O_CREAT | O_EXCL : 0);
	if ((fd = OpenTransientFile(name, flags)) == -1)
	{
		if (op == DSM_OP_ATTACH || errno != EEXIST)
			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not open shared memory segment \"%s\": %m",
							name)));
		return false;
	}

	/*
	 * If we're attaching the segment, determine the current size; if we are
	 * creating the segment, set the size to the requested value.
	 */
	if (op == DSM_OP_ATTACH)
	{
		struct stat st;

		if (fstat(fd, &st) != 0)
		{
			int			save_errno;

			/* Back out what's already been done. */
			save_errno = errno;
			CloseTransientFile(fd);
			errno = save_errno;

			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not stat shared memory segment \"%s\": %m",
							name)));
			return false;
		}
		request_size = st.st_size;
	}
	else
	{
		/*
		 * Allocate a buffer full of zeros.
		 *
		 * Note: palloc zbuffer, instead of just using a local char array, to
		 * ensure it is reasonably well-aligned; this may save a few cycles
		 * transferring data to the kernel.
		 */
		char	   *zbuffer = (char *) palloc0(ZBUFFER_SIZE);
		Size		remaining = request_size;
		bool		success = true;

		/*
		 * Zero-fill the file. We have to do this the hard way to ensure that
		 * all the file space has really been allocated, so that we don't
		 * later seg fault when accessing the memory mapping.  This is pretty
		 * pessimal.
		 */
		while (success && remaining > 0)
		{
			Size		goal = remaining;

			if (goal > ZBUFFER_SIZE)
				goal = ZBUFFER_SIZE;
			pgstat_report_wait_start(WAIT_EVENT_DSM_FILL_ZERO_WRITE);
			if (write(fd, zbuffer, goal) == goal)
				remaining -= goal;
			else
				success = false;
			pgstat_report_wait_end();
		}

		if (!success)
		{
			int			save_errno;

			/* Back out what's already been done. */
			save_errno = errno;
			CloseTransientFile(fd);
			unlink(name);
			errno = save_errno ? save_errno : ENOSPC;

			ereport(elevel,
					(errcode_for_dynamic_shared_memory(),
					 errmsg("could not resize shared memory segment \"%s\" to %zu bytes: %m",
							name, request_size)));
			return false;
		}
	}

	/* Map it. */
	address = mmap(NULL, request_size, PROT_READ | PROT_WRITE,
				   MAP_SHARED | MAP_HASSEMAPHORE | MAP_NOSYNC, fd, 0);
	if (address == MAP_FAILED)
	{
		int			save_errno;

		/* Back out what's already been done. */
		save_errno = errno;
		CloseTransientFile(fd);
		if (op == DSM_OP_CREATE)
			unlink(name);
		errno = save_errno;

		ereport(elevel,
				(errcode_for_dynamic_shared_memory(),
				 errmsg("could not map shared memory segment \"%s\": %m",
						name)));
		return false;
	}
	*mapped_address = address;
	*mapped_size = request_size;

	if (CloseTransientFile(fd) != 0)
	{
		ereport(elevel,
				(errcode_for_file_access(),
				 errmsg("could not close shared memory segment \"%s\": %m",
						name)));
		return false;
	}

	return true;
}
#endif

/*
 * Implementation-specific actions that must be performed when a segment is to
 * be preserved even when no backend has it attached.
 *
 * Except on Windows, we don't need to do anything at all.  But since Windows
 * cleans up segments automatically when no references remain, we duplicate
 * the segment handle into the postmaster process.  The postmaster needn't
 * do anything to receive the handle; Windows transfers it automatically.
 */
/*
 * dsm_impl_pin_segment - (中文)段被"钉住"时的平台层动作(Windows 需要,其他平台空操作)
 *
 * 【作用】dsm_pin_segment() 调用本函数:Windows 下把本进程的段句柄
 * 用 DuplicateHandle 复制进 postmaster(句柄经 Windows 自动传递,
 * postmaster 无需准备),结果存入 impl_private_pm_handle。其他平台
 * 无操作。
 *
 * 【设计思想】Windows 的映射对象在"引用计数归零"时自动销毁,而
 * pin 的语义是"无任何后端附着也要存活":复制到 postmaster 的句柄
 * 就是那个保住对象的"引线"。该句柄只在 postmaster 进程里有效,但
 * 我们并不在别处使用它,只等 unpin 时关闭。
 *
 * 【参数】
 *   handle                  —— 段句柄(仅用于错误消息);
 *   impl_private            —— 本进程的映射对象句柄(Windows);
 *   impl_private_pm_handle  —— 输出参数:存放到 postmaster 的句柄。
 * 【返回值】无(失败 ERROR)。
 */
void
dsm_impl_pin_segment(dsm_handle handle, void *impl_private,
					 void **impl_private_pm_handle)
{
	switch (dynamic_shared_memory_type)
	{
#ifdef USE_DSM_WINDOWS
		case DSM_IMPL_WINDOWS:
			if (IsUnderPostmaster)
			{
				HANDLE		hmap;

				if (!DuplicateHandle(GetCurrentProcess(), impl_private,
									 PostmasterHandle, &hmap, 0, FALSE,
									 DUPLICATE_SAME_ACCESS))
				{
					char		name[64];

					snprintf(name, 64, "%s.%u", SEGMENT_NAME_PREFIX, handle);
					_dosmaperr(GetLastError());
					ereport(ERROR,
							(errcode_for_dynamic_shared_memory(),
							 errmsg("could not duplicate handle for \"%s\": %m",
									name)));
				}

				/*
				 * Here, we remember the handle that we created in the
				 * postmaster process.  This handle isn't actually usable in
				 * any process other than the postmaster, but that doesn't
				 * matter.  We're just holding onto it so that, if the segment
				 * is unpinned, dsm_impl_unpin_segment can close it.
				 */
				*impl_private_pm_handle = hmap;
			}
			break;
#endif
		default:
			break;
	}
}

/*
 * Implementation-specific actions that must be performed when a segment is no
 * longer to be preserved, so that it will be cleaned up when all backends
 * have detached from it.
 *
 * Except on Windows, we don't need to do anything at all.  For Windows, we
 * close the extra handle that dsm_impl_pin_segment created in the
 * postmaster's process space.
 */
/*
 * dsm_impl_unpin_segment - (中文)段被解除 pin 时的平台层动作(Windows 需要,其他平台空操作)
 *
 * 【作用】dsm_unpin_segment() 调用本函数:Windows 下用
 * DuplicateHandle(DUPLICATE_CLOSE_SOURCE) 关闭并释放 pin 时复制到
 * postmaster 的那个句柄,让映射对象重新回到"引用归零即销毁"的轨道。
 * 其他平台无操作。
 *
 * 【设计思想】与 dsm_impl_pin_segment 精确配对:复制进 postmaster 的
 * 句柄若不被显式关闭,对象永远有引用、永远不会销毁。
 *
 * 【参数】
 *   handle       —— 段句柄(仅用于错误消息);
 *   impl_private —— 指向"存于控制段的 postmaster 句柄"的指针(Windows;
 *                   函数成功后置 NULL)。
 * 【返回值】无(失败 ERROR)。
 */
void
dsm_impl_unpin_segment(dsm_handle handle, void **impl_private)
{
	switch (dynamic_shared_memory_type)
	{
#ifdef USE_DSM_WINDOWS
		case DSM_IMPL_WINDOWS:
			if (IsUnderPostmaster)
			{
				if (*impl_private &&
					!DuplicateHandle(PostmasterHandle, *impl_private,
									 NULL, NULL, 0, FALSE,
									 DUPLICATE_CLOSE_SOURCE))
				{
					char		name[64];

					snprintf(name, 64, "%s.%u", SEGMENT_NAME_PREFIX, handle);
					_dosmaperr(GetLastError());
					ereport(ERROR,
							(errcode_for_dynamic_shared_memory(),
							 errmsg("could not duplicate handle for \"%s\": %m",
									name)));
				}

				*impl_private = NULL;
			}
			break;
#endif
		default:
			break;
	}
}

/*
 * errcode_for_dynamic_shared_memory - (中文)把 DSM 操作的 errno 映射为 SQLSTATE
 *
 * 【作用】DSM 各实现报错时统一经本函数选 SQLSTATE:EFBIG(文件过大)
 * 或 ENOMEM 映射为 ERRCODE_OUT_OF_MEMORY,其余按文件访问错误处理
 * (errcode_for_file_access)。
 *
 * 【设计思想】DSM 操作失败常源于"内存/段空间不足",归入 out_of_memory
 * 便于上层(与应用、监控)正确归类。
 *
 * 【参数】无(读全局 errno)。
 * 【返回值】SQLSTATE 错误码。
 */
static int
errcode_for_dynamic_shared_memory(void)
{
	if (errno == EFBIG || errno == ENOMEM)
		return errcode(ERRCODE_OUT_OF_MEMORY);
	else
		return errcode_for_file_access();
}
