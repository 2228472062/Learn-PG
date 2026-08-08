/*-------------------------------------------------------------------------
 *
 * dsm.c
 *	  manage dynamic shared memory segments
 *
 * This file provides a set of services to make programming with dynamic
 * shared memory segments more convenient.  Unlike the low-level
 * facilities provided by dsm_impl.h and dsm_impl.c, mappings and segments
 * created using this module will be cleaned up automatically.  Mappings
 * will be removed when the resource owner under which they were created
 * is cleaned up, unless dsm_pin_mapping() is used, in which case they
 * have session lifespan.  Segments will be removed when there are no
 * remaining mappings, or at postmaster shutdown in any case.  After a
 * hard postmaster crash, remaining segments will be removed, if they
 * still exist, at the next postmaster startup.
 *
 * 【模块总览(中文)】
 * 本文件实现"动态共享内存(DSM)"的进程级管理,是 dsm_impl.c(平台层)
 * 之上的"便利层"与"生命周期层":
 *
 * 【与平台层的关系】dsm_impl.c 只提供最原始的"创建/打开/调整大小/
 * 销毁一个操作系统共享内存段"(shm_open / shmget / mmap / Windows API)。
 * 本文件在其上增加:引用计数、跨进程句柄、自动清理、资源所有者管理、
 * on-detach 回调、以及"从主共享内存区切分 DSM 段"的能力。
 *
 * 【核心数据结构】
 * - 控制段(dsm_control,一个特殊的 DSM 段):记录所有活跃段的状态。
 *   dsm_control_header 含 nitems/maxitems 与 item[] 数组;每个
 *   dsm_control_item 记录 handle、refcnt(引用计数,2+ 活跃、1 濒死
 *   "等待销毁"、0 槽位空闲)、pinned(是否被"钉住"到 postmaster 关闭)
 *   等。控制段全生命周期存活(不引用计数),由 postmaster 创建,句柄
 *   存在 PGShmemHeader->dsm_control 里,各进程经 dsm_attach 附着;
 * - 每进程的 dsm_segment_list:本进程已附着段的链表(进程私有),退出时
 *   逐段减引用计数;
 * - 主共享内存区(可选,min_dynamic_shared_memory > 0 时):在传统共享
 *   内存段里预留一块空间,用 FreePageManager 管理空闲页,可从中切出
 *   DSM 段(handle 为奇数,由 make_main_region_dsm_handle 生成)。
 *
 * 【引用计数协议】refcnt 语义:0 = 槽位空闲;1 = 濒死(最后一个引用
 * 者已离开、正在销毁或等待销毁);>= 2 = 活跃(1 个创建者引用 + 每
 * 个附着者 1 个引用,pin 另加 1)。计数降到 1 的进程负责销毁段。创建
 * 后计数从 2 起步。这个约定使得"最后一个 detach 的进程"必然触发
 * 销毁,而"被信号杀死在销毁途中"留下的 1 会在 postmaster 关闭或下次
 * 启动时被清理。
 *
 * 【自动清理】映射默认挂在当前 ResourceOwner 下,事务/查询结束自动
 * detach;dsm_pin_mapping() 可延长到会话级。段本身由引用计数决定
 * 生死;postmaster 关闭时 dsm_postmaster_shutdown() 兜底销毁所有
 * 剩余段;崩溃重启时用旧控制段句柄(存于 pg_control)找回并销毁
 * 孤儿段。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/dsm.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <fcntl.h>
#include <unistd.h>
#ifndef WIN32
#include <sys/mman.h>
#endif
#include <sys/stat.h>

#include "common/pg_prng.h"
#include "lib/ilist.h"
#include "miscadmin.h"
#include "port/pg_bitutils.h"
#include "storage/dsm.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/lwlock.h"
#include "storage/pg_shmem.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/freepage.h"
#include "utils/memutils.h"
#include "utils/resowner.h"

#define PG_DYNSHMEM_CONTROL_MAGIC		0x9a503d32
/* (中文)控制段的"魔数":附在控制段头部,用于判定"映射到的内存确实是
 * 我们的控制段"(配合 dsm_control_segment_sane 的健全性检查)。 */

#define PG_DYNSHMEM_FIXED_SLOTS			64
#define PG_DYNSHMEM_SLOTS_PER_BACKEND	5
/* (中文)控制段槽位容量计算:固定 64 个槽位 + 每个后端 5 个槽位
 * (× MaxBackends)。固定部分留给 postmaster 启动早期、后端尚未
 * 启动时就需要的段;每后端 5 个应对各子系统(并行查询、逻辑解码、
 * bgworker 等)的常规需求。 */

#define INVALID_CONTROL_SLOT		((uint32) -1)
/* (中文)无效控制槽位哨兵值:dsm_segment.control_slot 初始为此值,
 * 表示"尚未在控制段里登记"(create/attach 未完成或已 detach)。 */

/* Backend-local tracking for on-detach callbacks. */
/* (中文)一条"on-detach 回调"记录(进程私有):段被 detach 时执行
 * function(seg, arg)。挂在 dsm_segment.on_detach 单链表上。 */
typedef struct dsm_segment_detach_callback
{
	on_dsm_detach_callback function;
	Datum		arg;
	slist_node	node;
} dsm_segment_detach_callback;

/* Backend-local state for a dynamic shared memory segment. */
/* (中文)一个 DSM 段的进程私有描述符(不进共享内存):
 * - node          : dsm_segment_list 的链表节点;
 * - resowner      : 拥有该映射的资源所有者(NULL = 已 pin 到会话级);
 * - handle        : 段的句柄(跨进程标识,偶数 = 平台层真实段,奇数 =
 *                    主共享内存区伪段);
 * - control_slot  : 在控制段里的槽位下标(INVALID_CONTROL_SLOT 表示未
 *                    登记);
 * - impl_private  : 平台层私有数据(dsm_impl_op 使用,如 shm 名称);
 * - mapped_address: 本进程的映射地址(NULL = 未映射);
 * - mapped_size   : 本进程映射的大小;
 * - on_detach     : 本进程注册的 on-detach 回调链表。 */
struct dsm_segment
{
	dlist_node	node;			/* List link in dsm_segment_list. */
	ResourceOwner resowner;		/* Resource owner. */
	dsm_handle	handle;			/* Segment name. */
	uint32		control_slot;	/* Slot in control segment. */
	void	   *impl_private;	/* Implementation-specific private data. */
	void	   *mapped_address; /* Mapping address, or NULL if unmapped. */
	Size		mapped_size;	/* Size of our mapping. */
	slist_head	on_detach;		/* On-detach callbacks. */
};

/* Shared-memory state for a dynamic shared memory segment. */
/* (中文)控制段中一个段条目的共享状态:
 * - handle                : 段句柄;
 * - refcnt                : 引用计数(2+ 活跃、1 濒死=等待/正在销毁、
 *                            0 = 槽位空闲,见文件头"引用计数协议");
 * - first_page / npages   : 仅主共享内存区伪段有效:段在主区里的
 *                            起始页号与页数;
 * - impl_private_pm_handle: 仅 Windows 需要:postmaster 持有的段句柄
 *                            (pin 时保存、unpin 时使用);
 * - pinned                : 是否被 dsm_pin_segment 钉住(钉住的段在
 *                            无人引用时也不销毁,活到 postmaster 关闭)。 */
typedef struct dsm_control_item
{
	dsm_handle	handle;
	uint32		refcnt;			/* 2+ = active, 1 = moribund, 0 = gone */
	size_t		first_page;
	size_t		npages;
	void	   *impl_private_pm_handle; /* only needed on Windows */
	bool		pinned;
} dsm_control_item;

/* Layout of the dynamic shared memory control segment. */
/* (中文)DSM 控制段的整体布局:
 * - magic   : 魔数(PG_DYNSHMEM_CONTROL_MAGIC),识别"这是我们的控制段";
 * - nitems  : 当前已登记条目的个数(前 nitems 个槽位中 refcnt 为 0 的
 *             表示已释放的空槽);
 * - maxitems: 数组容量(启动时按 MaxBackends 算好,运行期不变);
 * - item[]  : 每段一个条目的柔性数组。 */
typedef struct dsm_control_header
{
	uint32		magic;
	uint32		nitems;
	uint32		maxitems;
	dsm_control_item item[FLEXIBLE_ARRAY_MEMBER];
} dsm_control_header;

static void dsm_cleanup_for_mmap(void);
static void dsm_postmaster_shutdown(int code, Datum arg);
static dsm_segment *dsm_create_descriptor(void);
static bool dsm_control_segment_sane(dsm_control_header *control,
									 Size mapped_size);
static uint64 dsm_control_bytes_needed(uint32 nitems);
/*
 * make_main_region_dsm_handle - (中文)为主区伪段生成句柄(恒为奇数)
 *
 * 【作用】为"从主共享内存区切出的伪段"构造句柄:置最低位 1(区别于
 * 平台层真实段的偶数句柄)、槽位号左移 1 位嵌入、其余高位用随机数
 * 填充。
 *
 * 【设计思想】随机高位降低"新段与刚销毁的段句柄雷同"导致跨生命期
 * 误认的概率;槽位号编码进句柄则保证同一槽位两次生命周期间句柄不同
 * (槽位号不同?此处主要用途是去重)。
 *
 * 【参数】slot —— 段在控制段里的槽位下标。
 * 【返回值】伪段句柄(奇数)。
 */
static inline dsm_handle
make_main_region_dsm_handle(int slot);
static inline bool is_main_region_dsm_handle(dsm_handle handle);

/* Has this backend initialized the dynamic shared memory system yet? */
/* (中文)本进程是否已完成 DSM 初始化(dsm_backend_startup):懒初始化
 * 标志,dsm_create/dsm_attach 首次调用时若为 false 会先补齐。 */
static bool dsm_init_done = false;

/* Preallocated DSM space in the main shared memory region. */
/* (中文)主共享内存区里预留的 DSM 空间(min_dynamic_shared_memory 配置
 * 决定大小,0 表示不预留):dsm_main_space_begin 是区域起点(同时兼作
 * FreePageManager 头的位置),dsm_main_space_size 是区域大小。 */
static void *dsm_main_space_begin = NULL;
static size_t dsm_main_space_size;

static void dsm_main_space_request(void *arg);
static void dsm_main_space_init(void *arg);

/* (中文)本文件向共享内存子系统登记的 request/init 回调:request 阶段
 * 按 min_dynamic_shared_memory 预留主区空间;init 阶段在其上初始化
 * FreePageManager(空闲页管理器)。 */
const ShmemCallbacks dsm_shmem_callbacks = {
	.request_fn = dsm_main_space_request,
	.init_fn = dsm_main_space_init,
};

/*
 * List of dynamic shared memory segments used by this backend.
 *
 * At process exit time, we must decrement the reference count of each
 * segment we have attached; this list makes it possible to find all such
 * segments.
 *
 * This list should always be empty in the postmaster.  We could probably
 * allow the postmaster to map dynamic shared memory segments before it
 * begins to start child processes, provided that each process adjusted
 * the reference counts for those segments in the control segment at
 * startup time, but there's no obvious need for such a facility, which
 * would also be complex to handle in the EXEC_BACKEND case.  Once the
 * postmaster has begun spawning children, there's an additional problem:
 * each new mapping would require an update to the control segment,
 * which requires locking, in which the postmaster must not be involved.
 */
/* (中文)本进程已附着的 DSM 段链表:进程退出(dsm_backend_shutdown)时
 * 逐段减引用计数。此表在 postmaster 中必须恒为空——postmaster 不应
 * 映射任何 DSM 段:映射控制段需要加锁,而 postmaster 必须避免参与
 * 这类锁(且 EXEC_BACKEND 下传递映射状态过于复杂)。 */
static dlist_head dsm_segment_list = DLIST_STATIC_INIT(dsm_segment_list);

/*
 * Control segment information.
 *
 * Unlike ordinary shared memory segments, the control segment is not
 * reference counted; instead, it lasts for the postmaster's entire
 * life cycle.  For simplicity, it doesn't have a dsm_segment object either.
 */
/* (中文)控制段的进程内全局状态:
 * - dsm_control_handle     : 控制段的句柄;
 * - dsm_control            : 控制段在本进程的映射地址(头部指针);
 * - dsm_control_mapped_size: 映射大小;
 * - dsm_control_impl_private:平台层私有数据。
 * 控制段不做引用计数、没有 dsm_segment 对象,活到 postmaster 整个
 * 生命周期;postmaster 关闭时由 dsm_postmaster_shutdown 销毁。 */
static dsm_handle dsm_control_handle;
static dsm_control_header *dsm_control;
static Size dsm_control_mapped_size = 0;
static void *dsm_control_impl_private = NULL;


/* ResourceOwner callbacks to hold DSM segments */
/* (中文)DSM 段的资源所有者(resowner)回调与描述:
 * 段映射默认登记到当前 ResourceOwner,资源释放时(resowner 释放的
 * "锁之前"阶段、RELEASE_PRIO_DSMS 优先级)调用 ResOwnerReleaseDSM
 * 完成 detach;DebugPrint 用于资源泄漏告警时的打印。 */
static void ResOwnerReleaseDSM(Datum res);
static char *ResOwnerPrintDSM(Datum res);

static const ResourceOwnerDesc dsm_resowner_desc =
{
	.name = "dynamic shared memory segment",
	.release_phase = RESOURCE_RELEASE_BEFORE_LOCKS,
	.release_priority = RELEASE_PRIO_DSMS,
	.ReleaseResource = ResOwnerReleaseDSM,
	.DebugPrint = ResOwnerPrintDSM
};

/* Convenience wrappers over ResourceOwnerRemember/Forget */
/* (中文)两个便捷包装:把"记住/忘记某个 DSM 段"包装成资源所有者的
 * 标准调用,统一携带 dsm_resowner_desc 描述。 */
static inline void
ResourceOwnerRememberDSM(ResourceOwner owner, dsm_segment *seg)
{
	ResourceOwnerRemember(owner, PointerGetDatum(seg), &dsm_resowner_desc);
}
static inline void
ResourceOwnerForgetDSM(ResourceOwner owner, dsm_segment *seg)
{
	ResourceOwnerForget(owner, PointerGetDatum(seg), &dsm_resowner_desc);
}

/*
 * Start up the dynamic shared memory system.
 *
 * This is called just once during each cluster lifetime, at postmaster
 * startup time.
 */
/*
 * dsm_postmaster_startup - (中文)postmaster 启动时初始化整个 DSM 系统(创建控制段)
 *
 * 【作用】每个集群生命周期只调用一次(postmaster 启动时,共享内存段
 * 已建好):1) mmap 实现下清理上次运行的残留文件(dsm_cleanup_for_mmap;
 * POSIX/SysV 的清理由调用方更早经 dsm_cleanup_using_control_segment
 * 完成);2) 按 MaxBackends 计算控制段槽位数并创建控制段(循环生成偶数
 * 句柄,避开 DSM_HANDLE_INVALID 哨兵值);3) 登记 on_shmem_exit 钩子
 * (dsm_postmaster_shutdown);4) 把控制段句柄写入 shim->dsm_control,
 * 供各进程/重启时找回。
 *
 * 【设计思想】控制段本身也是一个 DSM 段,但它不引用计数、伴随
 * postmaster 一生。句柄存在主共享内存段头里,是所有进程与"崩溃重启"
 * 都能找到它的唯一途径。句柄只用偶数:奇数为主区伪段预留(见
 * is_main_region_dsm_handle)。
 *
 * 【参数】shim —— 主共享内存段头(PGShmemHeader),控制段句柄将写入
 * 其 dsm_control 字段。
 * 【返回值】无。
 */
void
dsm_postmaster_startup(PGShmemHeader *shim)
{
	void	   *dsm_control_address = NULL;
	uint32		maxitems;
	Size		segsize;

	Assert(!IsUnderPostmaster);

	/*
	 * If we're using the mmap implementations, clean up any leftovers.
	 * Cleanup isn't needed on Windows, and happens earlier in startup for
	 * POSIX and System V shared memory, via a direct call to
	 * dsm_cleanup_using_control_segment.
	 */
	if (dynamic_shared_memory_type == DSM_IMPL_MMAP)
		dsm_cleanup_for_mmap();

	/* Determine size for new control segment. */
	maxitems = PG_DYNSHMEM_FIXED_SLOTS
		+ PG_DYNSHMEM_SLOTS_PER_BACKEND * MaxBackends;
	elog(DEBUG2, "dynamic shared memory system will support %u segments",
		 maxitems);
	segsize = dsm_control_bytes_needed(maxitems);

	/*
	 * Loop until we find an unused identifier for the new control segment. We
	 * sometimes use DSM_HANDLE_INVALID as a sentinel value indicating "no
	 * control segment", so avoid generating that value for a real handle.
	 */
	for (;;)
	{
		Assert(dsm_control_address == NULL);
		Assert(dsm_control_mapped_size == 0);
		/* Use even numbers only */
		dsm_control_handle = pg_prng_uint32(&pg_global_prng_state) << 1;
		if (dsm_control_handle == DSM_HANDLE_INVALID)
			continue;
		if (dsm_impl_op(DSM_OP_CREATE, dsm_control_handle, segsize,
						&dsm_control_impl_private, &dsm_control_address,
						&dsm_control_mapped_size, ERROR))
			break;
	}
	dsm_control = dsm_control_address;
	on_shmem_exit(dsm_postmaster_shutdown, PointerGetDatum(shim));
	elog(DEBUG2,
		 "created dynamic shared memory control segment %u (%zu bytes)",
		 dsm_control_handle, segsize);
	shim->dsm_control = dsm_control_handle;

	/* Initialize control segment. */
	dsm_control->magic = PG_DYNSHMEM_CONTROL_MAGIC;
	dsm_control->nitems = 0;
	dsm_control->maxitems = maxitems;
}

/*
 * Determine whether the control segment from the previous postmaster
 * invocation still exists.  If so, remove the dynamic shared memory
 * segments to which it refers, and then the control segment itself.
 */
/*
 * dsm_cleanup_using_control_segment - (中文)按"上次运行的控制段句柄"清理孤儿 DSM 段
 *
 * 【作用】postmaster 启动早期(或崩溃重启时)调用:尝试附着上次运行
 * 留下的控制段(句柄存于 pg_control);若附着失败(系统重启、段没了或
 * 标识被复用)静默返回;若附着成功但内容不合常理(dsm_control_segment_sane
 * 失败)则 detach 后返回;否则遍历其条目,销毁所有引用计数非零、且
 * 非主共享内存区的残留段,最后销毁旧控制段本身。
 *
 * 【设计思想】这是"硬崩溃后内存回收"的关键一步:崩溃时引用计数无法
 * 正常递减,残留段只能靠旧的元数据找回。整段流程对失败极其宽容——
 * 清理只是尽力而为,失败说明旧段本就不存在或不可信。主区伪段(奇数
 * 句柄)无需处理:主区随主共享内存段重建。
 *
 * 【参数】old_control_handle —— 上次运行的控制段句柄。
 * 【返回值】无。
 */
void
dsm_cleanup_using_control_segment(dsm_handle old_control_handle)
{
	void	   *mapped_address = NULL;
	void	   *junk_mapped_address = NULL;
	void	   *impl_private = NULL;
	void	   *junk_impl_private = NULL;
	Size		mapped_size = 0;
	Size		junk_mapped_size = 0;
	uint32		nitems;
	uint32		i;
	dsm_control_header *old_control;

	/*
	 * Try to attach the segment.  If this fails, it probably just means that
	 * the operating system has been rebooted and the segment no longer
	 * exists, or an unrelated process has used the same shm ID.  So just fall
	 * out quietly.
	 */
	if (!dsm_impl_op(DSM_OP_ATTACH, old_control_handle, 0, &impl_private,
					 &mapped_address, &mapped_size, DEBUG1))
		return;

	/*
	 * We've managed to reattach it, but the contents might not be sane. If
	 * they aren't, we disregard the segment after all.
	 */
	old_control = (dsm_control_header *) mapped_address;
	if (!dsm_control_segment_sane(old_control, mapped_size))
	{
		dsm_impl_op(DSM_OP_DETACH, old_control_handle, 0, &impl_private,
					&mapped_address, &mapped_size, LOG);
		return;
	}

	/*
	 * OK, the control segment looks basically valid, so we can use it to get
	 * a list of segments that need to be removed.
	 */
	nitems = old_control->nitems;
	for (i = 0; i < nitems; ++i)
	{
		dsm_handle	handle;
		uint32		refcnt;

		/* If the reference count is 0, the slot is actually unused. */
		refcnt = old_control->item[i].refcnt;
		if (refcnt == 0)
			continue;

		/* If it was using the main shmem area, there is nothing to do. */
		handle = old_control->item[i].handle;
		if (is_main_region_dsm_handle(handle))
			continue;

		/* Log debugging information. */
		elog(DEBUG2, "cleaning up orphaned dynamic shared memory with ID %u (reference count %u)",
			 handle, refcnt);

		/* Destroy the referenced segment. */
		dsm_impl_op(DSM_OP_DESTROY, handle, 0, &junk_impl_private,
					&junk_mapped_address, &junk_mapped_size, LOG);
	}

	/* Destroy the old control segment, too. */
	elog(DEBUG2,
		 "cleaning up dynamic shared memory control segment with ID %u",
		 old_control_handle);
	dsm_impl_op(DSM_OP_DESTROY, old_control_handle, 0, &impl_private,
				&mapped_address, &mapped_size, LOG);
}

/*
 * When we're using the mmap shared memory implementation, "shared memory"
 * segments might even manage to survive an operating system reboot.
 * But there's no guarantee as to exactly what will survive: some segments
 * may survive, and others may not, and the contents of some may be out
 * of date.  In particular, the control segment may be out of date, so we
 * can't rely on it to figure out what to remove.  However, since we know
 * what directory contains the files we used as shared memory, we can simply
 * scan the directory and blow everything away that shouldn't be there.
 */
/*
 * dsm_cleanup_for_mmap - (中文)mmap 实现下的启动清理:扫目录删掉所有 DSM 文件
 *
 * 【作用】启动时扫描 PG_DYNSHMEM_DIR 目录,删除所有文件名以
 * PG_DYNSHMEM_MMAP_FILE_PREFIX 开头的文件。
 *
 * 【设计思想】mmap 实现的"共享内存"是普通文件,可能比控制段活得久、
 * 也可能内容过时——所以不能信任旧控制段,干脆按命名规则清空整个
 * 目录。先决条件:文件名规则唯一标识 DSM 文件,不可能误删用户文件。
 *
 * 【参数】无。
 * 【返回值】无(删除失败则 ERROR)。
 */
static void
dsm_cleanup_for_mmap(void)
{
	DIR		   *dir;
	struct dirent *dent;

	/* Scan the directory for something with a name of the correct format. */
	dir = AllocateDir(PG_DYNSHMEM_DIR);

	while ((dent = ReadDir(dir, PG_DYNSHMEM_DIR)) != NULL)
	{
		if (strncmp(dent->d_name, PG_DYNSHMEM_MMAP_FILE_PREFIX,
					strlen(PG_DYNSHMEM_MMAP_FILE_PREFIX)) == 0)
		{
			char		buf[MAXPGPATH + sizeof(PG_DYNSHMEM_DIR)];

			snprintf(buf, sizeof(buf), PG_DYNSHMEM_DIR "/%s", dent->d_name);

			elog(DEBUG2, "removing file \"%s\"", buf);

			/* We found a matching file; so remove it. */
			if (unlink(buf) != 0)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not remove file \"%s\": %m", buf)));
		}
	}

	/* Cleanup complete. */
	FreeDir(dir);
}

/*
 * At shutdown time, we iterate over the control segment and remove all
 * remaining dynamic shared memory segments.  We avoid throwing errors here;
 * the postmaster is shutting down either way, and this is just non-critical
 * resource cleanup.
 */
/*
 * dsm_postmaster_shutdown - (中文)postmaster 关闭时的 DSM 兜底清理(on_shmem_exit 钩子)
 *
 * 【作用】postmaster 关闭流程中执行:若控制段内容不合常理(某个后端
 * 异常退出可能写坏了它)仅告警并放弃——元数据已失,残留段只能遗留;
 * 否则遍历全部条目,销毁引用计数非零的残留段(跳过主区伪段),最后
 * 销毁控制段本身,并把 shim->dsm_control 清零。
 *
 * 【设计思想】这是最后的"垃圾回收"网:正常运行时引用计数机制已销毁
 * 绝大多数段,这里只处理"所有引用者都已消失却因异常没走销毁流程"
 * 的残局。全程避免抛错(用 LOG/WARNING 级别),因为 postmaster 反正
 * 要关,清理失败不应再添乱。
 *
 * 【参数】
 *   code —— 退出码(on_shmem_exit 约定,未使用);
 *   arg  —— 注册时传入的主共享内存段头指针(PGShmemHeader)。
 * 【返回值】无。
 */
static void
dsm_postmaster_shutdown(int code, Datum arg)
{
	uint32		nitems;
	uint32		i;
	void	   *dsm_control_address;
	void	   *junk_mapped_address = NULL;
	void	   *junk_impl_private = NULL;
	Size		junk_mapped_size = 0;
	PGShmemHeader *shim = (PGShmemHeader *) DatumGetPointer(arg);

	/*
	 * If some other backend exited uncleanly, it might have corrupted the
	 * control segment while it was dying.  In that case, we warn and ignore
	 * the contents of the control segment.  This may end up leaving behind
	 * stray shared memory segments, but there's not much we can do about that
	 * if the metadata is gone.
	 */
	nitems = dsm_control->nitems;
	if (!dsm_control_segment_sane(dsm_control, dsm_control_mapped_size))
	{
		ereport(LOG,
				(errmsg("dynamic shared memory control segment is corrupt")));
		return;
	}

	/* Remove any remaining segments. */
	for (i = 0; i < nitems; ++i)
	{
		dsm_handle	handle;

		/* If the reference count is 0, the slot is actually unused. */
		if (dsm_control->item[i].refcnt == 0)
			continue;

		handle = dsm_control->item[i].handle;
		if (is_main_region_dsm_handle(handle))
			continue;

		/* Log debugging information. */
		elog(DEBUG2, "cleaning up orphaned dynamic shared memory with ID %u",
			 handle);

		/* Destroy the segment. */
		dsm_impl_op(DSM_OP_DESTROY, handle, 0, &junk_impl_private,
					&junk_mapped_address, &junk_mapped_size, LOG);
	}

	/* Remove the control segment itself. */
	elog(DEBUG2,
		 "cleaning up dynamic shared memory control segment with ID %u",
		 dsm_control_handle);
	dsm_control_address = dsm_control;
	dsm_impl_op(DSM_OP_DESTROY, dsm_control_handle, 0,
				&dsm_control_impl_private, &dsm_control_address,
				&dsm_control_mapped_size, LOG);
	dsm_control = dsm_control_address;
	shim->dsm_control = 0;
}

/*
 * Prepare this backend for dynamic shared memory usage.  Under EXEC_BACKEND,
 * we must reread the state file and map the control segment; in other cases,
 * we'll have inherited the postmaster's mapping and global variables.
 */
/*
 * dsm_backend_startup - (中文)本进程首次使用 DSM 前的懒初始化
 *
 * 【作用】把 dsm_init_done 置 true(此后本进程的 DSM 基础设施可用)。
 * EXEC_BACKEND 模式下还会:附着控制段(句柄来自段头,经
 * dsm_set_control_handle 传递)、做健全性检查,不合法则 FATAL(说明
 * 系统状态严重损坏)。
 *
 * 【设计思想】普通 Unix 进程经 fork() 继承了 postmaster 的控制段映射
 * 与全部全局变量,无需任何操作,只置标志即可;EXEC_BACKEND 必须自己
 * 重建映射。懒初始化让 dsm_create/dsm_attach 不必要求调用方先做
 * 显式准备。
 *
 * 【参数】无。
 * 【返回值】无(失败即 ERROR/FATAL)。
 */
static void
dsm_backend_startup(void)
{
#ifdef EXEC_BACKEND
	if (IsUnderPostmaster)
	{
		void	   *control_address = NULL;

		/* Attach control segment. */
		Assert(dsm_control_handle != 0);
		dsm_impl_op(DSM_OP_ATTACH, dsm_control_handle, 0,
					&dsm_control_impl_private, &control_address,
					&dsm_control_mapped_size, ERROR);
		dsm_control = control_address;
		/* If control segment doesn't look sane, something is badly wrong. */
		if (!dsm_control_segment_sane(dsm_control, dsm_control_mapped_size))
		{
			dsm_impl_op(DSM_OP_DETACH, dsm_control_handle, 0,
						&dsm_control_impl_private, &control_address,
						&dsm_control_mapped_size, WARNING);
			ereport(FATAL,
					(errcode(ERRCODE_INTERNAL_ERROR),
					 errmsg("dynamic shared memory control segment is not valid")));
		}
	}
#endif

	dsm_init_done = true;
}

#ifdef EXEC_BACKEND
/*
 * When running under EXEC_BACKEND, we get a callback here when the main
 * shared memory segment is re-attached, so that we can record the control
 * handle retrieved from it.
 */
/*
 * dsm_set_control_handle - (中文)(EXEC_BACKEND)子进程从主共享内存段头取回控制段句柄
 *
 * 【作用】EXEC_BACKEND 模式下,子进程重新附着主共享内存段后,把段头
 * 里的 dsm_control 字段(控制段句柄)记录进本进程的
 * dsm_control_handle,供 dsm_backend_startup 附着控制段使用。
 *
 * 【参数】h —— 控制段句柄(非 0)。
 * 【返回值】无。
 */
void
dsm_set_control_handle(dsm_handle h)
{
	Assert(dsm_control_handle == 0 && h != 0);
	dsm_control_handle = h;
}
#endif

/*
 * Reserve space in the main shared memory segment for DSM segments.
 */
/*
 * dsm_main_space_request - (中文)登记"主共享内存区 DSM 空间"的需求(request 阶段)
 *
 * 【作用】request 回调:把 min_dynamic_shared_memory(MB)换算成字节,
 * 用 ShmemRequestStruct 向共享内存子系统登记一块名为 "Preallocated
 * DSM" 的区域,指针槽指向 dsm_main_space_begin。配置为 0 时不登记。
 *
 * 【设计思想】通过标准的共享内存回调机制预留空间,使 CreateShared
 * MemoryAndSemaphores 的总大小计算自动涵盖它,无需手工维护。
 *
 * 【参数】arg —— 回调 opaque 参数(未使用)。
 * 【返回值】无。
 */
static void
dsm_main_space_request(void *arg)
{
	dsm_main_space_size = 1024 * 1024 * (size_t) min_dynamic_shared_memory;

	if (dsm_main_space_size == 0)
		return;

	ShmemRequestStruct(.name = "Preallocated DSM",
					   .size = dsm_main_space_size,
					   .ptr = &dsm_main_space_begin,
		);
}

/*
 * dsm_main_space_init - (中文)初始化主区 DSM 空间(init 阶段)
 *
 * 【作用】在预留区域起点建立 FreePageManager(空闲页管理器):区域头
 * 几页留给 FreePageManager 自身结构,其余全部作为空闲页交给它管理,
 * 之后 dsm_create 即可从中切页(见 dsm_create 的"主区伪段"路径)。
 *
 * 【设计思想】"一页一页切"而非"整个区域一块用",使多个并发请求
 * 能共享主区空间,也允许段销毁后(FreePageManagerPut)空间复用。
 * 配置为 0 时直接返回。
 *
 * 【参数】arg —— 回调 opaque 参数(未使用)。
 * 【返回值】无。
 */
static void
dsm_main_space_init(void *arg)
{
	FreePageManager *fpm = (FreePageManager *) dsm_main_space_begin;
	size_t		first_page = 0;
	size_t		pages;

	if (dsm_main_space_size == 0)
		return;

	/* Reserve space for the FreePageManager. */
	while (first_page * FPM_PAGE_SIZE < sizeof(FreePageManager))
		++first_page;

	/* Initialize it and give it all the rest of the space. */
	FreePageManagerInitialize(fpm, dsm_main_space_begin);
	pages = (dsm_main_space_size / FPM_PAGE_SIZE) - first_page;
	FreePageManagerPut(fpm, first_page, pages);
}

/*
 * Create a new dynamic shared memory segment.
 *
 * If there is a non-NULL CurrentResourceOwner, the new segment is associated
 * with it and must be detached before the resource owner releases, or a
 * warning will be logged.  If CurrentResourceOwner is NULL, the segment
 * remains attached until explicitly detached or the session ends.
 * Creating with a NULL CurrentResourceOwner is equivalent to creating
 * with a non-NULL CurrentResourceOwner and then calling dsm_pin_mapping.
 */
/*
 * dsm_create - (中文)创建一个新的动态共享内存段
 *
 * 【作用】完整创建一个段:1) 懒初始化(需要时);2) 建描述符;3) 若
 * 配置了主区,优先在持 DynamicSharedMemoryControlLock 独占锁的情况下
 * 从 FreePageManager 切页,成为"主区伪段"(handle 为奇数);主区不够
 * 或未配置时,循环生成偶数句柄交给平台层创建真实段;4) 在控制段里
 * 找一个空闲槽位登记(复用空槽或追加新槽),refcnt 从 2 起步(1 个
 * 创建者 + 1 个 pin 保护位,见文件头协议);5) 槽位用尽时:归还主区
 * 页/销毁已建段/回收描述符,按 flags 返回 NULL 或报错。
 *
 * 【设计思想】整个过程在 DynamicSharedMemoryControlLock 独占锁保护下
 * 完成(主区切页与槽位登记是同一临界区),保证"段 + 槽位"的原子性。
 * 持锁期间的平台层操作(DSM_OP_CREATE)在无主区路径时会被暂时释放锁
 * 规避长等待。创建的段自动挂在当前 ResourceOwner 下(或 NULL 即
 * 会话级,等价于 dsm_pin_mapping)。
 *
 * 【参数】
 *   size  —— 段大小(字节);
 *   flags —— DSM_CREATE_NULL_IF_MAXSEGMENTS:槽位耗尽时返回 NULL
 *            而非报错。
 * 【返回值】段描述符;槽位耗尽且带 NULL_IF 标志时返回 NULL。
 */
dsm_segment *
dsm_create(Size size, int flags)
{
	dsm_segment *seg;
	uint32		i;
	uint32		nitems;
	size_t		npages = 0;
	size_t		first_page = 0;
	FreePageManager *dsm_main_space_fpm = dsm_main_space_begin;
	bool		using_main_dsm_region = false;

	/*
	 * Unsafe in postmaster. It might seem pointless to allow use of dsm in
	 * single user mode, but otherwise some subsystems will need dedicated
	 * single user mode code paths.
	 */
	Assert(IsUnderPostmaster || !IsPostmasterEnvironment);

	if (!dsm_init_done)
		dsm_backend_startup();

	/* Create a new segment descriptor. */
	seg = dsm_create_descriptor();

	/*
	 * Lock the control segment while we try to allocate from the main shared
	 * memory area, if configured.
	 */
	if (dsm_main_space_fpm)
	{
		npages = size / FPM_PAGE_SIZE;
		if (size % FPM_PAGE_SIZE > 0)
			++npages;

		LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
		if (FreePageManagerGet(dsm_main_space_fpm, npages, &first_page))
		{
			/* We can carve out a piece of the main shared memory segment. */
			seg->mapped_address = (char *) dsm_main_space_begin +
				first_page * FPM_PAGE_SIZE;
			seg->mapped_size = npages * FPM_PAGE_SIZE;
			using_main_dsm_region = true;
			/* We'll choose a handle below. */
		}
	}

	if (!using_main_dsm_region)
	{
		/*
		 * We need to create a new memory segment.  Loop until we find an
		 * unused segment identifier.
		 */
		if (dsm_main_space_fpm)
			LWLockRelease(DynamicSharedMemoryControlLock);
		for (;;)
		{
			Assert(seg->mapped_address == NULL && seg->mapped_size == 0);
			/* Use even numbers only */
			seg->handle = pg_prng_uint32(&pg_global_prng_state) << 1;
			if (seg->handle == DSM_HANDLE_INVALID)	/* Reserve sentinel */
				continue;
			if (dsm_impl_op(DSM_OP_CREATE, seg->handle, size, &seg->impl_private,
							&seg->mapped_address, &seg->mapped_size, ERROR))
				break;
		}
		LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
	}

	/* Search the control segment for an unused slot. */
	nitems = dsm_control->nitems;
	for (i = 0; i < nitems; ++i)
	{
		if (dsm_control->item[i].refcnt == 0)
		{
			if (using_main_dsm_region)
			{
				seg->handle = make_main_region_dsm_handle(i);
				dsm_control->item[i].first_page = first_page;
				dsm_control->item[i].npages = npages;
			}
			else
				Assert(!is_main_region_dsm_handle(seg->handle));
			dsm_control->item[i].handle = seg->handle;
			/* refcnt of 1 triggers destruction, so start at 2 */
			dsm_control->item[i].refcnt = 2;
			dsm_control->item[i].impl_private_pm_handle = NULL;
			dsm_control->item[i].pinned = false;
			seg->control_slot = i;
			LWLockRelease(DynamicSharedMemoryControlLock);
			return seg;
		}
	}

	/* Verify that we can support an additional mapping. */
	if (nitems >= dsm_control->maxitems)
	{
		if (using_main_dsm_region)
			FreePageManagerPut(dsm_main_space_fpm, first_page, npages);
		LWLockRelease(DynamicSharedMemoryControlLock);
		if (!using_main_dsm_region)
			dsm_impl_op(DSM_OP_DESTROY, seg->handle, 0, &seg->impl_private,
						&seg->mapped_address, &seg->mapped_size, WARNING);
		if (seg->resowner != NULL)
			ResourceOwnerForgetDSM(seg->resowner, seg);
		dlist_delete(&seg->node);
		pfree(seg);

		if ((flags & DSM_CREATE_NULL_IF_MAXSEGMENTS) != 0)
			return NULL;
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_RESOURCES),
				 errmsg("too many dynamic shared memory segments")));
	}

	/* Enter the handle into a new array slot. */
	if (using_main_dsm_region)
	{
		seg->handle = make_main_region_dsm_handle(nitems);
		dsm_control->item[i].first_page = first_page;
		dsm_control->item[i].npages = npages;
	}
	dsm_control->item[nitems].handle = seg->handle;
	/* refcnt of 1 triggers destruction, so start at 2 */
	dsm_control->item[nitems].refcnt = 2;
	dsm_control->item[nitems].impl_private_pm_handle = NULL;
	dsm_control->item[nitems].pinned = false;
	seg->control_slot = nitems;
	dsm_control->nitems++;
	LWLockRelease(DynamicSharedMemoryControlLock);

	return seg;
}

/*
 * Attach a dynamic shared memory segment.
 *
 * See comments for dsm_segment_handle() for an explanation of how this
 * is intended to be used.
 *
 * This function will return NULL if the segment isn't known to the system.
 * This can happen if we're asked to attach the segment, but then everyone
 * else detaches it (causing it to be destroyed) before we get around to
 * attaching it.
 *
 * If there is a non-NULL CurrentResourceOwner, the attached segment is
 * associated with it and must be detached before the resource owner releases,
 * or a warning will be logged.  Otherwise the segment remains attached until
 * explicitly detached or the session ends.  See the note atop dsm_create().
 */
/*
 * dsm_attach - (中文)按句柄附着(映射)一个已存在的动态共享内存段
 *
 * 【作用】1) 懒初始化;2) 断言本进程未重复附着同一句柄(调试交叉
 * 检查,命中说明应先试 dsm_find_mapping);3) 建描述符;4) 在持锁
 * 情况下遍历控制段找句柄匹配的槽:refcnt <= 1 的槽跳过(0 空闲、1
 * 濒死且句柄可能已被复用),找到则 refcnt++ 并记录槽位;主区伪段
 * 直接由槽位里的 first_page/npages 算出地址;5) 没找到(段已被销毁)
 * 则 detach 描述符、返回 NULL;6) 真实段交给平台层 DSM_OP_ATTACH
 * 完成映射。
 *
 * 【设计思想】"先加引用计数、再真正映射"的顺序保证:加引用计数后
 * 即使其他进程全部退出,段也会因我们的引用而存活到我们完成映射。
 * 每进程同一段只映射一次的约定(dsm_segment_list 维护)简化了
 * 引用计数与清理逻辑。
 *
 * 【参数】h —— 段句柄(经 dsm_segment_handle 从创建者那里获得)。
 * 【返回值】段描述符(已映射);段已不存在时返回 NULL。
 */
dsm_segment *
dsm_attach(dsm_handle h)
{
	dsm_segment *seg;
	dlist_iter	iter;
	uint32		i;
	uint32		nitems;

	/* Unsafe in postmaster (and pointless in a stand-alone backend). */
	Assert(IsUnderPostmaster);

	if (!dsm_init_done)
		dsm_backend_startup();

	/*
	 * Since this is just a debugging cross-check, we could leave it out
	 * altogether, or include it only in assert-enabled builds.  But since the
	 * list of attached segments should normally be very short, let's include
	 * it always for right now.
	 *
	 * If you're hitting this error, you probably want to attempt to find an
	 * existing mapping via dsm_find_mapping() before calling dsm_attach() to
	 * create a new one.
	 */
	dlist_foreach(iter, &dsm_segment_list)
	{
		seg = dlist_container(dsm_segment, node, iter.cur);
		if (seg->handle == h)
			elog(ERROR, "can't attach the same segment more than once");
	}

	/* Create a new segment descriptor. */
	seg = dsm_create_descriptor();
	seg->handle = h;

	/* Bump reference count for this segment in shared memory. */
	LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
	nitems = dsm_control->nitems;
	for (i = 0; i < nitems; ++i)
	{
		/*
		 * If the reference count is 0, the slot is actually unused.  If the
		 * reference count is 1, the slot is still in use, but the segment is
		 * in the process of going away; even if the handle matches, another
		 * slot may already have started using the same handle value by
		 * coincidence so we have to keep searching.
		 */
		if (dsm_control->item[i].refcnt <= 1)
			continue;

		/* If the handle doesn't match, it's not the slot we want. */
		if (dsm_control->item[i].handle != seg->handle)
			continue;

		/* Otherwise we've found a match. */
		dsm_control->item[i].refcnt++;
		seg->control_slot = i;
		if (is_main_region_dsm_handle(seg->handle))
		{
			seg->mapped_address = (char *) dsm_main_space_begin +
				dsm_control->item[i].first_page * FPM_PAGE_SIZE;
			seg->mapped_size = dsm_control->item[i].npages * FPM_PAGE_SIZE;
		}
		break;
	}
	LWLockRelease(DynamicSharedMemoryControlLock);

	/*
	 * If we didn't find the handle we're looking for in the control segment,
	 * it probably means that everyone else who had it mapped, including the
	 * original creator, died before we got to this point. It's up to the
	 * caller to decide what to do about that.
	 */
	if (seg->control_slot == INVALID_CONTROL_SLOT)
	{
		dsm_detach(seg);
		return NULL;
	}

	/* Here's where we actually try to map the segment. */
	if (!is_main_region_dsm_handle(seg->handle))
		dsm_impl_op(DSM_OP_ATTACH, seg->handle, 0, &seg->impl_private,
					&seg->mapped_address, &seg->mapped_size, ERROR);

	return seg;
}

/*
 * At backend shutdown time, detach any segments that are still attached.
 * (This is similar to dsm_detach_all, except that there's no reason to
 * unmap the control segment before exiting, so we don't bother.)
 */
/*
 * dsm_backend_shutdown - (中文)后端退出时 detach 所有仍附着的段
 *
 * 【作用】shmem_exit() 流程中调用(见 ipc.c):循环 detach 本进程
 * 链表上的所有段,把引用计数全部归还。
 *
 * 【设计思想】与 dsm_detach_all 类似,但没必要在退出前拆除控制段
 * 映射(进程反正要结束,OS 会回收),因此只处理业务段。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
dsm_backend_shutdown(void)
{
	while (!dlist_is_empty(&dsm_segment_list))
	{
		dsm_segment *seg;

		seg = dlist_head_element(dsm_segment, node, &dsm_segment_list);
		dsm_detach(seg);
	}
}

/*
 * Detach all shared memory segments, including the control segments.  This
 * should be called, along with PGSharedMemoryDetach, in processes that
 * might inherit mappings but are not intended to be connected to dynamic
 * shared memory.
 */
/*
 * dsm_detach_all - (中文)detach 全部段,包括控制段本身
 *
 * 【作用】先 detach 链表上所有业务段,再对控制段执行平台层
 * DSM_OP_DETACH(拆除控制段映射)。与 PGSharedMemoryDetach 配套,
 * 供"继承了映射但不该连到 DSM"的进程(如某些启动早期的子进程)
 * 使用。
 *
 * 【设计思想】彻底切断本进程与 DSM 系统的全部关联;控制段不引用
 * 计数,detach 只是解除本进程的映射,段本身仍由 postmaster 持有。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
dsm_detach_all(void)
{
	void	   *control_address = dsm_control;

	while (!dlist_is_empty(&dsm_segment_list))
	{
		dsm_segment *seg;

		seg = dlist_head_element(dsm_segment, node, &dsm_segment_list);
		dsm_detach(seg);
	}

	if (control_address != NULL)
		dsm_impl_op(DSM_OP_DETACH, dsm_control_handle, 0,
					&dsm_control_impl_private, &control_address,
					&dsm_control_mapped_size, ERROR);
}

/*
 * Detach from a shared memory segment, destroying the segment if we
 * remove the last reference.
 *
 * This function should never fail.  It will often be invoked when aborting
 * a transaction, and a further error won't serve any purpose.  It's not a
 * complete disaster if we fail to unmap or destroy the segment; it means a
 * resource leak, but that doesn't necessarily preclude further operations.
 */
/*
 * dsm_detach - (中文)解除与一个段的关联;若这是最后一个引用则销毁段
 *
 * 【作用】1) 在 HOLD_INTERRUPTS 保护下逐个弹出并执行 on-detach 回调
 * (先摘除再执行,回调再抛错也不会死循环);2) 若有映射,先解除平台层
 * 映射(主区伪段无需平台操作)——必须"先拆映射、后减计数",保证"看到
 * 计数归 1 的进程"可以断定再无残留映射;3) 在锁内把控制段槽位
 * refcnt 减 1,减到 1 说明自己是最后一个引用者:负责销毁段(主区伪段
 * 归还 FreePageManager 页面;真实段 DSM_OP_DESTROY),成功后把槽位
 * refcnt 清零(空槽,可复用);4) 从资源所有者与链表摘除描述符并释放。
 *
 * 【设计思想】"永不失败"原则:本函数常在事务 abort 路径上被调用,再
 * 抛错毫无意义;平台操作失败用 WARNING 容忍(最坏是资源泄漏)。销毁
 * 途中被信号杀死时,槽位停留在 refcnt=1,由 postmaster 关闭或下次
 * 启动清理(原注释详述)。pinned 段断言"不会自然到达 1",因为 pin 的
 * 引用计数 +1 保证了这点。
 *
 * 【参数】seg —— 要 detach 的段描述符。
 * 【返回值】无。
 */
void
dsm_detach(dsm_segment *seg)
{
	/*
	 * Invoke registered callbacks.  Just in case one of those callbacks
	 * throws a further error that brings us back here, pop the callback
	 * before invoking it, to avoid infinite error recursion.  Don't allow
	 * interrupts while running the individual callbacks in non-error code
	 * paths, to avoid leaving cleanup work unfinished if we're interrupted by
	 * a statement timeout or similar.
	 */
	HOLD_INTERRUPTS();
	while (!slist_is_empty(&seg->on_detach))
	{
		slist_node *node;
		dsm_segment_detach_callback *cb;
		on_dsm_detach_callback function;
		Datum		arg;

		node = slist_pop_head_node(&seg->on_detach);
		cb = slist_container(dsm_segment_detach_callback, node, node);
		function = cb->function;
		arg = cb->arg;
		pfree(cb);

		function(seg, arg);
	}
	RESUME_INTERRUPTS();

	/*
	 * Try to remove the mapping, if one exists.  Normally, there will be, but
	 * maybe not, if we failed partway through a create or attach operation.
	 * We remove the mapping before decrementing the reference count so that
	 * the process that sees a zero reference count can be certain that no
	 * remaining mappings exist.  Even if this fails, we pretend that it
	 * works, because retrying is likely to fail in the same way.
	 */
	if (seg->mapped_address != NULL)
	{
		if (!is_main_region_dsm_handle(seg->handle))
			dsm_impl_op(DSM_OP_DETACH, seg->handle, 0, &seg->impl_private,
						&seg->mapped_address, &seg->mapped_size, WARNING);
		seg->impl_private = NULL;
		seg->mapped_address = NULL;
		seg->mapped_size = 0;
	}

	/* Reduce reference count, if we previously increased it. */
	if (seg->control_slot != INVALID_CONTROL_SLOT)
	{
		uint32		refcnt;
		uint32		control_slot = seg->control_slot;

		LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
		Assert(dsm_control->item[control_slot].handle == seg->handle);
		Assert(dsm_control->item[control_slot].refcnt > 1);
		refcnt = --dsm_control->item[control_slot].refcnt;
		seg->control_slot = INVALID_CONTROL_SLOT;
		LWLockRelease(DynamicSharedMemoryControlLock);

		/* If new reference count is 1, try to destroy the segment. */
		if (refcnt == 1)
		{
			/* A pinned segment should never reach 1. */
			Assert(!dsm_control->item[control_slot].pinned);

			/*
			 * If we fail to destroy the segment here, or are killed before we
			 * finish doing so, the reference count will remain at 1, which
			 * will mean that nobody else can attach to the segment.  At
			 * postmaster shutdown time, or when a new postmaster is started
			 * after a hard kill, another attempt will be made to remove the
			 * segment.
			 *
			 * The main case we're worried about here is being killed by a
			 * signal before we can finish removing the segment.  In that
			 * case, it's important to be sure that the segment still gets
			 * removed. If we actually fail to remove the segment for some
			 * other reason, the postmaster may not have any better luck than
			 * we did.  There's not much we can do about that, though.
			 */
			if (is_main_region_dsm_handle(seg->handle) ||
				dsm_impl_op(DSM_OP_DESTROY, seg->handle, 0, &seg->impl_private,
							&seg->mapped_address, &seg->mapped_size, WARNING))
			{
				LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
				if (is_main_region_dsm_handle(seg->handle))
					FreePageManagerPut((FreePageManager *) dsm_main_space_begin,
									   dsm_control->item[control_slot].first_page,
									   dsm_control->item[control_slot].npages);
				Assert(dsm_control->item[control_slot].handle == seg->handle);
				Assert(dsm_control->item[control_slot].refcnt == 1);
				dsm_control->item[control_slot].refcnt = 0;
				LWLockRelease(DynamicSharedMemoryControlLock);
			}
		}
	}

	/* Clean up our remaining backend-private data structures. */
	if (seg->resowner != NULL)
		ResourceOwnerForgetDSM(seg->resowner, seg);
	dlist_delete(&seg->node);
	pfree(seg);
}

/*
 * Keep a dynamic shared memory mapping until end of session.
 *
 * By default, mappings are owned by the current resource owner, which
 * typically means they stick around for the duration of the current query
 * only.
 */
/*
 * dsm_pin_mapping - (中文)把段的映射"钉"到会话级(不再随资源所有者释放)
 *
 * 【作用】从当前资源所有者的登记中摘除该段(resowner 置 NULL),此后
 * 映射不再随查询/事务结束而自动 detach,一直保留到显式
 * dsm_unpin_mapping 或进程结束。
 *
 * 【设计思想】默认映射挂 ResourceOwner(通常活一个查询);需要跨
 * 查询存活(如并行 worker 之间反复使用)时调用本函数。
 *
 * 【参数】seg —— 段描述符。
 * 【返回值】无。
 */
void
dsm_pin_mapping(dsm_segment *seg)
{
	if (seg->resowner != NULL)
	{
		ResourceOwnerForgetDSM(seg->resowner, seg);
		seg->resowner = NULL;
	}
}

/*
 * Arrange to remove a dynamic shared memory mapping at cleanup time.
 *
 * dsm_pin_mapping() can be used to preserve a mapping for the entire
 * lifetime of a process; this function reverses that decision, making
 * the segment owned by the current resource owner.  This may be useful
 * just before performing some operation that will invalidate the segment
 * for future use by this backend.
 */
/*
 * dsm_unpin_mapping - (中文)撤销 dsm_pin_mapping:让映射重新归当前资源所有者管理
 *
 * 【作用】把段重新登记到 CurrentResourceOwner(先扩容以防登记失败)。
 * 适合"即将做使段对本后端失效的操作"之前调用,让清理有兜底。
 *
 * 【设计思想】与 dsm_pin_mapping 互为逆操作;断言 resowner 为 NULL
 * 保证不会重复登记。
 *
 * 【参数】seg —— 段描述符。
 * 【返回值】无。
 */
void
dsm_unpin_mapping(dsm_segment *seg)
{
	Assert(seg->resowner == NULL);
	ResourceOwnerEnlarge(CurrentResourceOwner);
	seg->resowner = CurrentResourceOwner;
	ResourceOwnerRememberDSM(seg->resowner, seg);
}

/*
 * Keep a dynamic shared memory segment until postmaster shutdown, or until
 * dsm_unpin_segment is called.
 *
 * This function should not be called more than once per segment, unless the
 * segment is explicitly unpinned with dsm_unpin_segment in between calls.
 *
 * Note that this function does not arrange for the current process to
 * keep the segment mapped indefinitely; if that behavior is desired,
 * dsm_pin_mapping() should be used from each process that needs to
 * retain the mapping.
 */
/*
 * dsm_pin_segment - (中文)把段"钉"到 postmaster 关闭为止(跨进程级别,引用计数 +1)
 *
 * 【作用】给控制段里该槽位的引用计数 +1 并置 pinned 标志(已 pin 的
 * 段再 pin 报错);真实段还调用平台层 dsm_impl_pin_segment 把"段句柄"
 * 升级保存(Windows 需要,handle 存入槽位的 impl_private_pm_handle)。
 *
 * 【设计思想】普通引用计数随附着者消亡而归零并销毁段;pin 的 +1 让
 * 计数在任何时候都 >= 2,因此"所有进程都 detach 后段依然存活"——
 * 直到显式 dsm_unpin_segment 或 postmaster 关闭。注意 pin 只管"段
 * 本身"的存活,不保证任何进程还映射着它;需要映射保留请用
 * dsm_pin_mapping。
 *
 * 【参数】seg —— 段描述符。
 * 【返回值】无。
 */
void
dsm_pin_segment(dsm_segment *seg)
{
	void	   *handle = NULL;

	/*
	 * Bump reference count for this segment in shared memory. This will
	 * ensure that even if there is no session which is attached to this
	 * segment, it will remain until postmaster shutdown or an explicit call
	 * to unpin.
	 */
	LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
	if (dsm_control->item[seg->control_slot].pinned)
		elog(ERROR, "cannot pin a segment that is already pinned");
	if (!is_main_region_dsm_handle(seg->handle))
		dsm_impl_pin_segment(seg->handle, seg->impl_private, &handle);
	dsm_control->item[seg->control_slot].pinned = true;
	dsm_control->item[seg->control_slot].refcnt++;
	dsm_control->item[seg->control_slot].impl_private_pm_handle = handle;
	LWLockRelease(DynamicSharedMemoryControlLock);
}

/*
 * Unpin a dynamic shared memory segment that was previously pinned with
 * dsm_pin_segment.  This function should not be called unless dsm_pin_segment
 * was previously called for this segment.
 *
 * The argument is a dsm_handle rather than a dsm_segment in case you want
 * to unpin a segment to which you haven't attached.  This turns out to be
 * useful if, for example, a reference to one shared memory segment is stored
 * within another shared memory segment.  You might want to unpin the
 * referenced segment before destroying the referencing segment.
 */
/*
 * dsm_unpin_segment - (中文)解除对段的 pin(引用计数 -1,可能触发销毁)
 *
 * 【作用】按句柄在控制段里找槽位(找不到或未 pin 即报错),调平台层
 * dsm_impl_unpin_segment(必须持锁,因为它可能改写槽位里的
 * impl_private_pm_handle),计数减 1 并清 pinned;若减到 1(只剩"濒死"
 * 保护位)则本进程负责销毁:主区伪段归还页面,真实段 DSM_OP_DESTROY,
 * 成功后槽位清零。销毁成功与否都清空槽位处理。
 *
 * 【设计思想】参数用句柄而非描述符,方便"没附着也能 unpin"的场景
 * (如段 A 里存着对段 B 的引用,A 销毁前要 unpin B)。销毁路径的错误
 * 处理与 dsm_detach 相同:到达这里时当前进程必然没有该段映射(否则
 * 计数会大于 1),所以平台操作可以传空指针。
 *
 * 【参数】handle —— 段句柄。
 * 【返回值】无。
 */
void
dsm_unpin_segment(dsm_handle handle)
{
	uint32		control_slot = INVALID_CONTROL_SLOT;
	bool		destroy = false;
	uint32		i;

	/* Find the control slot for the given handle. */
	LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
	for (i = 0; i < dsm_control->nitems; ++i)
	{
		/* Skip unused slots and segments that are concurrently going away. */
		if (dsm_control->item[i].refcnt <= 1)
			continue;

		/* If we've found our handle, we can stop searching. */
		if (dsm_control->item[i].handle == handle)
		{
			control_slot = i;
			break;
		}
	}

	/*
	 * We should definitely have found the slot, and it should not already be
	 * in the process of going away, because this function should only be
	 * called on a segment which is pinned.
	 */
	if (control_slot == INVALID_CONTROL_SLOT)
		elog(ERROR, "cannot unpin unknown segment handle");
	if (!dsm_control->item[control_slot].pinned)
		elog(ERROR, "cannot unpin a segment that is not pinned");
	Assert(dsm_control->item[control_slot].refcnt > 1);

	/*
	 * Allow implementation-specific code to run.  We have to do this before
	 * releasing the lock, because impl_private_pm_handle may get modified by
	 * dsm_impl_unpin_segment.
	 */
	if (!is_main_region_dsm_handle(handle))
		dsm_impl_unpin_segment(handle,
							   &dsm_control->item[control_slot].impl_private_pm_handle);

	/* Note that 1 means no references (0 means unused slot). */
	if (--dsm_control->item[control_slot].refcnt == 1)
		destroy = true;
	dsm_control->item[control_slot].pinned = false;

	/* Now we can release the lock. */
	LWLockRelease(DynamicSharedMemoryControlLock);

	/* Clean up resources if that was the last reference. */
	if (destroy)
	{
		void	   *junk_impl_private = NULL;
		void	   *junk_mapped_address = NULL;
		Size		junk_mapped_size = 0;

		/*
		 * For an explanation of how error handling works in this case, see
		 * comments in dsm_detach.  Note that if we reach this point, the
		 * current process certainly does not have the segment mapped, because
		 * if it did, the reference count would have still been greater than 1
		 * even after releasing the reference count held by the pin.  The fact
		 * that there can't be a dsm_segment for this handle makes it OK to
		 * pass the mapped size, mapped address, and private data as NULL
		 * here.
		 */
		if (is_main_region_dsm_handle(handle) ||
			dsm_impl_op(DSM_OP_DESTROY, handle, 0, &junk_impl_private,
						&junk_mapped_address, &junk_mapped_size, WARNING))
		{
			LWLockAcquire(DynamicSharedMemoryControlLock, LW_EXCLUSIVE);
			if (is_main_region_dsm_handle(handle))
				FreePageManagerPut((FreePageManager *) dsm_main_space_begin,
								   dsm_control->item[control_slot].first_page,
								   dsm_control->item[control_slot].npages);
			Assert(dsm_control->item[control_slot].handle == handle);
			Assert(dsm_control->item[control_slot].refcnt == 1);
			dsm_control->item[control_slot].refcnt = 0;
			LWLockRelease(DynamicSharedMemoryControlLock);
		}
	}
}

/*
 * Find an existing mapping for a shared memory segment, if there is one.
 */
/*
 * dsm_find_mapping - (中文)查找本进程已有的段映射(按句柄)
 *
 * 【作用】线性扫描 dsm_segment_list,返回句柄匹配的段描述符;没有则
 * 返回 NULL。
 *
 * 【设计思想】避免重复 attach:每个进程同一段至多映射一次,需要再次
 * 使用时先查本函数。链表通常很短(每个后端同时使用的段不多),线性
 * 扫描足够。
 *
 * 【参数】handle —— 段句柄。
 * 【返回值】匹配的段描述符;未找到返回 NULL。
 */
dsm_segment *
dsm_find_mapping(dsm_handle handle)
{
	dlist_iter	iter;
	dsm_segment *seg;

	dlist_foreach(iter, &dsm_segment_list)
	{
		seg = dlist_container(dsm_segment, node, iter.cur);
		if (seg->handle == handle)
			return seg;
	}

	return NULL;
}

/*
 * Get the address at which a dynamic shared memory segment is mapped.
 */
/*
 * dsm_segment_address - (中文)返回段的映射起始地址
 *
 * 【作用】获取段在本进程虚拟地址空间中的映射地址,供读写段内容。
 *
 * 【设计思想】DSM 各进程的映射地址不同,共享结构里不能存普通指针、
 * 必须存偏移(见文件头);本函数把"描述符 → 地址"的换算收口在一处。
 *
 * 【参数】seg —— 段描述符(必须已映射)。
 * 【返回值】映射地址。
 */
void *
dsm_segment_address(dsm_segment *seg)
{
	Assert(seg->mapped_address != NULL);
	return seg->mapped_address;
}

/*
 * Get the size of a mapping.
 */
/*
 * dsm_segment_map_length - (中文)返回段的映射大小
 *
 * 【作用】返回本进程映射该段的大小(字节),创建时的 size 与平台层
 * 实际对齐后的结果一致。
 *
 * 【参数】seg —— 段描述符(必须已映射)。
 * 【返回值】映射字节数。
 */
Size
dsm_segment_map_length(dsm_segment *seg)
{
	Assert(seg->mapped_address != NULL);
	return seg->mapped_size;
}

/*
 * Get a handle for a mapping.
 *
 * To establish communication via dynamic shared memory between two backends,
 * one of them should first call dsm_create() to establish a new shared
 * memory mapping.  That process should then call dsm_segment_handle() to
 * obtain a handle for the mapping, and pass that handle to the
 * coordinating backend via some means (e.g. bgw_main_arg, or via the
 * main shared memory segment).  The recipient, once in possession of the
 * handle, should call dsm_attach().
 */
/*
 * dsm_segment_handle - (中文)返回段的句柄(跨进程标识)
 *
 * 【作用】返回 seg->handle。建立进程间共享的典型流程:创建者
 * dsm_create() → 本函数拿句柄 → 经 bgw_main_arg 或主共享内存传给
 * 其他进程 → 对方 dsm_attach()。
 *
 * 【参数】seg —— 段描述符。
 * 【返回值】段句柄。
 */
dsm_handle
dsm_segment_handle(dsm_segment *seg)
{
	return seg->handle;
}

/*
 * Register an on-detach callback for a dynamic shared memory segment.
 */
/*
 * on_dsm_detach - (中文)注册段的 on-detach 回调(段被 detach 时执行)
 *
 * 【作用】把 (function, arg) 压入 seg->on_detach 单链表头部。回调在
 * dsm_detach 里逐个执行,常用来释放段内引用的资源(如段内的锁、其他
 * 段的引用)。
 *
 * 【设计思想】回调分配在 TopMemoryContext,生命周期不受当前内存
 * 上下文影响;LIFO 执行顺序与退出回调惯例一致。
 *
 * 【参数】
 *   seg      —— 段描述符;
 *   function —— 回调函数(参数:seg + arg);
 *   arg      —— 回调随附 Datum。
 * 【返回值】无。
 */
void
on_dsm_detach(dsm_segment *seg, on_dsm_detach_callback function, Datum arg)
{
	dsm_segment_detach_callback *cb;

	cb = MemoryContextAlloc(TopMemoryContext,
							sizeof(dsm_segment_detach_callback));
	cb->function = function;
	cb->arg = arg;
	slist_push_head(&seg->on_detach, &cb->node);
}

/*
 * Unregister an on-detach callback for a dynamic shared memory segment.
 */
/*
 * cancel_on_dsm_detach - (中文)撤销一条已注册的 on-detach 回调
 *
 * 【作用】在 seg->on_detach 链表里找到 function 与 arg 都匹配的第一
 * 条记录并删除、释放;找不到则静默返回。
 *
 * 【设计思想】支持任意位置撤销(与 ipc.c 的 cancel_before_shmem_exit
 * 的 LIFO 限制不同),因为 detach 回调的注册/撤销模式并不保证严格的
 * 栈式配对。
 *
 * 【参数】
 *   seg      —— 段描述符;
 *   function —— 期待撤销的回调函数;
 *   arg      —— 期待撤销的随附参数。
 * 【返回值】无。
 */
void
cancel_on_dsm_detach(dsm_segment *seg, on_dsm_detach_callback function,
					 Datum arg)
{
	slist_mutable_iter iter;

	slist_foreach_modify(iter, &seg->on_detach)
	{
		dsm_segment_detach_callback *cb;

		cb = slist_container(dsm_segment_detach_callback, node, iter.cur);
		if (cb->function == function && cb->arg == arg)
		{
			slist_delete_current(&iter);
			pfree(cb);
			break;
		}
	}
}

/*
 * Discard all registered on-detach callbacks without executing them.
 */
/*
 * reset_on_dsm_detach - (中文)丢弃全部 on-detach 回调(不执行)
 *
 * 【作用】遍历 dsm_segment_list:释放每个段链表上已注册的 on-detach
 * 回调,并把 control_slot 置为 INVALID_CONTROL_SLOT(相当于"不再参与
 * 引用计数")。
 *
 * 【设计思想】供 on_exit_reset() 使用(见 ipc.c):子进程 fork 出来
 * 后,必须丢弃继承自 postmaster 的 detach 回调并断绝与段的引用计数
 * 关系,否则退出时会替 postmaster 清理段。把 control_slot 置无效是
 * 防止 dsm_detach 时再去减共享引用计数。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
reset_on_dsm_detach(void)
{
	dlist_iter	iter;

	dlist_foreach(iter, &dsm_segment_list)
	{
		dsm_segment *seg = dlist_container(dsm_segment, node, iter.cur);

		/* Throw away explicit on-detach actions one by one. */
		while (!slist_is_empty(&seg->on_detach))
		{
			slist_node *node;
			dsm_segment_detach_callback *cb;

			node = slist_pop_head_node(&seg->on_detach);
			cb = slist_container(dsm_segment_detach_callback, node, node);
			pfree(cb);
		}

		/*
		 * Decrementing the reference count is a sort of implicit on-detach
		 * action; make sure we don't do that, either.
		 */
		seg->control_slot = INVALID_CONTROL_SLOT;
	}
}

/*
 * Create a segment descriptor.
 */
/*
 * dsm_create_descriptor - (中文)创建并初始化一个空的段描述符
 *
 * 【作用】在 TopMemoryContext 分配 dsm_segment,压入本进程链表头;
 * 初始化 control_slot/impl_private/mapped_address/mapped_size,并把
 * 描述符登记到 CurrentResourceOwner(若非 NULL)。handle 留给调用方
 * (dsm_create/dsm_attach)赋值。
 *
 * 【设计思想】描述符挂在 TopMemoryContext,不受临时内存上下文影响;
 * resowner 登记使"事务 abort 时自动 detach"成为默认行为。
 *
 * 【参数】无。
 * 【返回值】新描述符(handle 未初始化)。
 */
static dsm_segment *
dsm_create_descriptor(void)
{
	dsm_segment *seg;

	if (CurrentResourceOwner)
		ResourceOwnerEnlarge(CurrentResourceOwner);

	seg = MemoryContextAlloc(TopMemoryContext, sizeof(dsm_segment));
	dlist_push_head(&dsm_segment_list, &seg->node);

	/* seg->handle must be initialized by the caller */
	seg->control_slot = INVALID_CONTROL_SLOT;
	seg->impl_private = NULL;
	seg->mapped_address = NULL;
	seg->mapped_size = 0;

	seg->resowner = CurrentResourceOwner;
	if (CurrentResourceOwner)
		ResourceOwnerRememberDSM(CurrentResourceOwner, seg);

	slist_init(&seg->on_detach);

	return seg;
}

/*
 * Sanity check a control segment.
 *
 * The goal here isn't to detect everything that could possibly be wrong with
 * the control segment; there's not enough information for that.  Rather, the
 * goal is to make sure that someone can iterate over the items in the segment
 * without overrunning the end of the mapping and crashing.  We also check
 * the magic number since, if that's messed up, this may not even be one of
 * our segments at all.
 */
/*
 * dsm_control_segment_sane - (中文)控制段健全性检查
 *
 * 【作用】判定映射到的内存是否"看起来像"合法的控制段:映射大小足以
 * 容纳头部?魔数匹配?maxitems 个条目能放进映射?nitems <= maxitems?
 * 全部通过才认为可用。
 *
 * 【设计思想】目的不是穷尽检测一切损坏(信息不足),而是确保"遍历
 * item[] 不会越界崩溃",并排除"这根本不是我们的段"(如 shm ID 被
 * 无关进程复用)。用于崩溃重启后的旧控制段与关闭时的自检。
 *
 * 【参数】
 *   control    —— 映射地址(当作控制段头读);
 *   mapped_size —— 映射大小。
 * 【返回值】true 表示通过检查。
 */
static bool
dsm_control_segment_sane(dsm_control_header *control, Size mapped_size)
{
	if (mapped_size < offsetof(dsm_control_header, item))
		return false;			/* Mapped size too short to read header. */
	if (control->magic != PG_DYNSHMEM_CONTROL_MAGIC)
		return false;			/* Magic number doesn't match. */
	if (dsm_control_bytes_needed(control->maxitems) > mapped_size)
		return false;			/* Max item count won't fit in map. */
	if (control->nitems > control->maxitems)
		return false;			/* Overfull. */
	return true;
}

/*
 * Compute the number of control-segment bytes needed to store a given
 * number of items.
 */
/*
 * dsm_control_bytes_needed - (中文)计算容纳 n 个条目所需的控制段字节数
 *
 * 【作用】返回"头部 + n × dsm_control_item"的总字节数。
 *
 * 【设计思想】创建控制段与健全性检查共用此计算,保证两处大小口径
 * 一致;用 uint64 运算防溢出。
 *
 * 【参数】nitems —— 条目数。
 * 【返回值】所需字节数。
 */
static uint64
dsm_control_bytes_needed(uint32 nitems)
{
	return offsetof(dsm_control_header, item)
		+ sizeof(dsm_control_item) * (uint64) nitems;
}

static inline dsm_handle
make_main_region_dsm_handle(int slot)
{
	dsm_handle	handle;

	/*
	 * We need to create a handle that doesn't collide with any existing extra
	 * segment created by dsm_impl_op(), so we'll make it odd.  It also
	 * mustn't collide with any other main area pseudo-segment, so we'll
	 * include the slot number in some of the bits.  We also want to make an
	 * effort to avoid newly created and recently destroyed handles from being
	 * confused, so we'll make the rest of the bits random.
	 */
	handle = 1;
	handle |= slot << 1;
	handle |= pg_prng_uint32(&pg_global_prng_state) << (pg_leftmost_one_pos32(dsm_control->maxitems) + 1);
	return handle;
}

/*
 * is_main_region_dsm_handle - (中文)判断句柄是否属于"主区伪段"
 * (奇数 = 是)。平台层真实段句柄恒为偶数(见 dsm_postmaster_startup /
 * dsm_create 里 "Use even numbers only"),两者用最低位区分。
 */
static inline bool
is_main_region_dsm_handle(dsm_handle handle)
{
	return handle & 1;
}

/* ResourceOwner callbacks */

/*
 * ResOwnerReleaseDSM - (中文)资源所有者释放回调:detach 一个 DSM 段
 *
 * 【作用】资源所有者释放时被调用(如事务/查询结束):先把 resowner
 * 置 NULL 再 dsm_detach,防止 detach 内部的清理再次触碰资源所有者
 * 登记(循环调用)。
 *
 * 【参数】res —— 段描述符(Datum 包装)。
 * 【返回值】无。
 */
static void
ResOwnerReleaseDSM(Datum res)
{
	dsm_segment *seg = (dsm_segment *) DatumGetPointer(res);

	seg->resowner = NULL;
	dsm_detach(seg);
}

/*
 * ResOwnerPrintDSM - (中文)资源所有者泄漏打印回调
 *
 * 【作用】资源泄漏告警(resowner 释放时仍有未释放资源)时打印段的
 * 可读描述,便于定位是哪个段漏了。
 *
 * 【参数】res —— 段描述符(Datum 包装)。
 * 【返回值】描述字符串(psprintf 分配)。
 */
static char *
ResOwnerPrintDSM(Datum res)
{
	dsm_segment *seg = (dsm_segment *) DatumGetPointer(res);

	return psprintf("dynamic shared memory segment %u",
					dsm_segment_handle(seg));
}
