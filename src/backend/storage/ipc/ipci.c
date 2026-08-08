/*-------------------------------------------------------------------------
 *
 * ipci.c
 *	  POSTGRES inter-process communication initialization code.
 *
 * 【模块总览(中文)】
 * 本文件是"共享内存初始化"的总调度:它不实现具体的分配算法(那在
 * shmem.c),也不实现具体子系统(各自模块),而是把这些拼成完整的
 * 启动序列。
 *
 * 【职责】
 * 1. 估算共享内存总大小:CalculateShmemSize() 汇总三类需求——固定
 *    基数(100KB)、ShmemGetRequestedSize()(各子系统通过新式
 *    request 回调登记的总量)、以及 total_addin_request(旧式扩展
 *    经 RequestAddinShmemSpace() 申报的量),并向上取整到 8KB 倍数。
 * 2. 实际创建与初始化:CreateSharedMemoryAndSemaphores() 按顺序执行
 *    "创建段 → InitShmemAllocator() 建立分配器 → ShmemInitRequested()
 *    落地全部登记区域 → dsm_postmaster_startup() 建立动态共享内存
 *    基础设施 → 调用扩展的 shmem_startup_hook"。
 * 3. 早期登记:RegisterBuiltinShmemCallbacks() 借助
 *    subsystemlist.h 的宏展开,把全部内置子系统的 ShmemCallbacks
 *    一次性登记(在创建段之前调用,对应 request 阶段)。
 * 4. 运行期 GUC 反馈:InitializeShmemGUCs() 把计算出的共享内存大小、
 *    所需 huge page 数、OS 信号量数量写回 internal GUC,供
 *    pg_settings / pg_show_all_settings 展示。
 * 5. EXEC_BACKEND 模式下,AttachSharedMemoryStructs() 供子进程启动
 *    时重新附着共享内存。
 *
 * 【新旧扩展接口的过渡】本文件同时保留新式
 * (RegisterShmemCallbacks + subsystemlist.h)与旧式
 * (RequestAddinShmemSpace + shmem_startup_hook)两条扩展路径:
 * 旧式接口只被兼容性保留,新扩展应使用新式回调。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/ipci.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "miscadmin.h"
#include "pgstat.h"
#include "storage/dsm.h"
#include "storage/ipc.h"
#include "storage/lock.h"
#include "storage/pg_shmem.h"
#include "storage/proc.h"
#include "storage/shmem_internal.h"
#include "storage/subsystems.h"
#include "utils/guc.h"

/* GUCs */
/* (中文)GUC 变量:共享内存的实现类型(POSIX/SysV/匿名 mmap 等),由
 * shared_memory_type 配置项驱动,默认取平台默认值
 * DEFAULT_SHARED_MEMORY_TYPE。 */
int			shared_memory_type = DEFAULT_SHARED_MEMORY_TYPE;

/* (中文)扩展的 shmem_startup_hook:由 shared_preload_libraries 加载的
 * 库在 _PG_init() 里赋值。postmaster 完成内置区域初始化后调用它,让
 * 扩展初始化自己的共享内存区域。这是旧式扩展接口。 */
shmem_startup_hook_type shmem_startup_hook = NULL;

/* (中文)旧式扩展经 RequestAddinShmemSpace() 申报的额外共享内存总量,
 * 计入 CalculateShmemSize() 的汇总。 */
static Size total_addin_request = 0;

/*
 * RequestAddinShmemSpace
 *		Request that extra shmem space be allocated for use by
 *		a loadable module.
 *
 * This may only be called via the shmem_request_hook of a library that is
 * loaded into the postmaster via shared_preload_libraries.  Calls from
 * elsewhere will fail.
 */
/*
 * RequestAddinShmemSpace - (中文)[旧式接口]为扩展模块申报额外共享内存
 *
 * 【作用】把 size 累加进 total_addin_request,计入共享内存总需求。只允许
 * 在 process_shmem_requests_in_progress 为真时调用,即只能在经
 * shared_preload_libraries 加载的库的 shmem_request_hook 里调用,其他
 * 时机调用直接 FATAL。
 *
 * 【设计思想】这是旧式扩展接口:先在这里申报大小,等共享内存段创建好
 * 之后,扩展在 shmem_startup_hook 里再用 ShmemInitStruct()(须配合
 * ShmemInitHash 等)实际取用内存。新式接口应改用 RegisterShmemCallbacks
 * 的 request_fn 里调用 ShmemRequestStruct(),见 shmem.c 的文件头说明。
 * 申报必须发生在段大小计算之前,否则份额无法兑现。
 *
 * 【参数】size —— 需要的字节数(>0)。
 * 【返回值】无。
 */
void
RequestAddinShmemSpace(Size size)
{
	if (!process_shmem_requests_in_progress)
		elog(FATAL, "cannot request additional shared memory outside shmem_request_hook");
	total_addin_request = add_size(total_addin_request, size);
}

/*
 * CalculateShmemSize
 *		Calculates the amount of shared memory needed.
 */
/*
 * CalculateShmemSize - (中文)计算共享内存段需要的总字节数
 *
 * 【作用】汇总共享内存总需求:100KB 固定基数(给"不值得逐一估算的小
 * 部件")+ ShmemGetRequestedSize()(新式 request 回调登记的全部需求,
 * 含 ShmemIndex)+ total_addin_request(旧式扩展申报),最后向上取整到
 * 8KB 的倍数返回。
 *
 * 【设计思想】大块需求都由各子系统给出精确估算,小部件用一个固定余量
 * 覆盖,避免维护成本过高。所有加法都用 add_size() 做溢出检测,确保总
 * 大小不超出 size_t 可表示范围——只要这里没溢出,后续实际分配阶段就
 * 不必再逐一检查溢出。末尾的 8KB 取整让段大小与典型页大小对齐。
 *
 * 【参数】无。
 * 【返回值】共享内存段总字节数。
 */
Size
CalculateShmemSize(void)
{
	Size		size;

	/*
	 * Size of the Postgres shared-memory block is estimated via moderately-
	 * accurate estimates for the big hogs, plus 100K for the stuff that's too
	 * small to bother with estimating.
	 *
	 * We take some care to ensure that the total size request doesn't
	 * overflow size_t.  If this gets through, we don't need to be so careful
	 * during the actual allocation phase.
	 */
	size = 100000;
	size = add_size(size, ShmemGetRequestedSize());

	/* include additional requested shmem from preload libraries */
	size = add_size(size, total_addin_request);

	/* might as well round it off to a multiple of a typical page size */
	size = add_size(size, 8192 - (size % 8192));

	return size;
}

#ifdef EXEC_BACKEND
/*
 * AttachSharedMemoryStructs
 *		Initialize a postmaster child process's access to shared memory
 *      structures.
 *
 * In !EXEC_BACKEND mode, we inherit everything through the fork, and this
 * isn't needed.
 */
/*
 * AttachSharedMemoryStructs - (中文)(EXEC_BACKEND 模式)子进程重新建立共享内存访问
 *
 * 【作用】EXEC_BACKEND 模式下子进程启动时调用(此模式无 fork 继承,必须
 * 自己重建一切):1) InitializeFastPathLocks()——重算 fast-path 组数量
 * (子进程不继承 postmaster 计算好的值);2) ShmemAttachRequested()——
 * 把所有登记区域的指针重新指向共享内存;3) 调用扩展的
 * shmem_startup_hook() 让扩展恢复自己的指针。
 *
 * 【设计思想】前置条件:InitProcess() 必须先执行(MyProc 非空),且处于
 * 子进程环境(IsUnderPostmaster)。普通 Unix 环境下不需要此函数——子进程
 * 通过 fork() 原样继承了 postmaster 的所有指针变量。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
AttachSharedMemoryStructs(void)
{
	/* InitProcess must've been called already */
	Assert(MyProc != NULL);
	Assert(IsUnderPostmaster);

	/*
	 * In EXEC_BACKEND mode, backends don't inherit the number of fast-path
	 * groups we calculated before setting the shmem up, so recalculate it.
	 */
	InitializeFastPathLocks();

	/* Establish pointers to all shared memory areas in this backend */
	ShmemAttachRequested();

	/*
	 * Now give loadable modules a chance to set up their shmem allocations
	 */
	if (shmem_startup_hook)
		shmem_startup_hook();
}
#endif

/*
 * CreateSharedMemoryAndSemaphores
 *		Creates and initializes shared memory and semaphores.
 */
/*
 * CreateSharedMemoryAndSemaphores - (中文)创建并初始化共享内存(与信号量)的总入口
 *
 * 【作用】postmaster(或单机后端)启动时调用,按顺序执行完整的共享内存
 * 初始化序列:
 * 1. CalculateShmemSize() 计算总大小;
 * 2. PGSharedMemoryCreate(size, &shim) 创建操作系统共享内存段(返回段头
 *    seghdr 与"匿名段描述符"shim,后者交给 DSM 用于在段内再切分);
 * 3. 断言 huge_pages_status 已不再"未知"(运行期必须确定);
 * 4. InitShmemAllocator(seghdr) 建立共享内存分配器与 ShmemIndex;
 * 5. ShmemInitRequested() 落地全部登记区域并执行各子系统 init 回调;
 * 6. dsm_postmaster_startup(shim) 初始化动态共享内存(DSM)基础设施;
 * 7. 调用扩展的 shmem_startup_hook(旧式扩展接口)。
 *
 * 【设计思想】这个顺序是"总调度",各步骤之间存在依赖:分配器必须先于
 * 一切区域落地;DSM 需要共享内存段就位;扩展最后初始化是因为它们可能
 * 依赖任何内置子系统。名虽为 CreateSharedMemoryAndSemaphores,信号量
 * (ProcGlobal)由 shmem 里的 ProcGlobalShmem 子系统负责创建,这里只
 * 是总入口。
 *
 * 【参数】无。
 * 【返回值】无(任何失败都会以 ERROR/PANIC 终止)。
 */
void
CreateSharedMemoryAndSemaphores(void)
{
	PGShmemHeader *shim;
	PGShmemHeader *seghdr;
	Size		size;

	Assert(!IsUnderPostmaster);

	/* Compute the size of the shared-memory block */
	size = CalculateShmemSize();
	elog(DEBUG3, "invoking IpcMemoryCreate(size=%zu)", size);

	/*
	 * Create the shmem segment
	 */
	seghdr = PGSharedMemoryCreate(size, &shim);

	/*
	 * Make sure that huge pages are never reported as "unknown" while the
	 * server is running.
	 */
	Assert(strcmp("unknown",
				  GetConfigOption("huge_pages_status", false, false)) != 0);

	/*
	 * Set up shared memory allocation mechanism
	 */
	InitShmemAllocator(seghdr);

	/* Initialize all shmem areas */
	ShmemInitRequested();

	/* Initialize dynamic shared memory facilities. */
	dsm_postmaster_startup(shim);

	/*
	 * Now give loadable modules a chance to set up their shmem allocations
	 */
	if (shmem_startup_hook)
		shmem_startup_hook();
}

/*
 * Early initialization of various subsystems, giving them a chance to
 * register their shared memory needs before the shared memory segment is
 * allocated.
 */
/*
 * RegisterBuiltinShmemCallbacks - (中文)登记全部内置子系统的共享内存回调
 *
 * 【作用】通过宏展开#include "storage/subsystemlist.h" 中列出的每个
 * 子系统,逐个调用 RegisterShmemCallbacks() 登记其 ShmemCallbacks
 * (含 request_fn/init_fn 等)。必须在共享内存段创建之前调用,对应
 * request 阶段。
 *
 * 【设计思想】采用"列表头文件 + 宏展开"的 X-macro 技巧:新增内置子系统
 * 时只需在 subsystemlist.h 里加一行,本文件的展开逻辑与各子系统的调用
 * 顺序由列表决定,避免手工维护一长串 RegisterShmemCallbacks 调用。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
RegisterBuiltinShmemCallbacks(void)
{
	/*
	 * Call RegisterShmemCallbacks(...) on each subsystem listed in
	 * subsystemlist.h
	 */
#define PG_SHMEM_SUBSYSTEM(subsystem_callbacks) \
	RegisterShmemCallbacks(&(subsystem_callbacks));

#include "storage/subsystemlist.h"

#undef PG_SHMEM_SUBSYSTEM
}

/*
 * InitializeShmemGUCs
 *
 * This function initializes runtime-computed GUCs related to the amount of
 * shared memory required for the current configuration.
 */
/*
 * InitializeShmemGUCs - (中文)初始化与共享内存规模相关的运行期 GUC
 *
 * 【作用】把按当前配置计算出的几个规模指标写成 internal GUC(便于在
 * pg_settings / pg_show_all_settings 里查看):
 * - shared_memory_size:共享内存总大小(向上取整到 MB);
 * - shared_memory_size_in_huge_pages:所需 huge page 数(huge page 不可用
 *   时跳过);
 * - num_os_semaphores:需要的 OS 信号量个数(来自 ProcGlobalSemas())。
 *
 * 【设计思想】这些值由配置与平台动态决定,无法用静态默认值表达,因此
 * 以 PGC_INTERNAL + PGC_S_DYNAMIC_DEFAULT 的方式注入 GUC 系统:对用户
 * 只读、不可修改。调用时机在共享内存创建完成后,确保 CalculateShmemSize
 * 的结果是最终值。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
InitializeShmemGUCs(void)
{
	char		buf[64];
	Size		size_b;
	Size		size_mb;
	Size		hp_size;

	/*
	 * Calculate the shared memory size and round up to the nearest megabyte.
	 */
	size_b = CalculateShmemSize();
	size_mb = add_size(size_b, (1024 * 1024) - 1) / (1024 * 1024);
	sprintf(buf, "%zu", size_mb);
	SetConfigOption("shared_memory_size", buf,
					PGC_INTERNAL, PGC_S_DYNAMIC_DEFAULT);

	/*
	 * Calculate the number of huge pages required.
	 */
	GetHugePageSize(&hp_size, NULL);
	if (hp_size != 0)
	{
		Size		hp_required;

		hp_required = size_b / hp_size;
		if (size_b % hp_size != 0)
			hp_required = add_size(hp_required, 1);
		sprintf(buf, "%zu", hp_required);
		SetConfigOption("shared_memory_size_in_huge_pages", buf,
						PGC_INTERNAL, PGC_S_DYNAMIC_DEFAULT);
	}

	sprintf(buf, "%d", ProcGlobalSemas());
	SetConfigOption("num_os_semaphores", buf, PGC_INTERNAL, PGC_S_DYNAMIC_DEFAULT);
}
