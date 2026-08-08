/*-------------------------------------------------------------------------
 *
 * shmem.c
 *	  create shared memory and initialize shared memory data structures.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 传统的"固定共享内存(shmem)"基础设施:在共享
 * 内存段里分配、登记、按名查找各种共享数据结构。锁表、缓冲池控制块、
 * PGPROC 进程表、WAL 缓冲等所有"所有后端必须共享"的状态,最终都经由
 * 本文件的接口落进共享内存,是跨进程协作的地基。
 *
 * 【核心数据流(新架构)】
 * 现代代码走"request → allocate → init"三段式协议:
 * 1. request 阶段(postmaster 启动早期):各子系统用
 *    RegisterShmemCallbacks() 登记生命周期回调;ShmemCallRequestCallbacks()
 *    依次调用回调的 request_fn,回调内部用 ShmemRequestStruct() /
 *    ShmemRequestHash() 等"登记需求"(只记账、不分配);
 * 2. ShmemGetRequestedSize() 把全部需求累加(含 ShmemIndex 索引表自身),
 *    得到共享内存总大小,由 postmaster 一次性创建共享内存段;
 * 3. ShmemInitRequested() 按登记顺序用 ShmemAlloc 切分内存、把结果写入
 *    ShmemIndex 索引表,再依次调用各子系统的 init_fn 做初始化。
 * (EXEC_BACKEND 模式下子进程无法继承指针,后端启动时改走
 * ShmemAttachRequested() 重新"附着"而非初始化。)
 * 与旧版"GetSharedMemorySize() 手写汇总需求"的架构相比,新架构不再
 * 需要维护一份与分配代码同步的总需求清单:新增子系统只需登记回调。
 *
 * 【核心数据结构】
 * - ShmemAllocatorData:分配器头,记录空闲偏移量 free_offset(自旋锁
 *   保护)、ShmemIndex 的位置与保护它的 LWLock;
 * - ShmemIndex:一张"名字 → (地址, 大小)"的共享哈希表,是共享内存的
 *   全局目录,任何进程都可按字符串名字找到(或创建)一个共享结构;
 * - ShmemIndexEnt:ShmemIndex 的条目。
 *
 * 【遗留接口】ShmemInitStruct()/ShmemInitHash() 是旧接口,如今主要为
 * 扩展兼容保留(新代码必须用 ShmemRequest* 系列)。共享内存一经分配
 * 永不释放;哈希表条目被删后其槽位可复用。注意:本文件管理的传统
 * 共享内存在所有进程映射到相同地址,因此共享结构里可以直接放普通指针;
 * 地址不同的动态共享内存见 dsm.c。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/shmem.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * POSTGRES processes share one or more regions of shared memory.
 * The shared memory is created by a postmaster and is inherited
 * by each backend via fork() (or, in some ports, via other OS-specific
 * methods).  The routines in this file are used for allocating and
 * binding to shared memory data structures.
 *
 * This module provides facilities to allocate fixed-size structures in shared
 * memory, for things like variables shared between all backend processes.
 * Each such structure has a string name to identify it, specified when it is
 * requested.  shmem_hash.c provides a shared hash table implementation on top
 * of that.
 *
 * Shared memory areas should usually not be allocated after postmaster
 * startup, although we do allow small allocations later for the benefit of
 * extension modules that are loaded after startup.  Despite that allowance,
 * extensions that need shared memory should be added in
 * shared_preload_libraries, because the allowance is quite small and there is
 * no guarantee that any memory is available after startup.
 *
 * Nowadays, there is also another way to allocate shared memory called
 * Dynamic Shared Memory.  See dsm.c for that facility.  One big difference
 * between traditional shared memory handled by shmem.c and dynamic shared
 * memory is that traditional shared memory areas are mapped to the same
 * address in all processes, so you can use normal pointers in shared memory
 * structs.  With Dynamic Shared Memory, you must use offsets or DSA pointers
 * instead.
 *
 * Shared memory managed by shmem.c can never be freed, once allocated.  Each
 * hash table has its own free list, so hash buckets can be reused when an
 * item is deleted.
 *
 * Usage
 * -----
 *
 * To allocate shared memory, you need to register a set of callback functions
 * which handle the lifecycle of the allocation.  In the request_fn callback,
 * call ShmemRequestStruct() with the desired name and size.  When the area is
 * later allocated or attached to, the global variable pointed to by the .ptr
 * option is set to the shared memory location of the allocation.  The init_fn
 * callback can perform additional initialization.
 *
 *	typedef struct MyShmemData {
 *		...
 *	} MyShmemData;
 *
 *	static MyShmemData *MyShmem;
 *
 *	static void my_shmem_request(void *arg);
 *	static void my_shmem_init(void *arg);
 *
 *  const ShmemCallbacks MyShmemCallbacks = {
 *		.request_fn = my_shmem_request,
 *		.init_fn = my_shmem_init,
 *	};
 *
 *	static void
 *	my_shmem_request(void *arg)
 *	{
 *		ShmemRequestStruct(.name = "My shmem area",
 *						   .size = sizeof(MyShmemData),
 *						   .ptr = (void **) &MyShmem,
 *			);
 *	}
 *
 * In builtin PostgreSQL code, add the callbacks to the list in
 * src/include/storage/subsystemlist.h.  In an add-in module, you can register
 * the callbacks by calling RegisterShmemCallbacks(&MyShmemCallbacks) in the
 * extension's _PG_init() function.
 *
 * Lifecycle
 * ---------
 *
 * Initializing shared memory happens in multiple phases.  In the first phase,
 * during postmaster startup, all the request_fn callbacks are called.  Only
 * after all the request_fn callbacks have been called and all the shmem areas
 * have been requested by the ShmemRequestStruct() calls we know how much
 * shared memory we need in total.  After that, postmaster allocates global
 * shared memory segment, and calls all the init_fn callbacks to initialize
 * all the requested shmem areas.
 *
 * In standard Unix-ish environments, individual backends do not need to
 * re-establish their local pointers into shared memory, because they inherit
 * correct values of those variables via fork() from the postmaster.  However,
 * this does not work in the EXEC_BACKEND case.  In ports using EXEC_BACKEND,
 * backend startup also calls the shmem_request callbacks to re-establish the
 * knowledge about each shared memory area, sets the pointer variables
 * (*options->ptr), and calls the attach_fn callback, if any, for additional
 * per-backend setup.
 *
 * Legacy ShmemInitStruct()/ShmemInitHash() functions
 * --------------------------------------------------
 *
 * ShmemInitStruct()/ShmemInitHash() is another way of registering shmem
 * areas.  It pre-dates the ShmemRequestStruct()/ShmemRequestHash() functions,
 * and should not be used in new code, but as of this writing it is still
 * widely used in extensions.
 *
 * To allocate a shmem area with ShmemInitStruct(), you need to separately
 * register the size needed for the area by calling RequestAddinShmemSpace()
 * from the extension's shmem_request_hook, and allocate the area by calling
 * ShmemInitStruct() from the extension's shmem_startup_hook.  There are no
 * init/attach callbacks.  Instead, the caller of ShmemInitStruct() must check
 * the return status of ShmemInitStruct() and initialize the struct if it was
 * not previously initialized.
 *
 * Calling ShmemAlloc() directly
 * -----------------------------
 *
 * There's a more low-level way of allocating shared memory too: you can call
 * ShmemAlloc() directly.  It's used to implement the higher level mechanisms,
 * and should generally not be called directly.
 */

#include "postgres.h"

#include <unistd.h>

#include "access/slru.h"
#include "fmgr.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "port/pg_bitutils.h"
#include "port/pg_numa.h"
#include "storage/lwlock.h"
#include "storage/pg_shmem.h"
#include "storage/shmem.h"
#include "storage/shmem_internal.h"
#include "storage/spin.h"
#include "utils/builtins.h"
#include "utils/tuplestore.h"

/*
 * Registered callbacks.
 *
 * During postmaster startup, we accumulate the callbacks from all subsystems
 * in this list.
 *
 * This is in process private memory, although on Unix-like systems, we expect
 * all the registrations to happen at postmaster startup time and be inherited
 * by all the child processes via fork().
 */
/* (中文)本进程已登记的全部共享内存回调组(ShmemCallbacks)列表:
 * 在 postmaster 启动早期由各子系统/扩展调用 RegisterShmemCallbacks()
 * 追加。它保存在进程私有内存;Unix 系下所有登记发生在 postmaster 启动
 * 时,子进程经 fork() 继承;EXEC_BACKEND 模式下每个进程自行重新登记。
 * request/init/attach 阶段都会遍历这个列表调用相应的回调。 */
static List *registered_shmem_callbacks;

/*
 * In the shmem request phase, all the shmem areas requested with the
 * ShmemRequest*() functions are accumulated here.
 */
/* (中文)一条"共享内存需求"记录:options 是该区域的属性(名字/大小/对齐/
 * 指针槽等),kind 是该区域的类别(普通结构 SHMEM_KIND_STRUCT / 哈希表
 * SHMEM_KIND_HASH / SLRU 缓冲 SHMEM_KIND_SLRU),类别决定后续在共享
 * 内存里如何建立/恢复对应的控制结构。 */
typedef struct
{
	ShmemStructOpts *options;
	ShmemRequestKind kind;
} ShmemRequest;

/* (中文)request 阶段所有 ShmemRequest*() 登记的需求都会追加到这个列表,
 * 供 ShmemGetRequestedSize() 汇总大小、ShmemInitRequested() /
 * ShmemAttachRequested() 依次落地。 */
static List *pending_shmem_requests;

/*
 * Per-process state machine, for sanity checking that we do things in the
 * right order.
 *
 * Postmaster:
 *   INITIAL -> REQUESTING -> INITIALIZING -> DONE
 *
 * Backends in EXEC_BACKEND mode:
 *   INITIAL -> REQUESTING -> ATTACHING -> DONE
 *
 * Late request:
 *   DONE -> REQUESTING -> AFTER_STARTUP_ATTACH_OR_INIT -> DONE
 */
/* (中文)共享内存初始化流程的进程内状态机,用于校验各阶段调用顺序正确:
 * - 启动阶段(postmaster 或单机后端):INITIAL(未开始)→ REQUESTING
 *   (正在收集 request 回调)→ INITIALIZING(段已创建、正在初始化)→ DONE;
 * - EXEC_BACKEND 子进程:REQUESTING 之后进入 ATTACHING(附着已有区域)
 *   再到 DONE;
 * - 运行期扩展的"迟到登记":DONE → REQUESTING →
 *   AFTER_STARTUP_ATTACH_OR_INIT → DONE。
 * 所有公开接口都断言当前状态,违规调用(如 postmaster 之外申请共享内存)
 * 会立即报错。 */
enum shmem_request_state
{
	/* Initial state */
	SRS_INITIAL,

	/*
	 * When we start calling the shmem_request callbacks, we enter the
	 * SRS_REQUESTING phase.  All ShmemRequestStruct calls happen in this
	 * state.
	 */
	SRS_REQUESTING,

	/*
	 * Postmaster has finished all shmem requests, and is now initializing the
	 * shared memory segment.  init_fn callbacks are called in this state.
	 */
	SRS_INITIALIZING,

	/*
	 * A postmaster child process is starting up.  attach_fn callbacks are
	 * called in this state.
	 */
	SRS_ATTACHING,

	/* An after-startup allocation or attachment is in progress */
	SRS_AFTER_STARTUP_ATTACH_OR_INIT,

	/* Normal state after shmem initialization / attachment */
	SRS_DONE,
};
static enum shmem_request_state shmem_request_state = SRS_INITIAL;

/*
 * This is the first data structure stored in the shared memory segment, at
 * the offset that PGShmemHeader->content_offset points to.  Allocations by
 * ShmemAlloc() are carved out of the space after this.
 *
 * For the base pointer and the total size of the shmem segment, we rely on
 * the PGShmemHeader.
 */
/* (中文)共享内存分配器的控制头,位于共享内存段最开头(PGShmemHeader 的
 * content_offset 指向的位置),ShmemAlloc() 分配的每一块都从它之后切出。
 *
 * 字段含义:
 * - free_offset : 距离段基址(ShmemBase)的空闲偏移量,即"下一条分配的
 *   起始候选位置";受 shmem_lock 自旋锁保护;
 * - shmem_lock  : 保护 free_offset 的自旋锁(分配是高频热路径,用最廉价
 *   的自旋锁);
 * - index       : ShmemIndex 索引表在共享内存中的位置(HASHHDR);
 * - index_size  : ShmemIndex 占用的共享内存字节数;
 * - index_lock  : 保护 ShmemIndex 的 LWLock(可睡眠,供慢速查找路径用)。
 *
 * 关于段基址与段总大小,本结构不重复存储,直接依赖 PGShmemHeader。 */
typedef struct ShmemAllocatorData
{
	Size		free_offset;	/* offset to first free space from ShmemBase */

	/* protects 'free_offset' */
	slock_t		shmem_lock;

	HASHHDR    *index;			/* location of ShmemIndex */
	size_t		index_size;		/* size of shmem region holding ShmemIndex */
	LWLock		index_lock;		/* protects ShmemIndex */
} ShmemAllocatorData;

#define ShmemIndexLock (&ShmemAllocator->index_lock)
/* (中文)访问 ShmemIndex 索引表时使用的 LWLock(指向分配器头中的
 * index_lock)。凡是对索引表的查找/插入/遍历都必须先取得它。 */

static void *ShmemAllocRaw(Size size, Size alignment, Size *allocated_size);

/* shared memory global variables */

/* (中文)以下三个全局变量描述整个共享内存段(在 InitShmemAllocator()
 * 中设置):
 * - ShmemSegHdr : 段头 PGShmemHeader,含 content_offset 与段总大小
 *   totalsize;
 * - ShmemBase   : 段起始地址(与 ShmemSegHdr 相同);
 * - ShmemEnd    : 段结束地址 +1,与 ShmemBase 一起构成
 *   ShmemAddrIsValid() 的合法区间。 */
static PGShmemHeader *ShmemSegHdr;	/* shared mem segment header */
static void *ShmemBase;			/* start address of shared memory */
static void *ShmemEnd;			/* end+1 address of shared memory */

/* (中文)指向共享内存中分配器控制头(ShmemAllocatorData)的指针,进程内
 * 缓存,由 InitShmemAllocator() 设置;所有 ShmemAlloc*() 都经由它。 */
static ShmemAllocatorData *ShmemAllocator;

/*
 * ShmemIndex is a global directory of shmem areas, itself also stored in the
 * shared memory.
 */
/* (中文)ShmemIndex:共享内存区域的"全局目录"哈希表,本身也存放在共享
 * 内存中。键是区域的字符串名字,条目是 ShmemIndexEnt(地址、请求大小、
 * 实际大小)。所有进程用它按名查找/登记共享结构。 */
static HTAB *ShmemIndex;

 /* max size of data structure string name */
#define SHMEM_INDEX_KEYSIZE		 (48)
/* (中文)ShmemIndex 的键(共享结构名字)最大字节数,名字超长会被截断。
 * 这也是 ShmemIndexEnt.key 数组的大小。 */

/*
 * # of additional entries to reserve in the shmem index table, for
 * allocations after postmaster startup.  (This is not a hard limit, the hash
 * table can grow larger than that if there is shared memory available)
 */
/* (中文)ShmemIndex 预留的额外条目数:postmaster 启动之后扩展模块还可能
 * 继续登记共享区域,所以建表时多留 128 个槽位。这不是硬上限,若共享
 * 内存还够,哈希表可以动态扩容。 */
#define SHMEM_INDEX_ADDITIONAL_SIZE		 (128)

/* this is a hash bucket in the shmem index table */
/* (中文)ShmemIndex 索引表的一个条目(哈希桶):
 * - key            : 区域名字(SHMEM_INDEX_KEYSIZE 字节定长);
 * - location       : 区域在共享内存中的地址;
 * - size           : 请求分配的字节数;
 * - allocated_size : 实际分配的字节数(含对齐填充,可能大于 size),
 *                     供 pg_shmem_allocations 视图精确记账。 */
typedef struct
{
	char		key[SHMEM_INDEX_KEYSIZE];	/* string name */
	void	   *location;		/* location in shared mem */
	Size		size;			/* # bytes requested for the structure */
	Size		allocated_size; /* # bytes actually allocated */
} ShmemIndexEnt;

/* To get reliable results for NUMA inquiry we need to "touch pages" once */
/* (中文)NUMA 查询辅助标志:第一次执行 pg_get_shmem_allocations_numa 时,
 * 必须先"touch"共享内存的每一页(触发内核映射),否则内核会因页未映射
 * 返回 -2(ENOENT),NUMA 统计失真。首次完成后置为 false,之后不再 touch。 */
static bool firstNumaTouch = true;

static void CallShmemCallbacksAfterStartup(const ShmemCallbacks *callbacks);
static void InitShmemIndexEntry(ShmemRequest *request);
static bool AttachShmemIndexEntry(ShmemRequest *request, bool missing_ok);

Datum		pg_numa_available(PG_FUNCTION_ARGS);

/*
 *	ShmemRequestStruct() --- request a named shared memory area
 *
 * Subsystems call this to register their shared memory needs.  This is
 * usually done early in postmaster startup, before the shared memory segment
 * has been created, so that the size can be included in the estimate for
 * total amount of shared memory needed.  We set aside a small amount of
 * memory for allocations that happen later, for the benefit of non-preloaded
 * extensions, but that should not be relied upon.
 *
 * This does not yet allocate the memory, but merely registers the need for
 * it.  The actual allocation happens later in the postmaster startup
 * sequence.
 *
 * This must be called from a shmem_request callback function, registered with
 * RegisterShmemCallbacks().  This enforces a coding pattern that works the
 * same in normal Unix systems and with EXEC_BACKEND.  On Unix systems, the
 * shmem_request callbacks are called once, early in postmaster startup, and
 * the child processes inherit the struct descriptors and any other
 * per-process state from the postmaster.  In EXEC_BACKEND mode, shmem_request
 * callbacks are *also* called in each backend, at backend startup, to
 * re-establish the struct descriptors.  By calling the same function in both
 * cases, we ensure that all the shmem areas are registered the same way in
 * all processes.
 *
 * 'options' defines the name and size of the area, and any other optional
 * features.  Leave unused options as zeros.  The options are copied to
 * longer-lived memory, so it doesn't need to live after the
 * ShmemRequestStruct() call and can point to a local variable in the calling
 * function.  The 'name' must point to a long-lived string though, only the
 * pointer to it is copied.
 */
/*
 * ShmemRequestStructWithOpts - (中文)登记一个"命名共享内存区域"的需求(request 阶段)
 *
 * 【作用】供 shmem_request 回调调用:把一个命名共享内存区域的属性
 * (ShmemStructOpts:名字、大小、对齐、指针槽等)登记进待处理队列
 * pending_shmem_requests。此时并不分配内存,只是记账,以便随后统一
 * 计算共享内存总大小(见 ShmemGetRequestedSize)。
 *
 * 【设计思想】options 会被整体拷贝到 TopMemoryContext(长生命期),所以
 * 调用方可以传栈上的临时结构;但 name 字符串只拷贝"指针",因此它必须
 * 指向长生命期字符串。拷贝的理由:request 回调可能在 EXEC_BACKEND 的
 * 子进程里也执行一遍,这些登记项要活到 init/attach 回调跑完才释放。
 *
 * 【参数】options —— 区域属性,见 ShmemStructOpts:name(用于 ShmemIndex
 * 按名查找)、size(字节数)、alignment(起始地址对齐)、ptr(指向一个
 * 全局指针变量,创建/附着后会被赋值为该区域的共享内存地址)。未用字段
 * 填 0。
 * 【返回值】无。
 */
void
ShmemRequestStructWithOpts(const ShmemStructOpts *options)
{
	ShmemStructOpts *options_copy;

	options_copy = MemoryContextAlloc(TopMemoryContext,
									  sizeof(ShmemStructOpts));
	memcpy(options_copy, options, sizeof(ShmemStructOpts));

	ShmemRequestInternal(options_copy, SHMEM_KIND_STRUCT);
}

/*
 * Internal workhorse of ShmemRequestStruct() and ShmemRequestHash().
 *
 * Note: Unlike in the public ShmemRequestStruct() and ShmemRequestHash()
 * functions, 'options' is *not* copied.  It must be allocated in
 * TopMemoryContext by the caller, and will be freed after the init/attach
 * callbacks have been called.  This allows ShmemRequestHash() to pass a
 * pointer to the extended ShmemHashOpts struct instead.
 */
/*
 * ShmemRequestInternal - (中文)ShmemRequestStruct()/ShmemRequestHash() 的公共内部实现
 *
 * 【作用】执行"共享内存需求登记"的公共校验与入队:校验 name 非空;校验
 * size 合法(postmaster 启动阶段必须为正整数,子进程阶段允许
 * SHMEM_ATTACH_UNKNOWN_SIZE 表示"只附着、大小以已存在区域为准");校验
 * alignment 为 2 的幂;校验当前正处于 SRS_REQUESTING 状态(即只能在
 * request 回调里调用);校验名字未重复登记;最后追加进
 * pending_shmem_requests。
 *
 * 【设计思想】把公共逻辑收敛到一个函数,ShmemRequestStructWithOpts()
 * 与 ShmemRequestHash()(及 SLRU 变体)只负责构造不同类别的 options。
 * 与公开入口不同:本函数不拷贝 options,调用方必须保证它分配在
 * TopMemoryContext 且存活到 init/attach 回调执行完——这样
 * ShmemRequestHash() 才能传入扩展过的 ShmemHashOpts(无法只拷基类)。
 *
 * 【参数】
 *   options —— 共享内存区域属性(内部约定:生命周期由调用方负责);
 *   kind    —— 区域类别(SHMEM_KIND_STRUCT/HASH/SLRU),决定后续初始化的
 *               具体方式。
 * 【返回值】无(校验失败直接 ERROR)。
 */
void
ShmemRequestInternal(ShmemStructOpts *options, ShmemRequestKind kind)
{
	ShmemRequest *request;

	/* Check the options */
	if (options->name == NULL)
		elog(ERROR, "shared memory request is missing 'name' option");

	if (IsUnderPostmaster)
	{
		if (options->size <= 0 && options->size != SHMEM_ATTACH_UNKNOWN_SIZE)
			elog(ERROR, "invalid size %zd for shared memory request for \"%s\"",
				 options->size, options->name);
	}
	else
	{
		if (options->size == SHMEM_ATTACH_UNKNOWN_SIZE)
			elog(ERROR, "SHMEM_ATTACH_UNKNOWN_SIZE cannot be used during startup");
		if (options->size <= 0)
			elog(ERROR, "invalid size %zd for shared memory request for \"%s\"",
				 options->size, options->name);
	}

	if (options->alignment != 0 && pg_nextpower2_size_t(options->alignment) != options->alignment)
		elog(ERROR, "invalid alignment %zu for shared memory request for \"%s\"",
			 options->alignment, options->name);

	/* Check that we're in the right state */
	if (shmem_request_state != SRS_REQUESTING)
		elog(ERROR, "ShmemRequestStruct can only be called from a shmem_request callback");

	/* Check that it's not already registered in this process */
	foreach_ptr(ShmemRequest, existing, pending_shmem_requests)
	{
		if (strcmp(existing->options->name, options->name) == 0)
			ereport(ERROR,
					(errmsg("shared memory struct \"%s\" is already registered",
							options->name)));
	}

	/* Request looks valid, remember it */
	request = palloc(sizeof(ShmemRequest));
	request->options = options;
	request->kind = kind;
	pending_shmem_requests = lappend(pending_shmem_requests, request);
}

/*
 *	ShmemGetRequestedSize() --- estimate the total size of all registered shared
 *                              memory structures.
 *
 * This is called at postmaster startup, before the shared memory segment has
 * been created.
 */
/*
 * ShmemGetRequestedSize - (中文)估算所有已登记共享内存需求的总大小
 *
 * 【作用】postmaster 创建共享内存段之前调用,汇总两部分:1) ShmemIndex
 * 索引表自身的估算大小(条目数 = 已登记需求数 + SHMEM_INDEX_ADDITIONAL_SIZE
 * 预留),并取整到缓存行;2) 每个登记项按其对齐要求向上取整后的字节数
 * (对齐小于缓存行时按缓存行算)。返回总字节数,供创建共享内存段用。
 *
 * 【设计思想】此处"对齐摊派"的计算必须与 ShmemAllocRaw() 实际分配时的
 * 行为严格一致(同样:小于缓存行的对齐按缓存行处理),否则会出现"按预算
 * 创建的段装不下实际分配"的偏差。ShmemIndex 的大小此处只是与
 * InitShmemAllocator() 里 hash_estimate_size 相同的估算,两处算法一致,
 * 实际分配以 InitShmemAllocator 为准。
 *
 * 【参数】无。
 * 【返回值】创建共享内存段所需的总字节数。
 */
size_t
ShmemGetRequestedSize(void)
{
	size_t		size;

	/* memory needed for the ShmemIndex */
	size = hash_estimate_size(list_length(pending_shmem_requests) + SHMEM_INDEX_ADDITIONAL_SIZE,
							  sizeof(ShmemIndexEnt));
	size = CACHELINEALIGN(size);

	/* memory needed for all the requested areas */
	foreach_ptr(ShmemRequest, request, pending_shmem_requests)
	{
		size_t		alignment = request->options->alignment;

		/* pad the start address for alignment like ShmemAllocRaw() does */
		if (alignment < PG_CACHE_LINE_SIZE)
			alignment = PG_CACHE_LINE_SIZE;
		size = TYPEALIGN(alignment, size);

		size = add_size(size, request->options->size);
	}

	return size;
}

/*
 *	ShmemInitRequested() --- allocate and initialize requested shared memory
 *                            structures.
 *
 * This is called once at postmaster startup, after the shared memory segment
 * has been created.
 */
/*
 * ShmemInitRequested - (中文)初始化所有已登记的共享内存区域(postmaster 启动阶段)
 *
 * 【作用】共享内存段创建完成后调用(仅 postmaster 或单机后端,不允许
 * 子进程调用):对每个登记项调用 InitShmemIndexEntry() 真正切分内存并把
 * 结果写入 ShmemIndex,然后释放临时 options 与登记列表;最后依次调用
 * 每个子系统回调的 init_fn 完成各自的初始化。
 *
 * 【设计思想】采用"先全部切分、全部入索引,再统一调用 init_fn"的顺序
 * 而非边切边 init:这样所有区域的指针先全部就位,任何 init_fn 里都可以
 * 引用其他子系统的共享区域。此时尚无并发进程,因此全程不需要加锁
 * (代码注释也说明了这一点)。执行完毕后状态机转入 SRS_DONE。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
ShmemInitRequested(void)
{
	/* should be called only by the postmaster or a standalone backend */
	Assert(!IsUnderPostmaster);
	Assert(shmem_request_state == SRS_INITIALIZING);

	/*
	 * Initialize the ShmemIndex entries and perform basic initialization of
	 * all the requested memory areas.  There are no concurrent processes yet,
	 * so no need for locking.
	 */
	foreach_ptr(ShmemRequest, request, pending_shmem_requests)
	{
		InitShmemIndexEntry(request);
		pfree(request->options);
	}
	list_free_deep(pending_shmem_requests);
	pending_shmem_requests = NIL;

	/*
	 * Call the subsystem-specific init callbacks to finish initialization of
	 * all the areas.
	 */
	foreach_ptr(const ShmemCallbacks, callbacks, registered_shmem_callbacks)
	{
		if (callbacks->init_fn)
			callbacks->init_fn(callbacks->opaque_arg);
	}

	shmem_request_state = SRS_DONE;
}

/*
 * Re-establish process private state related to shmem areas.
 *
 * This is called at backend startup in EXEC_BACKEND mode, in every backend.
 */
/*
 * ShmemAttachRequested - (中文)(EXEC_BACKEND 模式)子进程启动时重新"附着"共享内存区域
 *
 * 【作用】仅在 EXEC_BACKEND 编译模式下调用:子进程经 exec 重新启动、
 * 无法通过 fork() 继承 postmaster 的指针变量,因此在重新执行过 request
 * 回调(SRS_REQUESTING)之后,到 ShmemIndex 里逐个查找每个登记区域,
 * 把指针变量重新指向共享内存中的位置,再调用各子系统的 attach_fn。
 *
 * 【设计思想】与 postmaster 的 ShmemInitRequested() 对称:那边"创建",
 * 这边"附着",绝不改动已分配区域的内容。整个附着过程持有
 * ShmemIndexLock 的共享锁,防止并发登记/分配;attach_fn 也在锁内执行,
 * 因此 attach_fn 必须足够轻量、不能再请求共享内存(请求分配需要独占
 * 锁,会与这里冲突/死锁)。
 *
 * 【参数】无。
 * 【返回值】无。
 */
#ifdef EXEC_BACKEND
void
ShmemAttachRequested(void)
{
	ListCell   *lc;

	/* Must be initializing a (non-standalone) backend */
	Assert(IsUnderPostmaster);
	Assert(ShmemAllocator->index != NULL);
	Assert(shmem_request_state == SRS_REQUESTING);
	shmem_request_state = SRS_ATTACHING;

	LWLockAcquire(ShmemIndexLock, LW_SHARED);

	/*
	 * Attach to all the requested memory areas.
	 */
	foreach_ptr(ShmemRequest, request, pending_shmem_requests)
	{
		AttachShmemIndexEntry(request, false);
		pfree(request->options);
	}
	list_free_deep(pending_shmem_requests);
	pending_shmem_requests = NIL;

	/* Call attach callbacks */
	foreach(lc, registered_shmem_callbacks)
	{
		const ShmemCallbacks *callbacks = (const ShmemCallbacks *) lfirst(lc);

		if (callbacks->attach_fn)
			callbacks->attach_fn(callbacks->opaque_arg);
	}

	LWLockRelease(ShmemIndexLock);

	shmem_request_state = SRS_DONE;
}
#endif

/*
 * Insert requested shmem area into the shared memory index and initialize it.
 *
 * Note that this only does performs basic initialization depending on
 * ShmemRequestKind, like setting the global pointer variable to the area for
 * SHMEM_KIND_STRUCT or setting up the backend-private HTAB control struct.
 * This does *not* call the subsystem-specific init callbacks.  That's done
 * later after all the shmem areas have been initialized or attached to.
 */
/*
 * InitShmemIndexEntry - (中文)把登记的共享内存区域实际分配出来并登记进 ShmemIndex
 *
 * 【作用】在 ShmemIndex 里插入名字条目,用 ShmemAllocRaw() 切出所需
 * 内存,把 (size、allocated_size、location) 填进条目;再按区域类别做
 * 基础初始化:SHMEM_KIND_STRUCT 把地址写入调用者的全局指针变量;
 * SHMEM_KIND_HASH 在共享内存里原地建立哈希表控制结构;SHMEM_KIND_SLRU
 * 建立 SLRU 缓冲区的控制块。
 *
 * 【设计思想】"基础初始化"与"子系统 init 回调"刻意分离:本函数只做与
 * 分配方式/区域类别强相关的事;所有区域就位后,ShmemInitRequested() 才
 * 统一调用子系统回调去做那些依赖其他区域的操作。分配失败时先移除刚
 * 插入的索引条目再抛错,避免共享内存里留下"半死"条目(占着名字和空间)。
 *
 * 【参数】request —— 登记项(含 options 属性与类别 kind)。
 * 【返回值】无(失败直接 ERROR)。
 */
static void
InitShmemIndexEntry(ShmemRequest *request)
{
	const char *name = request->options->name;
	ShmemIndexEnt *index_entry;
	bool		found;
	size_t		allocated_size;
	void	   *structPtr;

	/* look it up in the shmem index */
	index_entry = (ShmemIndexEnt *)
		hash_search(ShmemIndex, name, HASH_ENTER_NULL, &found);
	if (found)
		elog(ERROR, "shared memory struct \"%s\" is already initialized", name);
	if (!index_entry)
	{
		/* tried to add it to the hash table, but there was no space */
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("could not create ShmemIndex entry for data structure \"%s\"",
						name)));
	}

	/*
	 * We inserted the entry to the shared memory index.  Allocate requested
	 * amount of shared memory for it, and initialize the index entry.
	 */
	structPtr = ShmemAllocRaw(request->options->size,
							  request->options->alignment,
							  &allocated_size);
	if (structPtr == NULL)
	{
		/* out of memory; remove the failed ShmemIndex entry */
		hash_search(ShmemIndex, name, HASH_REMOVE, NULL);
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("not enough shared memory for data structure"
						" \"%s\" (%zd bytes requested)",
						name, request->options->size)));
	}
	index_entry->size = request->options->size;
	index_entry->allocated_size = allocated_size;
	index_entry->location = structPtr;

	/* Initialize depending on the kind of shmem area it is */
	switch (request->kind)
	{
		case SHMEM_KIND_STRUCT:
			if (request->options->ptr)
				*(request->options->ptr) = index_entry->location;
			break;
		case SHMEM_KIND_HASH:
			shmem_hash_init(structPtr, request->options);
			break;
		case SHMEM_KIND_SLRU:
			shmem_slru_init(structPtr, request->options);
			break;
	}
}

/*
 * Look up a named shmem area in the shared memory index and attach to it.
 *
 * Note that this only performs the basic attachment actions depending on
 * ShmemRequestKind, like setting the global pointer variable to the area for
 * SHMEM_KIND_STRUCT or setting up the backend-private HTAB control struct.
 * This does *not* call the subsystem-specific attach callbacks.  That's done
 * later after all the shmem areas have been initialized or attached to.
 */
/*
 * AttachShmemIndexEntry - (中文)按名在 ShmemIndex 中查找共享内存区域并"附着"(恢复指针)
 *
 * 【作用】子进程(EXEC_BACKEND)或运行期扩展"附着"一个已存在的命名区域:
 * 在 ShmemIndex 里按名字查找;若不存在:missing_ok 为 true 时返回 false
 * 由调用方自行处理,否则报错。若找到,先校验请求的 size 与索引中记录的
 * 大小一致(SHMEM_ATTACH_UNKNOWN_SIZE 表示跳过校验),再按区域类别恢复
 * 本进程的指针/控制结构(STRUCT 赋指针、HASH 建本地控制结构、SLRU 同理)。
 *
 * 【设计思想】与 InitShmemIndexEntry 完全对称(查找 vs 插入),同样只做
 * "类别相关的基础附着",子系统级 attach_fn 由调用方随后统一执行。大小
 * 校验防止"两个进程用不同大小附着同一个名字"造成越界读写。
 *
 * 【参数】
 *   request   —— 登记项(含 options 属性与类别 kind);
 *   missing_ok —— true 时允许区域不存在(返回 false),false 时不存在即报错。
 * 【返回值】true 表示找到并附着成功;false 表示区域不存在(仅 missing_ok
 * 时会出现)。
 */
static bool
AttachShmemIndexEntry(ShmemRequest *request, bool missing_ok)
{
	const char *name = request->options->name;
	ShmemIndexEnt *index_entry;

	/* Look it up in the shmem index */
	index_entry = (ShmemIndexEnt *)
		hash_search(ShmemIndex, name, HASH_FIND, NULL);
	if (!index_entry)
	{
		if (!missing_ok)
			ereport(ERROR,
					(errmsg("could not find ShmemIndex entry for data structure \"%s\"",
							request->options->name)));
		return false;
	}

	/* Check that the size in the index matches the request */
	if (index_entry->size != request->options->size &&
		request->options->size != SHMEM_ATTACH_UNKNOWN_SIZE)
	{
		ereport(ERROR,
				(errmsg("shared memory struct \"%s\" was created with"
						" different size: existing %zu, requested %zd",
						name, index_entry->size, request->options->size)));
	}

	/*
	 * Re-establish the caller's pointer variable, or do other actions to
	 * attach depending on the kind of shmem area it is.
	 */
	switch (request->kind)
	{
		case SHMEM_KIND_STRUCT:
			if (request->options->ptr)
				*(request->options->ptr) = index_entry->location;
			break;
		case SHMEM_KIND_HASH:
			shmem_hash_attach(index_entry->location, request->options);
			break;
		case SHMEM_KIND_SLRU:
			shmem_slru_attach(index_entry->location, request->options);
			break;
	}

	return true;
}

/*
 *	InitShmemAllocator() --- set up basic pointers to shared memory.
 *
 * Called at postmaster or stand-alone backend startup, to initialize the
 * allocator's data structure in the shared memory segment.  In EXEC_BACKEND,
 * this is also called at backend startup, to set up pointers to the
 * already-initialized data structure.
 */
/*
 * InitShmemAllocator - (中文)建立共享内存分配器的基本指针与 ShmemIndex 索引表
 *
 * 【作用】postmaster(或单机后端)启动时:1) 定位 ShmemAllocatorData(它
 * 位于段头 content_offset 处),初始化其自旋锁与 free_offset(首个分配
 * 起点对齐到缓存行);2) 设置 ShmemSegHdr/ShmemBase/ShmemEnd 三个全局
 * 指针;3) 在共享内存里创建 ShmemIndex 哈希表,并把"ShmemIndex 自身"
 * 也登记进索引,使 pg_shmem_allocations 视图能看到它。EXEC_BACKEND 下
 * 子进程也调用本函数,但只重设指针、附着已有的分配器与索引表,绝不
 * 重新初始化它们。
 *
 * 【设计思想】ShmemIndex 本身也放在共享内存,存在"分配器初始化需要
 * 索引表、索引表分配又依赖分配器"的循环依赖。解法是:先用
 * hash_estimate_size 手工算出索引表大小,直接用 ShmemAlloc() 切一块
 * 原始空间,再调用 shmem_hash_create() 在其上原地建表(所以注释明确
 * 说明这里不能用依赖 ShmemIndex 的 ShmemInitHash())。首条分配对齐到
 * 缓存行,保证此后所有 ShmemAlloc 分配都从缓存行边界开始。
 *
 * 【参数】seghdr —— 共享内存段头(PGShmemHeader),内含 content_offset
 * (分配器头的位置)与 totalsize(段总大小)。
 * 【返回值】无(失败直接 ERROR)。
 */
void
InitShmemAllocator(PGShmemHeader *seghdr)
{
	Size		offset;
	int64		hash_nelems;
	HASHCTL		info;
	int			hash_flags;

#ifndef EXEC_BACKEND
	Assert(!IsUnderPostmaster);
#endif
	Assert(seghdr != NULL);

	if (IsUnderPostmaster)
	{
		Assert(shmem_request_state == SRS_INITIAL);
	}
	else
	{
		Assert(shmem_request_state == SRS_REQUESTING);
		shmem_request_state = SRS_INITIALIZING;
	}

	/*
	 * We assume the pointer and offset are MAXALIGN.  Not a hard requirement,
	 * but it's true today and keeps the math below simpler.
	 */
	Assert(seghdr == (void *) MAXALIGN(seghdr));
	Assert(seghdr->content_offset == MAXALIGN(seghdr->content_offset));

	/*
	 * Allocations after this point should go through ShmemAlloc, which
	 * expects to allocate everything on cache line boundaries.  Make sure the
	 * first allocation begins on a cache line boundary.
	 */
	offset = CACHELINEALIGN(seghdr->content_offset + sizeof(ShmemAllocatorData));
	if (offset > seghdr->totalsize)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory (%zu bytes requested)",
						offset)));

	/*
	 * In postmaster or stand-alone backend, initialize the shared memory
	 * allocator so that we can allocate shared memory for ShmemIndex using
	 * ShmemAlloc().  In a regular backend just set up the pointers required
	 * by ShmemAlloc().
	 */
	ShmemAllocator = (ShmemAllocatorData *) ((char *) seghdr + seghdr->content_offset);
	if (!IsUnderPostmaster)
	{
		SpinLockInit(&ShmemAllocator->shmem_lock);
		ShmemAllocator->free_offset = offset;
		LWLockInitialize(&ShmemAllocator->index_lock, LWTRANCHE_SHMEM_INDEX);
	}

	ShmemSegHdr = seghdr;
	ShmemBase = seghdr;
	ShmemEnd = (char *) ShmemBase + seghdr->totalsize;

	/*
	 * Create (or attach to) the shared memory index of shmem areas.
	 *
	 * This is the same initialization as ShmemInitHash() does, but we cannot
	 * use ShmemInitHash() here because it relies on ShmemIndex being already
	 * initialized.
	 */
	hash_nelems = list_length(pending_shmem_requests) + SHMEM_INDEX_ADDITIONAL_SIZE;

	info.keysize = SHMEM_INDEX_KEYSIZE;
	info.entrysize = sizeof(ShmemIndexEnt);
	hash_flags = HASH_ELEM | HASH_STRINGS | HASH_FIXED_SIZE;

	if (!IsUnderPostmaster)
	{
		ShmemAllocator->index_size = hash_estimate_size(hash_nelems, info.entrysize);
		ShmemAllocator->index = (HASHHDR *) ShmemAlloc(ShmemAllocator->index_size);
	}
	ShmemIndex = shmem_hash_create(ShmemAllocator->index,
								   ShmemAllocator->index_size,
								   IsUnderPostmaster,
								   "ShmemIndex", hash_nelems,
								   &info, hash_flags);
	Assert(ShmemIndex != NULL);

	/*
	 * Add an entry for ShmemIndex itself into ShmemIndex, so that it's
	 * visible in the pg_shmem_allocations view
	 */
	if (!IsUnderPostmaster)
	{
		bool		found;
		ShmemIndexEnt *result = (ShmemIndexEnt *)
			hash_search(ShmemIndex, "ShmemIndex", HASH_ENTER, &found);

		Assert(!found);
		result->size = ShmemAllocator->index_size;
		result->allocated_size = ShmemAllocator->index_size;
		result->location = ShmemAllocator->index;
	}
}

/*
 * Reset state on postmaster crash restart.
 */
/*
 * ResetShmemAllocator - (中文)postmaster 崩溃重启时重置共享内存分配器的进程内状态
 *
 * 【作用】postmaster 因子进程崩溃进入重启流程后调用:把状态机打回
 * SRS_INITIAL、清空待处理需求列表,使下一次启动能重新执行一遍完整的
 * request → create → init 流程。
 *
 * 【设计思想】刻意不清空 registered_shmem_callbacks:重启后还要再次
 * 调用这些回调,而 postmaster 是同一个进程,回调函数指针依然有效。
 * 共享内存段本身由操作系统层在旧段基础上重建,不在此处理。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
ResetShmemAllocator(void)
{
	Assert(!IsUnderPostmaster);
	shmem_request_state = SRS_INITIAL;

	pending_shmem_requests = NIL;

	/*
	 * Note that we don't clear the registered callbacks.  We will need to
	 * call them again as we restart
	 */
}

/*
 * ShmemAlloc -- allocate max-aligned chunk from shared memory
 *
 * Throws error if request cannot be satisfied.
 *
 * Assumes ShmemSegHdr is initialized.
 */
/*
 * ShmemAlloc - (中文)从共享内存分配一个按缓存行对齐的块(空间不足即报错)
 *
 * 【作用】传统共享内存分配入口:切出一块至少 size 字节、起始地址按
 * 缓存行对齐的内存。空间不足时抛出 "out of shared memory" 错误。
 *
 * 【设计思想】整个分配过程只持一把自旋锁(仅保护 free_offset 的
 * 读-改-写),开销极小,适合高频小分配;共享内存分配一旦完成就永不
 * 释放(没有对应的 free 接口),所以分配器只需一个"空闲偏移量"指针,
 * 不需要空闲链表。缓存行对齐是为了避免关键数据结构被拆到两行缓存上,
 * 引发无谓的 cache-line 争用(详见 ShmemAllocRaw 的注释)。
 *
 * 【参数】size —— 请求的字节数(必须 > 0)。
 * 【返回值】新分配区域的起始地址(非空);空间不足时 ERROR,不会返回 NULL。
 */
void *
ShmemAlloc(Size size)
{
	void	   *newSpace;
	Size		allocated_size;

	newSpace = ShmemAllocRaw(size, 0, &allocated_size);
	if (!newSpace)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory (%zu bytes requested)",
						size)));
	return newSpace;
}

/*
 * ShmemAllocNoError -- allocate max-aligned chunk from shared memory
 *
 * As ShmemAlloc, but returns NULL if out of space, rather than erroring.
 */
/*
 * ShmemAllocNoError - (中文)共享内存分配,空间不足时返回 NULL 而非报错
 *
 * 【作用】与 ShmemAlloc 语义相同,但空间不足时返回 NULL,由调用方自行
 * 处理失败路径(例如"能省则省"的运行期扩展分配)。
 *
 * 【设计思想】两者都委托 ShmemAllocRaw()(alignment 传 0 = 使用默认的
 * 缓存行对齐),只把"失败策略"的差异放在外层包装上,避免重复实现。
 *
 * 【参数】size —— 请求的字节数(必须 > 0)。
 * 【返回值】分配到的区域指针;空间不足时 NULL。
 */
void *
ShmemAllocNoError(Size size)
{
	Size		allocated_size;

	return ShmemAllocRaw(size, 0, &allocated_size);
}

/*
 * ShmemAllocRaw -- allocate align chunk and return allocated size
 *
 * Also sets *allocated_size to the number of bytes allocated, which will
 * be equal to the number requested plus any padding we choose to add.
 */
/*
 * ShmemAllocRaw - (中文)共享内存分配的内部实现:可指定对齐,并回传实际占用字节数
 *
 * 【作用】在自旋锁保护下读取空闲偏移量,按 alignment 向上对齐(小于
 * 缓存行大小则按缓存行对齐),若能容纳 size 字节则推进空闲偏移量并返回
 * 地址,否则返回 NULL;同时通过 allocated_size 回传"本次实际占用的字节
 * 数"(含对齐填充)。
 *
 * 【设计思想】把对齐填充计入 allocated_size 是给 ShmemIndex 记账用:
 * pg_shmem_allocations 视图需要知道一块区域真实吃掉多少空间。所有分配
 * 至少按缓存行对齐,避免关键结构横跨两条缓存行(经验表明 MAXALIGN 在
 * 现代 CPU 上已不够,见上方原注释)。锁内不调用任何可能阻塞的代码,保证
 * 分配 O(1)、可被任意进程并发执行。注意:对齐只在"当前空闲偏移量"上
 * 计算,前一条分配的尾部与本次分配的头部之间会残留填充洞,这是"只分配
 * 不释放"分配器的固有取舍。
 *
 * 【参数】
 *   size           —— 请求字节数(>0);
 *   alignment      —— 起始地址对齐要求(0 表示采用缓存行对齐;非 0 必须
 *                     是 2 的幂);
 *   allocated_size —— 输出参数:实际占用字节数(请求字节数 + 对齐填充)。
 * 【返回值】分配区域起始地址;空间不足时返回 NULL(此时 allocated_size
 * 依然被赋值)。
 */
static void *
ShmemAllocRaw(Size size, Size alignment, Size *allocated_size)
{
	Size		rawStart;
	Size		newStart;
	Size		newFree;
	void	   *newSpace;

	/*
	 * Ensure all space is adequately aligned.  We used to only MAXALIGN this
	 * space but experience has proved that on modern systems that is not good
	 * enough.  Many parts of the system are very sensitive to critical data
	 * structures getting split across cache line boundaries.  To avoid that,
	 * attempt to align the beginning of the allocation to a cache line
	 * boundary.  The calling code will still need to be careful about how it
	 * uses the allocated space - e.g. by padding each element in an array of
	 * structures out to a power-of-two size - but without this, even that
	 * won't be sufficient.
	 */
	if (alignment < PG_CACHE_LINE_SIZE)
		alignment = PG_CACHE_LINE_SIZE;

	Assert(ShmemSegHdr != NULL);

	SpinLockAcquire(&ShmemAllocator->shmem_lock);

	rawStart = ShmemAllocator->free_offset;
	newStart = TYPEALIGN(alignment, rawStart);

	newFree = newStart + size;
	if (newFree <= ShmemSegHdr->totalsize)
	{
		newSpace = (char *) ShmemBase + newStart;
		ShmemAllocator->free_offset = newFree;
	}
	else
		newSpace = NULL;

	SpinLockRelease(&ShmemAllocator->shmem_lock);

	/* note this assert is okay with newSpace == NULL */
	Assert(newSpace == (void *) TYPEALIGN(alignment, newSpace));

	*allocated_size = newFree - rawStart;
	return newSpace;
}

/*
 * ShmemAddrIsValid -- test if an address refers to shared memory
 *
 * Returns true if the pointer points within the shared memory segment.
 */
/*
 * ShmemAddrIsValid - (中文)判断一个地址是否位于共享内存段内
 *
 * 【作用】检测指针是否落在 [ShmemBase, ShmemEnd) 区间。典型用途:判断
 * 某个指针来自共享内存还是本进程私有内存(例如判断指针是否需要做
 * 与段基址相关的换算)。
 *
 * 【设计思想】传统共享内存在所有进程中映射到相同的地址范围,因此用
 * 区间比较即可完成判断;前提是 ShmemBase/ShmemEnd 已由
 * InitShmemAllocator() 设置。
 *
 * 【参数】addr —— 待测指针。
 * 【返回值】地址在段内返回 true,否则 false。
 */
bool
ShmemAddrIsValid(const void *addr)
{
	return (addr >= ShmemBase) && (addr < ShmemEnd);
}

/*
 * Register callbacks that define a shared memory area (or multiple areas).
 *
 * The system will call the callbacks at different stages of postmaster or
 * backend startup, to allocate and initialize the area.
 *
 * This is normally called early during postmaster startup, but if the
 * SHMEM_CALLBACKS_ALLOW_AFTER_STARTUP is set, this can also be used after
 * startup, although after startup there's no guarantee that there's enough
 * shared memory available.  When called after startup, this immediately calls
 * the right callbacks depending on whether another backend had already
 * initialized the area.
 *
 * Note: In EXEC_BACKEND mode, this needs to be called in every backend
 * process.  That's needed because we cannot pass down the callback function
 * pointers from the postmaster process, because different processes may have
 * loaded libraries to different addresses.
 */
/*
 * RegisterShmemCallbacks - (中文)登记一组"定义共享内存区域"的生命周期回调
 *
 * 【作用】子系统在启动早期(或扩展在 _PG_init() 中)调用,把 request_fn /
 * init_fn / attach_fn 等回调登记进 registered_shmem_callbacks 列表,系统
 * 会在启动的各阶段自动调用它们。若在启动完成(SRS_DONE)之后调用,则要求
 * 回调带 SHMEM_CALLBACKS_ALLOW_AFTER_STARTUP 标志,并立即走
 * CallShmemCallbacksAfterStartup():其他进程已初始化这些区域就"附着"、
 * 否则"新建",不用等永远不会再来的启动流程。
 *
 * 【设计思想】EXEC_BACKEND 模式下每个进程都必须调用本函数:不同进程
 * 加载的扩展可能落在不同的地址,postmaster 里的函数指针无法原样传给
 * 子进程,只能由子进程自己重新登记。
 *
 * 【参数】callbacks —— 指向(通常是静态的)ShmemCallbacks 结构,内含各
 * 阶段回调函数指针与 opaque_arg。
 * 【返回值】无。
 */
void
RegisterShmemCallbacks(const ShmemCallbacks *callbacks)
{
	if (shmem_request_state == SRS_DONE && IsUnderPostmaster)
	{
		/*
		 * After-startup initialization or attachment.  Call the appropriate
		 * callbacks immediately.
		 */
		if ((callbacks->flags & SHMEM_CALLBACKS_ALLOW_AFTER_STARTUP) == 0)
			elog(ERROR, "cannot request shared memory at this time");

		CallShmemCallbacksAfterStartup(callbacks);
	}
	else
	{
		/* Remember the callbacks for later */
		registered_shmem_callbacks = lappend(registered_shmem_callbacks,
											 (void *) callbacks);
	}
}

/*
 * Register a shmem area (or multiple areas) after startup.
 */
/*
 * CallShmemCallbacksAfterStartup - (中文)启动完成后立即执行一组 shmem 回调
 *
 * 【作用】RegisterShmemCallbacks() 在 SRS_DONE 之后被调用时的执行路径:
 * 状态机临时进入 SRS_REQUESTING,调用 request_fn 收集登记项;然后持有
 * ShmemIndexLock 独占锁:先检查登记的各区域"全部已存在"还是"全部不
 * 存在"(两者混合即报错——一个回调登记的多个区域必须同进退,否则无法
 * 决定之后该调 init_fn 还是 attach_fn);随后逐个 AttachShmemIndexEntry()
 * (已存在)或 InitShmemIndexEntry()(不存在);最后调用对应的 attach_fn
 * 或 init_fn 收尾。
 *
 * 【设计思想】运行期分配共享内存是有风险的操作(段内可能已无空闲),所以
 * 只允许显式声明 SHMEM_CALLBACKS_ALLOW_AFTER_STARTUP 的扩展使用,且要求
 * 其登记的区块构成一个"自洽单元"(要么全在、要么全不在),避免歧义。
 *
 * 【参数】callbacks —— 要执行的回调组。
 * 【返回值】无(状态机保证最终回到 SRS_DONE)。
 */
static void
CallShmemCallbacksAfterStartup(const ShmemCallbacks *callbacks)
{
	bool		found_any;
	bool		notfound_any;

	Assert(shmem_request_state == SRS_DONE);
	shmem_request_state = SRS_REQUESTING;

	/*
	 * Call the request callback first.  The callback makes ShmemRequest*()
	 * calls for each shmem area, adding them to pending_shmem_requests.
	 */
	Assert(pending_shmem_requests == NIL);
	if (callbacks->request_fn)
		callbacks->request_fn(callbacks->opaque_arg);
	shmem_request_state = SRS_AFTER_STARTUP_ATTACH_OR_INIT;

	if (pending_shmem_requests == NIL)
	{
		shmem_request_state = SRS_DONE;
		return;
	}

	/*
	 * Hold ShmemIndexLock while we allocate all the shmem entries and run all
	 * the initializers.
	 */
	LWLockAcquire(ShmemIndexLock, LW_EXCLUSIVE);

	/*
	 * Check if the requested shared memory areas have already been
	 * initialized.  We assume all the areas requested by the request callback
	 * to form a coherent unit such that they're all already initialized or
	 * none.  Otherwise it would be ambiguous which callback, init or attach,
	 * to callback afterwards.
	 */
	found_any = notfound_any = false;
	foreach_ptr(ShmemRequest, request, pending_shmem_requests)
	{
		if (hash_search(ShmemIndex, request->options->name, HASH_FIND, NULL))
			found_any = true;
		else
			notfound_any = true;
	}
	if (found_any && notfound_any)
		elog(ERROR, "some of the requested shmem areas have already been initialized");

	/*
	 * Allocate or attach all the shmem areas requested by the request_fn
	 * callback.
	 */
	foreach_ptr(ShmemRequest, request, pending_shmem_requests)
	{
		if (found_any)
			AttachShmemIndexEntry(request, false);
		else
			InitShmemIndexEntry(request);

		pfree(request->options);
	}
	list_free_deep(pending_shmem_requests);
	pending_shmem_requests = NIL;

	/* Finish by calling the appropriate subsystem-specific callback */
	if (found_any)
	{
		if (callbacks->attach_fn)
			callbacks->attach_fn(callbacks->opaque_arg);
	}
	else
	{
		if (callbacks->init_fn)
			callbacks->init_fn(callbacks->opaque_arg);
	}

	LWLockRelease(ShmemIndexLock);
	shmem_request_state = SRS_DONE;
}

/*
 * Call all shmem request callbacks.
 */
/*
 * ShmemCallRequestCallbacks - (中文)调用所有已登记回调的 request_fn(收集共享内存需求)
 *
 * 【作用】postmaster 启动早期调用:状态机由 SRS_INITIAL 进入 SRS_REQUESTING
 * 后,依次调用每个已登记回调的 request_fn,让各子系统通过
 * ShmemRequest*() 把各自的共享内存需求登记进 pending_shmem_requests。
 *
 * 【设计思想】"先全部收集、后统一分配"的两段式设计,使总需求在真正分配
 * 之前完全确定,ShmemGetRequestedSize() 才能算出精确的段大小;request_fn
 * 里严禁调用任何与分配有关的东西,只能登记需求。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
ShmemCallRequestCallbacks(void)
{
	ListCell   *lc;

	Assert(shmem_request_state == SRS_INITIAL);
	shmem_request_state = SRS_REQUESTING;

	foreach(lc, registered_shmem_callbacks)
	{
		const ShmemCallbacks *callbacks = (const ShmemCallbacks *) lfirst(lc);

		if (callbacks->request_fn)
			callbacks->request_fn(callbacks->opaque_arg);
	}
}

/*
 * ShmemInitStruct -- Create/attach to a structure in shared memory.
 *
 *		This is called during initialization to find or allocate
 *		a data structure in shared memory.  If no other process
 *		has created the structure, this routine allocates space
 *		for it.  If it exists already, a pointer to the existing
 *		structure is returned.
 *
 *	Returns: pointer to the object.  *foundPtr is set true if the object was
 *		already in the shmem index (hence, already initialized).
 *
 * Note: This is a legacy interface, kept for backwards compatibility with
 * extensions.  Use ShmemRequestStruct() in new code!
 */
/*
 * ShmemInitStruct - (中文)[遗留接口]创建或附着到一个命名的共享内存结构
 *
 * 【作用】按名字在共享内存中查找一个结构:若其他进程已创建,返回已有
 * 指针并置 *foundPtr = true;否则新建并置 *foundPtr = false,调用方必须
 * 根据 foundPtr 决定是否初始化结构内容。新代码应使用
 * ShmemRequestStruct(),本函数仅为兼容旧扩展而保留。
 *
 * 【设计思想】foundPtr 直接承载"首次初始化"语义:只有创建者
 * (foundPtr == false)需要填充内容,附着者直接使用。整个查找/创建过程在
 * ShmemIndexLock 独占锁内原子完成,防止两个进程同时创建同一个名字的
 * 区域(那样会双双返回同一块内存、互相覆盖初始化)。
 *
 * 【参数】
 *   name     —— 结构名(最长 SHMEM_INDEX_KEYSIZE);
 *   size     —— 请求字节数(>0);
 *   foundPtr —— 输出参数:true 表示区域已存在(无需初始化)。
 * 【返回值】共享内存中该结构的指针(永不为 NULL,失败即 ERROR)。
 */
void *
ShmemInitStruct(const char *name, Size size, bool *foundPtr)
{
	void	   *ptr = NULL;
	ShmemStructOpts options = {
		.name = name,
		.size = size,
		.ptr = &ptr,
	};
	ShmemRequest request = {&options, SHMEM_KIND_STRUCT};

	Assert(shmem_request_state == SRS_DONE ||
		   shmem_request_state == SRS_INITIALIZING ||
		   shmem_request_state == SRS_REQUESTING);

	LWLockAcquire(ShmemIndexLock, LW_EXCLUSIVE);

	/*
	 * During postmaster startup, look up the existing entry if any.
	 */
	*foundPtr = false;
	if (IsUnderPostmaster)
		*foundPtr = AttachShmemIndexEntry(&request, true);

	/* Initialize it if not found */
	if (!*foundPtr)
		InitShmemIndexEntry(&request);

	LWLockRelease(ShmemIndexLock);

	Assert(ptr != NULL);
	return ptr;
}

/* SQL SRF showing allocated shared memory */
/*
 * pg_get_shmem_allocations - (中文)SQL 集合函数:列出共享内存中各命名分配的空间占用
 *
 * 【作用】实现 pg_shmem_allocations 视图:在 ShmemIndexLock 共享锁内遍历
 * ShmemIndex,对每个命名区域输出一行 (名字, 段内偏移, 请求大小, 实际
 * 大小);遍历完后补两行汇总:一行 "<anonymous>" 表示经 ShmemAlloc 直接
 * 分配、未登记名字的空间(总已分配量减去命名部分),一行表示尚未使用的
 * 剩余共享内存。
 *
 * 【设计思想】偏移用 (char*)location - (char*)ShmemSegHdr 计算,便于
 * 各进程输出一致、可直接换算成地址;遍历持共享锁保证索引表不被并发
 * 修改,同时允许其他进程正常只读访问。
 *
 * 【参数】fcinfo —— SRF 调用上下文(结果经 rsinfo 以物化 tuplestore
 * 返回)。
 * 【返回值】Datum 0(行集合通过 tuplestore 返回)。
 */
Datum
pg_get_shmem_allocations(PG_FUNCTION_ARGS)
{
#define PG_GET_SHMEM_SIZES_COLS 4
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	HASH_SEQ_STATUS hstat;
	ShmemIndexEnt *ent;
	Size		named_allocated = 0;
	Datum		values[PG_GET_SHMEM_SIZES_COLS];
	bool		nulls[PG_GET_SHMEM_SIZES_COLS];

	InitMaterializedSRF(fcinfo, 0);

	LWLockAcquire(ShmemIndexLock, LW_SHARED);

	hash_seq_init(&hstat, ShmemIndex);

	/* output all allocated entries */
	memset(nulls, 0, sizeof(nulls));
	while ((ent = (ShmemIndexEnt *) hash_seq_search(&hstat)) != NULL)
	{
		values[0] = CStringGetTextDatum(ent->key);
		values[1] = Int64GetDatum((char *) ent->location - (char *) ShmemSegHdr);
		values[2] = Int64GetDatum(ent->size);
		values[3] = Int64GetDatum(ent->allocated_size);
		named_allocated += ent->allocated_size;

		tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc,
							 values, nulls);
	}

	/* output shared memory allocated but not counted via the shmem index */
	values[0] = CStringGetTextDatum("<anonymous>");
	nulls[1] = true;
	values[2] = Int64GetDatum(ShmemAllocator->free_offset - named_allocated);
	values[3] = values[2];
	tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc, values, nulls);

	/* output as-of-yet unused shared memory */
	nulls[0] = true;
	values[1] = Int64GetDatum(ShmemAllocator->free_offset);
	nulls[1] = false;
	values[2] = Int64GetDatum(ShmemSegHdr->totalsize - ShmemAllocator->free_offset);
	values[3] = values[2];
	tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc, values, nulls);

	LWLockRelease(ShmemIndexLock);

	return (Datum) 0;
}

/*
 * SQL SRF showing NUMA memory nodes for allocated shared memory
 *
 * Compared to pg_get_shmem_allocations(), this function does not return
 * information about shared anonymous allocations and unused shared memory.
 */
/*
 * pg_get_shmem_allocations_numa - (中文)SQL 集合函数:按 NUMA 节点统计各命名分配的内存页分布
 *
 * 【作用】实现 pg_shmem_allocations_numa 视图:对每个命名区域,把其地址
 * 范围折算到 OS 物理页边界(start 向下取整、end 向上取整,保证整页
 * 统计不遗漏),调用 libnuma 查询每页所属的 NUMA 节点,输出 (区域名,
 * 节点号, 该区域落在该节点上的字节数);每种区域还会追加一行"无节点"
 * 统计(-2/ENOENT,如被换出的页)。
 *
 * 【设计思想】NUMA 查询以物理页为单位,而共享内存分配不一定对齐页边界,
 * 所以先做页对齐换算。首次调用时须逐页 touch(见 firstNumaTouch 注释),
 * 否则内核尚未映射的页会返回 -2,统计失真。每次查询页数多、耗时长,
 * 循环中定期 CHECK_FOR_INTERRUPTS 保证可被取消;libnuma 不可用或初始化
 * 失败时直接报错。
 *
 * 【参数】fcinfo —— SRF 调用上下文。
 * 【返回值】Datum 0(行集合通过 tuplestore 返回)。
 */
Datum
pg_get_shmem_allocations_numa(PG_FUNCTION_ARGS)
{
#define PG_GET_SHMEM_NUMA_SIZES_COLS 3
	ReturnSetInfo *rsinfo = (ReturnSetInfo *) fcinfo->resultinfo;
	HASH_SEQ_STATUS hstat;
	ShmemIndexEnt *ent;
	Datum		values[PG_GET_SHMEM_NUMA_SIZES_COLS];
	bool		nulls[PG_GET_SHMEM_NUMA_SIZES_COLS];
	Size		os_page_size;
	void	  **page_ptrs;
	int		   *pages_status;
	uint64		shm_total_page_count,
				shm_ent_page_count,
				max_nodes;
	Size	   *nodes;

	if (pg_numa_init() == -1)
		elog(ERROR, "libnuma initialization failed or NUMA is not supported on this platform");

	InitMaterializedSRF(fcinfo, 0);

	max_nodes = pg_numa_get_max_node();
	nodes = palloc_array(Size, max_nodes + 2);

	/*
	 * Shared memory allocations can vary in size and may not align with OS
	 * memory page boundaries, while NUMA queries work on pages.
	 *
	 * To correctly map each allocation to NUMA nodes, we need to: 1.
	 * Determine the OS memory page size. 2. Align each allocation's start/end
	 * addresses to page boundaries. 3. Query NUMA node information for all
	 * pages spanning the allocation.
	 */
	os_page_size = pg_get_shmem_pagesize();

	/*
	 * Allocate memory for page pointers and status based on total shared
	 * memory size. This simplified approach allocates enough space for all
	 * pages in shared memory rather than calculating the exact requirements
	 * for each segment.
	 *
	 * Add 1, because we don't know how exactly the segments align to OS
	 * pages, so the allocation might use one more memory page. In practice
	 * this is not very likely, and moreover we have more entries, each of
	 * them using only fraction of the total pages.
	 */
	shm_total_page_count = (ShmemSegHdr->totalsize / os_page_size) + 1;
	page_ptrs = palloc0_array(void *, shm_total_page_count);
	pages_status = palloc_array(int, shm_total_page_count);

	if (firstNumaTouch)
		elog(DEBUG1, "NUMA: page-faulting shared memory segments for proper NUMA readouts");

	LWLockAcquire(ShmemIndexLock, LW_SHARED);

	hash_seq_init(&hstat, ShmemIndex);

	/* output all allocated entries */
	while ((ent = (ShmemIndexEnt *) hash_seq_search(&hstat)) != NULL)
	{
		char	   *startptr,
				   *endptr;
		Size		total_len;

		/*
		 * Calculate the range of OS pages used by this segment. The segment
		 * may start / end half-way through a page, we want to count these
		 * pages too. So we align the start/end pointers down/up, and then
		 * calculate the number of pages from that.
		 */
		startptr = (char *) TYPEALIGN_DOWN(os_page_size, ent->location);
		endptr = (char *) TYPEALIGN(os_page_size,
									(char *) ent->location + ent->allocated_size);
		total_len = (endptr - startptr);

		shm_ent_page_count = total_len / os_page_size;

		/*
		 * If we ever get 0xff (-1) back from kernel inquiry, then we probably
		 * have a bug in mapping buffers to OS pages.
		 */
		memset(pages_status, 0xff, sizeof(int) * shm_ent_page_count);

		/*
		 * Setup page_ptrs[] with pointers to all OS pages for this segment,
		 * and get the NUMA status using pg_numa_query_pages.
		 *
		 * In order to get reliable results we also need to touch memory
		 * pages, so that inquiry about NUMA memory node doesn't return -2
		 * (ENOENT, which indicates unmapped/unallocated pages).
		 */
		for (uint64 i = 0; i < shm_ent_page_count; i++)
		{
			page_ptrs[i] = startptr + (i * os_page_size);

			if (firstNumaTouch)
				pg_numa_touch_mem_if_required(page_ptrs[i]);

			CHECK_FOR_INTERRUPTS();
		}

		if (pg_numa_query_pages(0, shm_ent_page_count, page_ptrs, pages_status) == -1)
			elog(ERROR, "failed NUMA pages inquiry status: %m");

		/* Count number of NUMA nodes used for this shared memory entry */
		memset(nodes, 0, sizeof(Size) * (max_nodes + 2));

		for (uint64 i = 0; i < shm_ent_page_count; i++)
		{
			int			s = pages_status[i];

			/* Ensure we are adding only valid index to the array */
			if (s >= 0 && s <= max_nodes)
			{
				/* valid NUMA node */
				nodes[s]++;
				continue;
			}
			else if (s == -2)
			{
				/* -2 means ENOENT (e.g. page was moved to swap) */
				nodes[max_nodes + 1]++;
				continue;
			}

			elog(ERROR, "invalid NUMA node id outside of allowed range "
				 "[0, " UINT64_FORMAT "]: %d", max_nodes, s);
		}

		/* no NULLs for regular nodes */
		memset(nulls, 0, sizeof(nulls));

		/*
		 * Add one entry for each NUMA node, including those without allocated
		 * memory for this segment.
		 */
		for (uint64 i = 0; i <= max_nodes; i++)
		{
			values[0] = CStringGetTextDatum(ent->key);
			values[1] = Int32GetDatum(i);
			values[2] = Int64GetDatum(nodes[i] * os_page_size);

			tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc,
								 values, nulls);
		}

		/* The last entry is used for pages without a NUMA node. */
		nulls[1] = true;
		values[0] = CStringGetTextDatum(ent->key);
		values[2] = Int64GetDatum(nodes[max_nodes + 1] * os_page_size);

		tuplestore_putvalues(rsinfo->setResult, rsinfo->setDesc,
							 values, nulls);
	}

	LWLockRelease(ShmemIndexLock);
	firstNumaTouch = false;

	return (Datum) 0;
}

/*
 * Determine the memory page size used for the shared memory segment.
 *
 * If the shared segment was allocated using huge pages, returns the size of
 * a huge page. Otherwise returns the size of regular memory page.
 *
 * This should be used only after the server is started.
 */
/*
 * pg_get_shmem_pagesize - (中文)返回共享内存段实际使用的 OS 页大小
 *
 * 【作用】供 NUMA 相关代码使用:若服务器以 huge pages 模式运行
 * (huge_pages_status == HUGE_PAGES_ON),返回 huge page 大小,否则返回
 * 普通系统页大小(sysconf / Windows GetSystemInfo)。
 *
 * 【设计思想】NUMA 页级查询必须先知道"共享内存实际用什么页粒度映射",
 * 才能正确折算页数。该值只在服务器启动后才确定(huge_pages_status 此时
 * 才被设置),因此断言 IsUnderPostmaster 且状态已知。
 *
 * 【参数】无。
 * 【返回值】页大小(字节)。
 */
Size
pg_get_shmem_pagesize(void)
{
	Size		os_page_size;
#ifdef WIN32
	SYSTEM_INFO sysinfo;

	GetSystemInfo(&sysinfo);
	os_page_size = sysinfo.dwPageSize;
#else
	os_page_size = sysconf(_SC_PAGESIZE);
#endif

	Assert(IsUnderPostmaster);
	Assert(huge_pages_status != HUGE_PAGES_UNKNOWN);

	if (huge_pages_status == HUGE_PAGES_ON)
		GetHugePageSize(&os_page_size, NULL);

	return os_page_size;
}

/*
 * pg_numa_available - (中文)SQL 函数:报告当前平台/运行时是否支持 NUMA 查询
 *
 * 【作用】返回 pg_numa_init() 是否成功,即系统是否编译且配置了 libnuma
 * 支持。供 SQL 层判断能否使用 pg_shmem_allocations_numa 等 NUMA 功能。
 *
 * 【参数】fcinfo —— 函数调用上下文。
 * 【返回值】bool:支持返回 true,否则 false。
 */
Datum
pg_numa_available(PG_FUNCTION_ARGS)
{
	PG_RETURN_BOOL(pg_numa_init() != -1);
}
