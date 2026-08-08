/*-------------------------------------------------------------------------
 *
 * method_io_uring.c
 *    AIO - perform AIO using Linux' io_uring
 *
 * For now we create one io_uring instance for each backend. These io_uring
 * instances have to be created in postmaster, during startup, to allow other
 * backends to process IO completions, if the issuing backend is currently
 * busy doing other things. Other backends may not use another backend's
 * io_uring instance to submit IO, that'd require additional locking that
 * would likely be harmful for performance.
 *
 * We likely will want to introduce a backend-local io_uring instance in the
 * future, e.g. for FE/BE network IO.
 *
 * 【模块总览(中文)】
 * 本文件实现 io_method=io_uring 的 AIO 方法:使用 Linux io_uring(内核
 * 5.1+ 的异步 I/O 接口)真正把 I/O 交给内核异步执行。与 worker 方法
 * 相比,io_uring 在本进程内完成提交与收割,省去进程间切换,延迟与
 * CPU 开销更低。
 *
 * 【核心架构】
 * - 每后端一个 io_uring 实例(ring):pg_get_aios 视角下,ring 的
 *   所有权属于"发起 IO 的后端",但任何后端都可以替它收割完成事件
 *   (这解决了"发起者阻塞时没人处理完成"的死锁问题,见 README)。
 *   为保证安全,每个 ring 配一把 completion_lock(轻量锁):任意时刻
 *   只有一个后端在收割该 ring;
 * - ring 在 postmaster 启动阶段创建(init),内存尽量放进共享内存
 *   (kernel 6.5+ 的 IORING_SETUP_NO_MMAP + io_uring_queue_init_mem,
 *   避免每进程大量 mmap 映射),否则由内核为每个 ring 单独建映射;
 * - 提交:pgaio_uring_submit() 把一批句柄翻译成 SQE(prep_readv/
 *   prep_writev,单段时退化为 prep_read/write),批量 io_uring_submit();
 * - 收割:pgaio_uring_drain_locked() 在临界区内批量取 CQE,逐个调用
 *   pgaio_io_process_completion()(运行完成回调、唤醒等待者);
 * - 等待:pgaio_uring_wait_one() 供等待者使用:锁 ring → 检查/等待
 *   内核 CQ(io_uring_wait_cqes)→ 收割;pgaio_uring_check_one() 是
 *   非阻塞版,用于轮询路径。
 *
 * 【IO 执行位置选择】io_uring 默认尽量在前台(进程上下文)执行 IO,
 * 批量缓冲读时这会阻塞 CPU 拷贝;pgaio_uring_should_use_async() 按
 * "是否缓冲 IO + 在途深度 + 单次 IO 大小"决定是否给 SQE 加
 * IOSQE_ASYNC 标志,强制内核把工作卸载到其 worker 线程,换取内存
 * 拷贝的并行化。
 *
 * 【与 EXEC_BACKEND 的关系】io_uring 与 EXEC_BACKEND(Windows 式
 * 进程启动)不兼容,该条件下 IOMETHOD_IO_URING_ENABLED 未定义,
 * 本文件整体被条件编译排除。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *    src/backend/storage/aio/method_io_uring.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

/* included early, for IOMETHOD_IO_URING_ENABLED */
#include "storage/aio.h"

#ifdef IOMETHOD_IO_URING_ENABLED

#include <sys/mman.h>
#include <unistd.h>

#include <liburing.h>

#include "miscadmin.h"
#include "storage/aio_internal.h"
#include "storage/fd.h"
#include "storage/proc.h"
#include "storage/shmem.h"
#include "storage/lwlock.h"
#include "storage/procnumber.h"
#include "utils/wait_event.h"


/* number of completions processed at once */
/* (中文)单次收割批处理的上限:从 CQ 队列一次最多取 32 个 CQE 处理。
 * 限制批大小,防止单个后端在替别人收割时长时间独占、饿死其他等 CQE
 * 的后端(见 pgaio_uring_drain_locked 注释)。 */
#define PGAIO_MAX_LOCAL_COMPLETED_IO 32


/* Entry points for IoMethodOps. */
/* (中文)方法回调的本地声明,便于对照 IoMethodOps 接口阅读。 */
static void pgaio_uring_shmem_request(void *arg);
static void pgaio_uring_shmem_init(void *arg);
static void pgaio_uring_init_backend(void);
static int	pgaio_uring_submit(uint16 num_staged_ios, PgAioHandle **staged_ios);
static void pgaio_uring_wait_one(PgAioHandle *ioh, uint64 ref_generation);
static void pgaio_uring_check_one(PgAioHandle *ioh, uint64 ref_generation);

/* helper functions */
static void pgaio_uring_sq_from_io(PgAioHandle *ioh, struct io_uring_sqe *sqe);


/* (中文)io_uring 方法的 IoMethodOps 定义:
 * - wait_on_fd_before_close = true:fd 关闭前必须等待引用它的 IO 全部
 *   完成——虽然 io_uring 大体容忍"在途 IO 的文件被关闭",但对打了
 *   IOSQE_ASYNC 标志的 IO 不成立(见英文注释里的邮件链接);
 * - 共享内存回调:request/init 用于申请并创建各后端的 ring;
 *   attach 缺省(ring 已在共享内存里,无需每进程重建映射);
 * - init_backend:把 pgaio_my_uring_context 指向本后端的上下文;
 * - submit/wait_one/check_one:提交、阻塞等待、非阻塞检查。 */
const IoMethodOps pgaio_uring_ops = {
	/*
	 * While io_uring mostly is OK with FDs getting closed while the IO is in
	 * flight, that is not true for IOs submitted with IOSQE_ASYNC.
	 *
	 * See
	 * https://postgr.es/m/5ons2rtmwarqqhhexb3dnqulw5rjgwgoct57vpdau4rujlrffj%403fls6d2mkiwc
	 */
	.wait_on_fd_before_close = true,

	.shmem_callbacks.request_fn = pgaio_uring_shmem_request,
	.shmem_callbacks.init_fn = pgaio_uring_shmem_init,
	.init_backend = pgaio_uring_init_backend,

	.submit = pgaio_uring_submit,
	.wait_one = pgaio_uring_wait_one,
	.check_one = pgaio_uring_check_one,
};

/*
 * Per-backend state when using io_method=io_uring
 */
/* (中文)每个后端的 io_uring 上下文(共享内存,数组按 ProcNumber 索引):
 * - completion_lock  : 收割锁。一个 ring 的完成事件可能被"任意"后端
 *   收割(发起者忙时别人代劳),该锁保证任意时刻只有一个人从 ring 取
 *   CQE,防止并发收割互相踩踏;
 * - io_uring_ring    : 真正的 io_uring 实例(SQ/CQ 队列)。
 * 整个结构按缓存行对齐(alignas PG_CACHE_LINE_SIZE),避免本后端结构的
 * completion_lock 与相邻后端(数组前一个元素)的 ring 产生伪共享
 * (false sharing)。 */
typedef struct PgAioUringContext
{
	/*
	 * Align the whole struct to a cacheline boundary, to prevent false
	 * sharing between completion_lock and prior backend's io_uring_ring.
	 */
	alignas(PG_CACHE_LINE_SIZE)

	/*
	 * Multiple backends can process completions for this backend's io_uring
	 * instance (e.g. when the backend issuing IO is busy doing something
	 * else).  To make that safe we have to ensure that only a single backend
	 * gets io completions from the io_uring instance at a time.
	 */
	LWLock		completion_lock;

	struct io_uring io_uring_ring;
} PgAioUringContext;

/*
 * Information about the capabilities that io_uring has.
 *
 * Depending on liburing and kernel version different features are
 * supported. At least for the kernel a kernel version check does not suffice
 * as various vendors do backport features to older kernels :(.
 */
/* (中文)运行环境对 io_uring 能力的一次性探测结果:
 * - checked        : 是否已探测过(懒初始化标志);
 * - mem_init_size  : 若 io_uring_queue_init_mem() 受支持(内核 6.5+,
 *                    允许用用户提供的内存做 ring,免去每 ring 一个
 *                    mmap),则为其返回"每个 ring 所需字节数"(>0);
 *                    否则为 -1(只能退回 io_uring 自行 mmap)。
 * 之所以要运行时探测而非查内核版本:厂商经常把新特性 backport 到
 * 老内核,版本号判断不可靠。 */
typedef struct PgAioUringCaps
{
	bool		checked;
	/* -1 if io_uring_queue_init_mem() is unsupported */
	int			mem_init_size;
} PgAioUringCaps;


/* PgAioUringContexts for all backends */
/* (中文)共享内存中的全部后端 io_uring 上下文数组(pgaio_uring_procs()
 * 个,按 ProcNumber 索引),init 阶段分配并逐个建 ring。 */
static PgAioUringContext *pgaio_uring_contexts;

/* the current backend's context */
/* (中文)本后端的 io_uring 上下文指针(init_backend 里按 MyProcNumber
 * 定位)。 */
static PgAioUringContext *pgaio_my_uring_context;

/* (中文)io_uring 能力探测结果的全局缓存(见 PgAioUringCaps 注释)。 */
static PgAioUringCaps pgaio_uring_caps =
{
	.checked = false,
	.mem_init_size = -1,
};

/*
 * pgaio_uring_procs - (中文)参与 io_uring 方法的后端总数
 *
 * 【作用】与 aio_init.c 的 AioProcs() 类似,但这里可以减去
 * MAX_IO_WORKERS:io_method=io_uring 时 worker 线程根本不会被启动
 * (两种方法互斥),为它们留句柄段/上下文纯属浪费。
 *
 * 【参数】无。
 * 【返回值】后端总数(MaxBackends + 辅助进程数 - IO worker 数)。
 */
static uint32
pgaio_uring_procs(void)
{
	/*
	 * We can subtract MAX_IO_WORKERS here as io workers are never used at the
	 * same time as io_method=io_uring.
	 */
	return MaxBackends + NUM_AUXILIARY_PROCS - MAX_IO_WORKERS;
}

/*
 * Initializes pgaio_uring_caps, unless that's already done.
 */
/*
 * pgaio_uring_check_capabilities - (中文)探测 io_uring 能力(懒初始化)
 *
 * 【作用】首次调用时探测"能否用调用方提供的内存创建 ring"
 * (IORING_SETUP_NO_MMAP + io_uring_queue_init_mem,内核 6.5+):
 * 在共享内存申请阶段(request)之前执行,因为结果直接决定共享内存
 * 的规模。探测方式:临时 mmap 一块 1MB 内存(注释说明 1MB 足够容纳
 * io_max_concurrency 范围内的 ring,先向下对齐到页大小),尝试创建
 * 测试 ring:成功则记录"每个 ring 需要的精确字节数"(返回值为所需
 * 内存大小);失败则当作"不支持"处理(具体失败原因留到 init 阶段
 * 的正式创建时报错)。最后释放测试内存、置 checked 标志。
 *
 * 【设计思想】为何要把 ring 放进共享内存?io_uring 默认对每个实例
 * 创建独立 mmap,后端很多时映射数量巨大,进程退出变慢;放进共享
 * 内存后零额外映射。无法用版本号判断支持与否(内核厂商爱 backport),
 * 只能实测。
 *
 * 【参数】无。
 * 【返回值】无(结果存于全局 pgaio_uring_caps)。
 */
static void
pgaio_uring_check_capabilities(void)
{
	if (pgaio_uring_caps.checked)
		return;

	/*
	 * By default io_uring creates a shared memory mapping for each io_uring
	 * instance, leading to a large number of memory mappings. Unfortunately a
	 * large number of memory mappings slows things down, backend exit is
	 * particularly affected.  To address that, newer kernels (6.5) support
	 * using user-provided memory for the memory, by putting the relevant
	 * memory into shared memory we don't need any additional mappings.
	 *
	 * To know whether this is supported, we unfortunately need to probe the
	 * kernel by trying to create a ring with userspace-provided memory. This
	 * also has a secondary benefit: We can determine precisely how much
	 * memory we need for each io_uring instance.
	 */
#if defined(HAVE_IO_URING_QUEUE_INIT_MEM) && defined(IORING_SETUP_NO_MMAP)
	{
		struct io_uring test_ring;
		size_t		ring_size;
		void	   *ring_ptr;
		struct io_uring_params p = {0};
		int			ret;

		/*
		 * Liburing does not yet provide an API to query how much memory a
		 * ring will need. So we over-estimate it here. As the memory is freed
		 * just below that's small temporary waste of memory.
		 *
		 * 1MB is more than enough for rings within io_max_concurrency's
		 * range.
		 */
		ring_size = 1024 * 1024;

		/*
		 * Hard to believe a system exists where 1MB would not be a multiple
		 * of the page size. But it's cheap to ensure...
		 */
		ring_size -= ring_size % sysconf(_SC_PAGESIZE);

		ring_ptr = mmap(NULL, ring_size, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
		if (ring_ptr == MAP_FAILED)
			elog(ERROR,
				 "mmap(%zu) to determine io_uring_queue_init_mem() support failed: %m",
				 ring_size);

		ret = io_uring_queue_init_mem(io_max_concurrency, &test_ring, &p, ring_ptr, ring_size);
		if (ret > 0)
		{
			pgaio_uring_caps.mem_init_size = ret;

			elog(DEBUG1,
				 "can use combined memory mapping for io_uring, each ring needs %d bytes",
				 ret);

			/* clean up the created ring, it was just for a test */
			io_uring_queue_exit(&test_ring);
		}
		else
		{
			/*
			 * There are different reasons for ring creation to fail, but it's
			 * ok to treat that just as io_uring_queue_init_mem() not being
			 * supported. We'll report a more detailed error in
			 * pgaio_uring_shmem_init().
			 */
			errno = -ret;
			elog(DEBUG1,
				 "cannot use combined memory mapping for io_uring, ring creation failed: %m");

		}

		if (munmap(ring_ptr, ring_size) != 0)
			elog(ERROR, "munmap() failed: %m");
	}
#else
	{
		elog(DEBUG1,
			 "can't use combined memory mapping for io_uring, kernel or liburing too old");
	}
#endif

	pgaio_uring_caps.checked = true;
}

/*
 * Memory for all PgAioUringContext instances
 */
/*
 * pgaio_uring_context_shmem_size - (中文)上下文结构数组的字节数
 *
 * 【作用】每个后端一个 PgAioUringContext(含锁与 ring 句柄),共
 * pgaio_uring_procs() 个。mul_size 防溢出。
 *
 * 【参数】无。
 * 【返回值】所需字节数。
 */
static size_t
pgaio_uring_context_shmem_size(void)
{
	return mul_size(pgaio_uring_procs(), sizeof(PgAioUringContext));
}

/*
 * Memory for the combined memory used by io_uring instances. Returns 0 if
 * that is not supported by kernel/liburing.
 */
/*
 * pgaio_uring_ring_shmem_size - (中文)为各 ring 预留的共享内存字节数
 *
 * 【作用】当 io_uring_queue_init_mem() 可用时,为所有后端的 ring 预留
 * "页对齐余量(1 页)+ 每 ring 需要的内存 × ring 数"。预留一块总内存
 * 再从其中按页边界切分,保证每个 ring 的数据都从页边界开始(io_uring
 * 要求;若启用大页,只要求页对齐,不需要对齐到大页边界)。不支持该
 * 特性时返回 0(ring 由内核自行 mmap)。
 *
 * 【参数】无。
 * 【返回值】预留字节数(可能为 0)。
 */
static size_t
pgaio_uring_ring_shmem_size(void)
{
	size_t		sz = 0;

	if (pgaio_uring_caps.mem_init_size > 0)
	{
		/*
		 * Memory for rings needs to be allocated to the page boundary,
		 * reserve space. Luckily it does not need to be aligned to hugepage
		 * boundaries, even if huge pages are used.
		 */
		sz = add_size(sz, sysconf(_SC_PAGESIZE));
		sz = add_size(sz, mul_size(pgaio_uring_procs(),
								   pgaio_uring_caps.mem_init_size));
	}

	return sz;
}

/*
 * pgaio_uring_shmem_size - (中文)io_uring 方法共享内存总需求
 *
 * 【作用】把"上下文数组"与"ring 内存池"两块的字节数相加,作为
 * request 阶段申报的总体积。
 *
 * 【参数】无。
 * 【返回值】总字节数。
 */
static size_t
pgaio_uring_shmem_size(void)
{
	size_t		sz;

	sz = pgaio_uring_context_shmem_size();
	sz = add_size(sz, pgaio_uring_ring_shmem_size());

	return sz;
}

/*
 * pgaio_uring_shmem_request - (中文)request 阶段:申报 io_uring 的共享内存
 *
 * 【作用】postmaster 启动早期调用:先探测能力(结果影响内存规模),
 * 再向共享内存子系统申报一整块"上下文数组 + ring 内存池"。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
pgaio_uring_shmem_request(void *arg)
{
	/*
	 * Kernel and liburing support for various features influences how much
	 * shmem we need, perform the necessary checks.
	 */
	pgaio_uring_check_capabilities();

	ShmemRequestStruct(.name = "AioUringContext",
					   .size = pgaio_uring_shmem_size(),
					   .ptr = (void **) &pgaio_uring_contexts,
		);
}

/*
 * pgaio_uring_shmem_init - (中文)init 阶段:在共享内存里创建所有 ring
 *
 * 【作用】共享内存分配完成后(postmaster)调用,为每个后端创建
 * io_uring 实例:
 * 1. 布局:上下文数组之后紧跟 ring 内存池;若支持用户内存建 ring,
 *    把池内起始位置对齐到页边界,再从池中按"每 ring 的精确大小"
 *    依次切分(记录剩余量,创建时逐个扣减);
 * 2. 逐个创建 ring:支持时用 io_uring_queue_init_mem(数据落在共享
 *    内存),否则退化为 io_uring_queue_init(内核自行 mmap)。队列深度
 *    均为 io_max_concurrency(每后端同时在途 IO 数上限);
 * 3. 创建失败时给出人性化错误:EPERM → 提示检查
 *    /proc/sys/kernel/io_uring_disabled;EMFILE → 提示提高 ulimit -n
 *    (注释说明:总进程数多时,每个 ring 都要占用文件描述符,RLIMIT
 *    压力大,未来可能应主动调整软限制);ENOSYS → 内核不支持;
 * 4. 初始化每把 completion_lock。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
pgaio_uring_shmem_init(void *arg)
{
	int			TotalProcs = pgaio_uring_procs();
	char	   *shmem;
	size_t		ring_mem_remain = 0;
	char	   *ring_mem_next = 0;

	/*
	 * We allocate memory for all PgAioUringContext instances and, if
	 * supported, the memory required for each of the io_uring instances, in
	 * one combined allocation.
	 *
	 * pgaio_uring_contexts is already set to the base of the allocation.
	 */
	shmem = (char *) pgaio_uring_contexts;
	shmem += pgaio_uring_context_shmem_size();

	/* if supported, handle memory alignment / sizing for io_uring memory */
	if (pgaio_uring_caps.mem_init_size > 0)
	{
		ring_mem_remain = pgaio_uring_ring_shmem_size();
		ring_mem_next = shmem;

		/* align to page boundary, see also pgaio_uring_ring_shmem_size() */
		ring_mem_next = (char *) TYPEALIGN(sysconf(_SC_PAGESIZE), ring_mem_next);

		/* account for alignment */
		ring_mem_remain -= ring_mem_next - shmem;
		shmem += ring_mem_next - shmem;

		shmem += ring_mem_remain;
	}

	for (int contextno = 0; contextno < TotalProcs; contextno++)
	{
		PgAioUringContext *context = &pgaio_uring_contexts[contextno];
		int			ret;

		/*
		 * Right now a high TotalProcs will cause problems in two ways:
		 *
		 * - RLIMIT_NOFILE needs to be big enough to allow all
		 * io_uring_queue_init() calls to succeed.
		 *
		 * - RLIMIT_NOFILE needs to be big enough to still have enough file
		 * descriptors to satisfy set_max_safe_fds() left over. Or, even
		 * better, have max_files_per_process left over FDs.
		 *
		 * We probably should adjust the soft RLIMIT_NOFILE to ensure that.
		 *
		 *
		 * XXX: Newer versions of io_uring support sharing the workers that
		 * execute some asynchronous IOs between io_uring instances. It might
		 * be worth using that - also need to evaluate if that causes
		 * noticeable additional contention?
		 */

		/*
		 * If supported (c.f. pgaio_uring_check_capabilities()), create ring
		 * with its data in shared memory. Otherwise fall back io_uring
		 * creating a memory mapping for each ring.
		 */
#if defined(HAVE_IO_URING_QUEUE_INIT_MEM) && defined(IORING_SETUP_NO_MMAP)
		if (pgaio_uring_caps.mem_init_size > 0)
		{
			struct io_uring_params p = {0};

			ret = io_uring_queue_init_mem(io_max_concurrency, &context->io_uring_ring, &p, ring_mem_next, ring_mem_remain);

			ring_mem_remain -= ret;
			ring_mem_next += ret;
		}
		else
#endif
		{
			ret = io_uring_queue_init(io_max_concurrency, &context->io_uring_ring, 0);
		}

		if (ret < 0)
		{
			char	   *hint = NULL;
			int			err = ERRCODE_INTERNAL_ERROR;

			/* add hints for some failures that errno explains sufficiently */
			if (-ret == EPERM)
			{
				err = ERRCODE_INSUFFICIENT_PRIVILEGE;
				hint = _("Check if io_uring is disabled via /proc/sys/kernel/io_uring_disabled.");
			}
			else if (-ret == EMFILE)
			{
				err = ERRCODE_INSUFFICIENT_RESOURCES;
				hint = psprintf(_("Consider increasing \"ulimit -n\" to at least %d."),
								TotalProcs + max_files_per_process);
			}
			else if (-ret == ENOSYS)
			{
				err = ERRCODE_FEATURE_NOT_SUPPORTED;
				hint = _("The kernel does not support io_uring.");
			}

			/* update errno to allow %m to work */
			errno = -ret;

			ereport(ERROR,
					errcode(err),
					errmsg("could not setup io_uring queue: %m"),
					hint != NULL ? errhint("%s", hint) : 0);
		}

		LWLockInitialize(&context->completion_lock, LWTRANCHE_AIO_URING_COMPLETION);
	}
}

/*
 * pgaio_uring_init_backend - (中文)每后端初始化:定位自己的 ring 上下文
 *
 * 【作用】每个后端进程启动时(经 IoMethodOps->init_backend)把
 * pgaio_my_uring_context 指向共享内存中按自己 ProcNumber 分配的那个
 * PgAioUringContext。ring 本身在 postmaster 阶段就已创建,这里只需
 * "认领"指针。
 *
 * 【参数】无。
 * 【返回值】无。
 */
static void
pgaio_uring_init_backend(void)
{
	Assert(MyProcNumber < pgaio_uring_procs());

	pgaio_my_uring_context = &pgaio_uring_contexts[MyProcNumber];
}

/*
 * pgaio_uring_submit - (中文)批量提交:把一批句柄翻译成 SQE 并交内核
 *
 * 【作用】IoMethodOps->submit 实现:对每个 staged 句柄——
 * 1. pgaio_io_prepare_submit()(状态 → SUBMITTED,挂 in-flight 链表);
 * 2. pgaio_uring_sq_from_io() 把句柄的 op/iovec 填进一个 SQE;
 * 然后循环调用 io_uring_submit() 真正把 SQE 队列交给内核:
 * - -EINTR(被信号打断):重试;
 * - 其他负值(尤其 EAGAIN):PANIC。注释解释了理由:我方对在途 IO
 *   有严格上限,内核健康时不该 EAGAIN;出现说明内核内存压力已极其
 *   严重,与其在此等待(调用者可能正持有关键锁),不如尽早崩溃重启;
 * - 提交数 != 期望数:理论上不可达,但若发生需重新提交,先 PANIC
 *   暴露问题。
 *
 * 【设计思想】注意"单段 iovec"会退化为 prep_read/prep_write(非
 * 向量版本),这对内核是更快的路径;多段才用 prep_readv/writev。
 * 返回实际提交数(必须等于 num_staged_ios)。
 *
 * 【参数】num_staged_ios —— 本批 IO 个数(≤ PGAIO_SUBMIT_BATCH_SIZE);
 *        staged_ios —— 句柄数组。
 * 【返回值】实际提交数(恒等于 num_staged_ios,否则 PANIC)。
 */
static int
pgaio_uring_submit(uint16 num_staged_ios, PgAioHandle **staged_ios)
{
	struct io_uring *uring_instance = &pgaio_my_uring_context->io_uring_ring;

	Assert(num_staged_ios <= PGAIO_SUBMIT_BATCH_SIZE);

	for (int i = 0; i < num_staged_ios; i++)
	{
		PgAioHandle *ioh = staged_ios[i];
		struct io_uring_sqe *sqe;

		sqe = io_uring_get_sqe(uring_instance);

		if (!sqe)
			elog(ERROR, "io_uring submission queue is unexpectedly full");

		pgaio_io_prepare_submit(ioh);
		pgaio_uring_sq_from_io(ioh, sqe);
	}

	while (true)
	{
		int			ret;

		pgstat_report_wait_start(WAIT_EVENT_AIO_IO_URING_SUBMIT);
		ret = io_uring_submit(uring_instance);
		pgstat_report_wait_end();

		if (ret == -EINTR)
		{
			pgaio_debug(DEBUG3,
						"aio method uring: submit EINTR, nios: %d",
						num_staged_ios);
		}
		else if (ret < 0)
		{
			/*
			 * The io_uring_enter() manpage suggests that the appropriate
			 * reaction to EAGAIN is:
			 *
			 * "The application should wait for some completions and try
			 * again"
			 *
			 * However, it seems unlikely that that would help in our case, as
			 * we apply a low limit to the number of outstanding IOs and thus
			 * also outstanding completions, making it unlikely that we'd get
			 * EAGAIN while the OS is in good working order.
			 *
			 * Additionally, it would be problematic to just wait here, our
			 * caller might hold critical locks. It'd possibly lead to
			 * delaying the crash-restart that seems likely to occur when the
			 * kernel is under such heavy memory pressure.
			 *
			 * Update errno to allow %m to work.
			 */
			errno = -ret;
			elog(PANIC, "io_uring submit failed: %m");
		}
		else if (ret != num_staged_ios)
		{
			/* likely unreachable, but if it is, we would need to re-submit */
			elog(PANIC, "io_uring submit submitted only %d of %d",
				 ret, num_staged_ios);
		}
		else
		{
			pgaio_debug(DEBUG4,
						"aio method uring: submitted %d IOs",
						num_staged_ios);
			break;
		}
	}

	return num_staged_ios;
}

/*
 * pgaio_uring_completion_error_callback - (中文)完成处理出错时的错误上下文回调
 *
 * 【作用】注册为错误上下文回调(error_context_stack),当"替别人收割
 * 完成事件"过程中发生错误(例如 PANIC、或完成回调里触发的问题)时,
 * 给错误消息附上"正在替进程 X 完成 I/O"的说明,帮助定位:不是这个
 * 后端自己的 IO 出了错,而是它代劳的对象。
 *
 * 【设计思想】若 IO 的拥有者就是本进程,上下文无意义,直接返回。
 * 通过 errcontext() 输出。回调的 arg 由收割循环逐 CQE 更新为当前
 * 处理的句柄(见 drain_locked)。
 *
 * 【参数】arg —— 当前正在处理完成的句柄(可能为 NULL,表示无句柄)。
 * 【返回值】无。
 */
static void
pgaio_uring_completion_error_callback(void *arg)
{
	ProcNumber	owner;
	PGPROC	   *owner_proc;
	int32		owner_pid;
	PgAioHandle *ioh = arg;

	if (!ioh)
		return;

	/* No need for context if a backend is completing the IO for itself */
	if (ioh->owner_procno == MyProcNumber)
		return;

	owner = ioh->owner_procno;
	owner_proc = GetPGProcByNumber(owner);
	owner_pid = owner_proc->pid;

	errcontext("completing I/O on behalf of process %d", owner_pid);
}

/*
 * pgaio_uring_drain_locked - (中文)收割指定 ring 的完成事件(调用者须持锁)
 *
 * 【作用】从 ring 的 CQ(完成队列)批量取出 CQE 并逐个处理:
 * 1. 前置:必须已持有该 ring 的 completion_lock(Assert),并挂上错误
 *    上下文回调(见 pgaio_uring_completion_error_callback);
 * 2. 先读"当前可用的 CQE 数",只收割这么多(不追加等待)——防止单个
 *    后端陷入"边收边有新完成"的无限循环,长时间饿死其他等待者;
 * 3. 循环:在临界区内批量 peek(每次最多 PGAIO_MAX_LOCAL_COMPLETED_IO
 *    个),对每个 CQE 取出句柄指针与结果(io_uring_cqe_get_data,
 *    即提交时塞入的 ioh)、标记 seen(释放 CQE 槽),然后调用
 *    pgaio_io_process_completion() 走标准完成路径(共享回调/唤醒/
 *    必要时本地回收);
 * 4. 恢复错误上下文栈。
 *
 * 【设计思想】完成处理必须运行在临界区内(完成回调要求);"只收割
 * 当时已就绪的数量"配合批上限,避免占住锁不放。注意:收割者可以
 * 是任何后端——这正是"发起者阻塞也不怕死锁"的关键设计(见文件头)。
 *
 * 【参数】context —— 要收割的 ring 所属上下文(锁由调用者持有)。
 * 【返回值】无。
 */
static void
pgaio_uring_drain_locked(PgAioUringContext *context)
{
	int			ready;
	int			orig_ready;
	ErrorContextCallback errcallback = {0};

	Assert(LWLockHeldByMeInMode(&context->completion_lock, LW_EXCLUSIVE));

	errcallback.callback = pgaio_uring_completion_error_callback;
	errcallback.previous = error_context_stack;
	error_context_stack = &errcallback;

	/*
	 * Don't drain more events than available right now. Otherwise it's
	 * plausible that one backend could get stuck, for a while, receiving CQEs
	 * without actually processing them.
	 */
	orig_ready = ready = io_uring_cq_ready(&context->io_uring_ring);

	while (ready > 0)
	{
		struct io_uring_cqe *cqes[PGAIO_MAX_LOCAL_COMPLETED_IO];
		uint32		ncqes;

		START_CRIT_SECTION();
		ncqes =
			io_uring_peek_batch_cqe(&context->io_uring_ring,
									cqes,
									Min(PGAIO_MAX_LOCAL_COMPLETED_IO, ready));
		Assert(ncqes <= ready);

		ready -= ncqes;

		for (uint32 i = 0; i < ncqes; i++)
		{
			struct io_uring_cqe *cqe = cqes[i];
			PgAioHandle *ioh = io_uring_cqe_get_data(cqe);
			int			result = cqe->res;

			errcallback.arg = ioh;

			io_uring_cqe_seen(&context->io_uring_ring, cqe);

			pgaio_io_process_completion(ioh, result);
			errcallback.arg = NULL;
		}

		END_CRIT_SECTION();

		pgaio_debug(DEBUG3,
					"drained %d/%d, now expecting %d",
					ncqes, orig_ready, io_uring_cq_ready(&context->io_uring_ring));
	}

	error_context_stack = errcallback.previous;
}

/*
 * pgaio_uring_wait_one - (中文)等待某 IO 完成(IoMethodOps->wait_one 实现)
 *
 * 【作用】被 pgaio_io_wait() 在句柄处于 SUBMITTED 状态时调用,负责
 * "推进完成"。流程:拿目标 ring(属于 IO 的发起者)的 completion_lock,
 * 循环:
 * - 句柄已被复用、或状态已离开 SUBMITTED(被别的后端完成了)→ 退出;
 * - ring 的 CQ 里已有完成 → 直接收割(不必进内核等);
 * - 否则 io_uring_wait_cqes() 阻塞等内核产生至少一个 CQE(-EINTR
 *   被打断则继续循环;其他错误 PANIC,理由同 submit),然后收割。
 *
 * 【设计思想】因为任意后端都能替发起者收割,"等待"与"完成"的解耦
 * 使得等待者只需"帮发起者把 CQE 处理掉",IO 自然完成。锁粒度上的
 * XXX 注释承认:绝大多数情况下是 ring 拥有者自己消费完成,这把锁
 * 多数时候是多余开销,但为了并发安全只能如此。回调参数
 * ref_generation 用于识别句柄是否已复用(避免收割到无关的新 IO)。
 *
 * 【参数】ioh —— 等待目标句柄;ref_generation —— 建立等待时的代数。
 * 【返回值】无。返回时该 IO 至少已推进到 COMPLETED_* 状态(或句柄
 * 已被复用)。
 */
static void
pgaio_uring_wait_one(PgAioHandle *ioh, uint64 ref_generation)
{
	PgAioHandleState state;
	ProcNumber	owner_procno = ioh->owner_procno;
	PgAioUringContext *owner_context = &pgaio_uring_contexts[owner_procno];
	bool		expect_cqe;
	int			waited = 0;

	/*
	 * XXX: It would be nice to have a smarter locking scheme, nearly all the
	 * time the backend owning the ring will consume the completions, making
	 * the locking unnecessarily expensive.
	 */
	LWLockAcquire(&owner_context->completion_lock, LW_EXCLUSIVE);

	while (true)
	{
		pgaio_debug_io(DEBUG3, ioh,
					   "wait_one io_gen: %" PRIu64 ", ref_gen: %" PRIu64 ", cycle %d",
					   ioh->generation,
					   ref_generation,
					   waited);

		if (pgaio_io_was_recycled(ioh, ref_generation, &state) ||
			state != PGAIO_HS_SUBMITTED)
		{
			/* the IO was completed by another backend */
			break;
		}
		else if (io_uring_cq_ready(&owner_context->io_uring_ring))
		{
			/* no need to wait in the kernel, io_uring has a completion */
			expect_cqe = true;
		}
		else
		{
			int			ret;
			struct io_uring_cqe *cqes;

			/* need to wait in the kernel */
			pgstat_report_wait_start(WAIT_EVENT_AIO_IO_URING_EXECUTION);
			ret = io_uring_wait_cqes(&owner_context->io_uring_ring, &cqes, 1, NULL, NULL);
			pgstat_report_wait_end();

			if (ret == -EINTR)
			{
				continue;
			}
			else if (ret != 0)
			{
				/* see comment after io_uring_submit() */
				errno = -ret;
				elog(PANIC, "io_uring wait failed: %m");
			}
			else
			{
				Assert(cqes != NULL);
				expect_cqe = true;
				waited++;
			}
		}

		if (expect_cqe)
		{
			pgaio_uring_drain_locked(owner_context);
		}
	}

	LWLockRelease(&owner_context->completion_lock);

	pgaio_debug(DEBUG3,
				"wait_one with %d sleeps",
				waited);
}

/*
 * pgaio_uring_check_one - (中文)非阻塞检查并顺手收割(IoMethodOps->check_one 实现)
 *
 * 【作用】供 pgaio_wref_check_done() 轮询路径使用,绝不阻塞:
 * 1. 廉价预检:不持锁看 CQ 是否非空(不可靠但省事),空则直接返回;
 * 2. LWLockConditionalAcquire 尝试拿 completion_lock,拿不到说明正有
 *    别人在收割(且很快会处理完),放弃;拿到了才有资格收割;
 * 3. 持锁后再确认一次 CQ 非空(预检可能读到旧值、或已被他人处理),
 *    然后 pgaio_uring_drain_locked() 收割全部就绪的完成。
 *
 * 【设计思想】"预检 + 条件拿锁 + 复查"三级递减成本:多数轮询路径上
 * 根本没有完成事件,一次无锁读即可返回。从正确性上说,漏收割一些
 * 完成也无妨(下次检查/等待还会处理),只是影响性能。
 *
 * 【参数】ioh —— 轮询目标句柄;ref_generation —— 建立等待时的代数。
 * 【返回值】无。
 */
static void
pgaio_uring_check_one(PgAioHandle *ioh, uint64 ref_generation)
{
	ProcNumber	owner_procno = ioh->owner_procno;
	PgAioUringContext *owner_context = &pgaio_uring_contexts[owner_procno];

	/*
	 * This check is not reliable when not holding the completion lock, but
	 * it's a useful cheap pre-check to see if it's worth trying to get the
	 * completion lock.
	 */
	if (!io_uring_cq_ready(&owner_context->io_uring_ring))
		return;

	/*
	 * If the completion lock is currently held, the holder will likely
	 * process any pending completions, give up.
	 */
	if (!LWLockConditionalAcquire(&owner_context->completion_lock, LW_EXCLUSIVE))
		return;

	pgaio_debug_io(DEBUG3, ioh,
				   "check_one io_gen: %" PRIu64 ", ref_gen: %" PRIu64,
				   ioh->generation,
				   ref_generation);

	/*
	 * Recheck if there are any completions, another backend could have
	 * processed them since we checked above, or our unlocked pre-check could
	 * have been reading outdated values.
	 *
	 * It is possible that the IO handle has been reused since the start of
	 * the call, but now that we have the lock, we can just as well drain all
	 * completions.
	 */
	if (io_uring_cq_ready(&owner_context->io_uring_ring))
		pgaio_uring_drain_locked(owner_context);

	LWLockRelease(&owner_context->completion_lock);
}

/*
 * io_uring executes IO in process context if possible. That's generally good,
 * as it reduces context switching. When performing a lot of buffered IO that
 * means that copying between page cache and userspace memory happens in the
 * foreground, as it can't be offloaded to DMA hardware as is possible when
 * using direct IO. When executing a lot of buffered IO this causes io_uring
 * to be slower than worker mode, as worker mode parallelizes the
 * copying. io_uring can be told to offload work to worker threads instead.
 *
 * If the IOs are small, we only benefit from forcing things into the
 * background if there is a lot of IO, as otherwise the overhead from context
 * switching is higher than the gain.
 *
 * If IOs are large, there is benefit from asynchronous processing at lower
 * queue depths, as IO latency is less of a crucial factor and parallelizing
 * memory copies is more important.  In addition, it is important to trigger
 * asynchronous processing even at low queue depth, as with foreground
 * processing we might never actually reach deep enough IO depths to trigger
 * asynchronous processing, which in turn would deprive readahead control
 * logic of information about whether a deeper look-ahead distance would be
 * advantageous.
 *
 * We have done some basic benchmarking to validate the thresholds used, but
 * it's quite plausible that there are better values.  See
 * https://postgr.es/m/3gkuvs3lz3u3skuaxfkxnsysfqslf2srigl6546vhesekve6v2%40va3r5esummvg
 * for some details of this benchmarking.
 */
/*
 * pgaio_uring_should_use_async - (中文)判断该 SQE 是否应加 IOSQE_ASYNC 标志
 *
 * 【作用】决定缓冲读是否强制内核用异步路径执行(标志 IOSQE_ASYNC,
 * 把工作卸载到内核的 worker 线程)。背景:io_uring 默认尽量在进程
 * 上下文(前台)执行 IO,这样省上下文切换;但对大量缓冲 IO,前台
 * 执行意味着"页缓存 ↔ 用户内存"的拷贝占住当前 CPU,无法像直接 IO
 * 那样交给 DMA,批量场景反而比 worker 模式(并行拷贝)慢。
 *
 * 【判定规则】(注释中的英文原文解释了每条的动机,含基准测试)
 * - 直接 IO(未标 PGAIO_HF_BUFFERED):恒 false——提交阶段 io_uring
 *   绝不会同步执行直接 IO,无需标志;
 * - 本后端在途 IO 深度 > 4:true——队列已经不浅,派发到后台的
 *   开销占比下降;
 * - 单次 IO ≥ 4 个块:true——大 IO 时并行拷贝收益大、延迟影响小,
 *   且要尽早触发异步处理,否则前台的顺序执行可能永远到不了足够深
 *   的队列,预读深度调节(基于实测反馈)也就无从谈起;
 * - 其余(小 IO、浅队列):false,避免上下文切换开销大于收益。
 *
 * 【参数】ioh —— 正在准备 SQE 的句柄;io_size —— 本次 IO 的总字节数。
 * 【返回值】true = 给 SQE 加 IOSQE_ASYNC;false = 保持默认前台执行。
 */
static bool
pgaio_uring_should_use_async(PgAioHandle *ioh, size_t io_size)
{
	/*
	 * With DIO there's no benefit from forcing asynchronous processing, as
	 * io_uring will never execute direct IO synchronously during submission.
	 */
	if (!(ioh->flags & PGAIO_HF_BUFFERED))
		return false;

	/*
	 * Once the IO queue depth is not that shallow anymore, the overhead of
	 * dispatching to the background is a less significant factor.
	 */
	if (dclist_count(&pgaio_my_backend->in_flight_ios) > 4)
		return true;

	/*
	 * If the IO is larger, the gains from parallelizing the memory copy are
	 * larger and typically the impact of the latency is smaller.
	 */
	if (io_size >= (BLCKSZ * 4))
		return true;

	return false;
}

/*
 * pgaio_uring_sq_from_io - (中文)把句柄的操作翻译成一个 SQE
 *
 * 【作用】把句柄的 op/iovec/偏移填进 io_uring 的提交队列元素(SQE):
 * - READV : 单段时用 io_uring_prep_read(非向量快路径),多段用
 *   prep_readv;并计算总字节数,按 pgaio_uring_should_use_async()
 *   决定是否追加 IOSQE_ASYNC;
 * - WRITEV: 对称处理;目前故意不加 IOSQE_ASYNC(注释说明:尚无证据
 *   表明写路径强制异步有性能收益);
 * - INVALID: 报错(不可能到达)。
 * 最后 io_uring_sqe_set_data() 把句柄指针塞进 SQE 的 user_data 槽,
 * 完成时由 CQE 原样带回(收割端用 io_uring_cqe_get_data 取回)。
 *
 * 【参数】ioh —— 已提交准备的句柄(状态 SUBMITTED);sqe —— 目标 SQE
 *        (由调用者 pgaio_uring_submit 经 io_uring_get_sqe 取得)。
 * 【返回值】无。
 */
static void
pgaio_uring_sq_from_io(PgAioHandle *ioh, struct io_uring_sqe *sqe)
{
	struct iovec *iov;
	size_t		io_size = 0;

	switch ((PgAioOp) ioh->op)
	{
		case PGAIO_OP_READV:
			iov = &pgaio_ctl->iovecs[ioh->iovec_off];
			if (ioh->op_data.read.iov_length == 1)
			{
				io_uring_prep_read(sqe,
								   ioh->op_data.read.fd,
								   iov->iov_base,
								   iov->iov_len,
								   ioh->op_data.read.offset);

				io_size = iov->iov_len;
			}
			else
			{
				io_uring_prep_readv(sqe,
									ioh->op_data.read.fd,
									iov,
									ioh->op_data.read.iov_length,
									ioh->op_data.read.offset);

				for (int i = 0; i < ioh->op_data.read.iov_length; i++, iov++)
					io_size += iov->iov_len;
			}

			if (pgaio_uring_should_use_async(ioh, io_size))
				io_uring_sqe_set_flags(sqe, IOSQE_ASYNC);

			break;

		case PGAIO_OP_WRITEV:
			iov = &pgaio_ctl->iovecs[ioh->iovec_off];
			if (ioh->op_data.write.iov_length == 1)
			{
				io_uring_prep_write(sqe,
									ioh->op_data.write.fd,
									iov->iov_base,
									iov->iov_len,
									ioh->op_data.write.offset);
			}
			else
			{
				io_uring_prep_writev(sqe,
									 ioh->op_data.write.fd,
									 iov,
									 ioh->op_data.write.iov_length,
									 ioh->op_data.write.offset);
			}

			/*
			 * For now don't trigger use of IOSQE_ASYNC for writes, it's not
			 * clear there is a performance benefit in doing so.
			 */

			break;

		case PGAIO_OP_INVALID:
			elog(ERROR, "trying to prepare invalid IO operation for execution");
	}

	io_uring_sqe_set_data(sqe, ioh);
}

#endif							/* IOMETHOD_IO_URING_ENABLED */
