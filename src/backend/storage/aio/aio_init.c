/*-------------------------------------------------------------------------
 *
 * aio_init.c
 *    AIO - Subsystem Initialization
 *
 * 【模块总览(中文)】
 * 本文件负责 AIO 子系统的全部初始化工作,分三个层次:
 *
 * 1) 共享内存布局规划(编译期意义上的"启动期"):通过 AioShmemCallbacks
 *    向共享内存子系统注册 request / init / attach 三个阶段回调:
 *    - request : 声明 AIO 需要的所有共享内存段及大小,并解决
 *      io_max_concurrency 的自动整定(AioChooseMaxConcurrency);
 *    - init    : 在共享内存分配完成后初始化 PgAioCtl 及各后端的
 *      PgAioBackend 状态、句柄池(每后端 io_max_concurrency 个句柄,
 *      每个句柄配 io_max_combine_limit 个 iovec 与等量 handle_data 槽);
 *    - attach  : 每个进程启动后把指针映射到自己地址空间(透传给当前
 *      IO 方法的 attach 回调,如 io_uring 需要在每个进程里重建 ring)。
 *
 * 2) 并发度整定:AioChooseMaxConcurrency() 依据"不可能有比允许 pin 的
 *    缓冲区数更多的在途 IO"与共享缓冲池规模,把 io_max_concurrency
 *    自动定为 NBuffers/进程数,上限 64。
 *
 * 3) 每后端初始化:pgaio_init_backend() 把 pgaio_my_backend 指向共享
 *    内存中本进程的 PgAioBackend,调用 IO 方法的 init_backend(如
 *    io_uring 建立 ring、worker 建立与 worker 池通信的管道),并登记
 *    进程退出钩子 pgaio_shutdown。IO worker 进程自身不初始化 AIO
 *    上下文(B_IO_WORKER 直接返回)。
 *
 * 注意:共享内存的划分是静态的——句柄池按"ProcNumber"分段,每个
 * 后端只访问自己的那一段,因此常规路径完全无锁。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *    src/backend/storage/aio/aio_init.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "miscadmin.h"
#include "storage/aio.h"
#include "storage/aio_internal.h"
#include "storage/aio_subsys.h"
#include "storage/bufmgr.h"
#include "storage/io_worker.h"
#include "storage/ipc.h"
#include "storage/proc.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/guc.h"


static void AioShmemRequest(void *arg);
static void AioShmemInit(void *arg);
static void AioShmemAttach(void *arg);

/* (中文)本文件向共享内存子系统登记的 request/init/attach 回调:
 * request 阶段声明各共享内存段与大小;init 阶段(仅 postmaster)初始化
 * 数据结构;attach 阶段(每个进程)把指针映射到本进程地址空间。 */
const ShmemCallbacks AioShmemCallbacks = {
	.request_fn = AioShmemRequest,
	.init_fn = AioShmemInit,
	.attach_fn = AioShmemAttach,
};

/* (中文)共享内存段指针(init/attach 阶段由共享内存子系统填入):
 * - AioBackendShmemPtr : PgAioBackend 数组(每进程一份),即
 *                        PgAioCtl->backend_state 的存储;
 * - AioHandleShmemPtr  : PgAioHandle 句柄池,即 PgAioCtl->io_handles;
 * - AioHandleIOVShmemPtr: iovec 池,即 PgAioCtl->iovecs;
 * - AioHandleDataShmemPtr: handle_data(uint64)池,即 PgAioCtl->handle_data。
 * 各段的实际布局关系见 AioShmemInit 的赋值。 */
static PgAioBackend *AioBackendShmemPtr;
static PgAioHandle *AioHandleShmemPtr;
static struct iovec *AioHandleIOVShmemPtr;
static uint64 *AioHandleDataShmemPtr;

/*
 * AioProcs - (中文)按 ProcNumber 计的 AIO 参与者总数
 *
 * 【作用】返回句柄池/后端状态数组的"进程维度"大小:MaxBackends
 * (普通后端 + 各种 bgworker) + NUM_AUXILIARY_PROCS(辅助进程,如
 * bgwriter/checkpointer/walwriter 等)。
 *
 * 【设计思想】注意不能直接减去 MAX_IO_WORKERS:虽然 IO worker 自己不
 * 使用 AIO 上下文,但它们的 ProcNumber 是从 MaxBackends 之后编号的,
 * 若按"总进程数 - MAX_IO_WORKERS"计算,仍可能有人把任务派发给
 * worker 的 ProcNumber 段,故直接取上限(多分配一点,安全)。
 *
 * 【参数】无。
 * 【返回值】进程数(句柄池在进程维度的长度)。
 */
static uint32
AioProcs(void)
{
	/*
	 * While AIO workers don't need their own AIO context, we can't currently
	 * guarantee that nothing gets assigned to an IO worker's ProcNumber if we
	 * just subtracted MAX_IO_WORKERS.
	 */
	return MaxBackends + NUM_AUXILIARY_PROCS;
}

/*
 * AioBackendShmemSize - (中文)计算 PgAioBackend 数组所需字节数
 *
 * 【作用】request 阶段使用:每个 AIO 参与者(AioProcs() 个)一份
 * PgAioBackend,即后端状态数组总大小。用 mul_size 防整数溢出。
 *
 * 【参数】无。
 * 【返回值】所需字节数。
 */
static Size
AioBackendShmemSize(void)
{
	return mul_size(AioProcs(), sizeof(PgAioBackend));
}

/*
 * AioHandleShmemSize - (中文)计算句柄池所需字节数
 *
 * 【作用】request 阶段使用:每个参与者 io_max_concurrency 个
 * PgAioHandle(整个句柄池 = AioProcs() × io_max_concurrency 个)。
 * 前置条件:io_max_concurrency 必须已整定为正数(Assert 校验,
 * 确保 AioShmemRequest 先于本函数执行了自动整定)。
 *
 * 【参数】无。
 * 【返回值】句柄池字节数。
 */
static Size
AioHandleShmemSize(void)
{
	Size		sz;

	/* verify AioChooseMaxConcurrency() did its thing */
	Assert(io_max_concurrency > 0);

	/* io handles */
	sz = mul_size(AioProcs(),
				  mul_size(io_max_concurrency, sizeof(PgAioHandle)));

	return sz;
}

/*
 * AioHandleIOVShmemSize - (中文)计算 iovec 池所需字节数
 *
 * 【作用】request 阶段使用:每个句柄最多 io_max_combine_limit 个 iovec
 * (一次多块 IO 的各段缓冲区),因此 iovec 总数 =
 * AioProcs() × io_max_concurrency(句柄数) × io_max_combine_limit。
 * 池放共享内存(而非句柄内)是为了让"单个 IO 的最大块数"可以随
 * PGC_POSTMASTER 级 GUC(io_combine_limit)启动时配置。
 *
 * 【参数】无。
 * 【返回值】iovec 池字节数。
 */
static Size
AioHandleIOVShmemSize(void)
{
	/* each IO handle can have up to io_max_combine_limit iovec objects */
	return mul_size(sizeof(struct iovec),
					mul_size(mul_size(io_max_combine_limit, AioProcs()),
							 io_max_concurrency));
}

/*
 * AioHandleDataShmemSize - (中文)计算 handle_data 池所需字节数
 *
 * 【作用】request 阶段使用:每个 iovec 对应一个"句柄数据"槽位
 * (如 Buffer ID,完成回调据此更新对应 BufferDesc),故规模与 iovec
 * 池一致(AioProcs() × io_max_concurrency × io_max_combine_limit 个
 * uint64)。注意实际 iovec 条目可能少于该上限:相邻页会合并进同一个
 * iovec 段(见 PgAioCtl->handle_data 的英文注释)。
 *
 * 【参数】无。
 * 【返回值】handle_data 池字节数。
 */
static Size
AioHandleDataShmemSize(void)
{
	/* each buffer referenced by an iovec can have associated data */
	return mul_size(sizeof(uint64),
					mul_size(mul_size(io_max_combine_limit, AioProcs()),
							 io_max_concurrency));
}

/*
 * Choose a suitable value for io_max_concurrency.
 *
 * It's unlikely that we could have more IOs in flight than buffers that we
 * would be allowed to pin.
 *
 * On the upper end, apply a cap too - just because shared_buffers is large,
 * it doesn't make sense have millions of buffers undergo IO concurrently.
 */
/*
 * AioChooseMaxConcurrency - (中文)自动整定 io_max_concurrency 的取值
 *
 * 【作用】当用户把 io_max_concurrency 设为 -1("自动")时,启动早期
 * (request 阶段)按系统配置推算一个合理值:每个后端可同时 pin 的缓冲
 * 区数不应超过"共享缓冲池按进程均分"的份额(NBuffers / 总进程数,
 * 与 LimitAdditionalPins() 同源思路),因为每发起一个 IO 至少要 pin 住
 * 一个缓冲区;下限 1;上限 64——shared_buffers 很大也不值得让几百万
 * 个缓冲区同时做 IO。
 *
 * 【设计思想】整定延迟到启动早期而非 GUC 校验钩子里做,是因为该值
 * 依赖 NBuffers/MaxBackends 等其他 GUC 的最终值。计算出的值随后经
 * SetConfigOption 写回 GUC(见 AioShmemRequest),让配置系统记录其
 * 来源;若 DBA 在配置里显式写了 -1,PGC_S_DYNAMIC_DEFAULT 覆盖不了,
 * 需用 PGC_S_OVERRIDE 强制。
 *
 * 【参数】无。
 * 【返回值】推荐的 io_max_concurrency 值(1 ~ 64)。
 */
static int
AioChooseMaxConcurrency(void)
{
	uint32		max_backends;
	int			max_proportional_pins;

	/* Similar logic to LimitAdditionalPins() */
	max_backends = MaxBackends + NUM_AUXILIARY_PROCS;
	max_proportional_pins = NBuffers / max_backends;

	max_proportional_pins = Max(max_proportional_pins, 1);

	/* apply upper limit */
	return Min(max_proportional_pins, 64);
}

/*
 * Register AIO subsystem's shared memory needs.
 */
/*
 * AioShmemRequest - (中文)request 阶段:声明 AIO 的共享内存需求
 *
 * 【作用】postmaster 启动、共享内存总量尚未决定时调用:
 * 1. 若 io_max_concurrency 仍是 -1,用 AioChooseMaxConcurrency() 整定
 *    并写回 GUC(来源标记为动态默认;DBA 显式配置的 -1 无法被动态
 *    默认覆盖时改用 PGC_S_OVERRIDE 强制);
 * 2. 向共享内存子系统逐一申报五段内存:主控制结构 PgAioCtl、每后端
 *    状态数组、句柄池、iovec 池、handle_data 池(指针写入静态变量,
 *    init 阶段直接用);
 * 3. 透传当前 IO 方法的 request 回调(如 worker 方法需要为任务队列
 *    申请共享内存、io_uring 需要为 ring 预留空间)。
 *
 * 【设计思想】"先集中申报、后统一分配、再分别初始化"的三段式协议是
 * 共享内存子系统的通用模式:先统计总需求避免重复分配、保证同一块
 * 区域只被一个子系统使用。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
AioShmemRequest(void *arg)
{
	/*
	 * Resolve io_max_concurrency if not already done
	 *
	 * We prefer to report this value's source as PGC_S_DYNAMIC_DEFAULT.
	 * However, if the DBA explicitly set io_max_concurrency = -1 in the
	 * config file, then PGC_S_DYNAMIC_DEFAULT will fail to override that and
	 * we must force the matter with PGC_S_OVERRIDE.
	 */
	if (io_max_concurrency == -1)
	{
		char		buf[32];

		snprintf(buf, sizeof(buf), "%d", AioChooseMaxConcurrency());
		SetConfigOption("io_max_concurrency", buf, PGC_POSTMASTER,
						PGC_S_DYNAMIC_DEFAULT);
		if (io_max_concurrency == -1)	/* failed to apply it? */
			SetConfigOption("io_max_concurrency", buf, PGC_POSTMASTER,
							PGC_S_OVERRIDE);
	}

	ShmemRequestStruct(.name = "AioCtl",
					   .size = sizeof(PgAioCtl),
					   .ptr = (void **) &pgaio_ctl,
		);

	ShmemRequestStruct(.name = "AioBackend",
					   .size = AioBackendShmemSize(),
					   .ptr = (void **) &AioBackendShmemPtr,
		);

	ShmemRequestStruct(.name = "AioHandle",
					   .size = AioHandleShmemSize(),
					   .ptr = (void **) &AioHandleShmemPtr,
		);

	ShmemRequestStruct(.name = "AioHandleIOV",
					   .size = AioHandleIOVShmemSize(),
					   .ptr = (void **) &AioHandleIOVShmemPtr,
		);

	ShmemRequestStruct(.name = "AioHandleData",
					   .size = AioHandleDataShmemSize(),
					   .ptr = (void **) &AioHandleDataShmemPtr,
		);

	if (pgaio_method_ops->shmem_callbacks.request_fn)
		pgaio_method_ops->shmem_callbacks.request_fn(pgaio_method_ops->shmem_callbacks.opaque_arg);
}

/*
 * Initialize AIO shared memory during postmaster startup.
 */
/*
 * AioShmemInit - (中文)init 阶段:初始化共享内存中的 AIO 数据结构
 *
 * 【作用】共享内存分配完成后(仅 postmaster)调用:
 * 1. 设置 PgAioCtl 的规模字段与四块内存的互相接线(backend_state /
 *    io_handles / iovecs / handle_data);
 * 2. 逐进程(procno 0 .. AioProcs()-1)初始化 PgAioBackend:
 *    - 计算该进程句柄段在句柄池里的起始偏移 io_handle_off(静态划分,
 *      之后 pgaio_my_backend 直接按 ProcNumber 索引,无需加锁);
 *    - 初始化空闲/in-flight 链表与 staged 数组;
 *    - 逐个初始化该进程的 io_max_concurrency 个句柄:代数从 1 起
 *      (0 表示"从未发放",保留给 pgaio_io_get_wref 的 Assert),
 *      归属进程写死为 procno,分配 iovec/handle_data 段偏移,初始化
 *      条件变量,挂进空闲链表;
 * 3. 透传当前 IO 方法的 init 回调(如 worker 方法初始化任务队列、
 *    io_uring 初始化 ring)。
 *
 * 【设计思想】句柄池的"按进程静态分段"是本子系统无锁并发的根基:
 * 每个后端只触碰自己那一段句柄,跨进程的唯一交互点是"完成回调被
 * 别处执行"时的状态字段读。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
AioShmemInit(void *arg)
{
	uint32		io_handle_off = 0;
	uint32		iovec_off = 0;
	uint32		per_backend_iovecs = io_max_concurrency * io_max_combine_limit;

	pgaio_ctl->io_handle_count = AioProcs() * io_max_concurrency;
	pgaio_ctl->iovec_count = AioProcs() * per_backend_iovecs;

	pgaio_ctl->backend_state = AioBackendShmemPtr;
	pgaio_ctl->io_handles = AioHandleShmemPtr;
	pgaio_ctl->iovecs = AioHandleIOVShmemPtr;
	pgaio_ctl->handle_data = AioHandleDataShmemPtr;

	for (uint32 procno = 0; procno < AioProcs(); procno++)
	{
		PgAioBackend *bs = &pgaio_ctl->backend_state[procno];

		bs->io_handle_off = io_handle_off;
		io_handle_off += io_max_concurrency;

		dclist_init(&bs->idle_ios);
		memset(bs->staged_ios, 0, sizeof(PgAioHandle *) * PGAIO_SUBMIT_BATCH_SIZE);
		dclist_init(&bs->in_flight_ios);

		/* initialize per-backend IOs */
		for (int i = 0; i < io_max_concurrency; i++)
		{
			PgAioHandle *ioh = &pgaio_ctl->io_handles[bs->io_handle_off + i];

			ioh->generation = 1;
			ioh->owner_procno = procno;
			ioh->iovec_off = iovec_off;
			ioh->handle_data_len = 0;
			ioh->report_return = NULL;
			ioh->resowner = NULL;
			ioh->num_callbacks = 0;
			ioh->distilled_result.status = PGAIO_RS_UNKNOWN;
			ioh->flags = 0;

			ConditionVariableInit(&ioh->cv);

			dclist_push_tail(&bs->idle_ios, &ioh->node);
			iovec_off += io_max_combine_limit;
		}
	}

	if (pgaio_method_ops->shmem_callbacks.init_fn)
		pgaio_method_ops->shmem_callbacks.init_fn(pgaio_method_ops->shmem_callbacks.opaque_arg);
}

/*
 * AioShmemAttach - (中文)attach 阶段:各进程附着 AIO 共享内存
 *
 * 【作用】每个后端进程启动、共享内存映射完成后调用:把当前 IO 方法的
 * attach 回调透传下去(如 io_uring 需要在每个进程的地址空间里重新
 * 初始化 ring;worker 方法则通常无此需求)。AIO 自身的指针(句柄池等)
 * 由共享内存子系统统一映射,无需在此处理。
 *
 * 【参数】arg —— 未使用(回调协议保留)。
 * 【返回值】无。
 */
static void
AioShmemAttach(void *arg)
{
	if (pgaio_method_ops->shmem_callbacks.attach_fn)
		pgaio_method_ops->shmem_callbacks.attach_fn(pgaio_method_ops->shmem_callbacks.opaque_arg);
}

/*
 * pgaio_init_backend - (中文)后端进程的 AIO 本地初始化
 *
 * 【作用】每个非 IO-worker 后端进程启动时调用:
 * 1. 校验尚未初始化(Assert)且本进程有合法 PGPROC(ProcNumber 在
 *    AioProcs() 范围内),否则报错;
 * 2. 把 pgaio_my_backend 指向共享内存中本进程的 PgAioBackend;
 * 3. 调用当前 IO 方法的 init_backend(如 io_uring 建立本进程的 ring,
 *    worker 建立与 worker 池通信的管道、订阅 worker 的通知);
 * 4. 登记进程退出回调 pgaio_shutdown(等待在途 IO 收尾)。
 *
 * 【设计思想】IO worker 进程(B_IO_WORKER)不发起 AIO、没有自己的
 * 句柄,直接跳过,避免为它们分配上下文。此函数必须由常规后端在
 * 首次使用 AIO 前调用(通常在共享内存子系统 attach 之后)。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
pgaio_init_backend(void)
{
	/* shouldn't be initialized twice */
	Assert(!pgaio_my_backend);

	if (MyBackendType == B_IO_WORKER)
		return;

	if (MyProc == NULL || MyProcNumber >= AioProcs())
		elog(ERROR, "aio requires a normal PGPROC");

	pgaio_my_backend = &pgaio_ctl->backend_state[MyProcNumber];

	if (pgaio_method_ops->init_backend)
		pgaio_method_ops->init_backend();

	before_shmem_exit(pgaio_shutdown, 0);
}
