/*-------------------------------------------------------------------------
 *
 * shm_mq.c
 *	  single-reader, single-writer shared memory message queue
 *
 * Both the sender and the receiver must have a PGPROC; their respective
 * process latches are used for synchronization.  Only the sender may send,
 * and only the receiver may receive.  This is intended to allow a user
 * backend to communicate with worker backends that it has registered.
 *
 * 【模块总览(中文)】
 * 本文件实现"单读单写"的共享内存消息队列(single-reader, single-writer
 * shared memory message queue),是并行查询(parallel query)与后台工作者
 * (bgworker)之间传递数据的核心通信原语。队列本体 shm_mq 存放在动态共享
 * 内存段(DSM)中:一个进程作为发送者(sender)写入,另一个进程作为接收者
 * (receiver)读出,二者通过各自的进程闩锁(procLatch)互相唤醒。
 *
 * 【消息格式与缓冲结构】
 * 每条消息 = 一个 Size 长度的头部(消息字节数)+ 消息数据,环内写入都按
 * MAXIMUM_ALIGNOF 对齐。数据存放在环形缓冲区 mq_ring 中,两个单调递增
 * 的字节计数 mq_bytes_read / mq_bytes_written 之差给出"未读字节数",
 * 读写游标即计数对环大小取模。
 *
 * 【同步设计】
 * - 环形缓冲区数据区完全不加锁:读方只读"自己确认未读"的区域,写方只写
 *   "读方已消费掉"的区域,两者永不重叠;游标计数用 64 位原子读写 + 内存
 *   屏障(barrier)同步;
 * - 等待/唤醒借助 latch.c 的进程闩锁:发/收方在缓冲区满/空时 WaitLatch
 *   睡眠,对方写完/读完后 SetLatch 唤醒;
 * - mq_detached 标志表示任一方已退出,置位后必须唤醒对方,使其从阻塞中
 *   返回 SHM_MQ_DETACHED 而不是永远等待;
 * - 小数据的"攒批"优化:大量小消息时,把"推进共享计数 + SetLatch 唤醒
 *   对方"推迟到攒够 1/4 环大小再一次性执行(见 mqh_send_pending /
 *   mqh_consume_pending),因为 SetLatch 相当昂贵且会造成 CPU 缓存失效。
 *
 * 【典型调用链】
 * 并行查询建立管道时:shm_mq_create 建队列 → shm_mq_set_sender /
 * shm_mq_set_receiver 登记两端 → 双方各自 shm_mq_attach 得到句柄 →
 * 发送方 shm_mq_send(shm_mq_sendv 的包装)→ 接收方 shm_mq_receive →
 * 结束后 shm_mq_detach。需要等待对方"上线"时用 shm_mq_wait_for_attach。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/storage/ipc/shm_mq.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "miscadmin.h"
#include "pgstat.h"
#include "port/pg_bitutils.h"
#include "postmaster/bgworker.h"
#include "storage/proc.h"
#include "storage/shm_mq.h"
#include "storage/spin.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

/*
 * This structure represents the actual queue, stored in shared memory.
 *
 * Some notes on synchronization:
 *
 * mq_receiver and mq_bytes_read can only be changed by the receiver; and
 * mq_sender and mq_bytes_written can only be changed by the sender.
 * mq_receiver and mq_sender are protected by mq_mutex, although, importantly,
 * they cannot change once set, and thus may be read without a lock once this
 * is known to be the case.
 *
 * mq_bytes_read and mq_bytes_written are not protected by the mutex.  Instead,
 * they are written atomically using 8 byte loads and stores.  Memory barriers
 * must be carefully used to synchronize reads and writes of these values with
 * reads and writes of the actual data in mq_ring.
 *
 * mq_detached needs no locking.  It can be set by either the sender or the
 * receiver, but only ever from false to true, so redundant writes don't
 * matter.  It is important that if we set mq_detached and then set the
 * counterparty's latch, the counterparty must be certain to see the change
 * after waking up.  Since SetLatch begins with a memory barrier and ResetLatch
 * ends with one, this should be OK.
 *
 * mq_ring_size and mq_ring_offset never change after initialization, and
 * can therefore be read without the lock.
 *
 * Importantly, mq_ring can be safely read and written without a lock.
 * At any given time, the difference between mq_bytes_read and
 * mq_bytes_written defines the number of bytes within mq_ring that contain
 * unread data, and mq_bytes_read defines the position where those bytes
 * begin.  The sender can increase the number of unread bytes at any time,
 * but only the receiver can give license to overwrite those bytes, by
 * incrementing mq_bytes_read.  Therefore, it's safe for the receiver to read
 * the unread bytes it knows to be present without the lock.  Conversely,
 * the sender can write to the unused portion of the ring buffer without
 * the lock, because nobody else can be reading or writing those bytes.  The
 * receiver could be making more bytes unused by incrementing mq_bytes_read,
 * but that's OK.  Note that it would be unsafe for the receiver to read any
 * data it's already marked as read, or to write any data; and it would be
 * unsafe for the sender to reread any data after incrementing
 * mq_bytes_written, but fortunately there's no need for any of that.
 */
/* 共享内存中的消息队列本体(单读单写):
 * - mq_mutex          : 保护 mq_receiver / mq_sender / mq_detached 的
 *                       自旋锁(mq_bytes_read/written 与 mq_ring 不用它);
 * - mq_receiver       : 接收方 PGPROC。只能被"登记方"设置一次,一经设置
 *                       不再变化,因此"已知被设置"后可以免锁读取;
 * - mq_sender         : 发送方 PGPROC,语义同上;
 * - mq_bytes_read     : 已消费(读)的累计字节数,仅接收方写;原子读写,
 *                       与 mq_ring 的读写之间靠内存屏障同步;
 * - mq_bytes_written  : 已写入的累计字节数,仅发送方写;语义同上;
 * - mq_ring_size      : 环形缓冲区字节数(初始化后不变,可免锁读);
 * - mq_detached       : 任一方已脱离的标志,只从 false 变 true,冗余写
 *                       无害故无需加锁;置位后必须再置对方 latch,保证
 *                       对方醒来后必然看到新值(SetLatch 前有内存屏障,
 *                       ResetLatch 后有);
 * - mq_ring_offset    : 数据区相对 mq_ring 字段起始的字节偏移(对齐后的
 *                       真实数据起点,初始化后不变);
 * - mq_ring[]         : 环形数据区(柔性数组),容量 mq_ring_size。
 *
 * 环形缓冲区协议(无锁读写的关键):"未读字节数"= mq_bytes_written -
 * mq_bytes_read;发送方只写"读方已消费"的区域,接收方只读"自己确认未读"
 * 的区域,因此双方可以不持锁直接读写各自的区域,游标推进互相独立、互不
 * 覆盖。 */
struct shm_mq
{
	slock_t		mq_mutex;
	PGPROC	   *mq_receiver;
	PGPROC	   *mq_sender;
	pg_atomic_uint64 mq_bytes_read;
	pg_atomic_uint64 mq_bytes_written;
	Size		mq_ring_size;
	bool		mq_detached;
	uint8		mq_ring_offset;
	char		mq_ring[FLEXIBLE_ARRAY_MEMBER];
};

/*
 * This structure is a backend-private handle for access to a queue.
 *
 * mqh_queue is a pointer to the queue we've attached, and mqh_segment is
 * an optional pointer to the dynamic shared memory segment that contains it.
 * (If mqh_segment is provided, we register an on_dsm_detach callback to
 * make sure we detach from the queue before detaching from DSM.)
 *
 * If this queue is intended to connect the current process with a background
 * worker that started it, the user can pass a pointer to the worker handle
 * to shm_mq_attach(), and we'll store it in mqh_handle.  The point of this
 * is to allow us to begin sending to or receiving from that queue before the
 * process we'll be communicating with has even been started.  If it fails
 * to start, the handle will allow us to notice that and fail cleanly, rather
 * than waiting forever; see shm_mq_wait_internal.  This is mostly useful in
 * simple cases - e.g. where there are just 2 processes communicating; in
 * more complex scenarios, every process may not have a BackgroundWorkerHandle
 * available, or may need to watch for the failure of more than one other
 * process at a time.
 *
 * When a message exists as a contiguous chunk of bytes in the queue - that is,
 * it is smaller than the size of the ring buffer and does not wrap around
 * the end - we return the message to the caller as a pointer into the buffer.
 * For messages that are larger or happen to wrap, we reassemble the message
 * locally by copying the chunks into a backend-local buffer.  mqh_buffer is
 * the buffer, and mqh_buflen is the number of bytes allocated for it.
 *
 * mqh_send_pending, is number of bytes that is written to the queue but not
 * yet updated in the shared memory.  We will not update it until the written
 * data is 1/4th of the ring size or the tuple queue is full.  This will
 * prevent frequent CPU cache misses, and it will also avoid frequent
 * SetLatch() calls, which are quite expensive.
 *
 * mqh_partial_bytes, mqh_expected_bytes, and mqh_length_word_complete
 * are used to track the state of non-blocking operations.  When the caller
 * attempts a non-blocking operation that returns SHM_MQ_WOULD_BLOCK, they
 * are expected to retry the call at a later time with the same argument;
 * we need to retain enough state to pick up where we left off.
 * mqh_length_word_complete tracks whether we are done sending or receiving
 * (whichever we're doing) the entire length word.  mqh_partial_bytes tracks
 * the number of bytes read or written for either the length word or the
 * message itself, and mqh_expected_bytes - which is used only for reads -
 * tracks the expected total size of the payload.
 *
 * mqh_counterparty_attached tracks whether we know the counterparty to have
 * attached to the queue at some previous point.  This lets us avoid some
 * mutex acquisitions.
 *
 * mqh_context is the memory context in effect at the time we attached to
 * the shm_mq.  The shm_mq_handle itself is allocated in this context, and
 * we make sure any other allocations we do happen in this context as well,
 * to avoid nasty surprises.
 */
/* 后端私有的队列句柄(本进程 palloc 内存,不进共享内存):
 * - mqh_queue        : 所附着的队列指针;
 * - mqh_segment      : 可选:队列所在的 DSM 段;非 NULL 时注册
 *                       on_dsm_detach 回调,保证段拆除前自动脱离队列;
 * - mqh_handle       : 可选:对端 bgworker 的句柄,用于在对方启动之前就
 *                      开始 send/receive——等不到时靠它察觉对方死亡,
 *                      避免永久等待(见 shm_mq_wait_internal);
 * - mqh_buffer       : 本进程私有的拼装缓冲,用于"消息过大 / 跨环回绕"
 *                      需要重组的场景;消息小且连续时直接返回环内指针,
 *                      省掉一次拷贝;
 * - mqh_buflen       : mqh_buffer 的已分配字节数;
 * - mqh_consume_pending: 已从环中读出、但尚未写回共享计数 mq_bytes_read
 *                      的字节数;攒够 1/4 环大小再一次性提交,减少
 *                      SetLatch 与 CPU 缓存失效开销;
 * - mqh_send_pending : 已写入环中、但尚未计入 mq_bytes_written 的字节数,
 *                      同理延迟提交;
 * - mqh_partial_bytes: 当前正在发送/接收的"长度字或消息体"中已完成部分
 *                      的字节数;nowait 模式中途退出后靠它续传;
 * - mqh_expected_bytes: 接收侧:整个消息体应有的字节数(读长度字后得知);
 * - mqh_length_word_complete: 长度字是否已完整发送/接收;
 * - mqh_counterparty_attached: 是否已确认对方已 attach(避免反复取锁);
 * - mqh_context      : attach 时的内存上下文,句柄与后续所有分配都在其中
 *                      进行,防止上下文被意外切换。 */
struct shm_mq_handle
{
	shm_mq	   *mqh_queue;
	dsm_segment *mqh_segment;
	BackgroundWorkerHandle *mqh_handle;
	char	   *mqh_buffer;
	Size		mqh_buflen;
	Size		mqh_consume_pending;
	Size		mqh_send_pending;
	Size		mqh_partial_bytes;
	Size		mqh_expected_bytes;
	bool		mqh_length_word_complete;
	bool		mqh_counterparty_attached;
	MemoryContext mqh_context;
};

/* 内部函数的前置声明,权威注释见各定义处。 */
static void shm_mq_detach_internal(shm_mq *mq);
static shm_mq_result shm_mq_send_bytes(shm_mq_handle *mqh, Size nbytes,
									   const void *data, bool nowait, Size *bytes_written);
static shm_mq_result shm_mq_receive_bytes(shm_mq_handle *mqh,
										  Size bytes_needed, bool nowait, Size *nbytesp,
										  void **datap);
static bool shm_mq_counterparty_gone(shm_mq *mq,
									 BackgroundWorkerHandle *handle);
static bool shm_mq_wait_internal(shm_mq *mq, PGPROC **ptr,
								 BackgroundWorkerHandle *handle);
static void shm_mq_inc_bytes_read(shm_mq *mq, Size n);
static void shm_mq_inc_bytes_written(shm_mq *mq, Size n);
static void shm_mq_detach_callback(dsm_segment *seg, Datum arg);

/* Minimum queue size is enough for header and at least one chunk of data. */
/* 队列的最小合法大小:能容纳"对齐后的头结构 + 至少一个对齐单元的数据"。
 * 创建者应保证传入的段大小 >= 此值(见 shm_mq_create 的断言)。 */
const Size	shm_mq_minimum_size =
MAXALIGN(offsetof(shm_mq, mq_ring)) + MAXIMUM_ALIGNOF;

/* 接收侧重组缓冲的初始大小:长度字被拆开时,先按这个大小分配缓冲 */
#define MQH_INITIAL_BUFSIZE				8192

/*
 * Initialize a new shared message queue.
 */
/*
 * shm_mq_create - (中文)在共享内存中初始化一个新的消息队列
 *
 * 【作用】把调用方提供的共享内存区域(address 起 size 字节)初始化为一个
 * 空队列:清零两端 PGPROC 指针与读写字节计数,登记环大小与数据区偏移。
 * 必须由"建立队列"的进程在把该内存共享给其他进程之前调用。
 *
 * 【设计思想】size 先向下 MAXALIGN,使环大小成为 MAXIMUM_ALIGNOF 的整数
 * 倍,保证环内每次对齐写入都不会跨 MAXALIGN 边界(见 shm_mq_send_bytes);
 * mq_ring_offset 记录"对齐后的数据区起点",显式跳过头结构与数据区之间的
 * 填充字节。
 *
 * 【参数】
 *   address —— 共享内存区域的起始地址;
 *   size    —— 该区域的字节数(应 >= shm_mq_minimum_size)。
 * 【返回值】指向初始化好的 shm_mq(即 address)。
 */
shm_mq *
shm_mq_create(void *address, Size size)
{
	shm_mq	   *mq = address;
	Size		data_offset = MAXALIGN(offsetof(shm_mq, mq_ring));

	/* If the size isn't MAXALIGN'd, just discard the odd bytes. */
	size = MAXALIGN_DOWN(size);

	/* Queue size must be large enough to hold some data. */
	Assert(size > data_offset);

	/* Initialize queue header. */
	SpinLockInit(&mq->mq_mutex);
	mq->mq_receiver = NULL;
	mq->mq_sender = NULL;
	pg_atomic_init_u64(&mq->mq_bytes_read, 0);
	pg_atomic_init_u64(&mq->mq_bytes_written, 0);
	mq->mq_ring_size = size - data_offset;
	mq->mq_detached = false;
	mq->mq_ring_offset = data_offset - offsetof(shm_mq, mq_ring);

	return mq;
}

/*
 * Set the identity of the process that will receive from a shared message
 * queue.
 */
/*
 * shm_mq_set_receiver - (中文)登记消息队列的接收方
 *
 * 【作用】建立方在把队列交给接收方之前调用:把 mq_receiver 设为接收方的
 * PGPROC。若发送方已先登记,则顺手 SetLatch 唤醒它——它可能正等在对端
 * attach 的闩锁上(见 shm_mq_wait_internal)。
 *
 * 【设计思想】持锁写 mq_receiver(断言此前为 NULL,保证只设置一次),然后
 * 在读锁释放后唤醒发送方。这一"唤醒"使"先登记接收方还是先登记发送方"
 * 的顺序无关化,任一方先启动都不会死等。
 *
 * 【参数】
 *   mq   —— 队列;
 *   proc —— 接收方进程的 PGPROC。
 * 【返回值】无。
 */
void
shm_mq_set_receiver(shm_mq *mq, PGPROC *proc)
{
	PGPROC	   *sender;

	SpinLockAcquire(&mq->mq_mutex);
	Assert(mq->mq_receiver == NULL);
	mq->mq_receiver = proc;
	sender = mq->mq_sender;
	SpinLockRelease(&mq->mq_mutex);

	if (sender != NULL)
		SetLatch(&sender->procLatch);
}

/*
 * Set the identity of the process that will send to a shared message queue.
 */
/*
 * shm_mq_set_sender - (中文)登记消息队列的发送方
 *
 * 【作用】建立方在把队列交给发送方之前调用:把 mq_sender 设为发送方的
 * PGPROC。若接收方已先登记,则顺手 SetLatch 唤醒它(它可能正等发送方
 * attach)。
 *
 * 【设计思想】与 shm_mq_set_receiver 完全对称:持锁单次写入 + 锁外唤醒
 * 对方,保证两个方向的"先启动者等待后启动者"都成立。
 *
 * 【参数】
 *   mq   —— 队列;
 *   proc —— 发送方进程的 PGPROC。
 * 【返回值】无。
 */
void
shm_mq_set_sender(shm_mq *mq, PGPROC *proc)
{
	PGPROC	   *receiver;

	SpinLockAcquire(&mq->mq_mutex);
	Assert(mq->mq_sender == NULL);
	mq->mq_sender = proc;
	receiver = mq->mq_receiver;
	SpinLockRelease(&mq->mq_mutex);

	if (receiver != NULL)
		SetLatch(&receiver->procLatch);
}

/*
 * Get the configured receiver.
 */
/*
 * shm_mq_get_receiver - (中文)读取队列配置的接收方
 *
 * 【作用】返回 mq_receiver。本函数不能免锁读:调用方无法确定该字段
 * "是否已被设置",因此总是持锁读取,换取正确的 NULL/非 NULL 语义。
 * (已知被设置后,热路径代码改用免锁读,见 shm_mq_sendv。)
 *
 * 【参数】mq —— 队列。
 * 【返回值】接收方 PGPROC;未设置时返回 NULL。
 */
PGPROC *
shm_mq_get_receiver(shm_mq *mq)
{
	PGPROC	   *receiver;

	SpinLockAcquire(&mq->mq_mutex);
	receiver = mq->mq_receiver;
	SpinLockRelease(&mq->mq_mutex);

	return receiver;
}

/*
 * Get the configured sender.
 */
/*
 * shm_mq_get_sender - (中文)读取队列配置的发送方
 *
 * 【作用】返回 mq_sender。与 shm_mq_get_receiver 对称,总是持锁读取以
 * 获得可靠的 NULL/非 NULL 语义。
 *
 * 【参数】mq —— 队列。
 * 【返回值】发送方 PGPROC;未设置时返回 NULL。
 */
PGPROC *
shm_mq_get_sender(shm_mq *mq)
{
	PGPROC	   *sender;

	SpinLockAcquire(&mq->mq_mutex);
	sender = mq->mq_sender;
	SpinLockRelease(&mq->mq_mutex);

	return sender;
}

/*
 * Attach to a shared message queue so we can send or receive messages.
 *
 * The memory context in effect at the time this function is called should
 * be one which will last for at least as long as the message queue itself.
 * We'll allocate the handle in that context, and future allocations that
 * are needed to buffer incoming data will happen in that context as well.
 *
 * If seg != NULL, the queue will be automatically detached when that dynamic
 * shared memory segment is detached.
 *
 * If handle != NULL, the queue can be read or written even before the
 * other process has attached.  We'll wait for it to do so if needed.  The
 * handle must be for a background worker initialized with bgw_notify_pid
 * equal to our PID.
 *
 * shm_mq_detach() should be called when done.  This will free the
 * shm_mq_handle and mark the queue itself as detached, so that our
 * counterpart won't get stuck waiting for us to fill or drain the queue
 * after we've already lost interest.
 */
/*
 * shm_mq_attach - (中文)附着到一个队列,得到本进程私有句柄
 *
 * 【作用】发送方或接收方在"确认自己已被登记为 mq_sender / mq_receiver"
 * 后调用:分配并初始化 shm_mq_handle,返回给上层使用。
 *
 * 【设计思想】句柄与后续所有缓冲都分配在当前内存上下文,调用方应保证
 * 该上下文存活期 >= 队列使用期;若给了 seg,注册 on_dsm_detach 回调,
 * DSM 段被拆除时自动执行"仅标记 detached"的清理(此时句柄可能已被
 * 释放,回调不得触碰它,见 shm_mq_detach_internal);handle 参数允许
 * 本进程在对方还没启动时就提前 send/receive,配合 shm_mq_wait_internal
 * 的死亡检测避免永久等待。
 *
 * 【参数】
 *   mq     —— 队列;
 *   seg    —— 队列所在的 DSM 段,可 NULL;
 *   handle —— 对端 bgworker 的句柄,可 NULL。
 * 【返回值】新的句柄;用完须 shm_mq_detach 释放。
 */
shm_mq_handle *
shm_mq_attach(shm_mq *mq, dsm_segment *seg, BackgroundWorkerHandle *handle)
{
	shm_mq_handle *mqh = palloc_object(shm_mq_handle);

	Assert(mq->mq_receiver == MyProc || mq->mq_sender == MyProc);
	mqh->mqh_queue = mq;
	mqh->mqh_segment = seg;
	mqh->mqh_handle = handle;
	mqh->mqh_buffer = NULL;
	mqh->mqh_buflen = 0;
	mqh->mqh_consume_pending = 0;
	mqh->mqh_send_pending = 0;
	mqh->mqh_partial_bytes = 0;
	mqh->mqh_expected_bytes = 0;
	mqh->mqh_length_word_complete = false;
	mqh->mqh_counterparty_attached = false;
	mqh->mqh_context = CurrentMemoryContext;

	if (seg != NULL)
		on_dsm_detach(seg, shm_mq_detach_callback, PointerGetDatum(mq));

	return mqh;
}

/*
 * Associate a BackgroundWorkerHandle with a shm_mq_handle just as if it had
 * been passed to shm_mq_attach.
 */
/*
 * shm_mq_set_handle - (中文)给已有句柄补充设置 bgworker 句柄
 *
 * 【作用】在 shm_mq_attach 之后、开始使用之前,把 BackgroundWorkerHandle
 * 挂到句柄上,效果与 attach 时直接传入相同。常用于"attach 时还拿不到
 * worker 句柄、稍后才获得"的场合。
 *
 * 【设计思想】仅做一次"空 → 非空"的赋值(断言防重复设置);此后
 * shm_mq_wait_internal 等路径即可借该句柄检测对端死亡。
 *
 * 【参数】
 *   mqh    —— 句柄;
 *   handle —— 对端 bgworker 的句柄。
 * 【返回值】无。
 */
void
shm_mq_set_handle(shm_mq_handle *mqh, BackgroundWorkerHandle *handle)
{
	Assert(mqh->mqh_handle == NULL);
	mqh->mqh_handle = handle;
}

/*
 * Write a message into a shared message queue.
 */
/*
 * shm_mq_send - (中文)向队列发送一条消息(单缓冲版本)
 *
 * 【作用】把单块内存中的 nbytes 字节作为一条完整消息发到队列;内部把
 * 数据包装成单个 iovec 后转调 shm_mq_sendv。
 *
 * 【设计思想】共享内存队列要求消息带"长度头",shm_mq_sendv 负责写长度
 * 字;本函数只是把"单块数据"适配到"多块数据"的统一接口上,便于上层在
 * 单块 / 散列两种形态间自由选择,行为与 shm_mq_sendv 完全相同。
 *
 * 【参数】
 *   mqh         —— 句柄(须以发送方身份附着);
 *   nbytes      —— 消息体字节数;
 *   data        —— 消息数据;
 *   nowait      —— true:队列满时返回 SHM_MQ_WOULD_BLOCK;
 *   force_flush —— true:立即把已写数据计到 mq_bytes_written 并唤醒
 *                  接收方。
 * 【返回值】SHM_MQ_SUCCESS / SHM_MQ_WOULD_BLOCK / SHM_MQ_DETACHED。
 */
shm_mq_result
shm_mq_send(shm_mq_handle *mqh, Size nbytes, const void *data, bool nowait,
			bool force_flush)
{
	shm_mq_iovec iov;

	iov.data = data;
	iov.len = nbytes;

	return shm_mq_sendv(mqh, &iov, 1, nowait, force_flush);
}

/*
 * Write a message into a shared message queue, gathered from multiple
 * addresses.
 *
 * When nowait = false, we'll wait on our process latch when the ring buffer
 * fills up, and then continue writing once the receiver has drained some data.
 * The process latch is reset after each wait.
 *
 * When nowait = true, we do not manipulate the state of the process latch;
 * instead, if the buffer becomes full, we return SHM_MQ_WOULD_BLOCK.  In
 * this case, the caller should call this function again, with the same
 * arguments, each time the process latch is set.  (Once begun, the sending
 * of a message cannot be aborted except by detaching from the queue; changing
 * the length or payload will corrupt the queue.)
 *
 * When force_flush = true, we immediately update the shm_mq's mq_bytes_written
 * and notify the receiver (if it is already attached).  Otherwise, we don't
 * update it until we have written an amount of data greater than 1/4th of the
 * ring size.
 */
/*
 * shm_mq_sendv - (中文)把一条散列(多段)消息写入队列
 *
 * 【作用】发送方把 iov[0..iovcnt) 里的数据拼成一条消息发出:先写消息
 * 长度字(一个 Size),再写各段数据。nowait = false 时在缓冲区满时等待
 * 接收方消费后再继续;nowait = true 时直接返回 SHM_MQ_WOULD_BLOCK,
 * 调用方应等 latch 置位后用相同参数重试(消息一旦开始发送就不能中止,
 * 否则会破坏队列)。
 *
 * 【设计思想】
 * - 消息上限 MaxAllocSize,防止单条消息把接收方内存打爆(接收侧也复核);
 * - 长度字用 mqh_partial_bytes / mqh_length_word_complete 支持"写一半
 *   被打断(nowait / 错误)后续传";
 * - 数据段尽量"零拷贝":直接把 iov 内存 memcpy 进环,而非先拼成连续
 *   缓冲;但除最后一段外,每段写入必须 MAXALIGN 对齐——若一段的结尾
 *   凑不满对齐,就把尾部字节与下一段开头合并进临时缓冲(tmpbuf)再写;
 * - force_flush 或已写数据超过环的 1/4 时,才把 mqh_send_pending 计进
 *   共享写计数并 SetLatch 唤醒接收方(攒批减少系统调用与缓存失效);
 * - 若发现队列已 detached,重置续传状态后返回 SHM_MQ_DETACHED,方便
 *   调用方接着尝试发送下一条消息。
 *
 * 【参数】
 *   mqh         —— 句柄(须为发送方);
 *   iov         —— 消息数据段数组;
 *   iovcnt      —— 段数;
 *   nowait      —— true:不等待,满则 WOULD_BLOCK;
 *   force_flush —— true:本次立即推进共享写计数并唤醒接收方。
 * 【返回值】SHM_MQ_SUCCESS / SHM_MQ_WOULD_BLOCK / SHM_MQ_DETACHED。
 */
shm_mq_result
shm_mq_sendv(shm_mq_handle *mqh, shm_mq_iovec *iov, int iovcnt, bool nowait,
			 bool force_flush)
{
	shm_mq_result res;
	shm_mq	   *mq = mqh->mqh_queue;
	PGPROC	   *receiver;
	Size		nbytes = 0;
	Size		bytes_written;
	int			i;
	int			which_iov = 0;
	Size		offset;

	Assert(mq->mq_sender == MyProc);

	/* Compute total size of write. */
	for (i = 0; i < iovcnt; ++i)
		nbytes += iov[i].len;

	/* Prevent writing messages overwhelming the receiver. */
	if (nbytes > MaxAllocSize)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("cannot send a message of size %zu via shared memory queue",
						nbytes)));

	/* Try to write, or finish writing, the length word into the buffer. */
	while (!mqh->mqh_length_word_complete)
	{
		Assert(mqh->mqh_partial_bytes < sizeof(Size));
		res = shm_mq_send_bytes(mqh, sizeof(Size) - mqh->mqh_partial_bytes,
								((char *) &nbytes) + mqh->mqh_partial_bytes,
								nowait, &bytes_written);

		if (res == SHM_MQ_DETACHED)
		{
			/* Reset state in case caller tries to send another message. */
			mqh->mqh_partial_bytes = 0;
			mqh->mqh_length_word_complete = false;
			return res;
		}
		mqh->mqh_partial_bytes += bytes_written;

		if (mqh->mqh_partial_bytes >= sizeof(Size))
		{
			Assert(mqh->mqh_partial_bytes == sizeof(Size));

			mqh->mqh_partial_bytes = 0;
			mqh->mqh_length_word_complete = true;
		}

		if (res != SHM_MQ_SUCCESS)
			return res;

		/* Length word can't be split unless bigger than required alignment. */
		Assert(mqh->mqh_length_word_complete || sizeof(Size) > MAXIMUM_ALIGNOF);
	}

	/* Write the actual data bytes into the buffer. */
	Assert(mqh->mqh_partial_bytes <= nbytes);
	offset = mqh->mqh_partial_bytes;
	do
	{
		Size		chunksize;

		/* Figure out which bytes need to be sent next. */
		if (offset >= iov[which_iov].len)
		{
			offset -= iov[which_iov].len;
			++which_iov;
			if (which_iov >= iovcnt)
				break;
			continue;
		}

		/*
		 * We want to avoid copying the data if at all possible, but every
		 * chunk of bytes we write into the queue has to be MAXALIGN'd, except
		 * the last.  Thus, if a chunk other than the last one ends on a
		 * non-MAXALIGN'd boundary, we have to combine the tail end of its
		 * data with data from one or more following chunks until we either
		 * reach the last chunk or accumulate a number of bytes which is
		 * MAXALIGN'd.
		 */
		if (which_iov + 1 < iovcnt &&
			offset + MAXIMUM_ALIGNOF > iov[which_iov].len)
		{
			char		tmpbuf[MAXIMUM_ALIGNOF];
			int			j = 0;

			for (;;)
			{
				if (offset < iov[which_iov].len)
				{
					tmpbuf[j] = iov[which_iov].data[offset];
					j++;
					offset++;
					if (j == MAXIMUM_ALIGNOF)
						break;
				}
				else
				{
					offset -= iov[which_iov].len;
					which_iov++;
					if (which_iov >= iovcnt)
						break;
				}
			}

			res = shm_mq_send_bytes(mqh, j, tmpbuf, nowait, &bytes_written);

			if (res == SHM_MQ_DETACHED)
			{
				/* Reset state in case caller tries to send another message. */
				mqh->mqh_partial_bytes = 0;
				mqh->mqh_length_word_complete = false;
				return res;
			}

			mqh->mqh_partial_bytes += bytes_written;
			if (res != SHM_MQ_SUCCESS)
				return res;
			continue;
		}

		/*
		 * If this is the last chunk, we can write all the data, even if it
		 * isn't a multiple of MAXIMUM_ALIGNOF.  Otherwise, we need to
		 * MAXALIGN_DOWN the write size.
		 */
		chunksize = iov[which_iov].len - offset;
		if (which_iov + 1 < iovcnt)
			chunksize = MAXALIGN_DOWN(chunksize);
		res = shm_mq_send_bytes(mqh, chunksize, &iov[which_iov].data[offset],
								nowait, &bytes_written);

		if (res == SHM_MQ_DETACHED)
		{
			/* Reset state in case caller tries to send another message. */
			mqh->mqh_length_word_complete = false;
			mqh->mqh_partial_bytes = 0;
			return res;
		}

		mqh->mqh_partial_bytes += bytes_written;
		offset += bytes_written;
		if (res != SHM_MQ_SUCCESS)
			return res;
	} while (mqh->mqh_partial_bytes < nbytes);

	/* Reset for next message. */
	mqh->mqh_partial_bytes = 0;
	mqh->mqh_length_word_complete = false;

	/* If queue has been detached, let caller know. */
	if (mq->mq_detached)
		return SHM_MQ_DETACHED;

	/*
	 * If the counterparty is known to have attached, we can read mq_receiver
	 * without acquiring the spinlock.  Otherwise, more caution is needed.
	 */
	if (mqh->mqh_counterparty_attached)
		receiver = mq->mq_receiver;
	else
	{
		SpinLockAcquire(&mq->mq_mutex);
		receiver = mq->mq_receiver;
		SpinLockRelease(&mq->mq_mutex);
		if (receiver != NULL)
			mqh->mqh_counterparty_attached = true;
	}

	/*
	 * If the caller has requested force flush or we have written more than
	 * 1/4 of the ring size, mark it as written in shared memory and notify
	 * the receiver.
	 */
	if (force_flush || mqh->mqh_send_pending > (mq->mq_ring_size >> 2))
	{
		shm_mq_inc_bytes_written(mq, mqh->mqh_send_pending);
		if (receiver != NULL)
			SetLatch(&receiver->procLatch);
		mqh->mqh_send_pending = 0;
	}

	return SHM_MQ_SUCCESS;
}

/*
 * Receive a message from a shared message queue.
 *
 * We set *nbytes to the message length and *data to point to the message
 * payload.  If the entire message exists in the queue as a single,
 * contiguous chunk, *data will point directly into shared memory; otherwise,
 * it will point to a temporary buffer.  This mostly avoids data copying in
 * the hoped-for case where messages are short compared to the buffer size,
 * while still allowing longer messages.  In either case, the return value
 * remains valid until the next receive operation is performed on the queue.
 *
 * When nowait = false, we'll wait on our process latch when the ring buffer
 * is empty and we have not yet received a full message.  The sender will
 * set our process latch after more data has been written, and we'll resume
 * processing.  Each call will therefore return a complete message
 * (unless the sender detaches the queue).
 *
 * When nowait = true, we do not manipulate the state of the process latch;
 * instead, whenever the buffer is empty and we need to read from it, we
 * return SHM_MQ_WOULD_BLOCK.  In this case, the caller should call this
 * function again after the process latch has been set.
 */
/*
 * shm_mq_receive - (中文)从队列接收一条完整消息
 *
 * 【作用】接收方调用:先等待发送方 attach(必要时),读出长度字与消息体,
 * 通过 *nbytesp / *datap 返回。消息在环中连续不跨绕时,datap 直接指向
 * 环内(零拷贝);否则拼装到本地 mqh_buffer 再返回。返回值在下次 receive
 * 之前一直有效。
 *
 * 【设计思想】
 * - 对端未 attach 时的检查顺序有讲究:nowait 模式先查
 *   shm_mq_counterparty_gone 再查 mq_sender 是否为 NULL——顺序反了会
 *   把"快速 attach 又快速 detach"的发送方误判成"从未 attach";
 * - 长度字可能被拆成多次读到(仅当 sizeof(Size) > MAXIMUM_ALIGNOF 时),
 *   用 mqh_buffer 拼装;正常路径一次读全长度字,还能顺带判断"消息体
 *   是否也在缓冲里",是则直接返回,省一次循环;
 * - 消息长度大于 MaxAllocSize 时抛错(发送侧已拦截,这里做防御);
 * - 消费记账 mqh_consume_pending 攒够环大小 1/4 才写回共享计数并唤醒
 *   发送方(SetLatch 昂贵);消息完全连续时一次计入全部字节;
 * - 跨绕消息:先确认本地缓冲够大(按 2 的幂扩容,上限 MaxAllocSize),
 *   再循环"拷贝一段 → 读下一段",直至凑齐整条消息。
 *
 * 【参数】
 *   mqh     —— 句柄(须为接收方);
 *   nbytesp —— 输出:消息体字节数;
 *   datap   —— 输出:消息数据指针(环内或本地缓冲);
 *   nowait  —— true:数据不足时返回 SHM_MQ_WOULD_BLOCK。
 * 【返回值】SHM_MQ_SUCCESS / SHM_MQ_WOULD_BLOCK / SHM_MQ_DETACHED。
 */
shm_mq_result
shm_mq_receive(shm_mq_handle *mqh, Size *nbytesp, void **datap, bool nowait)
{
	shm_mq	   *mq = mqh->mqh_queue;
	shm_mq_result res;
	Size		rb = 0;
	Size		nbytes;
	void	   *rawdata;

	Assert(mq->mq_receiver == MyProc);

	/* We can't receive data until the sender has attached. */
	if (!mqh->mqh_counterparty_attached)
	{
		if (nowait)
		{
			int			counterparty_gone;

			/*
			 * We shouldn't return at this point at all unless the sender
			 * hasn't attached yet.  However, the correct return value depends
			 * on whether the sender is still attached.  If we first test
			 * whether the sender has ever attached and then test whether the
			 * sender has detached, there's a race condition: a sender that
			 * attaches and detaches very quickly might fool us into thinking
			 * the sender never attached at all.  So, test whether our
			 * counterparty is definitively gone first, and only afterwards
			 * check whether the sender ever attached in the first place.
			 */
			counterparty_gone = shm_mq_counterparty_gone(mq, mqh->mqh_handle);
			if (shm_mq_get_sender(mq) == NULL)
			{
				if (counterparty_gone)
					return SHM_MQ_DETACHED;
				else
					return SHM_MQ_WOULD_BLOCK;
			}
		}
		else if (!shm_mq_wait_internal(mq, &mq->mq_sender, mqh->mqh_handle)
				 && shm_mq_get_sender(mq) == NULL)
		{
			mq->mq_detached = true;
			return SHM_MQ_DETACHED;
		}
		mqh->mqh_counterparty_attached = true;
	}

	/*
	 * If we've consumed an amount of data greater than 1/4th of the ring
	 * size, mark it consumed in shared memory.  We try to avoid doing this
	 * unnecessarily when only a small amount of data has been consumed,
	 * because SetLatch() is fairly expensive and we don't want to do it too
	 * often.
	 */
	if (mqh->mqh_consume_pending > mq->mq_ring_size / 4)
	{
		shm_mq_inc_bytes_read(mq, mqh->mqh_consume_pending);
		mqh->mqh_consume_pending = 0;
	}

	/* Try to read, or finish reading, the length word from the buffer. */
	while (!mqh->mqh_length_word_complete)
	{
		/* Try to receive the message length word. */
		Assert(mqh->mqh_partial_bytes < sizeof(Size));
		res = shm_mq_receive_bytes(mqh, sizeof(Size) - mqh->mqh_partial_bytes,
								   nowait, &rb, &rawdata);
		if (res != SHM_MQ_SUCCESS)
			return res;

		/*
		 * Hopefully, we'll receive the entire message length word at once.
		 * But if sizeof(Size) > MAXIMUM_ALIGNOF, then it might be split over
		 * multiple reads.
		 */
		if (mqh->mqh_partial_bytes == 0 && rb >= sizeof(Size))
		{
			Size		needed;

			nbytes = *(Size *) rawdata;

			/* If we've already got the whole message, we're done. */
			needed = MAXALIGN(sizeof(Size)) + MAXALIGN(nbytes);
			if (rb >= needed)
			{
				mqh->mqh_consume_pending += needed;
				*nbytesp = nbytes;
				*datap = ((char *) rawdata) + MAXALIGN(sizeof(Size));
				return SHM_MQ_SUCCESS;
			}

			/*
			 * We don't have the whole message, but we at least have the whole
			 * length word.
			 */
			mqh->mqh_expected_bytes = nbytes;
			mqh->mqh_length_word_complete = true;
			mqh->mqh_consume_pending += MAXALIGN(sizeof(Size));
			rb -= MAXALIGN(sizeof(Size));
		}
		else
		{
			Size		lengthbytes;

			/* Can't be split unless bigger than required alignment. */
			Assert(sizeof(Size) > MAXIMUM_ALIGNOF);

			/* Message word is split; need buffer to reassemble. */
			if (mqh->mqh_buffer == NULL)
			{
				mqh->mqh_buffer = MemoryContextAlloc(mqh->mqh_context,
													 MQH_INITIAL_BUFSIZE);
				mqh->mqh_buflen = MQH_INITIAL_BUFSIZE;
			}
			Assert(mqh->mqh_buflen >= sizeof(Size));

			/* Copy partial length word; remember to consume it. */
			if (mqh->mqh_partial_bytes + rb > sizeof(Size))
				lengthbytes = sizeof(Size) - mqh->mqh_partial_bytes;
			else
				lengthbytes = rb;
			memcpy(&mqh->mqh_buffer[mqh->mqh_partial_bytes], rawdata,
				   lengthbytes);
			mqh->mqh_partial_bytes += lengthbytes;
			mqh->mqh_consume_pending += MAXALIGN(lengthbytes);
			rb -= lengthbytes;

			/* If we now have the whole word, we're ready to read payload. */
			if (mqh->mqh_partial_bytes >= sizeof(Size))
			{
				Assert(mqh->mqh_partial_bytes == sizeof(Size));
				mqh->mqh_expected_bytes = *(Size *) mqh->mqh_buffer;
				mqh->mqh_length_word_complete = true;
				mqh->mqh_partial_bytes = 0;
			}
		}
	}
	nbytes = mqh->mqh_expected_bytes;

	/*
	 * Should be disallowed on the sending side already, but better check and
	 * error out on the receiver side as well rather than trying to read a
	 * prohibitively large message.
	 */
	if (nbytes > MaxAllocSize)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("invalid message size %zu in shared memory queue",
						nbytes)));

	if (mqh->mqh_partial_bytes == 0)
	{
		/*
		 * Try to obtain the whole message in a single chunk.  If this works,
		 * we need not copy the data and can return a pointer directly into
		 * shared memory.
		 */
		res = shm_mq_receive_bytes(mqh, nbytes, nowait, &rb, &rawdata);
		if (res != SHM_MQ_SUCCESS)
			return res;
		if (rb >= nbytes)
		{
			mqh->mqh_length_word_complete = false;
			mqh->mqh_consume_pending += MAXALIGN(nbytes);
			*nbytesp = nbytes;
			*datap = rawdata;
			return SHM_MQ_SUCCESS;
		}

		/*
		 * The message has wrapped the buffer.  We'll need to copy it in order
		 * to return it to the client in one chunk.  First, make sure we have
		 * a large enough buffer available.
		 */
		if (mqh->mqh_buflen < nbytes)
		{
			Size		newbuflen;

			/*
			 * Increase size to the next power of 2 that's >= nbytes, but
			 * limit to MaxAllocSize.
			 */
			newbuflen = pg_nextpower2_size_t(nbytes);
			newbuflen = Min(newbuflen, MaxAllocSize);

			if (mqh->mqh_buffer != NULL)
			{
				pfree(mqh->mqh_buffer);
				mqh->mqh_buffer = NULL;
				mqh->mqh_buflen = 0;
			}
			mqh->mqh_buffer = MemoryContextAlloc(mqh->mqh_context, newbuflen);
			mqh->mqh_buflen = newbuflen;
		}
	}

	/* Loop until we've copied the entire message. */
	for (;;)
	{
		Size		still_needed;

		/* Copy as much as we can. */
		Assert(mqh->mqh_partial_bytes + rb <= nbytes);
		if (rb > 0)
		{
			memcpy(&mqh->mqh_buffer[mqh->mqh_partial_bytes], rawdata, rb);
			mqh->mqh_partial_bytes += rb;
		}

		/*
		 * Update count of bytes that can be consumed, accounting for
		 * alignment padding.  Note that this will never actually insert any
		 * padding except at the end of a message, because the buffer size is
		 * a multiple of MAXIMUM_ALIGNOF, and each read and write is as well.
		 */
		Assert(mqh->mqh_partial_bytes == nbytes || rb == MAXALIGN(rb));
		mqh->mqh_consume_pending += MAXALIGN(rb);

		/* If we got all the data, exit the loop. */
		if (mqh->mqh_partial_bytes >= nbytes)
			break;

		/* Wait for some more data. */
		still_needed = nbytes - mqh->mqh_partial_bytes;
		res = shm_mq_receive_bytes(mqh, still_needed, nowait, &rb, &rawdata);
		if (res != SHM_MQ_SUCCESS)
			return res;
		if (rb > still_needed)
			rb = still_needed;
	}

	/* Return the complete message, and reset for next message. */
	*nbytesp = nbytes;
	*datap = mqh->mqh_buffer;
	mqh->mqh_length_word_complete = false;
	mqh->mqh_partial_bytes = 0;
	return SHM_MQ_SUCCESS;
}

/*
 * Wait for the other process that's supposed to use this queue to attach
 * to it.
 *
 * The return value is SHM_MQ_DETACHED if the worker has already detached or
 * if it dies; it is SHM_MQ_SUCCESS if we detect that the worker has attached.
 * Note that we will only be able to detect that the worker has died before
 * attaching if a background worker handle was passed to shm_mq_attach().
 */
/*
 * shm_mq_wait_for_attach - (中文)等待对端进程 attach 到队列
 *
 * 【作用】发送方 / 接收方在"想先于对方启动"时调用:阻塞直到对方把
 * mq_sender / mq_receiver 设置好,或对方(通过 bgworker 句柄可感知的
 * 进程死亡 / 队列 detached)确定不会来了。
 *
 * 【设计思想】根据"我是接收方还是发送方"选择要等待的字段;实际等待逻辑
 * 在 shm_mq_wait_internal:轮询检查字段、检测 worker 状态,期间睡在本
 * 进程 latch 上(对方 set_sender / set_receiver 或 detach 时会 SetLatch)。
 *
 * 【参数】mqh —— 句柄。
 * 【返回值】SHM_MQ_SUCCESS:对端已 attach;SHM_MQ_DETACHED:对端已死或
 *          已脱离(注意:无 bgworker 句柄时若对端一直不 attach,本函数
 *          可能永久等待,调用方应尽量避免这种用法)。
 */
shm_mq_result
shm_mq_wait_for_attach(shm_mq_handle *mqh)
{
	shm_mq	   *mq = mqh->mqh_queue;
	PGPROC	  **victim;

	if (shm_mq_get_receiver(mq) == MyProc)
		victim = &mq->mq_sender;
	else
	{
		Assert(shm_mq_get_sender(mq) == MyProc);
		victim = &mq->mq_receiver;
	}

	if (shm_mq_wait_internal(mq, victim, mqh->mqh_handle))
		return SHM_MQ_SUCCESS;
	else
		return SHM_MQ_DETACHED;
}

/*
 * Detach from a shared message queue, and destroy the shm_mq_handle.
 */
/*
 * shm_mq_detach - (中文)脱离队列并销毁句柄
 *
 * 【作用】用完队列后的清理:先把尚未提交的 mqh_send_pending 计进共享写
 * 计数(这样接收方还能读到已写出的那些数据),通知对端"我已离开"
 * (置 mq_detached 并唤醒对方),注销 DSM 回调,最后释放本地缓冲与句柄。
 *
 * 【设计思想】"通知对端"是正确性关键:不让对方阻塞在我们身上。发送方
 * detach 后,接收方仍可读完环里剩余消息,之后的 receive 返回
 * SHM_MQ_DETACHED;接收方 detach 后,发送方的 send 立即得到
 * SHM_MQ_DETACHED。
 *
 * 【参数】mqh —— 句柄。
 * 【返回值】无。
 */
void
shm_mq_detach(shm_mq_handle *mqh)
{
	/* Before detaching, notify the receiver about any already-written data. */
	if (mqh->mqh_send_pending > 0)
	{
		shm_mq_inc_bytes_written(mqh->mqh_queue, mqh->mqh_send_pending);
		mqh->mqh_send_pending = 0;
	}

	/* Notify counterparty that we're outta here. */
	shm_mq_detach_internal(mqh->mqh_queue);

	/* Cancel on_dsm_detach callback, if any. */
	if (mqh->mqh_segment)
		cancel_on_dsm_detach(mqh->mqh_segment,
							 shm_mq_detach_callback,
							 PointerGetDatum(mqh->mqh_queue));

	/* Release local memory associated with handle. */
	if (mqh->mqh_buffer != NULL)
		pfree(mqh->mqh_buffer);
	pfree(mqh);
}

/*
 * Notify counterparty that we're detaching from shared message queue.
 *
 * The purpose of this function is to make sure that the process
 * with which we're communicating doesn't block forever waiting for us to
 * fill or drain the queue once we've lost interest.  When the sender
 * detaches, the receiver can read any messages remaining in the queue;
 * further reads will return SHM_MQ_DETACHED.  If the receiver detaches,
 * further attempts to send messages will likewise return SHM_MQ_DETACHED.
 *
 * This is separated out from shm_mq_detach() because if the on_dsm_detach
 * callback fires, we only want to do this much.  We do not try to touch
 * the local shm_mq_handle, as it may have been pfree'd already.
 */
/*
 * shm_mq_detach_internal - (中文)向对端宣告"本端脱离"(仅共享状态部分)
 *
 * 【作用】在自旋锁内判断谁是"受害者"(对方)、置 mq_detached = true,
 * 锁外 SetLatch 唤醒对方。与 shm_mq_detach 分离的原因:on_dsm_detach
 * 回调(DSM 段被拆除时)只做这一步,不碰可能已被 pfree 的本地句柄。
 *
 * 【设计思想】只置标志 + 唤醒,不做任何本地清理;SetLatch 前有内存屏障,
 * 保证对方醒来后必然看到 mq_detached 的新值,不会醒来后继续死等。
 *
 * 【参数】mq —— 队列。
 * 【返回值】无。
 */
static void
shm_mq_detach_internal(shm_mq *mq)
{
	PGPROC	   *victim;

	SpinLockAcquire(&mq->mq_mutex);
	if (mq->mq_sender == MyProc)
		victim = mq->mq_receiver;
	else
	{
		Assert(mq->mq_receiver == MyProc);
		victim = mq->mq_sender;
	}
	mq->mq_detached = true;
	SpinLockRelease(&mq->mq_mutex);

	if (victim != NULL)
		SetLatch(&victim->procLatch);
}

/*
 * Get the shm_mq from handle.
 */
/*
 * shm_mq_get_queue - (中文)从句柄取回队列指针
 *
 * 【作用】句柄 → 队列的简单访问器,方便调用方在只有句柄时访问队列的
 * 公共字段。
 *
 * 【参数】mqh —— 句柄。
 * 【返回值】队列指针。
 */
shm_mq *
shm_mq_get_queue(shm_mq_handle *mqh)
{
	return mqh->mqh_queue;
}

/*
 * Write bytes into a shared message queue.
 */
/*
 * shm_mq_send_bytes - (中文)把 nbytes 字节写入环形缓冲区(逐段发送泵)
 *
 * 【作用】shm_mq_sendv 的底层字节泵:循环计算可用空间,分多次 memcpy
 * 把数据写进环(每次不跨环尾),直到写完或队列状态变化。已写入但尚未
 * 计入共享计数的字节记入 mqh_send_pending。
 *
 * 【设计思想】
 * - 可用空间 = ringsize - (写计数 + 待提交 pending) - 读计数,再按
 *   "不跨环尾"切成 sendnow 一段写入;
 * - 写 mq_ring 前 pg_memory_barrier()(与 shm_mq_inc_bytes_read 的读
 *   屏障配对),保证接收方看到的是"已可见的数据";
 * - 环满时的策略:对端未 attach → 先等它 attach(nowait 则先查
 *   counterparty_gone 判 DETACHED,再看 receiver 判 WOULD_BLOCK);
 *   对端已 attach → 先把 pending 提交并唤醒接收方,再睡在自身 latch 上
 *   等对方读走数据(nowait 则返回 WOULD_BLOCK)。WaitLatch 前不清
 *   latch:对"已置位的 latch 再置一次"远比"重置后等待"便宜,多绕一圈
 *   换省一次原子操作;
 * - mq_detached 每轮循环都重新读(带 pg_compiler_barrier),防止编译器
 *   把它缓存进寄存器;置位则立即带已发送字节数返回 DETACHED;
 * - 每次写入按 MAXALIGN 计到 pending(只在消息结尾处才会实际出现补齐),
 *   保证环形计数与对齐规则自洽。
 *
 * 【参数】
 *   mqh           —— 句柄;
 *   nbytes        —— 本次要写的字节数;
 *   data          —— 数据源;
 *   nowait        —— true:不等待;
 *   bytes_written —— 输出:实际写入的字节数(可能 < nbytes)。
 * 【返回值】SHM_MQ_SUCCESS / SHM_MQ_WOULD_BLOCK / SHM_MQ_DETACHED。
 */
static shm_mq_result
shm_mq_send_bytes(shm_mq_handle *mqh, Size nbytes, const void *data,
				  bool nowait, Size *bytes_written)
{
	shm_mq	   *mq = mqh->mqh_queue;
	Size		sent = 0;
	uint64		used;
	Size		ringsize = mq->mq_ring_size;
	Size		available;

	while (sent < nbytes)
	{
		uint64		rb;
		uint64		wb;

		/* Compute number of ring buffer bytes used and available. */
		rb = pg_atomic_read_u64(&mq->mq_bytes_read);
		wb = pg_atomic_read_u64(&mq->mq_bytes_written) + mqh->mqh_send_pending;
		Assert(wb >= rb);
		used = wb - rb;
		Assert(used <= ringsize);
		available = Min(ringsize - used, nbytes - sent);

		/*
		 * Bail out if the queue has been detached.  Note that we would be in
		 * trouble if the compiler decided to cache the value of
		 * mq->mq_detached in a register or on the stack across loop
		 * iterations.  It probably shouldn't do that anyway since we'll
		 * always return, call an external function that performs a system
		 * call, or reach a memory barrier at some point later in the loop,
		 * but just to be sure, insert a compiler barrier here.
		 */
		pg_compiler_barrier();
		if (mq->mq_detached)
		{
			*bytes_written = sent;
			return SHM_MQ_DETACHED;
		}

		if (available == 0 && !mqh->mqh_counterparty_attached)
		{
			/*
			 * The queue is full, so if the receiver isn't yet known to be
			 * attached, we must wait for that to happen.
			 */
			if (nowait)
			{
				if (shm_mq_counterparty_gone(mq, mqh->mqh_handle))
				{
					*bytes_written = sent;
					return SHM_MQ_DETACHED;
				}
				if (shm_mq_get_receiver(mq) == NULL)
				{
					*bytes_written = sent;
					return SHM_MQ_WOULD_BLOCK;
				}
			}
			else if (!shm_mq_wait_internal(mq, &mq->mq_receiver,
										   mqh->mqh_handle))
			{
				mq->mq_detached = true;
				*bytes_written = sent;
				return SHM_MQ_DETACHED;
			}
			mqh->mqh_counterparty_attached = true;

			/*
			 * The receiver may have read some data after attaching, so we
			 * must not wait without rechecking the queue state.
			 */
		}
		else if (available == 0)
		{
			/* Update the pending send bytes in the shared memory. */
			shm_mq_inc_bytes_written(mq, mqh->mqh_send_pending);

			/*
			 * Since mq->mqh_counterparty_attached is known to be true at this
			 * point, mq_receiver has been set, and it can't change once set.
			 * Therefore, we can read it without acquiring the spinlock.
			 */
			Assert(mqh->mqh_counterparty_attached);
			SetLatch(&mq->mq_receiver->procLatch);

			/*
			 * We have just updated the mqh_send_pending bytes in the shared
			 * memory so reset it.
			 */
			mqh->mqh_send_pending = 0;

			/* Skip manipulation of our latch if nowait = true. */
			if (nowait)
			{
				*bytes_written = sent;
				return SHM_MQ_WOULD_BLOCK;
			}

			/*
			 * Wait for our latch to be set.  It might already be set for some
			 * unrelated reason, but that'll just result in one extra trip
			 * through the loop.  It's worth it to avoid resetting the latch
			 * at top of loop, because setting an already-set latch is much
			 * cheaper than setting one that has been reset.
			 */
			(void) WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH, 0,
							 WAIT_EVENT_MESSAGE_QUEUE_SEND);

			/* Reset the latch so we don't spin. */
			ResetLatch(MyLatch);

			/* An interrupt may have occurred while we were waiting. */
			CHECK_FOR_INTERRUPTS();
		}
		else
		{
			Size		offset;
			Size		sendnow;

			offset = wb % (uint64) ringsize;
			sendnow = Min(available, ringsize - offset);

			/*
			 * Write as much data as we can via a single memcpy(). Make sure
			 * these writes happen after the read of mq_bytes_read, above.
			 * This barrier pairs with the one in shm_mq_inc_bytes_read.
			 * (Since we're separating the read of mq_bytes_read from a
			 * subsequent write to mq_ring, we need a full barrier here.)
			 */
			pg_memory_barrier();
			memcpy(&mq->mq_ring[mq->mq_ring_offset + offset],
				   (const char *) data + sent, sendnow);
			sent += sendnow;

			/*
			 * Update count of bytes written, with alignment padding.  Note
			 * that this will never actually insert any padding except at the
			 * end of a run of bytes, because the buffer size is a multiple of
			 * MAXIMUM_ALIGNOF, and each read is as well.
			 */
			Assert(sent == nbytes || sendnow == MAXALIGN(sendnow));

			/*
			 * For efficiency, we don't update the bytes written in the shared
			 * memory and also don't set the reader's latch here.  Refer to
			 * the comments atop the shm_mq_handle structure for more
			 * information.
			 */
			mqh->mqh_send_pending += MAXALIGN(sendnow);
		}
	}

	*bytes_written = sent;
	return SHM_MQ_SUCCESS;
}

/*
 * Wait until at least *nbytesp bytes are available to be read from the
 * shared message queue, or until the buffer wraps around.  If the queue is
 * detached, returns SHM_MQ_DETACHED.  If nowait is specified and a wait
 * would be required, returns SHM_MQ_WOULD_BLOCK.  Otherwise, *datap is set
 * to the location at which data bytes can be read, *nbytesp is set to the
 * number of bytes which can be read at that address, and the return value
 * is SHM_MQ_SUCCESS.
 */
/*
 * shm_mq_receive_bytes - (中文)等待并返回一段可读的连续数据(读取泵)
 *
 * 【作用】shm_mq_receive 的底层读取泵:确保至少 bytes_needed 字节可读,
 * 或者数据在环尾截断(此时返回能读到的那一段),通过 *datap / *nbytesp
 * 给出"当前可连续读的字节区间"。注意它可能返回比请求少的字节(跨绕),
 * 由上层循环继续处理。
 *
 * 【设计思想】
 * - used = 写计数 - (读计数 + 未提交消费 pending),offset = used 起点;
 *   满足"数据足够"或"即将跨绕"时,带 pg_read_barrier() 返回(与
 *   shm_mq_inc_bytes_written 的写屏障配对);
 * - detached 检查放在"已有数据够不够"之后:发送方脱离后,接收方仍应能
 *   读完环中残余消息;脱离后还须读屏障并复核写计数,防止漏看"写完数据
 *   之后才置 detached"的最后一批字节;
 * - 需要等待前先把 consume_pending 提交(腾出缓冲空间);然后 WaitLatch
 *   睡眠,醒来 ResetLatch + CHECK_FOR_INTERRUPTS,循环重查。
 *
 * 【参数】
 *   mqh          —— 句柄;
 *   bytes_needed —— 期望的字节数;
 *   nowait       —— true:不等待;
 *   nbytesp      —— 输出:可读字节数(<= 请求,跨绕时更小);
 *   datap        —— 输出:可读数据的地址。
 * 【返回值】SHM_MQ_SUCCESS / SHM_MQ_WOULD_BLOCK / SHM_MQ_DETACHED。
 */
static shm_mq_result
shm_mq_receive_bytes(shm_mq_handle *mqh, Size bytes_needed, bool nowait,
					 Size *nbytesp, void **datap)
{
	shm_mq	   *mq = mqh->mqh_queue;
	Size		ringsize = mq->mq_ring_size;
	uint64		used;
	uint64		written;

	for (;;)
	{
		Size		offset;
		uint64		read;

		/* Get bytes written, so we can compute what's available to read. */
		written = pg_atomic_read_u64(&mq->mq_bytes_written);

		/*
		 * Get bytes read.  Include bytes we could consume but have not yet
		 * consumed.
		 */
		read = pg_atomic_read_u64(&mq->mq_bytes_read) +
			mqh->mqh_consume_pending;
		used = written - read;
		Assert(used <= ringsize);
		offset = read % (uint64) ringsize;

		/* If we have enough data or buffer has wrapped, we're done. */
		if (used >= bytes_needed || offset + used >= ringsize)
		{
			*nbytesp = Min(used, ringsize - offset);
			*datap = &mq->mq_ring[mq->mq_ring_offset + offset];

			/*
			 * Separate the read of mq_bytes_written, above, from caller's
			 * attempt to read the data itself.  Pairs with the barrier in
			 * shm_mq_inc_bytes_written.
			 */
			pg_read_barrier();
			return SHM_MQ_SUCCESS;
		}

		/*
		 * Fall out before waiting if the queue has been detached.
		 *
		 * Note that we don't check for this until *after* considering whether
		 * the data already available is enough, since the receiver can finish
		 * receiving a message stored in the buffer even after the sender has
		 * detached.
		 */
		if (mq->mq_detached)
		{
			/*
			 * If the writer advanced mq_bytes_written and then set
			 * mq_detached, we might not have read the final value of
			 * mq_bytes_written above.  Insert a read barrier and then check
			 * again if mq_bytes_written has advanced.
			 */
			pg_read_barrier();
			if (written != pg_atomic_read_u64(&mq->mq_bytes_written))
				continue;

			return SHM_MQ_DETACHED;
		}

		/*
		 * We didn't get enough data to satisfy the request, so mark any data
		 * previously-consumed as read to make more buffer space.
		 */
		if (mqh->mqh_consume_pending > 0)
		{
			shm_mq_inc_bytes_read(mq, mqh->mqh_consume_pending);
			mqh->mqh_consume_pending = 0;
		}

		/* Skip manipulation of our latch if nowait = true. */
		if (nowait)
			return SHM_MQ_WOULD_BLOCK;

		/*
		 * Wait for our latch to be set.  It might already be set for some
		 * unrelated reason, but that'll just result in one extra trip through
		 * the loop.  It's worth it to avoid resetting the latch at top of
		 * loop, because setting an already-set latch is much cheaper than
		 * setting one that has been reset.
		 */
		(void) WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH, 0,
						 WAIT_EVENT_MESSAGE_QUEUE_RECEIVE);

		/* Reset the latch so we don't spin. */
		ResetLatch(MyLatch);

		/* An interrupt may have occurred while we were waiting. */
		CHECK_FOR_INTERRUPTS();
	}
}

/*
 * Test whether a counterparty who may not even be alive yet is definitely gone.
 */
/*
 * shm_mq_counterparty_gone - (中文)判断"可能还没活过来的对端"是否已确定
 * 消失
 *
 * 【作用】nowait 路径的快速判死:mq_detached 已置位 → 确定走了;有
 * bgworker 句柄且 worker 状态既不是 STARTED 也不是 NOT_YET_STARTED
 * (例如已退出)→ 确定死了,顺手把 mq_detached 置位"官方确认"。
 *
 * 【设计思想】这是"对端从未 attach"与"对端已死"之间唯一的区分手段
 * (配合 shm_mq_get_sender 为 NULL 判断使用,注意检查顺序,见
 * shm_mq_receive);没有句柄时无法得知未启动 worker 的死活,只能保守
 * 返回 false。
 *
 * 【参数】
 *   mq     —— 队列;
 *   handle —— bgworker 句柄(可 NULL)。
 * 【返回值】true 确定消失;false 还不能确定。
 */
static bool
shm_mq_counterparty_gone(shm_mq *mq, BackgroundWorkerHandle *handle)
{
	pid_t		pid;

	/* If the queue has been detached, counterparty is definitely gone. */
	if (mq->mq_detached)
		return true;

	/* If there's a handle, check worker status. */
	if (handle != NULL)
	{
		BgwHandleStatus status;

		/* Check for unexpected worker death. */
		status = GetBackgroundWorkerPid(handle, &pid);
		if (status != BGWH_STARTED && status != BGWH_NOT_YET_STARTED)
		{
			/* Mark it detached, just to make it official. */
			mq->mq_detached = true;
			return true;
		}
	}

	/* Counterparty is not definitively gone. */
	return false;
}

/*
 * This is used when a process is waiting for its counterpart to attach to the
 * queue.  We exit when the other process attaches as expected, or, if
 * handle != NULL, when the referenced background process or the postmaster
 * dies.  Note that if handle == NULL, and the process fails to attach, we'll
 * potentially get stuck here forever waiting for a process that may never
 * start.  We do check for interrupts, though.
 *
 * ptr is a pointer to the memory address that we're expecting to become
 * non-NULL when our counterpart attaches to the queue.
 */
/*
 * shm_mq_wait_internal - (中文)等待某个字段被对端填上(attach 等待核心)
 *
 * 【作用】循环检查 *ptr 是否非 NULL(即对端已 set_sender / set_receiver),
 * 期间睡在本进程 latch 上;mq_detached、worker 死亡或 postmaster 死亡
 * 都会使等待提前结束。handle == NULL 时对端若一直不 attach,本函数可能
 * 永远等下去(仅靠中断检查兜底),调用方应避免这种用法。
 *
 * 【设计思想】每轮循环都重新持锁检查指针(不可缓存旧值);worker 状态轮询
 * 借助 GetBackgroundWorkerPid 探测死亡;睡眠用 latch + WL_EXIT_ON_PM_DEATH,
 * 对方 set 字段或 detach 时都会经 SetLatch 唤醒我们。
 *
 * 【参数】
 *   mq     —— 队列;
 *   ptr    —— 待观察字段的地址(&mq_sender 或 &mq_receiver);
 *   handle —— bgworker 句柄(可 NULL)。
 * 【返回值】true:字段已被设置;false:队列 detached 或 worker 死亡。
 */
static bool
shm_mq_wait_internal(shm_mq *mq, PGPROC **ptr, BackgroundWorkerHandle *handle)
{
	bool		result = false;

	for (;;)
	{
		BgwHandleStatus status;
		pid_t		pid;

		/* Acquire the lock just long enough to check the pointer. */
		SpinLockAcquire(&mq->mq_mutex);
		result = (*ptr != NULL);
		SpinLockRelease(&mq->mq_mutex);

		/* Fail if detached; else succeed if initialized. */
		if (mq->mq_detached)
		{
			result = false;
			break;
		}
		if (result)
			break;

		if (handle != NULL)
		{
			/* Check for unexpected worker death. */
			status = GetBackgroundWorkerPid(handle, &pid);
			if (status != BGWH_STARTED && status != BGWH_NOT_YET_STARTED)
			{
				result = false;
				break;
			}
		}

		/* Wait to be signaled. */
		(void) WaitLatch(MyLatch, WL_LATCH_SET | WL_EXIT_ON_PM_DEATH, 0,
						 WAIT_EVENT_MESSAGE_QUEUE_INTERNAL);

		/* Reset the latch so we don't spin. */
		ResetLatch(MyLatch);

		/* An interrupt may have occurred while we were waiting. */
		CHECK_FOR_INTERRUPTS();
	}

	return result;
}

/*
 * Increment the number of bytes read.
 */
/*
 * shm_mq_inc_bytes_read - (中文)推进共享读计数并唤醒发送方
 *
 * 【作用】接收方消费数据后调用:把 mq_bytes_read 增加 n,并 SetLatch
 * 唤醒发送方,让它知道有新空间可写。
 *
 * 【设计思想】pg_read_barrier() 先于计数更新(与 shm_mq_send_bytes 的
 * 全屏障配对:保证发送方重算可用空间时,已消费的数据对新写入方可见);
 * 不用原子 fetch_add 而用 read + write 组合:该计数只由接收方一人写,
 * 朴素写避免不必要的总线锁;mq_sender 一经设置便不可变,免锁直读。
 *
 * 【参数】
 *   mq —— 队列;
 *   n  —— 新增的已读字节数。
 * 【返回值】无。
 */
static void
shm_mq_inc_bytes_read(shm_mq *mq, Size n)
{
	PGPROC	   *sender;

	/*
	 * Separate prior reads of mq_ring from the increment of mq_bytes_read
	 * which follows.  This pairs with the full barrier in
	 * shm_mq_send_bytes(). We only need a read barrier here because the
	 * increment of mq_bytes_read is actually a read followed by a dependent
	 * write.
	 */
	pg_read_barrier();

	/*
	 * There's no need to use pg_atomic_fetch_add_u64 here, because nobody
	 * else can be changing this value.  This method should be cheaper.
	 */
	pg_atomic_write_u64(&mq->mq_bytes_read,
						pg_atomic_read_u64(&mq->mq_bytes_read) + n);

	/*
	 * We shouldn't have any bytes to read without a sender, so we can read
	 * mq_sender here without a lock.  Once it's initialized, it can't change.
	 */
	sender = mq->mq_sender;
	Assert(sender != NULL);
	SetLatch(&sender->procLatch);
}

/*
 * Increment the number of bytes written.
 */
/*
 * shm_mq_inc_bytes_written - (中文)推进共享写计数
 *
 * 【作用】发送方把 pending 的字节正式计进 mq_bytes_written,使这些字节
 * 对接收方可见(对端随后经 latch 被唤醒去读)。
 *
 * 【设计思想】pg_write_barrier() 把"环中数据的写入"与"计数更新"排序
 * (与 shm_mq_receive_bytes 的读屏障配对),否则接收方可能先看到新计数、
 * 再读到旧数据;同样用 read + write 而非 fetch_add,以省总线锁(该计数
 * 只由发送方一人写)。
 *
 * 【参数】
 *   mq —— 队列;
 *   n  —— 新增的已写字节数。
 * 【返回值】无。
 */
static void
shm_mq_inc_bytes_written(shm_mq *mq, Size n)
{
	/*
	 * Separate prior reads of mq_ring from the write of mq_bytes_written
	 * which we're about to do.  Pairs with the read barrier found in
	 * shm_mq_receive_bytes.
	 */
	pg_write_barrier();

	/*
	 * There's no need to use pg_atomic_fetch_add_u64 here, because nobody
	 * else can be changing this value.  This method avoids taking the bus
	 * lock unnecessarily.
	 */
	pg_atomic_write_u64(&mq->mq_bytes_written,
						pg_atomic_read_u64(&mq->mq_bytes_written) + n);
}

/* Shim for on_dsm_detach callback. */
/*
 * shm_mq_detach_callback - (中文)DSM 段拆除时的回调(打桩函数)
 *
 * 【作用】on_dsm_detach 要求 (dsm_segment*, Datum) 的签名,这里把 arg
 * 解回队列指针后转调 shm_mq_detach_internal——只做"标记 detached +
 * 唤醒对方",因为此时本地句柄可能已被释放,不能触碰。
 *
 * 【参数】
 *   seg —— 被拆除的 DSM 段(未使用);
 *   arg —— 队列指针。
 * 【返回值】无。
 */
static void
shm_mq_detach_callback(dsm_segment *seg, Datum arg)
{
	shm_mq	   *mq = (shm_mq *) DatumGetPointer(arg);

	shm_mq_detach_internal(mq);
}
