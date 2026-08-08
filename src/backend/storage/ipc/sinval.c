/*-------------------------------------------------------------------------
 *
 * sinval.c
 *	  POSTGRES shared cache invalidation communication code.
 *
 * 【模块总览(中文)】
 * 本文件是"共享缓存失效(shared cache invalidation,简称 SI)"机制的
 * 后端入口层:把系统目录(system catalog)缓存失效消息的"发送"与
 * "接收"封装成两个高层接口 —— SendSharedInvalidMessages() /
 * ReceiveSharedInvalidMessages(),并把"落后太多的后端被催促追赶"
 * (catchup)的中断处理逻辑集中在这里。
 *
 * 【为什么要失效缓存】
 * 各后端进程在本地缓存着系统目录内容(syscache)与表结构信息
 * (relcache)。当某个后端修改了系统目录(DDL、权限变更等)时,它
 * 必须让所有其他后端的本地缓存随之失效,否则大家看到的元数据就会
 * 不一致。做法是:修改方把"某条缓存项该失效了"的消息写进共享内存
 * 中的一条环形消息队列(sinvaladt.c 负责管理,本文件不直接碰缓冲
 * 区,只调用其 SI 系列接口),读方在命令开始、事务提交等安全点把
 * 消息取出来,逐条对自己本地的 syscache / relcache 执行失效。
 *
 * 【职责分工】
 * 消息的搬运层(缓冲区、读游标、加锁、追赶策略)全部在 sinvaladt.c;
 * 本文件只负责:组装入队(SendSharedInvalidMessages)、出队并回调
 * (ReceiveSharedInvalidMessages,由 syscache.c / relcache.c 传入各自
 * 的失效处理函数)、以及"追赶中断"的处理。此外,standby 上做 WAL
 * 重放的 Startup 进程也通过 SendSharedInvalidMessages 把主库事务
 * 的失效消息广播给查询后端(见 standby.c 的 LogStandbyInvalidations)。
 *
 * 【并发与信号设计】
 * 空闲后端不会主动轮询消息队列,因此当队列即将写满、某个后端落后
 * 太多时,sinvaladt.c 会经 procsignal.c 给它发
 * PROCSIG_CATCHUP_INTERRUPT 信号;信号处理器(HandleCatchupInterrupt)
 * 只置一个标志 catchupInterruptPending 并唤醒 latch,真正的补读工作
 * 推迟到进程空闲的安全点执行(ProcessCatchupInterrupt)。"信号只负责
 * 提醒、处理延迟到安全点"是 PostgreSQL 中断处理的通用模式,因为
 * 信号处理器上下文不能拿锁、不能分配内存、不能抛错。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/ipc/sinval.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/xact.h"
#include "miscadmin.h"
#include "storage/latch.h"
#include "storage/sinvaladt.h"
#include "utils/inval.h"


/* (中文)本进程累计处理的失效消息条数(全局,供 pg_stat 等统计用;
 * 只增不减,不担心溢出)。ReceiveSharedInvalidMessages 每处理一条
 * 消息(含重置事件)就递增它。 */
uint64		SharedInvalidMessageCounter;


/*
 * Because backends sitting idle will not be reading sinval events, we
 * need a way to give an idle backend a swift kick in the rear and make
 * it catch up before the sinval queue overflows and forces it to go
 * through a cache reset exercise.  This is done by sending
 * PROCSIG_CATCHUP_INTERRUPT to any backend that gets too far behind.
 *
 * The signal handler will set an interrupt pending flag and will set the
 * processes latch. Whenever starting to read from the client, or when
 * interrupted while doing so, ProcessClientReadInterrupt() will call
 * ProcessCatchupEvent().
 */
/* (中文)"追赶中断"待处理标志:
 * sinvaladt.c 判定本后端落后太多(超过 SIG_THRESHOLD 条消息)时,会
 * 经 procsignal.c 向本进程发 PROCSIG_CATCHUP_INTERRUPT 信号;信号
 * 处理器 HandleCatchupInterrupt() 把它置为 true(同时由
 * procsignal_sigusr1_handler() 设置 latch 唤醒进程)。进程在每次
 * CHECK_FOR_INTERRUPTS()(空闲时经 ProcessClientReadInterrupt)检查
 * 到该标志后,调用 ProcessCatchupInterrupt() 补读消息,补读完成后
 * 该标志被复位。类型用 volatile sig_atomic_t:信号处理器与普通代码
 * 都会读写它,必须保证读写是原子的且编译器不做重排优化。 */
volatile sig_atomic_t catchupInterruptPending = false;


/*
 * SendSharedInvalidMessages
 *	Add shared-cache-invalidation message(s) to the global SI message queue.
 */
/*
 * SendSharedInvalidMessages - (中文)把一条或多条共享缓存失效消息写入全局 SI 消息队列
 *
 * 【作用】失效消息的"发送入口"。调用者(事务提交路径、standby 上的
 * WAL 重放、非事务性失效点等)把已构造好的 SharedInvalidationMessage
 * 数组交给本函数,由它转发给 sinvaladt.c 的 SIInsertDataEntries() 写入
 * 共享内存中的环形缓冲队列。所有其他后端稍后都会读到这些消息,并据此
 * 失效各自本地的 syscache / relcache 条目。
 *
 * 【设计思想】本函数只是薄薄一层转发:真正的入队逻辑(环形缓冲、加锁、
 * 溢出时的"重置"降级策略)全部在 sinvaladt.c,这里把调用方与共享内存
 * 细节隔离开。消息入队后并不立即生效——接收方会在各自的命令开始 /
 * 事务提交等安全点调用 ReceiveSharedInvalidMessages() 来消费,因此本
 * 函数不需要通知接收方,也不等待它们确认,可以放心地在持锁关键路径上
 * 使用。
 *
 * 【参数】
 *   msgs —— 指向待发送消息数组的首元素;内容只读,不会被修改。
 *   n    —— 数组元素个数,可为任意大小(内部按 WRITE_QUANTUM 分块写入)。
 * 【返回值】无。
 */
void
SendSharedInvalidMessages(const SharedInvalidationMessage *msgs, int n)
{
	SIInsertDataEntries(msgs, n);
}

/*
 * ReceiveSharedInvalidMessages
 *		Process shared-cache-invalidation messages waiting for this backend
 *
 * We guarantee to process all messages that had been queued before the
 * routine was entered.  It is of course possible for more messages to get
 * queued right after our last SIGetDataEntries call.
 *
 * NOTE: it is entirely possible for this routine to be invoked recursively
 * as a consequence of processing inside the invalFunction or resetFunction.
 * Furthermore, such a recursive call must guarantee that all outstanding
 * inval messages have been processed before it exits.  This is the reason
 * for the strange-looking choice to use a statically allocated buffer array
 * and counters; it's so that a recursive call can process messages already
 * sucked out of sinvaladt.c.
 */
/*
 * ReceiveSharedInvalidMessages - (中文)取回并处理本后端尚未消费的全部共享缓存失效消息
 *
 * 【作用】失效消息的"接收入口",由 AcceptInvalidationMessages() 调用
 * (而后者又分别在命令开始、事务提交/回滚、以及追赶中断处理时被调用)。
 * 调用者传入两个回调:
 *   - invalFunction:对单条消息执行失效处理的函数(sinval.c 的调用方
 *     syscache.c / relcache.c 各自提供,如 CacheInvalidateRelcache 等,
 *     见 utils/inval.c);
 *   - resetFunction:当发现本后端已经错过太多消息、被迫"整体重置"时
 *     调用,把本后端所有可失效的缓存状态清空重建(relcache 重建 /
 *     syscache 清空)。
 * 本函数保证:进入本函数之前已入队的消息,退出时一定已全部处理完毕
 * (之后新入队的当然可能漏掉,那属于下一次调用)。
 *
 * 【设计思想】
 * 1) 递归安全:消息处理函数内部可能访问系统目录,从而触发新的失效
 *    收集,再次递归进入本函数(例如 invalFunction 里查 syscache)。
 *    为此消息缓冲数组与下标/条数计数用 static 保存:外层递归尚未
 *    处理完的消息,在本层入口会被接着处理完,不会丢失也不会重复。
 *    volatile 关键字防止编译器误以为"不会发生递归"而做出错误优化。
 * 2) SIGetDataEntries() 返回 -1 表示 sinvaladt.c 判定本后端落后太多,
 *    必须整体重置:此时调用 resetFunction() 丢弃全部本地缓存状态,
 *    然后退出处理循环(重置后队列里已经没有针对本后端的"欠账",
 *    下一次调用从当前 maxMsgNum 开始即可)。
 * 3) 只要最后一次取数是"取满"(nummsgs == MAXINVALMSGS)就继续循环
 *    再取,直到某次返回不足 32 条,说明队列已掏空;否则下次进入时
 *    残留的消息仍会被处理,不会丢。
 * 4) 收尾的"追赶接力":如果本后端是被追赶信号唤醒的
 *    (catchupInterruptPending 为 true),处理完消息后调用
 *    SICleanupQueue(false, 0) —— 这既是清理已无人需要的消息,更重
 *    要的是把追赶信号转交给下一个落后最远的后端,形成"链式接力",
 *    避免同时有一大群后端一起涌来补消息造成负载尖峰。
 *
 * 【参数】
 *   invalFunction —— 单条消息的失效处理回调,原型
 *                     void (*)(SharedInvalidationMessage *msg);
 *   resetFunction  —— 整体重置回调,原型 void (*)(void)。
 * 【返回值】无。
 */
void
ReceiveSharedInvalidMessages(void (*invalFunction) (SharedInvalidationMessage *msg),
							 void (*resetFunction) (void))
{
#define MAXINVALMSGS 32
	static SharedInvalidationMessage messages[MAXINVALMSGS];

	/*
	 * We use volatile here to prevent bugs if a compiler doesn't realize that
	 * recursion is a possibility ...
	 */
	static volatile int nextmsg = 0;
	static volatile int nummsgs = 0;

	/* Deal with any messages still pending from an outer recursion */
	while (nextmsg < nummsgs)
	{
		SharedInvalidationMessage msg = messages[nextmsg++];

		SharedInvalidMessageCounter++;
		invalFunction(&msg);
	}

	do
	{
		int			getResult;

		nextmsg = nummsgs = 0;

		/* Try to get some more messages */
		getResult = SIGetDataEntries(messages, MAXINVALMSGS);

		if (getResult < 0)
		{
			/* got a reset message */
			elog(DEBUG4, "cache state reset");
			SharedInvalidMessageCounter++;
			resetFunction();
			break;				/* nothing more to do */
		}

		/* Process them, being wary that a recursive call might eat some */
		nextmsg = 0;
		nummsgs = getResult;

		while (nextmsg < nummsgs)
		{
			SharedInvalidationMessage msg = messages[nextmsg++];

			SharedInvalidMessageCounter++;
			invalFunction(&msg);
		}

		/*
		 * We only need to loop if the last SIGetDataEntries call (which might
		 * have been within a recursive call) returned a full buffer.
		 */
	} while (nummsgs == MAXINVALMSGS);

	/*
	 * We are now caught up.  If we received a catchup signal, reset that
	 * flag, and call SICleanupQueue().  This is not so much because we need
	 * to flush dead messages right now, as that we want to pass on the
	 * catchup signal to the next slowest backend.  "Daisy chaining" the
	 * catchup signal this way avoids creating spikes in system load for what
	 * should be just a background maintenance activity.
	 */
	if (catchupInterruptPending)
	{
		catchupInterruptPending = false;
		elog(DEBUG4, "sinval catchup complete, cleaning queue");
		SICleanupQueue(false, 0);
	}
}


/*
 * HandleCatchupInterrupt
 *
 * This is called when PROCSIG_CATCHUP_INTERRUPT is received.
 *
 * We used to directly call ProcessCatchupEvent directly when idle. These days
 * we just set a flag to do it later and notify the process of that fact by
 * setting the process's latch.
 */
/*
 * HandleCatchupInterrupt - (中文)追赶中断的信号处理器回调:仅记录"有追赶需求"
 *
 * 【作用】收到 PROCSIG_CATCHUP_INTERRUPT 信号时,由 procsignal.c 的
 * procsignal_sigusr1_handler() 调用。它把全局标志
 * catchupInterruptPending 置为 true 后立即返回。进程随后会在每次
 * CHECK_FOR_INTERRUPTS()(空闲时则是读客户端前的
 * ProcessClientReadInterrupt)中检查该标志,并调用
 * ProcessCatchupInterrupt() 真正执行补读。
 *
 * 【设计思想】信号处理器上下文能做的事情极其有限(不能取 LWLock、
 * 不能分配内存、不能抛 ERROR),所以这里只做"记账";唤醒沉睡进程
 * 的工作由 procsignal_sigusr1_handler() 里统一调用的 SetLatch()
 * 完成。"收到信号"与"处理信号"分离,是 PostgreSQL 中断处理的
 * 通用模式。本函数在信号上下文中执行,只做一次原子赋值,安全。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
HandleCatchupInterrupt(void)
{
	/*
	 * Note: this is called by a SIGNAL HANDLER. You must be very wary what
	 * you do here.
	 */

	catchupInterruptPending = true;

	/* latch will be set by procsignal_sigusr1_handler */
}

/*
 * ProcessCatchupInterrupt
 *
 * The portion of catchup interrupt handling that runs outside of the signal
 * handler, which allows it to actually process pending invalidations.
 */
/*
 * ProcessCatchupInterrupt - (中文)在信号处理器之外执行追赶中断的实际处理(补读失效消息)
 *
 * 【作用】在进程安全点被调用(主要经 CHECK_FOR_INTERRUPTS 路径,
 * 空闲时经 ProcessClientReadInterrupt)。只要 catchupInterruptPending
 * 仍为 true 就反复处理:
 *   - 在事务/事务块内:直接调用 AcceptInvalidationMessages(),它内部
 *     会调用 ReceiveSharedInvalidMessages() 补读,并最终把
 *     catchupInterruptPending 复位;
 *   - 在事务外(空闲后端):开一个空事务、随即提交,借助"事务启动时
 *     会自动调用 AcceptInvalidationMessages()"这一既有路径完成补读。
 *
 * 【设计思想】不直接调用 ReceiveSharedInvalidMessages() 的原因:如果
 * 补读中途出错(ERROR),在事务外没有异常清理上下文,缓存状态可能
 * 残留损坏;包进一个完整事务里,出错时由事务机制的清理路径统一兜底
 * (这正是英文注释里所说"tempting ... but not sure things would clean
 * up nicely"的取舍)。用 while 循环而非 if,是为了覆盖"处理过程中
 * 又收到新的追赶信号"的情况——标志由内层消息处理路径复位,循环会
 * 一直转到标志被清为止。
 *
 * 【参数】无。
 * 【返回值】无。
 */
void
ProcessCatchupInterrupt(void)
{
	while (catchupInterruptPending)
	{
		/*
		 * What we need to do here is cause ReceiveSharedInvalidMessages() to
		 * run, which will do the necessary work and also reset the
		 * catchupInterruptPending flag.  If we are inside a transaction we
		 * can just call AcceptInvalidationMessages() to do this.  If we
		 * aren't, we start and immediately end a transaction; the call to
		 * AcceptInvalidationMessages() happens down inside transaction start.
		 *
		 * It is awfully tempting to just call AcceptInvalidationMessages()
		 * without the rest of the xact start/stop overhead, and I think that
		 * would actually work in the normal case; but I am not sure that
		 * things would clean up nicely if we got an error partway through.
		 */
		if (IsTransactionOrTransactionBlock())
		{
			elog(DEBUG4, "ProcessCatchupEvent inside transaction");
			AcceptInvalidationMessages();
		}
		else
		{
			elog(DEBUG4, "ProcessCatchupEvent outside transaction");
			StartTransactionCommand();
			CommitTransactionCommand();
		}
	}
}
