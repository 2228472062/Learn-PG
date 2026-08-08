/*-------------------------------------------------------------------------
 *
 * smgr.c
 *	  public interface routines to storage manager switch.
 *
 * All file system operations on relations dispatch through these routines.
 * An SMgrRelation represents physical on-disk relation files that are open
 * for reading and writing.
 *
 * When a relation is first accessed through the relation cache, the
 * corresponding SMgrRelation entry is opened by calling smgropen(), and the
 * reference is stored in the relation cache entry.
 *
 * Accesses that don't go through the relation cache open the SMgrRelation
 * directly.  That includes flushing buffers from the buffer cache, as well as
 * all accesses in auxiliary processes like the checkpointer or the WAL redo
 * in the startup process.
 *
 * Operations like CREATE, DROP, ALTER TABLE also hold SMgrRelation references
 * independent of the relation cache.  They need to prepare the physical files
 * before updating the relation cache.
 *
 * There is a hash table that holds all the SMgrRelation entries in the
 * backend.  If you call smgropen() twice for the same rel locator, you get a
 * reference to the same SMgrRelation. The reference is valid until the end of
 * transaction.  This makes repeated access to the same relation efficient,
 * and allows caching things like the relation size in the SMgrRelation entry.
 *
 * At end of transaction, all SMgrRelation entries that haven't been pinned
 * are removed.  An SMgrRelation can hold kernel file system descriptors for
 * the underlying files, and we'd like to close those reasonably soon if the
 * file gets deleted.  The SMgrRelations references held by the relcache are
 * pinned to prevent them from being closed.
 *
 * There is another mechanism to close file descriptors early:
 * PROCSIGNAL_BARRIER_SMGRRELEASE.  It is a request to immediately close all
 * file descriptors.  Upon receiving that signal, the backend closes all file
 * descriptors held open by SMgrRelations, but because it can happen in the
 * middle of a transaction, we cannot destroy the SMgrRelation objects
 * themselves, as there could pointers to them in active use.  See
 * smgrrelease() and smgrreleaseall().
 *
 * NB: We need to hold interrupts across most of the functions in this file,
 * as otherwise interrupt processing, e.g. due to a < ERROR elog/ereport, can
 * trigger procsignal processing, which in turn can trigger
 * smgrreleaseall(). Most of the relevant code is not reentrant.  It seems
 * better to put the HOLD_INTERRUPTS()/RESUME_INTERRUPTS() here, instead of
 * trying to push them down to md.c where possible: For one, every smgr
 * implementation would be vulnerable, for another, a good bit of smgr.c code
 * itself is affected too.  Eventually we might want a more targeted solution,
 * allowing e.g. a networked smgr implementation to be interrupted, but many
 * other, more complicated, problems would need to be fixed for that to be
 * viable (e.g. smgr.c is often called with interrupts already held).
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 存储管理器(smgr,Storage Manager)的"分发层":
 * 它自身不读写磁盘,而是维护一张"存储管理器函数指针表"(smgrsw,目前
 * 唯一的实现是 md.c 的磁介质管理器),把上层发来的统一操作请求分发给
 * 具体实现,并承担 SMgrRelation 对象的生命周期管理。
 *
 * 上层组件(缓冲管理器 bufmgr、访问方法 heap/索引、VACUUM、DDL 等)
 * 通过本文件提供的 smgrXXX() 函数完成文件级操作:读页(smgrreadv)、
 * 写页(smgrwritev)、扩展(smgrextend/smgrzeroextend)、查询大小
 * (smgrnblocks)、预读(smgrprefetch)、截断(smgrtruncate)、删除
 * (smgrdounlinkall)、同步(smgrimmedsync/smgrregistersync)等。几乎
 * 每个操作都包在 HOLD_INTERRUPTS()/RESUME_INTERRUPTS() 之间:中断
 * 处理(可能触发 PROCSIGNAL_BARRIER_SMGRRELEASE,进而调用
 * smgrreleaseall() 关闭文件描述符)与本文件的大多数代码不可重入,必须
 * 推迟到操作完成后再放行。
 *
 * SMgrRelation 生命周期管理是本文件的另一半职责:
 * - 每个后端进程有一张哈希表(SMgrRelationHash),以 RelFileLocatorBackend
 *   为键缓存所有打开中的 SMgrRelation(即"物理文件句柄 + 每 fork 大小
 *   缓存");对同一 locator 调用两次 smgropen() 会得到同一对象,使重复
 *   访问高效,也允许在对象里缓存关系大小等信息;
 * - 对象有"引用计数"(pin)机制:被 relcache 或正在进行中的 DDL 持有的
 *   对象被 pin 住,保证在事务结束清理(AtEOXact_SMgr -> smgrdestroyall)
 *   时不被销毁;未 pin 的对象挂在 unpinned_relns 链表上,事务结束时
 *   统一销毁并关闭底层内核文件描述符;
 * - smgrrelease() 只关闭文件描述符、保留对象本身,供
 *   PROCSIGNAL_BARRIER_SMGRRELEASE 这类"事务中途释放资源"的场景使用。
 *
 * 本文件还负责删除/截断路径上的跨子系统协调:删除文件前先丢弃缓冲池
 * 中的对应缓冲(DropRelationsAllBuffers),删除前广播共享失效消息
 * (CacheInvalidateSmgr)让其他后端关闭悬空的 smgr 引用等。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/smgr/smgr.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/xlogutils.h"
#include "lib/ilist.h"
#include "miscadmin.h"
#include "storage/aio.h"
#include "storage/bufmgr.h"
#include "storage/ipc.h"
#include "storage/md.h"
#include "storage/smgr.h"
#include "utils/hsearch.h"
#include "utils/inval.h"


/*
 * 存储管理器模块接口的"函数指针表"类型(f_smgr):smgr.c 通过这张表与
 * 任意一个具体存储管理器解耦,新增一种存储设备(如网络文件系统、对象
 * 存储)只需实现这套接口并登记进 smgrsw 数组即可,smgr.c 与上层代码
 * 都不用改。
 *
 * 各函数指针含义(均为文件级操作,与 smgr.c 的公开函数一一对应):
 * - smgr_init / smgr_shutdown : 后端进程启动/退出时的初始化与收尾
 *                               (允许为 NULL);
 * - smgr_open / smgr_close    : 打开/关闭关系的所有 fork(打开只做
 *                               登记,不读盘);
 * - smgr_create / smgr_exists : 创建/探测某个 fork 的物理文件;
 * - smgr_unlink               : 删除某个 fork 的物理文件(注意:此函数
 *                               在事务提交/回滚后的清理阶段被调用,
 *                               太晚无法报错,只能 WARNING 不能 ERROR);
 * - smgr_extend / smgr_zeroextend : 在文件末尾追加 1 个 / 多个(清零)块;
 * - smgr_prefetch             : 预读若干块(尽力而为,可失败);
 * - smgr_maxcombine           : 返回从 blocknum 开始最多能把多少块
 *                               合并进一次 IO(含 blocknum 本身);
 * - smgr_readv                : 同步读取连续块;
 * - smgr_startreadv           : 异步读取(配合 AIO 框架);
 * - smgr_writev               : 写入已存在的块(扩展请用 smgr_extend);
 * - smgr_writeback            : 提示内核把脏页刷回磁盘;
 * - smgr_nblocks              : 查询关系当前块数;
 * - smgr_truncate             : 截断到指定块数;
 * - smgr_immedsync            : 立即 fsync;
 * - smgr_registersync         : 登记"下个检查点要 fsync 整个关系";
 * - smgr_fd                   : 返回指定块所在段的原始 fd(供 AIO 在
 *                               其他进程中执行 IO 时使用)。
 *
 * 错误处理约定:除 smgr_unlink 外,具体实现一般通过 elog(ERROR) 报告
 * 问题;引导(bootstrap)与 WAL 重放期间允许放宽部分"本应报错"的情况
 * (详见 md.c 的相关注释)。
 */
typedef struct f_smgr
{
	void		(*smgr_init) (void);	/* may be NULL */
	void		(*smgr_shutdown) (void);	/* may be NULL */
	void		(*smgr_open) (SMgrRelation reln);
	void		(*smgr_close) (SMgrRelation reln, ForkNumber forknum);
	void		(*smgr_create) (SMgrRelation reln, ForkNumber forknum,
								bool isRedo);
	bool		(*smgr_exists) (SMgrRelation reln, ForkNumber forknum);
	void		(*smgr_unlink) (RelFileLocatorBackend rlocator, ForkNumber forknum,
								bool isRedo);
	void		(*smgr_extend) (SMgrRelation reln, ForkNumber forknum,
								BlockNumber blocknum, const void *buffer, bool skipFsync);
	void		(*smgr_zeroextend) (SMgrRelation reln, ForkNumber forknum,
									BlockNumber blocknum, int nblocks, bool skipFsync);
	bool		(*smgr_prefetch) (SMgrRelation reln, ForkNumber forknum,
								  BlockNumber blocknum, int nblocks);
	uint32		(*smgr_maxcombine) (SMgrRelation reln, ForkNumber forknum,
									BlockNumber blocknum);
	void		(*smgr_readv) (SMgrRelation reln, ForkNumber forknum,
							   BlockNumber blocknum,
							   void **buffers, BlockNumber nblocks);
	void		(*smgr_startreadv) (PgAioHandle *ioh,
									SMgrRelation reln, ForkNumber forknum,
									BlockNumber blocknum,
									void **buffers, BlockNumber nblocks);
	void		(*smgr_writev) (SMgrRelation reln, ForkNumber forknum,
								BlockNumber blocknum,
								const void **buffers, BlockNumber nblocks,
								bool skipFsync);
	void		(*smgr_writeback) (SMgrRelation reln, ForkNumber forknum,
								   BlockNumber blocknum, BlockNumber nblocks);
	BlockNumber (*smgr_nblocks) (SMgrRelation reln, ForkNumber forknum);
	void		(*smgr_truncate) (SMgrRelation reln, ForkNumber forknum,
								  BlockNumber old_blocks, BlockNumber nblocks);
	void		(*smgr_immedsync) (SMgrRelation reln, ForkNumber forknum);
	void		(*smgr_registersync) (SMgrRelation reln, ForkNumber forknum);
	int			(*smgr_fd) (SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum, uint32 *off);
} f_smgr;

/* 存储管理器"注册表"数组:目前只登记了 md(磁介质/Unix 文件系统)一个
 * 实现,因此 NSmgr == 1,所有 SMgrRelation 的 smgr_which 恒为 0。未来
 * 若新增实现,只需在此追加一项(并保证编译进后端)。mdinit 在
 * smgrinit() 中被调用,做的是后端进程本地初始化。 */
static const f_smgr smgrsw[] = {
	/* magnetic disk */
	{
		.smgr_init = mdinit,
		.smgr_shutdown = NULL,
		.smgr_open = mdopen,
		.smgr_close = mdclose,
		.smgr_create = mdcreate,
		.smgr_exists = mdexists,
		.smgr_unlink = mdunlink,
		.smgr_extend = mdextend,
		.smgr_zeroextend = mdzeroextend,
		.smgr_prefetch = mdprefetch,
		.smgr_maxcombine = mdmaxcombine,
		.smgr_readv = mdreadv,
		.smgr_startreadv = mdstartreadv,
		.smgr_writev = mdwritev,
		.smgr_writeback = mdwriteback,
		.smgr_nblocks = mdnblocks,
		.smgr_truncate = mdtruncate,
		.smgr_immedsync = mdimmedsync,
		.smgr_registersync = mdregistersync,
		.smgr_fd = mdfd,
	}
};

/* 已登记的存储管理器实现个数(由编译器自动统计 smgrsw 数组长度) */
static const int NSmgr = lengthof(smgrsw);

/*
 * Each backend has a hashtable that stores all extant SMgrRelation objects.
 * In addition, "unpinned" SMgrRelation objects are chained together in a list.
 */
/* 本后端进程的 SMgrRelation 哈希表:以 RelFileLocatorBackend 为键,缓存
 * "打开中的关系"。第一次调用 smgropen() 时惰性创建(初始容量 400)。
 * 该表只在本进程内可见,不跨进程共享。 */
static HTAB *SMgrRelationHash = NULL;

/* 所有"未 pin"的 SMgrRelation 组成的双向链表:它们将在事务结束时
 * (AtEOXact_SMgr -> smgrdestroyall())被销毁。pincount 从 1 减到 0 时
 * (smgrunpin)入链,再次被 pin 时出链。 */
static dlist_head unpinned_relns;

/* local function prototypes */
static void smgrshutdown(int code, Datum arg);
static void smgrdestroy(SMgrRelation reln);

static void smgr_aio_reopen(PgAioHandle *ioh);
static char *smgr_aio_describe_identity(const PgAioTargetData *sd);


/* smgr 类型的 AIO 目标(target)回调表:供 AIO 框架在 IO 需要于其他进程
 * (如 IO worker)中执行时,用它重新打开文件(smgr_aio_reopen)、并在
 * 错误消息中描述 IO 目标(smgr_aio_describe_identity)。 */
const PgAioTargetInfo aio_smgr_target_info = {
	.name = "smgr",
	.reopen = smgr_aio_reopen,
	.describe_identity = smgr_aio_describe_identity,
};


/*
 * smgrinit (中文)初始化所有已登记的存储管理器
 *
 * 【作用】后端进程启动时(普通或 standalone 模式)被调用,依次调用每个
 * 存储管理器的 smgr_init() 初始化其私有状态(如 md.c 创建 MdCxt 内存
 * 上下文)。最后通过 on_proc_exit 注册退出钩子 smgrshutdown,保证进程
 * 退出时能回收这些资源。
 *
 * 【设计思想】注意时机:它发生在"每个后端进程"启动时,而不是
 * postmaster 启动时——因此这里创建/销毁的资源都是进程本地的,天然
 * 不需要跨进程同步。表驱动(for 遍历 smgrsw)使新增存储管理器不用改动
 * 本函数。
 *
 * 【参数】无。
 * 【返回值】无。
 *
 * smgrinit(), smgrshutdown() -- Initialize or shut down storage
 *								 managers.
 *
 * Note: smgrinit is called during backend startup (normal or standalone
 * case), *not* during postmaster start.  Therefore, any resources created
 * here or destroyed in smgrshutdown are backend-local.
 */
void
smgrinit(void)
{
	int			i;

	HOLD_INTERRUPTS();

	for (i = 0; i < NSmgr; i++)
	{
		if (smgrsw[i].smgr_init)
			smgrsw[i].smgr_init();
	}

	RESUME_INTERRUPTS();

	/* register the shutdown proc */
	on_proc_exit(smgrshutdown, 0);
}

/*
 * smgrshutdown (中文)进程退出钩子:关闭所有存储管理器
 *
 * 【作用】进程退出(on_proc_exit)时被调用,依次调用各存储管理器的
 * smgr_shutdown()(若有),完成进程本地资源的清理。期间同样
 * HOLD_INTERRUPTS()。
 *
 * 【参数】code、arg —— on_proc_exit 回调的标准参数,此处未使用。
 * 【返回值】无。
 *
 * on_proc_exit hook for smgr cleanup during backend shutdown
 */
static void
smgrshutdown(int code, Datum arg)
{
	int			i;

	HOLD_INTERRUPTS();

	for (i = 0; i < NSmgr; i++)
	{
		if (smgrsw[i].smgr_shutdown)
			smgrsw[i].smgr_shutdown();
	}

	RESUME_INTERRUPTS();
}

/*
 * smgropen (中文)获取(必要时创建)一个 SMgrRelation 对象
 *
 * 【作用】返回与 rlocator 对应的 SMgrRelation;若本进程哈希表中还没有,
 * 则创建并初始化之。注意:本函数只建立"对象/句柄",绝不实际打开底层
 * 文件(文件打开由 md.c 按需惰性完成)。
 *
 * 【生命周期约定】(PG 17 起):
 * - 事务内调用:对象有效期到事务结束(AtEOXact_SMgr),期间可以放心
 *   持有返回的指针;
 * - 事务外调用(如 checkpointer 等不用事务的后台进程,通常每轮检查点
 *   周期做一次):对象一直有效,直到显式调用 smgrdestroy()/
 *   smgrdestroyall()。
 *
 * 【设计思想】哈希表首次使用时惰性创建;对同一 locator 的重复
 * smgropen() 返回同一对象,使 smgr_cached_nblocks 等缓存可跨多次访问
 * 复用,避免反复向内核问询文件大小。新对象创建后通过
 * smgrsw[smgr_which].smgr_open() 通知具体实现完成其私有初始化。
 * 整个过程包在 HOLD_INTERRUPTS()/RESUME_INTERRUPTS() 里,防止哈希表
 * 操作与中断(可能触发 smgrreleaseall)交错。
 *
 * 【参数】
 *   rlocator —— 关系的物理位置标识(表空间 OID、数据库 OID、
 *                relfilenumber);
 *   backend  —— 本机进程号:仅临时关系传其所有者的 ProcNumber,普通
 *                关系传 INVALID_PROC_NUMBER。
 * 【返回值】SMgrRelation 指针(永远非 NULL)。
 *
 * smgropen() -- Return an SMgrRelation object, creating it if need be.
 *
 * In versions of PostgreSQL prior to 17, this function returned an object
 * with no defined lifetime.  Now, however, the object remains valid for the
 * lifetime of the transaction, up to the point where AtEOXact_SMgr() is
 * called, making it much easier for callers to know for how long they can
 * hold on to a pointer to the returned object.  If this function is called
 * outside of a transaction, the object remains valid until smgrdestroy() or
 * smgrdestroyall() is called.  Background processes that use smgr but not
 * transactions typically do this once per checkpoint cycle.
 *
 * This does not attempt to actually open the underlying files.
 */
SMgrRelation
smgropen(RelFileLocator rlocator, ProcNumber backend)
{
	RelFileLocatorBackend brlocator;
	SMgrRelation reln;
	bool		found;

	Assert(RelFileNumberIsValid(rlocator.relNumber));

	HOLD_INTERRUPTS();

	if (SMgrRelationHash == NULL)
	{
		/* First time through: initialize the hash table */
		HASHCTL		ctl;

		ctl.keysize = sizeof(RelFileLocatorBackend);
		ctl.entrysize = sizeof(SMgrRelationData);
		SMgrRelationHash = hash_create("smgr relation table", 400,
									   &ctl, HASH_ELEM | HASH_BLOBS);
		dlist_init(&unpinned_relns);
	}

	/* Look up or create an entry */
	brlocator.locator = rlocator;
	brlocator.backend = backend;
	reln = (SMgrRelation) hash_search(SMgrRelationHash,
									  &brlocator,
									  HASH_ENTER, &found);

	/* Initialize it if not present before */
	if (!found)
	{
		/* hash_search already filled in the lookup key */
		reln->smgr_targblock = InvalidBlockNumber;
		for (int i = 0; i <= MAX_FORKNUM; ++i)
			reln->smgr_cached_nblocks[i] = InvalidBlockNumber;
		reln->smgr_which = 0;	/* we only have md.c at present */

		/* it is not pinned yet */
		reln->pincount = 0;
		dlist_push_tail(&unpinned_relns, &reln->node);

		/* implementation-specific initialization */
		smgrsw[reln->smgr_which].smgr_open(reln);
	}

	RESUME_INTERRUPTS();

	return reln;
}

/*
 * smgrpin (中文)pin 住一个 SMgrRelation,防止其在事务结束时被销毁
 *
 * 【作用】relcache、DDL 等需要长期持有 SMgrRelation 指针的地方调用:
 * 把引用计数 +1。若此前引用计数为 0(对象挂在 unpinned_relns 链表上),
 * 先把它从链表中摘除,保证 AtEOXact_SMgr 不会销毁它。
 *
 * 【设计思想】pin/unpin 机制解决了"relcache 持有指针 vs 事务结束统一
 * 清理"的矛盾:relcache 在打开关系时 pin 自己的 SMgrRelation,事务
 * 结束时 unpin,使对象恰好跨事务存活。
 *
 * 【参数】reln —— 要 pin 的对象。
 * 【返回值】无。
 *
 * smgrpin() -- Prevent an SMgrRelation object from being destroyed at end of
 *				transaction
 */
void
smgrpin(SMgrRelation reln)
{
	if (reln->pincount == 0)
		dlist_delete(&reln->node);
	reln->pincount++;
}

/*
 * smgrunpin (中文)解除 pin,允许对象在事务结束时被销毁
 *
 * 【作用】引用计数 -1;减到 0 时重新挂回 unpinned_relns 链表,等待
 * AtEOXact_SMgr() 统一销毁。对象本身仍然有效(只是"到期可回收").
 *
 * 【参数】reln —— 要 unpin 的对象(调用方必须先 pin 过,否则触发
 *                 Assert)。
 * 【返回值】无。
 *
 * smgrunpin() -- Allow an SMgrRelation object to be destroyed at end of
 *				  transaction
 *
 * The object remains valid, but if there are no other pins on it, it is moved
 * to the unpinned list where it will be destroyed by AtEOXact_SMgr().
 */
void
smgrunpin(SMgrRelation reln)
{
	Assert(reln->pincount > 0);
	reln->pincount--;
	if (reln->pincount == 0)
		dlist_push_tail(&unpinned_relns, &reln->node);
}

/*
 * smgrdestroy (中文)销毁一个 SMgrRelation 对象并释放其资源
 *
 * 【作用】关闭该关系所有 fork 的底层文件(smgr_close),把它从
 * unpinned_relns 链表和 SMgrRelationHash 哈希表中摘除并释放。
 *
 * 【调用前提】pincount 必须为 0(未 pin),否则断言失败——被 pin 的
 * 对象还有使用者,销毁会造成悬挂指针。
 *
 * 【参数】reln —— 要销毁的对象。
 * 【返回值】无。
 *
 * smgrdestroy() -- Delete an SMgrRelation object.
 */
static void
smgrdestroy(SMgrRelation reln)
{
	ForkNumber	forknum;

	Assert(reln->pincount == 0);

	HOLD_INTERRUPTS();

	for (forknum = 0; forknum <= MAX_FORKNUM; forknum++)
		smgrsw[reln->smgr_which].smgr_close(reln, forknum);

	dlist_delete(&reln->node);

	if (hash_search(SMgrRelationHash,
					&(reln->smgr_rlocator),
					HASH_REMOVE, NULL) == NULL)
		elog(ERROR, "SMgrRelation hashtable corrupted");

	RESUME_INTERRUPTS();
}

/*
 * smgrrelease (中文)释放对象占用的文件描述符,但保留对象本身
 *
 * 【作用】关闭该关系所有 fork 的已打开文件,同时把缓存的大小信息
 * (smgr_cached_nblocks、smgr_targblock)全部置为无效,但 SMgrRelation
 * 对象与哈希表条目仍然保留,指针继续有效。
 *
 * 【设计思想】这是为 PROCSIGNAL_BARRIER_SMGRRELEASE 设计的"轻量清理":
 * 文件被删除时,其他进程持有的描述符会让磁盘空间无法释放;但屏障信号
 * 可能落在事务中途,此刻不能销毁对象(可能有活跃指针指向它),只能先
 * 关掉文件描述符止损,对象留待事务结束再销毁。
 *
 * 【参数】reln —— 要释放资源的对象。
 * 【返回值】无。
 *
 * smgrrelease() -- Release all resources used by this object.
 *
 * The object remains valid.
 */
void
smgrrelease(SMgrRelation reln)
{
	HOLD_INTERRUPTS();

	for (ForkNumber forknum = 0; forknum <= MAX_FORKNUM; forknum++)
	{
		smgrsw[reln->smgr_which].smgr_close(reln, forknum);
		reln->smgr_cached_nblocks[forknum] = InvalidBlockNumber;
	}
	reln->smgr_targblock = InvalidBlockNumber;

	RESUME_INTERRUPTS();
}

/*
 * smgrclose (中文)关闭一个 SMgrRelation(当前等价于 smgrrelease)
 *
 * 【作用】历史遗留接口:调用方声明"不再使用这个 SMgrRelation 引用"。
 * 由于 smgr.c 不追踪 smgropen() 返回的每一个引用,无法判断是否还有
 * 其他引用指向同一对象,因此不能现在就销毁对象,只能退化为
 * smgrrelease()(关文件、留对象)。
 *
 * 【参数】reln —— 要关闭的对象。
 * 【返回值】无。
 *
 * smgrclose() -- Close an SMgrRelation object.
 *
 * The SMgrRelation reference should not be used after this call.  However,
 * because we don't keep track of the references returned by smgropen(), we
 * don't know if there are other references still pointing to the same object,
 * so we cannot remove the SMgrRelation object yet.  Therefore, this is just a
 * synonym for smgrrelease() at the moment.
 */
void
smgrclose(SMgrRelation reln)
{
	smgrrelease(reln);
}

/*
 * smgrdestroyall (中文)销毁所有未 pin 的 SMgrRelation
 *
 * 【作用】遍历 unpinned_relns 链表,逐个 smgrdestroy()。必须在"除被
 * pin 者外不再有任何指向 SMgrRelation 的指针"的前提下调用,因此只被
 * AtEOXact_SMgr() 等事务边界钩子调用。
 *
 * 【设计思想】牺牲"进程生命周期内不关文件"的便利,换取"文件被删后
 * 描述符能及时关闭":事务结束后立即销毁临时使用的 SMgrRelation,避免
 * 长期占着内核文件描述符。
 *
 * 【参数】无。
 * 【返回值】无。
 *
 * smgrdestroyall() -- Release resources used by all unpinned objects.
 *
 * It must be known that there are no pointers to SMgrRelations, other than
 * those pinned with smgrpin().
 */
void
smgrdestroyall(void)
{
	dlist_mutable_iter iter;

	/* seems unsafe to accept interrupts while in a dlist_foreach_modify() */
	HOLD_INTERRUPTS();

	/*
	 * Zap all unpinned SMgrRelations.  We rely on smgrdestroy() to remove
	 * each one from the list.
	 */
	dlist_foreach_modify(iter, &unpinned_relns)
	{
		SMgrRelation rel = dlist_container(SMgrRelationData, node,
										   iter.cur);

		smgrdestroy(rel);
	}

	RESUME_INTERRUPTS();
}

/*
 * smgrreleaseall (中文)释放所有 SMgrRelation 占用的文件描述符(保留对象)
 *
 * 【作用】PROCSIGNAL_BARRIER_SMGRRELEASE 屏障信号的实际处理者(经由
 * ProcessBarrierSmgrRelease 调用):遍历哈希表中所有 SMgrRelation,
 * 逐个 smgrrelease()。
 *
 * 【设计思想】屏障可能到达事务中途,不能销毁对象(理由见 smgrrelease
 * 的注释),因此这里只关描述符;哈希表尚未建立时直接返回。
 *
 * 【参数】无。
 * 【返回值】无。
 *
 * smgrreleaseall() -- Release resources used by all objects.
 */
void
smgrreleaseall(void)
{
	HASH_SEQ_STATUS status;
	SMgrRelation reln;

	/* Nothing to do if hashtable not set up */
	if (SMgrRelationHash == NULL)
		return;

	/* seems unsafe to accept interrupts while iterating */
	HOLD_INTERRUPTS();

	hash_seq_init(&status, SMgrRelationHash);

	while ((reln = (SMgrRelation) hash_seq_search(&status)) != NULL)
	{
		smgrrelease(reln);
	}

	RESUME_INTERRUPTS();
}

/*
 * smgrreleaserellocator (中文)若指定 locator 的关系是打开状态,则释放其资源
 *
 * 【作用】效果等价于 smgrrelease(smgropen(rlocator)),但只做一次哈希
 * 表 HASH_FIND 查找:若条目不存在,直接返回,避免"先创建一个条目、
 * 随即又释放它"的无谓开销。
 *
 * 【参数】rlocator —— 要释放的关系定位(含 backend 字段)。
 * 【返回值】无。
 *
 * smgrreleaserellocator() -- Release resources for given RelFileLocator, if
 *							  it's open.
 *
 * This has the same effects as smgrrelease(smgropen(rlocator)), but avoids
 * uselessly creating a hashtable entry only to drop it again when no
 * such entry exists already.
 */
void
smgrreleaserellocator(RelFileLocatorBackend rlocator)
{
	SMgrRelation reln;

	/* Nothing to do if hashtable not set up */
	if (SMgrRelationHash == NULL)
		return;

	reln = (SMgrRelation) hash_search(SMgrRelationHash,
									  &rlocator,
									  HASH_FIND, NULL);
	if (reln != NULL)
		smgrrelease(reln);
}

/*
 * smgrexists (中文)判断某个 fork 的物理文件是否存在
 *
 * 【作用】分发给具体实现(mdexists)。典型调用场景:判断某个 fork
 * (如 init fork、fsm fork)是否已被创建。
 *
 * 【参数】
 *   reln    —— 目标关系;
 *   forknum —— 要探测的 fork 编号。
 * 【返回值】文件存在返回 true,否则 false。
 *
 * smgrexists() -- Does the underlying file for a fork exist?
 */
bool
smgrexists(SMgrRelation reln, ForkNumber forknum)
{
	bool		ret;

	HOLD_INTERRUPTS();
	ret = smgrsw[reln->smgr_which].smgr_exists(reln, forknum);
	RESUME_INTERRUPTS();

	return ret;
}

/*
 * smgrcreate (中文)创建新关系的物理文件
 *
 * 【作用】为"已存在但尚未落盘"的 SMgrRelation 创建某个 fork 的底层
 * 存储。isRedo 为 true(崩溃重放)时,允许文件已存在。
 *
 * 【参数】
 *   reln    —— 目标关系;
 *   forknum —— 要创建的 fork;
 *   isRedo  —— 是否处于 WAL 重放:为真时文件已存在不算错误。
 * 【返回值】无。
 *
 * smgrcreate() -- Create a new relation.
 *
 * Given an already-created (but presumably unused) SMgrRelation,
 * cause the underlying disk file or other storage for the fork
 * to be created.
 */
void
smgrcreate(SMgrRelation reln, ForkNumber forknum, bool isRedo)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_create(reln, forknum, isRedo);
	RESUME_INTERRUPTS();
}

/*
 * smgrdosyncall (中文)立即把所有给定关系的所有 fork 同步到磁盘
 *
 * 【作用】先 FlushRelationsAllBuffers() 把这些关系在共享缓冲池中的脏页
 * 全部写回内核,再对每个存在的 fork 调用 smgr_immedsync() 做 fsync。
 * 等效于"逐关系 FlushRelationBuffers + 逐 fork smgrimmedsync",但把
 * 缓冲冲刷合并成一次批量调用,显著更快,应优先使用。
 *
 * 【设计思想】典型调用者是 CREATE DATABASE 等"克隆"场景:新建立的
 * 物理文件必须在返回成功前保证已落盘,否则崩溃后可能得到不完整的新库。
 *
 * 【参数】
 *   rels  —— SMgrRelation 数组;
 *   nrels —— 数组长度。
 * 【返回值】无。
 *
 * smgrdosyncall() -- Immediately sync all forks of all given relations
 *
 * All forks of all given relations are synced out to the store.
 *
 * This is equivalent to FlushRelationBuffers() for each smgr relation,
 * then calling smgrimmedsync() for all forks of each relation, but it's
 * significantly quicker so should be preferred when possible.
 */
void
smgrdosyncall(SMgrRelation *rels, int nrels)
{
	int			i = 0;
	ForkNumber	forknum;

	if (nrels == 0)
		return;

	FlushRelationsAllBuffers(rels, nrels);

	HOLD_INTERRUPTS();

	/*
	 * Sync the physical file(s).
	 */
	for (i = 0; i < nrels; i++)
	{
		int			which = rels[i]->smgr_which;

		for (forknum = 0; forknum <= MAX_FORKNUM; forknum++)
		{
			if (smgrsw[which].smgr_exists(rels[i], forknum))
				smgrsw[which].smgr_immedsync(rels[i], forknum);
		}
	}

	RESUME_INTERRUPTS();
}

/*
 * smgrdounlinkall (中文)立即删除所有给定关系的所有 fork 文件
 *
 * 【作用】DROP TABLE 等操作的最终执行者,步骤:
 * 1) DropRelationsAllBuffers():丢弃这些关系在缓冲池中的全部缓冲(不
 *    写回,因为文件即将消失);
 * 2) 收集各关系的 locator,并在 smgr 层关闭所有 fork 的文件描述符;
 * 3) CacheInvalidateSmgr() 广播共享失效消息,让其他后端也关闭悬空的
 *    smgr 引用(注意:必须先广播再删文件,万一中途失败,其他后端仍会
 *    收到消息从而自行清理;本后端自己也会收到该消息,作为"已关闭自己
 *    的 smgr 引用"的兜底);
 * 4) 逐 fork 调用 smgr_unlink() 删除物理文件。
 *
 * 【约束】本函数"不可撤销",只能在事务已决定提交/回滚后的清理阶段
 * 调用,严禁在普通事务操作中使用;正因如此,smgr_unlink 的失败必须以
 * WARNING(而非 ERROR)报告。
 *
 * 【参数】
 *   rels  —— SMgrRelation 数组;
 *   nrels —— 数组长度;
 *   isRedo—— 重放模式下文件可能已不存在,允许(不报错)。
 * 【返回值】无。
 *
 * smgrdounlinkall() -- Immediately unlink all forks of all given relations
 *
 * All forks of all given relations are removed from the store.  This
 * should not be used during transactional operations, since it can't be
 * undone.
 *
 * If isRedo is true, it is okay for the underlying file(s) to be gone
 * already.
 */
void
smgrdounlinkall(SMgrRelation *rels, int nrels, bool isRedo)
{
	int			i = 0;
	RelFileLocatorBackend *rlocators;
	ForkNumber	forknum;

	if (nrels == 0)
		return;

	/*
	 * It would be unsafe to process interrupts between DropRelationBuffers()
	 * and unlinking the underlying files. This probably should be a critical
	 * section, but we're not there yet.
	 */
	HOLD_INTERRUPTS();

	/*
	 * Get rid of any remaining buffers for the relations.  bufmgr will just
	 * drop them without bothering to write the contents.
	 */
	DropRelationsAllBuffers(rels, nrels);

	/*
	 * create an array which contains all relations to be dropped, and close
	 * each relation's forks at the smgr level while at it
	 */
	rlocators = palloc_array(RelFileLocatorBackend, nrels);
	for (i = 0; i < nrels; i++)
	{
		RelFileLocatorBackend rlocator = rels[i]->smgr_rlocator;
		int			which = rels[i]->smgr_which;

		rlocators[i] = rlocator;

		/* Close the forks at smgr level */
		for (forknum = 0; forknum <= MAX_FORKNUM; forknum++)
			smgrsw[which].smgr_close(rels[i], forknum);
	}

	/*
	 * Send a shared-inval message to force other backends to close any
	 * dangling smgr references they may have for these rels.  We should do
	 * this before starting the actual unlinking, in case we fail partway
	 * through that step.  Note that the sinval messages will eventually come
	 * back to this backend, too, and thereby provide a backstop that we
	 * closed our own smgr rel.
	 */
	for (i = 0; i < nrels; i++)
		CacheInvalidateSmgr(rlocators[i]);

	/*
	 * Delete the physical file(s).
	 *
	 * Note: smgr_unlink must treat deletion failure as a WARNING, not an
	 * ERROR, because we've already decided to commit or abort the current
	 * xact.
	 */

	for (i = 0; i < nrels; i++)
	{
		int			which = rels[i]->smgr_which;

		for (forknum = 0; forknum <= MAX_FORKNUM; forknum++)
			smgrsw[which].smgr_unlink(rlocators[i], forknum, isRedo);
	}

	pfree(rlocators);

	RESUME_INTERRUPTS();
}


/*
 * smgrextend (中文)向文件追加一个新的数据块(扩展一个块)
 *
 * 【作用】在文件当前 EOF 处(即 blocknum >= 当前大小,通常 == 当前
 * 大小)写入一块。语义与 smgrwritev() 几乎相同(在指定位置写),但专
 * 用于扩展:若 blocknum 超出当前 EOF,操作系统保证中间空洞读出来是
 * 零,写操作本身相当于把 EOF 推进到 blocknum+1。
 *
 * 【设计思想】扩展成功后顺手维护 smgr_cached_nblocks 缓存:若缓存值
 * 与 blocknum 相符(预期的连续扩展),直接 +1;否则说明缓存已过时,
 * 置为 InvalidBlockNumber,下次 smgrnblocks() 再向内核问询,避免使用
 * 错误的缓存值。
 *
 * 【参数】
 *   reln      —— 目标关系;
 *   forknum   —— 目标 fork;
 *   blocknum  —— 新块的块号(应在当前 EOF 处);
 *   buffer    —— 待写入的一页数据(BLCKSZ 字节);
 *   skipFsync —— true 表示调用方另有 fsync 安排(或临时关系无需
 *                fsync),不登记到检查点。
 * 【返回值】无。
 *
 * smgrextend() -- Add a new block to a file.
 *
 * The semantics are nearly the same as smgrwrite(): write at the
 * specified position.  However, this is to be used for the case of
 * extending a relation (i.e., blocknum is at or beyond the current
 * EOF).  Note that we assume writing a block beyond current EOF
 * causes intervening file space to become filled with zeroes.
 */
void
smgrextend(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		   const void *buffer, bool skipFsync)
{
	HOLD_INTERRUPTS();

	smgrsw[reln->smgr_which].smgr_extend(reln, forknum, blocknum,
										 buffer, skipFsync);

	/*
	 * Normally we expect this to increase nblocks by one, but if the cached
	 * value isn't as expected, just invalidate it so the next call asks the
	 * kernel.
	 */
	if (reln->smgr_cached_nblocks[forknum] == blocknum)
		reln->smgr_cached_nblocks[forknum] = blocknum + 1;
	else
		reln->smgr_cached_nblocks[forknum] = InvalidBlockNumber;

	RESUME_INTERRUPTS();
}

/*
 * smgrzeroextend (中文)一次性向文件追加 nblocks 个清零块
 *
 * 【作用】smgrextend() 的多块版:把 [blocknum, blocknum+nblocks) 范围
 * 的块全部置零并扩展文件,用于需要快速分配大块空间的场景(如批量加载、
 * 初始化新 fork)。具体实现(mdzeroextend)可以整段调用 fallocate/写零,
 * 比逐块写高效得多。同样顺带维护 smgr_cached_nblocks 缓存。
 *
 * 【参数】
 *   reln, forknum, blocknum —— 目标关系、fork 与起始块号;
 *   nblocks —— 要追加的块数(> 0);
 *   skipFsync —— 见 smgrextend()。
 * 【返回值】无。
 *
 * smgrzeroextend() -- Add new zeroed out blocks to a file.
 *
 * Similar to smgrextend(), except the relation can be extended by
 * multiple blocks at once and the added blocks will be filled with
 * zeroes.
 */
void
smgrzeroextend(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
			   int nblocks, bool skipFsync)
{
	HOLD_INTERRUPTS();

	smgrsw[reln->smgr_which].smgr_zeroextend(reln, forknum, blocknum,
											 nblocks, skipFsync);

	/*
	 * Normally we expect this to increase the fork size by nblocks, but if
	 * the cached value isn't as expected, just invalidate it so the next call
	 * asks the kernel.
	 */
	if (reln->smgr_cached_nblocks[forknum] == blocknum)
		reln->smgr_cached_nblocks[forknum] = blocknum + nblocks;
	else
		reln->smgr_cached_nblocks[forknum] = InvalidBlockNumber;

	RESUME_INTERRUPTS();
}

/*
 * smgrprefetch (中文)预读一个关系的指定块区间(异步,尽力而为)
 *
 * 【作用】提前把 [blocknum, blocknum+nblocks) 的页面调入 OS 页缓存,
 * 期望后续正式读取时命中。分发给 mdprefetch,由 FilePrefetch 实现。
 *
 * 【返回值语义】常规返回 true。仅 WAL 重放(恢复)期间可能返回 false,
 * 表示对应文件不存在(多半是被更晚的 WAL 记录删掉了),调用方此时应
 * 放弃预读而非报错。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块号;nblocks —— 预读块数。
 * 【返回值】见上。
 *
 * smgrprefetch() -- Initiate asynchronous read of the specified block of a relation.
 *
 * In recovery only, this can return false to indicate that a file
 * doesn't exist (presumably it has been dropped by a later WAL
 * record).
 */
bool
smgrprefetch(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
			 int nblocks)
{
	bool		ret;

	HOLD_INTERRUPTS();
	ret = smgrsw[reln->smgr_which].smgr_prefetch(reln, forknum, blocknum, nblocks);
	RESUME_INTERRUPTS();

	return ret;
}

/*
 * smgrmaxcombine (中文)查询从某块起最多能把多少块合并进一次 IO
 *
 * 【作用】smgrreadv()/smgrwritev() 的调用方在规划"合并 IO"前,先调用
 * 本函数确认一次 IO 最多可覆盖多少块(返回值含 blocknum 本身)。当前
 * md 实现只受"段边界"限制:同一段文件内的连续块才能合并,跨段必须
 * 分开。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块号。
 * 【返回值】可从 blocknum 起合并的最大块数(>= 1)。
 *
 * smgrmaxcombine() - Return the maximum number of total blocks that can be
 *				 combined with an IO starting at blocknum.
 *
 * The returned value includes the IO for blocknum itself.
 */
uint32
smgrmaxcombine(SMgrRelation reln, ForkNumber forknum,
			   BlockNumber blocknum)
{
	uint32		ret;

	HOLD_INTERRUPTS();
	ret = smgrsw[reln->smgr_which].smgr_maxcombine(reln, forknum, blocknum);
	RESUME_INTERRUPTS();

	return ret;
}

/*
 * smgrreadv (中文)从关系读取连续的一批块到指定缓冲
 *
 * 【作用】缓冲管理器把磁盘页调入共享缓冲池时调用(instantiate pages),
 * 实现必须返回 PostgreSQL 标准页格式。跨段/短读等细节由具体实现
 * 处理。若计划一次读多块,调用方应先经 smgrmaxcombine() 确认可合并
 * 的块数上限。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块号;
 *   buffers  —— 输出缓冲指针数组(buffers[i] 指向接收第 i 块的 BLCKSZ
 *                缓冲);
 *   nblocks  —— 要读的块数。
 * 【返回值】无(失败以 ERROR 报告)。
 *
 * smgrreadv() -- read a particular block range from a relation into the
 *				 supplied buffers.
 *
 * This routine is called from the buffer manager in order to
 * instantiate pages in the shared buffer cache.  All storage managers
 * return pages in the format that POSTGRES expects.
 *
 * If more than one block is intended to be read, callers need to use
 * smgrmaxcombine() to check how many blocks can be combined into one IO.
 */
void
smgrreadv(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		  void **buffers, BlockNumber nblocks)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_readv(reln, forknum, blocknum, buffers,
										nblocks);
	RESUME_INTERRUPTS();
}

/*
 * smgrstartreadv (中文)smgrreadv() 的异步版本
 *
 * 【作用】借助 AIO 框架发起异步读:IO 提交后本函数立即返回,数据就绪
 * 时由完成回调(见 md.c 的 md_readv_complete)通知上层。smgr 抽象保持
 * "以块为单位"的接口:返回的字节数会换算成块数。
 *
 * 【调用方额外职责】
 * - 部分读(读到一半遇 EOF/错误)需要调用方自行对未读块重发 IO;
 * - 出错时 smgr 只向服务器日志(LOG_SERVER_ONLY)记录详情,上层须调用
 *   pgaio_result_report() 把消息转达给用户(PGAIO_RS_WARNING)或中止
 *   事务(PGAIO_RS_ERROR);
 * - Valgrind 下,按 io_method 与并发情况,"buffers"内存的 DEFINED 状态
 *   可能变化,需要接受这一点。
 *
 * 【参数】
 *   ioh —— AIO 句柄(指定使用的 IO 资源与完成回调);
 *   其余参数与 smgrreadv() 相同。
 * 【返回值】无。
 *
 * smgrstartreadv() -- asynchronous version of smgrreadv()
 *
 * This starts an asynchronous readv IO using the IO handle `ioh`. Other than
 * `ioh` all parameters are the same as smgrreadv().
 *
 * Completion callbacks above smgr will be passed the result as the number of
 * successfully read blocks if the read [partially] succeeds (Buffers for
 * blocks not successfully read might bear unspecified modifications, up to
 * the full nblocks). This maintains the abstraction that smgr operates on the
 * level of blocks, rather than bytes.
 *
 * Compared to smgrreadv(), more responsibilities fall on the caller:
 * - Partial reads need to be handled by the caller re-issuing IO for the
 *   unread blocks
 * - smgr will ereport(LOG_SERVER_ONLY) some problems, but higher layers are
 *   responsible for pgaio_result_report() to mirror that news to the user (if
 *   the IO results in PGAIO_RS_WARNING) or abort the (sub)transaction (if
 *   PGAIO_RS_ERROR).
 * - Under Valgrind, the "buffers" memory may or may not change status to
 *   DEFINED, depending on io_method and concurrent activity.
 */
void
smgrstartreadv(PgAioHandle *ioh,
			   SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
			   void **buffers, BlockNumber nblocks)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_startreadv(ioh,
											 reln, forknum, blocknum, buffers,
											 nblocks);
	RESUME_INTERRUPTS();
}

/*
 * smgrwritev (中文)把一批缓冲写入关系的指定位置(只用于覆写已有块)
 *
 * 【作用】把 [blocknum, blocknum+nblocks) 的数据写回文件。**只允许写
 * 已存在的块(块号 < 当前 EOF)**;扩展文件请用 smgrextend()。
 *
 * 【同步语义】本函数不是同步落盘:返回时数据只到了内核页缓存,真正的
 * fsync 由后续检查点(或 smgrimmedsync)完成。为保证"下次检查点之前
 * 一定 fsync 本页",必须存在某种机制阻止检查点"抢先越过"该写:缓冲
 * 管理器的写靠缓冲区锁保护;bulk_write.c 的批量写入则记录 RedoRecPtr、
 * 必要时自行 smgrimmedsync()(它依赖"没有其他后端在并发修改该页"这
 * 一前提)。
 *
 * 【skipFsync】true 表示调用方会另行安排 fsync(或临时关系无需),本
 * 函数不必登记到检查点;之后应配合 smgrregistersync()/smgrimmedsync()
 * 使用,最稳妥的路径是走 bulk_write.c 的批量加载设施。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块号;
 *   buffers  —— 待写数据指针数组;nblocks —— 块数;
 *   skipFsync —— 见上。
 * 【返回值】无(失败以 ERROR 报告)。
 *
 * smgrwritev() -- Write the supplied buffers out.
 *
 * This is to be used only for updating already-existing blocks of a
 * relation (ie, those before the current EOF).  To extend a relation,
 * use smgrextend().
 *
 * This is not a synchronous write -- the block is not necessarily
 * on disk at return, only dumped out to the kernel.  However,
 * provisions will be made to fsync the write before the next checkpoint.
 *
 * NB: The mechanism to ensure fsync at next checkpoint assumes that there is
 * something that prevents a concurrent checkpoint from "racing ahead" of the
 * write.  One way to prevent that is by holding a lock on the buffer; the
 * buffer manager's writes are protected by that.  The bulk writer facility
 * in bulk_write.c checks the redo pointer and calls smgrimmedsync() if a
 * checkpoint happened; that relies on the fact that no other backend can be
 * concurrently modifying the page.
 *
 * skipFsync indicates that the caller will make other provisions to
 * fsync the relation, so we needn't bother.  Temporary relations also
 * do not require fsync.
 *
 * If more than one block is intended to be read, callers need to use
 * smgrmaxcombine() to check how many blocks can be combined into one IO.
 */
void
smgrwritev(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		   const void **buffers, BlockNumber nblocks, bool skipFsync)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_writev(reln, forknum, blocknum,
										 buffers, nblocks, skipFsync);
	RESUME_INTERRUPTS();
}

/*
 * smgrwriteback (中文)通知内核把指定块区间写回磁盘(异步刷脏)
 *
 * 【作用】对 [blocknum, blocknum+nblocks) 范围发起内核级回写,用于
 * bgwriter 等批量刷脏路径,比逐块调用效率高。不做同步等待,不保证
 * 返回时数据已持久。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块号;nblocks —— 块数。
 * 【返回值】无。
 *
 * smgrwriteback() -- Trigger kernel writeback for the supplied range of
 *					   blocks.
 */
void
smgrwriteback(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
			  BlockNumber nblocks)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_writeback(reln, forknum, blocknum,
											nblocks);
	RESUME_INTERRUPTS();
}

/*
 * smgrnblocks (中文)返回关系当前拥有的块数
 *
 * 【作用】查询某个 fork 的文件大小(块数)。优先走缓存:仅当
 * smgrnblocks_cached() 返回有效值(目前仅在恢复期间缓存可用)时直接
 * 返回,否则调用具体实现的 smgr_nblocks() 向内核问询,并把结果存入
 * smgr_cached_nblocks 缓存备用。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】块数(>= 0)。
 *
 * smgrnblocks() -- Calculate the number of blocks in the
 *					supplied relation.
 */
BlockNumber
smgrnblocks(SMgrRelation reln, ForkNumber forknum)
{
	BlockNumber result;

	/* Check and return if we get the cached value for the number of blocks. */
	result = smgrnblocks_cached(reln, forknum);
	if (result != InvalidBlockNumber)
		return result;

	HOLD_INTERRUPTS();

	result = smgrsw[reln->smgr_which].smgr_nblocks(reln, forknum);

	reln->smgr_cached_nblocks[forknum] = result;

	RESUME_INTERRUPTS();

	return result;
}

/*
 * smgrnblocks_cached (中文)读取缓存的块数(若有)
 *
 * 【作用】返回 SMgrRelation 中缓存的关系大小。**目前只在恢复
 * (InRecovery)期间信任缓存**,因为系统没有"文件被别处扩大"的共享
 * 失效机制;恢复之外一律返回 InvalidBlockNumber 表示"无缓存"。别处
 * 代码直接读 smgr_cached_nblocks 时必须容忍过期数据。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】缓存的块数,或 InvalidBlockNumber(恢复外/未缓存)。
 *
 * smgrnblocks_cached() -- Get the cached number of blocks in the supplied
 *						   relation.
 *
 * Returns an InvalidBlockNumber when not in recovery and when the relation
 * fork size is not cached.
 */
BlockNumber
smgrnblocks_cached(SMgrRelation reln, ForkNumber forknum)
{
	/*
	 * For now, this function uses cached values only in recovery due to lack
	 * of a shared invalidation mechanism for changes in file size.  Code
	 * elsewhere reads smgr_cached_nblocks and copes with stale data.
	 */
	if (InRecovery && reln->smgr_cached_nblocks[forknum] != InvalidBlockNumber)
		return reln->smgr_cached_nblocks[forknum];

	return InvalidBlockNumber;
}

/*
 * smgrtruncate (中文)把给定关系的若干 fork 截断到指定大小
 *
 * 【作用】立即执行截断(不可回滚!),流程:
 * 1) DropRelationBuffers():丢弃被删块在缓冲池中的缓冲(不写回);
 * 2) CacheInvalidateSmgr():广播失效消息,强制其他后端关闭可能指向已删
 *    段文件的 smgr 引用,并清掉过期的 smgr_targblock 等缓存(消息也会
 *    回到本后端,造成一次多半没必要的本地 smgr 冲刷,但这不是热点路径);
 * 3) 逐 fork 调用 smgr_truncate 真截断,并维护本地 smgr_cached_nblocks
 *    缓存(注意重放场景可能出现 nblocks > old_nblocks:此时具体实现
 *    什么都不做,缓存应取 old 值而非请求值)。
 *
 * 【调用约束】调用方必须持有关系的 AccessExclusiveLock(保证其他后端
 * 收到上面的失效消息后才再次访问该关系);应在临界区(critical
 * section)内调用,但"获取当前大小"必须在临界区外完成,且两者之间
 * 不得处理中断或调用本关系的任何 smgr 函数。
 *
 * 【参数】
 *   reln      —— 目标关系;
 *   forknum   —— fork 编号数组;nforks —— 数组长度;
 *   old_nblocks —— 各 fork 当前大小数组(调用方事先查得);
 *   nblocks   —— 各 fork 截断后的目标大小数组。
 * 【返回值】无。
 *
 * smgrtruncate() -- Truncate the given forks of supplied relation to
 *					 each specified numbers of blocks
 *
 * The truncation is done immediately, so this can't be rolled back.
 *
 * The caller must hold AccessExclusiveLock on the relation, to ensure that
 * other backends receive the smgr invalidation event that this function sends
 * before they access any forks of the relation again.  The current size of
 * the forks should be provided in old_nblocks.  This function should normally
 * be called in a critical section, but the current size must be checked
 * outside the critical section, and no interrupts or smgr functions relating
 * to this relation should be called in between.
 */
void
smgrtruncate(SMgrRelation reln, ForkNumber *forknum, int nforks,
			 BlockNumber *old_nblocks, BlockNumber *nblocks)
{
	int			i;

	/*
	 * Get rid of any buffers for the about-to-be-deleted blocks. bufmgr will
	 * just drop them without bothering to write the contents.
	 */
	DropRelationBuffers(reln, forknum, nforks, nblocks);

	/*
	 * Send a shared-inval message to force other backends to close any smgr
	 * references they may have for this rel.  This is useful because they
	 * might have open file pointers to segments that got removed, and/or
	 * smgr_targblock variables pointing past the new rel end.  (The inval
	 * message will come back to our backend, too, causing a
	 * probably-unnecessary local smgr flush.  But we don't expect that this
	 * is a performance-critical path.)  As in the unlink code, we want to be
	 * sure the message is sent before we start changing things on-disk.
	 */
	CacheInvalidateSmgr(reln->smgr_rlocator);

	/* Do the truncation */
	for (i = 0; i < nforks; i++)
	{
		/* Make the cached size invalid if we encounter an error. */
		reln->smgr_cached_nblocks[forknum[i]] = InvalidBlockNumber;

		smgrsw[reln->smgr_which].smgr_truncate(reln, forknum[i],
											   old_nblocks[i], nblocks[i]);

		/*
		 * We might as well update the local smgr_cached_nblocks values. The
		 * smgr cache inval message that this function sent will cause other
		 * backends to invalidate their copies of smgr_cached_nblocks, and
		 * these ones too at the next command boundary. But ensure they aren't
		 * outright wrong until then.
		 *
		 * We can have nblocks > old_nblocks when a relation was truncated
		 * multiple times, a replica applied all the truncations, and later
		 * restarts from a restartpoint located before the truncations. The
		 * relation on disk will be the size of the last truncate. When
		 * replaying the first truncate, we will have nblocks > current size.
		 * In such cases, smgr_truncate does nothing, so set the cached size
		 * to the old size rather than the requested size.
		 */
		reln->smgr_cached_nblocks[forknum[i]] =
			nblocks[i] > old_nblocks[i] ? old_nblocks[i] : nblocks[i];
	}
}

/*
 * smgrregistersync (中文)登记:在下个检查点同步(fsync)整个关系
 *
 * 【作用】配合 skipFsync=true 的写使用:跳过逐次登记后,在这里一次性
 * 把整个关系(含各段)登记为"下次检查点需 fsync"。
 *
 * 【注意事项】调用前可能已有检查点过去:若在 smgrwrite/smgrextend 与
 * 本次调用之间发生过检查点,那次检查点已错过本关系的 fsync,必须改用
 * smgrimmedsync()。多数调用方应使用 bulk_write.c 的批量加载设施,它
 * 自动处理这一竞态。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】无。
 *
 * smgrregistersync() -- Request a relation to be sync'd at next checkpoint
 *
 * This can be used after calling smgrwrite() or smgrextend() with skipFsync =
 * true, to register the fsyncs that were skipped earlier.
 *
 * Note: be mindful that a checkpoint could already have happened between the
 * smgrwrite or smgrextend calls and this!  In that case, the checkpoint
 * already missed fsyncing this relation, and you should use smgrimmedsync
 * instead.  Most callers should use the bulk loading facility in bulk_write.c
 * which handles all that.
 */
void
smgrregistersync(SMgrRelation reln, ForkNumber forknum)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_registersync(reln, forknum);
	RESUME_INTERRUPTS();
}

/*
 * smgrimmedsync (中文)强制把关系的全部写同步到稳定存储(立即 fsync)
 *
 * 【作用】同步地把该 fork 之前所有写压到磁盘。典型用途:创建全新关系
 * (如新索引)——索引构建过程用 smgrwrite/smgrextend 直接写成品页、
 * 不逐条记 WAL,完成后一次 fsync 即可满足崩溃安全(等价于为该索引
 * 强制了一次检查点)。但注意:若需要 PITR/流复制,则仍必须写 WAL
 * 记录,仅靠 fsync 不够。
 *
 * 【配套约定】
 * - 之前的写应传 skipFsync=true,避免重复 fsync;
 * - 若关系可能在缓冲池中留有脏页,必须先 FlushRelationBuffers(),否则
 *   本次同步没有意义;
 * - 多数调用方应改用 bulk_write.c 的批量加载设施。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】无。
 *
 * smgrimmedsync() -- Force the specified relation to stable storage.
 *
 * Synchronously force all previous writes to the specified relation
 * down to disk.
 *
 * This is useful for building completely new relations (eg, new
 * indexes).  Instead of incrementally WAL-logging the index build
 * steps, we can just write completed index pages to disk with smgrwrite
 * or smgrextend, and then fsync the completed index file before
 * committing the transaction.  (This is sufficient for purposes of
 * crash recovery, since it effectively duplicates forcing a checkpoint
 * for the completed index.  But it is *not* sufficient if one wishes
 * to use the WAL log for PITR or replication purposes: in that case
 * we have to make WAL entries as well.)
 *
 * The preceding writes should specify skipFsync = true to avoid
 * duplicative fsyncs.
 *
 * Note that you need to do FlushRelationBuffers() first if there is
 * any possibility that there are dirty buffers for the relation;
 * otherwise the sync is not very meaningful.
 *
 * Most callers should use the bulk loading facility in bulk_write.c
 * instead of calling this directly.
 */
void
smgrimmedsync(SMgrRelation reln, ForkNumber forknum)
{
	HOLD_INTERRUPTS();
	smgrsw[reln->smgr_which].smgr_immedsync(reln, forknum);
	RESUME_INTERRUPTS();
}

/*
 * smgrfd (中文)返回指定块所在文件的原始文件描述符
 *
 * 【作用】仅供 AIO 框架使用:当 IO 需要在"发起进程之外的进程"(如 IO
 * worker)中执行时,worker 不能直接使用原进程的 VFD,必须重新打开
 * 文件;本函数返回该块所在段的原始内核 fd,并把块在段内的字节偏移
 * 写入 *off。
 *
 * 【调用前提】调用方必须保证当前不会处理中断,否则 fd 可能被提前
 * 关闭。
 *
 * 【参数】
 *   reln, forknum, blocknum —— 目标关系、fork 与块号;
 *   off —— 输出参数:块在文件内的字节偏移。
 * 【返回值】原始 fd;出错以 ERROR 报告。
 *
 * Return fd for the specified block number and update *off to the appropriate
 * position.
 *
 * This is only to be used for when AIO needs to perform the IO in a different
 * process than where it was issued (e.g. in an IO worker).
 */
static int
smgrfd(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum, uint32 *off)
{
	int			fd;

	/*
	 * The caller needs to prevent interrupts from being processed, otherwise
	 * the FD could be closed prematurely.
	 */
	Assert(!INTERRUPTS_CAN_BE_PROCESSED());

	fd = smgrsw[reln->smgr_which].smgr_fd(reln, forknum, blocknum, off);

	return fd;
}

/*
 * AtEOXact_SMgr (中文)事务结束钩子:销毁所有未 pin 的 SMgrRelation
 *
 * 【作用】事务提交或回滚时(两者同等对待)由事务层调用,通过
 * smgrdestroyall() 清理本事务期间打开、未被 pin 的关系对象。
 *
 * 【设计思想】这是"临时关系对象活得久一些(摊销多块盲目写的开销)与
 * 不能活得无限久(免得一直占着内核文件描述符、文件被删后无法释放)"
 * 之间的折中方案。
 *
 * 【参数】无。
 * 【返回值】无。
 *
 * AtEOXact_SMgr
 *
 * This routine is called during transaction commit or abort (it doesn't
 * particularly care which).  All unpinned SMgrRelation objects are destroyed.
 *
 * We do this as a compromise between wanting transient SMgrRelations to
 * live awhile (to amortize the costs of blind writes of multiple blocks)
 * and needing them to not live forever (since we're probably holding open
 * a kernel file descriptor for the underlying file, and we need to ensure
 * that gets closed reasonably soon if the file gets deleted).
 */
void
AtEOXact_SMgr(void)
{
	smgrdestroyall();
}

/*
 * ProcessBarrierSmgrRelease (中文)处理"释放所有 smgr 文件描述符"的进程屏障
 *
 * 【作用】收到 PROCSIGNAL_BARRIER_SMGRRELEASE 屏障信号时的回调:调用
 * smgrreleaseall() 关闭本进程所有 SMgrRelation 持有的文件描述符(例如
 * 为了让某个被删除文件的磁盘空间能立即释放),但保留对象本身。返回
 * true 表示屏障处理完成。
 *
 * 【参数】无。
 * 【返回值】恒为 true(屏障已完成)。
 *
 * This routine is called when we are ordered to release all open files by a
 * ProcSignalBarrier.
 */
bool
ProcessBarrierSmgrRelease(void)
{
	smgrreleaseall();
	return true;
}

/*
 * pgaio_io_set_target_smgr (中文)把 AIO 句柄的目标设置为 smgr,并填充目标数据
 *
 * 【作用】发起 smgr 类型 AIO(读/写)前调用:设置 IO 的目标类型为
 * PGAIO_TID_SMGR,并把关系定位、fork、起始块号、块数、是否跳过 fsync
 * 等写入 IO 句柄的目标数据区。这些信息在 IO 由其他进程执行时会被
 * smgr_aio_reopen() 用于重新定位并打开文件。
 *
 * 【设计思想】"backend"字段不保存:IO 的属主(owner)已隐含了执行
 * 进程,临时关系重建路径会以属主进程号重新打开对应文件。
 *
 * 【参数】
 *   ioh —— AIO 句柄;
 *   smgr —— 目标 SMgrRelation;forknum —— fork;blocknum —— 起始块;
 *   nblocks —— 块数;
 *   skip_fsync —— 是否跳过 fsync。注意临时关系被强制视为"跳过"(临时
 *                 关系永不 fsync),见 sd->smgr.skip_fsync 的赋值。
 * 【返回值】无。
 *
 * Set target of the IO handle to be smgr and initialize all the relevant
 * pieces of data.
 */
void
pgaio_io_set_target_smgr(PgAioHandle *ioh,
						 SMgrRelationData *smgr,
						 ForkNumber forknum,
						 BlockNumber blocknum,
						 int nblocks,
						 bool skip_fsync)
{
	PgAioTargetData *sd = pgaio_io_get_target_data(ioh);

	pgaio_io_set_target(ioh, PGAIO_TID_SMGR);

	/* backend is implied via IO owner */
	sd->smgr.rlocator = smgr->smgr_rlocator.locator;
	sd->smgr.forkNum = forknum;
	sd->smgr.blockNum = blocknum;
	sd->smgr.nblocks = nblocks;
	sd->smgr.is_temp = SmgrIsTemp(smgr);
	/* Temp relations should never be fsync'd */
	sd->smgr.skip_fsync = skip_fsync && !SmgrIsTemp(smgr);
}

/*
 * smgr_aio_reopen (中文)smgr AIO 目标的"重开文件"回调
 *
 * 【作用】当 AIO 在不同于发起者的进程(如 IO worker)中执行时被 AIO
 * 框架调用:依据目标数据里保存的 rlocator 重新 smgropen() 关系(临时
 * 关系以 IO 属主进程号打开,普通关系用 INVALID_PROC_NUMBER),再用
 * smgrfd() 重新打开目标块所在段文件,把原始 fd 写回操作数据区
 * (od->read.fd / od->write.fd),供实际 IO 使用。
 *
 * 【设计思想】smgr 的 fd 体系(VFD)绑定在进程本地,跨进程 IO 必须
 * "重开"而不能传递 fd,这正是"IO 目标回调"抽象存在的意义。断言
 * !INTERRUPTS_CAN_BE_PROCESSED() 保证重开过程中 fd 不会被中断处理
 * 关闭。
 *
 * 【参数】ioh —— 需要重开的 AIO 句柄。
 * 【返回值】无。
 *
 * Callback for the smgr AIO target, to reopen the file (e.g. because the IO
 * is executed in a worker).
 */
static void
smgr_aio_reopen(PgAioHandle *ioh)
{
	PgAioTargetData *sd = pgaio_io_get_target_data(ioh);
	PgAioOpData *od = pgaio_io_get_op_data(ioh);
	SMgrRelation reln;
	ProcNumber	procno;
	uint32		off;

	/*
	 * The caller needs to prevent interrupts from being processed, otherwise
	 * the FD could be closed again before we get to executing the IO.
	 */
	Assert(!INTERRUPTS_CAN_BE_PROCESSED());

	if (sd->smgr.is_temp)
		procno = pgaio_io_get_owner(ioh);
	else
		procno = INVALID_PROC_NUMBER;

	reln = smgropen(sd->smgr.rlocator, procno);
	switch (pgaio_io_get_op(ioh))
	{
		case PGAIO_OP_INVALID:
			pg_unreachable();
			break;
		case PGAIO_OP_READV:
			od->read.fd = smgrfd(reln, sd->smgr.forkNum, sd->smgr.blockNum, &off);
			Assert(off == od->read.offset);
			break;
		case PGAIO_OP_WRITEV:
			od->write.fd = smgrfd(reln, sd->smgr.forkNum, sd->smgr.blockNum, &off);
			Assert(off == od->write.offset);
			break;
	}
}

/*
 * smgr_aio_describe_identity (中文)生成 AIO 目标的文字描述(用于日志/错误消息)
 *
 * 【作用】AIO 出错或调试时,把 IO 目标格式化成可读字符串,例如
 * "block 42 in file \"base/5/16384\"":按 nblocks 为 0 / 1 / 多三种
 * 情况分别生成"文件"、"单块"、"连续块区间"形式的描述。路径通过
 * relpathbackend() 构造(临时关系用属主进程号)。
 *
 * 【参数】sd —— AIO 目标数据(必须是 smgr 类型)。
 * 【返回值】新分配的描述字符串(调用方负责 pfree)。
 *
 * Callback for the smgr AIO target, describing the target of the IO.
 */
static char *
smgr_aio_describe_identity(const PgAioTargetData *sd)
{
	RelPathStr	path;
	char	   *desc;

	path = relpathbackend(sd->smgr.rlocator,
						  sd->smgr.is_temp ?
						  MyProcNumber : INVALID_PROC_NUMBER,
						  sd->smgr.forkNum);

	if (sd->smgr.nblocks == 0)
		desc = psprintf(_("file \"%s\""), path.str);
	else if (sd->smgr.nblocks == 1)
		desc = psprintf(_("block %u in file \"%s\""),
						sd->smgr.blockNum,
						path.str);
	else
		desc = psprintf(_("blocks %u..%u in file \"%s\""),
						sd->smgr.blockNum,
						sd->smgr.blockNum + sd->smgr.nblocks - 1,
						path.str);

	return desc;
}
