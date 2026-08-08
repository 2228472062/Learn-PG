/*-------------------------------------------------------------------------
 *
 * md.c
 *	  This code manages relations that reside on magnetic disk.
 *
 * Or at least, that was what the Berkeley folk had in mind when they named
 * this file.  In reality, what this code provides is an interface from
 * the smgr API to Unix-like filesystem APIs, so it will work with any type
 * of device for which the operating system provides filesystem support.
 * It doesn't matter whether the bits are on spinning rust or some other
 * storage technology.
 *
 * 【模块总览(中文)】
 * 本文件实现 PostgreSQL 的"磁介质"存储管理器(md,magnetic disk),
 * 是 smgr 抽象层(见 smgr.c)在 Unix 文件系统上的落地:它把 smgr 的
 * 文件级操作翻译成 open/read/write/truncate/fsync/unlink 等系统调用,
 * 因此对任何提供文件系统的设备(传统磁盘、SSD、NFS 等)都适用。
 *
 * 核心设计:关系按"段"(segment)切分存储。老式文件系统单文件上限
 * (常见 2GB)可能小于一个大关系,因此 md 把每个关系切成多个段文件,
 * 每段至多 RELSEG_SIZE 个块(默认 131072 块 = 1GB,由 configure 的
 * --with-segsize 决定,见 pg_config.h)。磁盘上表现为:
 *   - 若干个恰好 RELSEG_SIZE 块的"满段" + 一个 0 <= 大小 < RELSEG_SIZE
 *     的"部分段"(二者合称"活动段") + 任意个大小为 0 的"非活动段"
 *     (mdtruncate() 截断后残留、等待时机处理/复用的空文件)。
 * 段文件命名:关系基础路径后追加 ".段号"(段 0 无后缀)。
 *
 * 本文件为每个关系的每个 fork 维护"已打开段"的数组(md_seg_fds,
 * 元素为 MdfdVec),统一分配在 MdCxt 内存上下文中。打开是惰性的:
 * mdopen 只做登记,真正的文件打开发生在首次读写访问时
 * (_mdfd_getseg/_mdfd_openseg);关闭从数组末尾往前推进,便于内存
 * 管理。文件都通过 fd.c 的 VFD(虚拟文件描述符)打开,受 fd.c 的统一
 * 限额与关闭管理。
 *
 * 同步(sync)路径:写页时若非 skipFsync 且非临时关系,通过
 * register_dirty_segment() 把"段文件"登记到 sync 请求队列,由
 * checkpointer(或后端自己)在检查点统一 fsync;被删关系留下的"空首
 * 段"(tombstone)的延迟删除(SYNC_UNLINK_REQUEST)也走同一队列。
 * 检查点/恢复期间按 FileTag 直接操作文件的回调为
 * mdsyncfiletag()/mdunlinkfiletag()/mdfiletagmatches()。
 *
 * 与上层的一致性:文件级"锁"语义由访问方法/锁管理器与 relcache 的
 * 失效机制保证(例如 mdclose 配合 CacheInvalidateSmgr 让所有后端尽快
 * 放弃对已删段的引用),md 自身只负责单进程内 fd 数组的一致性与
 * O_EXCL 等内核原语提供的创建互斥。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/smgr/md.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <limits.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/file.h>

#include "access/xlogutils.h"
#include "commands/tablespace.h"
#include "common/file_utils.h"
#include "miscadmin.h"
#include "pg_trace.h"
#include "pgstat.h"
#include "storage/aio.h"
#include "storage/bufmgr.h"
#include "storage/fd.h"
#include "storage/md.h"
#include "storage/relfilelocator.h"
#include "storage/smgr.h"
#include "storage/sync.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

/*
 * The magnetic disk storage manager keeps track of open file
 * descriptors in its own descriptor pool.  This is done to make it
 * easier to support relations that are larger than the operating
 * system's file size limit (often 2GBytes).  In order to do that,
 * we break relations up into "segment" files that are each shorter than
 * the OS file size limit.  The segment size is set by the RELSEG_SIZE
 * configuration constant in pg_config.h.
 *
 * On disk, a relation must consist of consecutively numbered segment
 * files in the pattern
 *	-- Zero or more full segments of exactly RELSEG_SIZE blocks each
 *	-- Exactly one partial segment of size 0 <= size < RELSEG_SIZE blocks
 *	-- Optionally, any number of inactive segments of size 0 blocks.
 * The full and partial segments are collectively the "active" segments.
 * Inactive segments are those that once contained data but are currently
 * not needed because of an mdtruncate() operation.  The reason for leaving
 * them present at size zero, rather than unlinking them, is that other
 * backends and/or the checkpointer might be holding open file references to
 * such segments.  If the relation expands again after mdtruncate(), such
 * that a deactivated segment becomes active again, it is important that
 * such file references still be valid --- else data might get written
 * out to an unlinked old copy of a segment file that will eventually
 * disappear.
 *
 * RELSEG_SIZE must fit into BlockNumber; but since we expose its value
 * as an integer GUC, it actually needs to fit in signed int.  It's worth
 * having a cross-check for this since configure's --with-segsize options
 * could let people select insane values.
 */
/* 编译期断言:RELSEG_SIZE 必须能放进带符号 int。
 * RELSEG_SIZE 定义时必须适合 BlockNumber,但既然它以整型 GUC 对外暴露
 * (configure 的 --with-segsize 可能选出离谱的值),必须保证其不超过
 * INT_MAX,否则 GUC 解析与相关算术都会出错。 */
StaticAssertDecl(RELSEG_SIZE > 0 && RELSEG_SIZE <= INT_MAX,
				 "RELSEG_SIZE must fit in an integer");

/*
 * File descriptors are stored in the per-fork md_seg_fds arrays inside
 * SMgrRelation. The length of these arrays is stored in md_num_open_segs.
 * Note that a fork's md_num_open_segs having a specific value does not
 * necessarily mean the relation doesn't have additional segments; we may
 * just not have opened the next segment yet.  (We could not have "all
 * segments are in the array" as an invariant anyway, since another backend
 * could extend the relation while we aren't looking.)  We do not have
 * entries for inactive segments, however; as soon as we find a partial
 * segment, we assume that any subsequent segments are inactive.
 *
 * The entire MdfdVec array is palloc'd in the MdCxt memory context.
 */
/* 单个段文件的描述结构(MdfdVec,"磁介质文件描述向量"):
 * - mdfd_vfd  : 该段文件在 fd.c 虚拟文件描述符池中的句柄(File);
 * - mdfd_segno: 段号(从 0 开始,即该段在关系中的序号)。
 * 每个关系 fork 维护一个 MdfdVec 数组(reln->md_seg_fds[forknum]),数组
 * 长度记录在 reln->md_num_open_segs[forknum] 中。注意:数组长度并不
 * 等于"关系的总段数"——我们可能还没打开后面的段(其他后端也可能并发
 * 扩展了关系);同时数组中不含非活动段:一旦发现"部分段"(未满段),
 * 就认为其后所有段都是非活动的。整个数组用一次 palloc 分配在 MdCxt
 * 上下文里,由 _fdvec_resize() 调整大小。 */

typedef struct _MdfdVec
{
	File		mdfd_vfd;		/* fd number in fd.c's pool */
	BlockNumber mdfd_segno;		/* segment number, from 0 */
} MdfdVec;

/* 所有 MdfdVec 数组的专用内存上下文(由 mdinit() 在进程启动时创建,
 * 挂在 TopMemoryContext 之下)。单独建一个上下文,便于统计与整块回收,
 * 避免与调用方的内存上下文纠缠。 */
static MemoryContext MdCxt;		/* context for all MdfdVec objects */


/* 初始化一个 FileTag(文件标签),用于描述 md.c 的一个段文件,作为
 * sync 请求队列(sync.c)的键:
 * - handler 置为 SYNC_HANDLER_MD,表示由 md 的回调(mdsyncfiletag /
 *   mdunlinkfiletag)处理;
 * - 记录关系 locator、fork 与段号,唯一对应一个物理文件。
 * 先 memset 清零,保证未用字段一致。 */
#define INIT_MD_FILETAG(a,xx_rlocator,xx_forknum,xx_segno) \
( \
	memset(&(a), 0, sizeof(FileTag)), \
	(a).handler = SYNC_HANDLER_MD, \
	(a).rlocator = (xx_rlocator), \
	(a).forknum = (xx_forknum), \
	(a).segno = (xx_segno) \
)


/*** behavior for mdopen & _mdfd_getseg ***/
/* mdopen/_mdfd_getseg 的"段不存在时怎么办"行为标志(可按位或组合):
 * - EXTENSION_FAIL            : 段不存在则直接 ereport(ERROR);
 * - EXTENSION_RETURN_NULL     : 段不存在(或被删)则返回 NULL;配合
 *                               FILE_POSSIBLY_DELETED(errno) 判定
 *                               "文件可能已被删除"这一特殊情形;
 * - EXTENSION_CREATE          : 允许按需创建新段(仅 mdextend/
 *                               mdzeroextend 等扩展路径使用);
 * - EXTENSION_CREATE_RECOVERY  : 恢复(recovery)期间允许创建缺失的段
 *                               (重放可能写入一个后来被删的关系的
 *                               高号段);
 * - EXTENSION_DONT_OPEN       : 若目标段尚未打开,直接返回 NULL,绝不
 *                               去打开文件(用于 mdwriteback:避免与
 *                               PROCSIGNAL_BARRIER_SMGRRELEASE 竞态,
 *                               不给自己留下一个即将被 unlink 文件的
 *                               描述符)。 */
/* ereport if segment not present */
#define EXTENSION_FAIL				(1 << 0)
/* return NULL if segment not present */
#define EXTENSION_RETURN_NULL		(1 << 1)
/* create new segments as needed */
#define EXTENSION_CREATE			(1 << 2)
/* create new segments if needed during recovery */
#define EXTENSION_CREATE_RECOVERY	(1 << 3)
/* don't try to open a segment, if not already open */
#define EXTENSION_DONT_OPEN			(1 << 5)


/*
 * Fixed-length string to represent paths to files that need to be built by
 * md.c.
 *
 * The maximum number of segments is MaxBlockNumber / RELSEG_SIZE, where
 * RELSEG_SIZE can be set to 1 (for testing only).
 */
/* 段号最多 SEGMENT_CHARS 个字符(与 OID 同宽,即无符号 32 位十进制
 * 最大 10 位);据此算出"关系路径 + '.' + 段号"的最大长度
 * MD_PATH_STR_MAXLEN,得到定长字符串类型 MdPathStr。用定长栈缓冲区
 * 而非 palloc,保证在临界区(如 mdtruncate 承诺不分配内存)或高频
 * 路径上也能安全使用。 */
#define SEGMENT_CHARS	OIDCHARS
#define MD_PATH_STR_MAXLEN \
	(\
		REL_PATH_STR_MAXLEN \
		+ sizeof((char)'.') \
		+ SEGMENT_CHARS \
	)
/* 定长路径字符串(MdPathStr):存放 md.c 需要构造的段文件路径(基础
 * relpath 最长 REL_PATH_STR_MAXLEN,加上 '.' 与段号)。用数组而非指针,
 * 便于栈上分配与整块按值传递。 */
typedef struct MdPathStr
{
	char		str[MD_PATH_STR_MAXLEN + 1];
} MdPathStr;


/* local routines */
static void mdunlinkfork(RelFileLocatorBackend rlocator, ForkNumber forknum,
						 bool isRedo);
static MdfdVec *mdopenfork(SMgrRelation reln, ForkNumber forknum, int behavior);
static void register_dirty_segment(SMgrRelation reln, ForkNumber forknum,
								   MdfdVec *seg);
static void register_unlink_tombstone(RelFileLocatorBackend rlocator);
static void register_forget_request(RelFileLocatorBackend rlocator, ForkNumber forknum,
									BlockNumber segno);
static void _fdvec_resize(SMgrRelation reln,
						  ForkNumber forknum,
						  int nseg);
static MdPathStr _mdfd_segpath(SMgrRelation reln, ForkNumber forknum,
							   BlockNumber segno);
static MdfdVec *_mdfd_openseg(SMgrRelation reln, ForkNumber forknum,
							  BlockNumber segno, int oflags);
static MdfdVec *_mdfd_getseg(SMgrRelation reln, ForkNumber forknum,
							 BlockNumber blkno, bool skipFsync, int behavior);
static BlockNumber _mdnblocks(SMgrRelation reln, ForkNumber forknum,
							  MdfdVec *seg);

static PgAioResult md_readv_complete(PgAioHandle *ioh, PgAioResult prior_result, uint8 cb_data);
static void md_readv_report(PgAioResult result, const PgAioTargetData *td, int elevel);

/* md 异步读(mdstartreadv)的 AIO 回调表:
 * - complete_shared : IO 完成时调用,把"字节数"换算成"块数"并判定
 *                     成功/部分/失败(md_readv_complete);
 * - report          : 出错时生成并输出错误消息(md_readv_report)。 */
const PgAioHandleCallbacks aio_md_readv_cb = {
	.complete_shared = md_readv_complete,
	.report = md_readv_report,
};


/*
 * _mdfd_open_flags (中文)返回 md 打开文件使用的标准 open 标志
 *
 * 【作用】md 管理的文件一律以"读写 + 二进制"(O_RDWR | PG_BINARY)打开;
 * 若启用了数据直接 I/O(io_direct_flags 含 IO_DIRECT_DATA),再附加
 * PG_O_DIRECT。集中定义,避免各调用点重复书写或彼此不一致。
 *
 * 【参数】无。
 * 【返回值】int 型 open 标志位。
 */
static inline int
_mdfd_open_flags(void)
{
	int			flags = O_RDWR | PG_BINARY;

	if (io_direct_flags & IO_DIRECT_DATA)
		flags |= PG_O_DIRECT;

	return flags;
}

/*
 * mdinit (中文)初始化磁介质存储管理器的进程本地状态
 *
 * 【作用】由 smgrinit()(经 smgrsw[0].smgr_init)在每次后端启动时调用,
 * 创建 MdCxt 内存上下文——之后所有 MdfdVec 段描述数组都在此分配。
 * 除内存上下文外,md 没有其他进程内共享状态。
 *
 * 【参数】无。
 * 【返回值】无。
 *
 * mdinit() -- Initialize private state for magnetic disk storage manager.
 */
void
mdinit(void)
{
	MdCxt = AllocSetContextCreate(TopMemoryContext,
								  "MdSmgr",
								  ALLOCSET_DEFAULT_SIZES);
}

/*
 * mdexists (中文)判断某个 fork 的物理文件是否存在
 *
 * 【作用】分两步:先 mdclose() 关闭该 fork 已打开的文件(恢复期间跳过
 * ——恢复里删除关系时本来就会关闭),确保能"看到"文件已被删除的事实;
 * 再用 mdopenfork(EXTENSION_RETURN_NULL) 尝试打开首段,能打开即有
 * 文件。注意:对"已标记删除、还没真正删掉"的残留文件,本函数返回
 * true。
 *
 * 【参数】
 *   reln —— 目标关系;forknum —— fork 编号。
 * 【返回值】首段文件存在返回 true。
 *
 * mdexists() -- Does the physical file exist?
 *
 * Note: this will return true for lingering files, with pending deletions
 */
bool
mdexists(SMgrRelation reln, ForkNumber forknum)
{
	/*
	 * Close it first, to ensure that we notice if the fork has been unlinked
	 * since we opened it.  As an optimization, we can skip that in recovery,
	 * which already closes relations when dropping them.
	 */
	if (!InRecovery)
		mdclose(reln, forknum);

	return (mdopenfork(reln, forknum, EXTENSION_RETURN_NULL) != NULL);
}

/*
 * mdcreate (中文)在磁盘上创建一个新关系的物理文件(指定 fork)
 *
 * 【作用】用 O_CREAT|O_EXCL 原子创建(保证不覆盖已存在文件;重放时若
 * 文件已存在,退回普通打开方式——isRedo 下"已存在"是正常现象)。首次
 * 使用某个表空间/数据库时,顺带创建其 per-database 子目录
 * (TablespaceCreateDbspace,一个有意为之的层次越界,见注释)。创建成功
 * 后:登记首段 MdfdVec;若非临时关系,register_dirty_segment() 把新
 * 文件登记给检查点 fsync。
 *
 * 【设计思想】O_EXCL 是这里的"并发互斥":两个后端不可能同时创建成功
 * 同一个文件,把"文件锁"的职责交给内核原子性,md 自己无需加锁。
 *
 * 【参数】
 *   reln —— 目标关系;forknum —— 要创建的 fork;
 *   isRedo —— 是否处于重放(重放时允许文件已存在)。
 * 【返回值】无(失败报 ERROR)。
 *
 * mdcreate() -- Create a new relation on magnetic disk.
 *
 * If isRedo is true, it's okay for the relation to exist already.
 */
void
mdcreate(SMgrRelation reln, ForkNumber forknum, bool isRedo)
{
	MdfdVec    *mdfd;
	RelPathStr	path;
	File		fd;

	if (isRedo && reln->md_num_open_segs[forknum] > 0)
		return;					/* created and opened already... */

	Assert(reln->md_num_open_segs[forknum] == 0);

	/*
	 * We may be using the target table space for the first time in this
	 * database, so create a per-database subdirectory if needed.
	 *
	 * XXX this is a fairly ugly violation of module layering, but this seems
	 * to be the best place to put the check.  Maybe TablespaceCreateDbspace
	 * should be here and not in commands/tablespace.c?  But that would imply
	 * importing a lot of stuff that smgr.c oughtn't know, either.
	 */
	TablespaceCreateDbspace(reln->smgr_rlocator.locator.spcOid,
							reln->smgr_rlocator.locator.dbOid,
							isRedo);

	path = relpath(reln->smgr_rlocator, forknum);

	fd = PathNameOpenFile(path.str, _mdfd_open_flags() | O_CREAT | O_EXCL);

	if (fd < 0)
	{
		int			save_errno = errno;

		if (isRedo)
			fd = PathNameOpenFile(path.str, _mdfd_open_flags());
		if (fd < 0)
		{
			/* be sure to report the error reported by create, not open */
			errno = save_errno;
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not create file \"%s\": %m", path.str)));
		}
	}

	_fdvec_resize(reln, forknum, 1);
	mdfd = &reln->md_seg_fds[forknum][0];
	mdfd->mdfd_vfd = fd;
	mdfd->mdfd_segno = 0;

	if (!SmgrIsTemp(reln))
		register_dirty_segment(reln, forknum, mdfd);
}

/*
 * mdunlink (中文)删除一个关系的物理文件(可按 fork 或全部)
 *
 * 【作用】真正删除关系的入口(经 smgrsw 由 smgrdounlinkall 调用)。
 * 参数 forknum 为具体编号则只删该 fork;为 InvalidForkNumber 则删除
 * 全部 fork。具体工作委托给 mdunlinkfork(),要点见那里。
 *
 * 【背景】本函数运行时通常已不在事务中(提交/回滚后的清理),因此任何
 * 失败都只能 WARNING 不能 ERROR。
 *
 * 【参数】
 *   rlocator —— 关系定位(注意:调用时 SMgrRelation 哈希表条目可能
 *               已不存在,故只传 locator);
 *   forknum  —— 要删除的 fork,或 InvalidForkNumber(全部);
 *   isRedo   —— 重放模式:文件已消失不足为奇,且应立刻删、不能延迟。
 * 【返回值】无。
 *
 * mdunlink() -- Unlink a relation.
 *
 * Note that we're passed a RelFileLocatorBackend --- by the time this is called,
 * there won't be an SMgrRelation hashtable entry anymore.
 *
 * forknum can be a fork number to delete a specific fork, or InvalidForkNumber
 * to delete all forks.
 *
 * For regular relations, we don't unlink the first segment file of the rel,
 * but just truncate it to zero length, and record a request to unlink it after
 * the next checkpoint.  Additional segments can be unlinked immediately,
 * however.  Leaving the empty file in place prevents that relfilenumber
 * from being reused.  The scenario this protects us from is:
 * 1. We delete a relation (and commit, and actually remove its file).
 * 2. We create a new relation, which by chance gets the same relfilenumber as
 *	  the just-deleted one (OIDs must've wrapped around for that to happen).
 * 3. We crash before another checkpoint occurs.
 * During replay, we would delete the file and then recreate it, which is fine
 * if the contents of the file were repopulated by subsequent WAL entries.
 * But if we didn't WAL-log insertions, but instead relied on fsyncing the
 * file after populating it (as we do at wal_level=minimal), the contents of
 * the file would be lost forever.  By leaving the empty file until after the
 * next checkpoint, we prevent reassignment of the relfilenumber until it's
 * safe, because relfilenumber assignment skips over any existing file.
 *
 * Additional segments, if any, are truncated and then unlinked.  The reason
 * for truncating is that other backends may still hold open FDs for these at
 * the smgr level, so that the kernel can't remove the file yet.  We want to
 * reclaim the disk space right away despite that.
 *
 * We do not need to go through this dance for temp relations, though, because
 * we never make WAL entries for temp rels, and so a temp rel poses no threat
 * to the health of a regular rel that has taken over its relfilenumber.
 * The fact that temp rels and regular rels have different file naming
 * patterns provides additional safety.  Other backends shouldn't have open
 * FDs for them, either.
 *
 * We also don't do it while performing a binary upgrade.  There is no reuse
 * hazard in that case, since after a crash or even a simple ERROR, the
 * upgrade fails and the whole cluster must be recreated from scratch.
 * Furthermore, it is important to remove the files from disk immediately,
 * because we may be about to reuse the same relfilenumber.
 *
 * All the above applies only to the relation's main fork; other forks can
 * just be removed immediately, since they are not needed to prevent the
 * relfilenumber from being recycled.  Also, we do not carefully
 * track whether other forks have been created or not, but just attempt to
 * unlink them unconditionally; so we should never complain about ENOENT.
 *
 * If isRedo is true, it's unsurprising for the relation to be already gone.
 * Also, we should remove the file immediately instead of queuing a request
 * for later, since during redo there's no possibility of creating a
 * conflicting relation.
 *
 * Note: we currently just never warn about ENOENT at all.  We could warn in
 * the main-fork, non-isRedo case, but it doesn't seem worth the trouble.
 *
 * Note: any failure should be reported as WARNING not ERROR, because
 * we are usually not in a transaction anymore when this is called.
 */
void
mdunlink(RelFileLocatorBackend rlocator, ForkNumber forknum, bool isRedo)
{
	/* Now do the per-fork work */
	if (forknum == InvalidForkNumber)
	{
		for (forknum = 0; forknum <= MAX_FORKNUM; forknum++)
			mdunlinkfork(rlocator, forknum, isRedo);
	}
	else
		mdunlinkfork(rlocator, forknum, isRedo);
}

/*
 * do_truncate (中文)把文件截断为 0 字节(尽力而为,失败仅告警)
 *
 * 【作用】mdunlinkfork 里用来"先截断、后删除"文件:截断为 0 后,其他
 * 后端仍握着的打开描述符将不再占用磁盘空间,从而立即回收空间。
 * ENOENT(文件本就不存在)不算错误;其余失败打 WARNING 后返回错误码,
 * 并保留 errno 供调用方判断。
 *
 * 【参数】path —— 文件路径。
 * 【返回值】0 成功;-1 失败(错误原因在 errno,且已打告警)。
 *
 * Truncate a file to release disk space.
 */
static int
do_truncate(const char *path)
{
	int			save_errno;
	int			ret;

	ret = pg_truncate(path, 0);

	/* Log a warning here to avoid repetition in callers. */
	if (ret < 0 && errno != ENOENT)
	{
		save_errno = errno;
		ereport(WARNING,
				(errcode_for_file_access(),
				 errmsg("could not truncate file \"%s\": %m", path)));
		errno = save_errno;
	}

	return ret;
}

/*
 * mdunlinkfork (中文)删除一个关系 fork 的全部物理文件
 *
 * 【作用】按 mdunlink() 注释中的策略执行:对主 fork 且"非重放 / 非
 * 二进制升级 / 非临时关系",只把首段截断为 0 并登记"下个检查点后
 * 删除"(register_unlink_tombstone)——留下一个空文件占住
 * relfilenumber,防止该编号在下次检查点前被复用(详见 mdunlink 的英文
 * 注释:避免崩溃后内容丢失);其余情况(重放、二进制升级、临时关系、
 * 非主 fork)直接"截断 + 立即 unlink"。无论哪种情况,删除前都先
 * register_forget_request() 撤销该文件尚未执行的同步请求。之后从段 1
 * 起循环删除所有附加段(含非活动段):每段同样"先截断释放空间,再
 * unlink",遇到 ENOENT 即停(预期中的"最后一个段之后")。
 *
 * 【设计思想】"截断再删"与"留空文件"的组合,精确解决了三个问题:
 * 别的后端持有的 fd 占住磁盘空间、relfilenumber 的复用安全、崩溃恢复
 * 时的文件一致性。
 *
 * 【参数】
 *   rlocator —— 关系定位;forknum —— fork;
 *   isRedo   —— 见 mdunlink()。
 * 【返回值】无(失败打 WARNING 后继续)。
 */
static void
mdunlinkfork(RelFileLocatorBackend rlocator, ForkNumber forknum, bool isRedo)
{
	RelPathStr	path;
	int			ret;
	int			save_errno;

	path = relpath(rlocator, forknum);

	/*
	 * Truncate and then unlink the first segment, or just register a request
	 * to unlink it later, as described in the comments for mdunlink().
	 */
	if (isRedo || IsBinaryUpgrade || forknum != MAIN_FORKNUM ||
		RelFileLocatorBackendIsTemp(rlocator))
	{
		if (!RelFileLocatorBackendIsTemp(rlocator))
		{
			/* Prevent other backends' fds from holding on to the disk space */
			ret = do_truncate(path.str);

			/* Forget any pending sync requests for the first segment */
			save_errno = errno;
			register_forget_request(rlocator, forknum, 0 /* first seg */ );
			errno = save_errno;
		}
		else
			ret = 0;

		/* Next unlink the file, unless it was already found to be missing */
		if (ret >= 0 || errno != ENOENT)
		{
			ret = unlink(path.str);
			if (ret < 0 && errno != ENOENT)
			{
				save_errno = errno;
				ereport(WARNING,
						(errcode_for_file_access(),
						 errmsg("could not remove file \"%s\": %m", path.str)));
				errno = save_errno;
			}
		}
	}
	else
	{
		/* Prevent other backends' fds from holding on to the disk space */
		ret = do_truncate(path.str);

		/* Register request to unlink first segment later */
		save_errno = errno;
		register_unlink_tombstone(rlocator);
		errno = save_errno;
	}

	/*
	 * Delete any additional segments.
	 *
	 * Note that because we loop until getting ENOENT, we will correctly
	 * remove all inactive segments as well as active ones.  Ideally we'd
	 * continue the loop until getting exactly that errno, but that risks an
	 * infinite loop if the problem is directory-wide (for instance, if we
	 * suddenly can't read the data directory itself).  We compromise by
	 * continuing after a non-ENOENT truncate error, but stopping after any
	 * unlink error.  If there is indeed a directory-wide problem, additional
	 * unlink attempts wouldn't work anyway.
	 */
	if (ret >= 0 || errno != ENOENT)
	{
		MdPathStr	segpath;
		BlockNumber segno;

		for (segno = 1;; segno++)
		{
			sprintf(segpath.str, "%s.%u", path.str, segno);

			if (!RelFileLocatorBackendIsTemp(rlocator))
			{
				/*
				 * Prevent other backends' fds from holding on to the disk
				 * space.  We're done if we see ENOENT, though.
				 */
				if (do_truncate(segpath.str) < 0 && errno == ENOENT)
					break;

				/*
				 * Forget any pending sync requests for this segment before we
				 * try to unlink.
				 */
				register_forget_request(rlocator, forknum, segno);
			}

			if (unlink(segpath.str) < 0)
			{
				/* ENOENT is expected after the last segment... */
				if (errno != ENOENT)
					ereport(WARNING,
							(errcode_for_file_access(),
							 errmsg("could not remove file \"%s\": %m", segpath.str)));
				break;
			}
		}
	}
}

/*
 * mdextend (中文)向关系文件末尾追加一个数据块
 *
 * 【作用】把 buffer 的一页(BLCKSZ 字节)写到 blocknum 处(blocknum 应
 * >= 当前 EOF,即"扩展")。细节:
 * - 块号 2^32-1(InvalidBlockNumber)是非法扩展目标,直接报错(上游
 *   bufmgr 本应有检查,这里只是兜底);
 * - _mdfd_getseg(EXTENSION_CREATE) 定位/创建块所在段;
 * - 段内偏移 = BLCKSZ * (blocknum % RELSEG_SIZE),用 FileWrite 写;
 * - 写满整块后,若非 skipFsync 且非临时关系,登记段为"待检查点 fsync"
 *   (register_dirty_segment)。
 *
 * 【设计思想】写越过 EOF 时,操作系统会以零填充中间空洞——本函数依赖
 * 这一点保证"中间空间读出为 0"的扩展语义。
 *
 * 【参数】
 *   reln, forknum, blocknum —— 目标关系、fork 与新块块号;
 *   buffer —— 待写页;skipFsync —— 跳过检查点登记。
 * 【返回值】无(失败报 ERROR,如磁盘满)。
 *
 * mdextend() -- Add a block to the specified relation.
 *
 * The semantics are nearly the same as mdwrite(): write at the
 * specified position.  However, this is to be used for the case of
 * extending a relation (i.e., blocknum is at or beyond the current
 * EOF).  Note that we assume writing a block beyond current EOF
 * causes intervening file space to become filled with zeroes.
 */
void
mdextend(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		 const void *buffer, bool skipFsync)
{
	pgoff_t		seekpos;
	ssize_t		nbytes;
	MdfdVec    *v;

	/* If this build supports direct I/O, the buffer must be I/O aligned. */
	if (PG_O_DIRECT != 0 && PG_IO_ALIGN_SIZE <= BLCKSZ)
		Assert((uintptr_t) buffer == TYPEALIGN(PG_IO_ALIGN_SIZE, buffer));

	/* This assert is too expensive to have on normally ... */
#ifdef CHECK_WRITE_VS_EXTEND
	Assert(blocknum >= mdnblocks(reln, forknum));
#endif

	/*
	 * If a relation manages to grow to 2^32-1 blocks, refuse to extend it any
	 * more --- we mustn't create a block whose number actually is
	 * InvalidBlockNumber.  (Note that this failure should be unreachable
	 * because of upstream checks in bufmgr.c.)
	 */
	if (blocknum == InvalidBlockNumber)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("cannot extend file \"%s\" beyond %u blocks",
						relpath(reln->smgr_rlocator, forknum).str,
						InvalidBlockNumber)));

	v = _mdfd_getseg(reln, forknum, blocknum, skipFsync, EXTENSION_CREATE);

	seekpos = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

	Assert(seekpos < (pgoff_t) BLCKSZ * RELSEG_SIZE);

	if ((nbytes = FileWrite(v->mdfd_vfd, buffer, BLCKSZ, seekpos, WAIT_EVENT_DATA_FILE_EXTEND)) != BLCKSZ)
	{
		if (nbytes < 0)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not extend file \"%s\": %m",
							FilePathName(v->mdfd_vfd)),
					 errhint("Check free disk space.")));
		/* short write: complain appropriately */
		ereport(ERROR,
				(errcode(ERRCODE_DISK_FULL),
				 errmsg("could not extend file \"%s\": wrote only %zd of %zu bytes at block %u",
						FilePathName(v->mdfd_vfd),
						nbytes, (size_t) BLCKSZ, blocknum),
				 errhint("Check free disk space.")));
	}

	if (!skipFsync && !SmgrIsTemp(reln))
		register_dirty_segment(reln, forknum, v);

	Assert(_mdnblocks(reln, forknum, v) <= ((BlockNumber) RELSEG_SIZE));
}

/*
 * mdzeroextend (中文)一次向关系文件追加 nblocks 个清零块
 *
 * 【作用】mdextend() 的多块版,循环按段切块处理:每段内计算本次可扩展
 * 的块数(不越过段边界);若块数 > 8 且配置允许,用 FileFallocate()
 * (posix_fallocate)扩展——通常比逐块 write 高效得多,且不会为扩展
 * 部分占用内核页缓存;否则用 FileZero()(基于 pg_pwritev 的整段写零)
 * 一次写出,避免逐块系统调用。每次扩展后登记"待检查点 fsync"(非
 * skipFsync 且非临时时)。
 *
 * 【设计思想】把"分配大段零页"从"逐块 write"里解放出来,是批量加载
 * 与预热路径提速的关键;小于等于 8 块的扩展仍走写零路径,因为过小的
 * fallocate 会干扰某些文件系统的延迟分配(延迟分配对空间利用率有利)。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块号;nblocks —— 扩展块数(> 0);
 *   skipFsync —— 见 mdextend()。
 * 【返回值】无。
 *
 * mdzeroextend() -- Add new zeroed out blocks to the specified relation.
 *
 * Similar to mdextend(), except the relation can be extended by multiple
 * blocks at once and the added blocks will be filled with zeroes.
 */
void
mdzeroextend(SMgrRelation reln, ForkNumber forknum,
			 BlockNumber blocknum, int nblocks, bool skipFsync)
{
	MdfdVec    *v;
	BlockNumber curblocknum = blocknum;
	int			remblocks = nblocks;

	Assert(nblocks > 0);

	/* This assert is too expensive to have on normally ... */
#ifdef CHECK_WRITE_VS_EXTEND
	Assert(blocknum >= mdnblocks(reln, forknum));
#endif

	/*
	 * If a relation manages to grow to 2^32-1 blocks, refuse to extend it any
	 * more --- we mustn't create a block whose number actually is
	 * InvalidBlockNumber or larger.
	 */
	if ((uint64) blocknum + nblocks >= (uint64) InvalidBlockNumber)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("cannot extend file \"%s\" beyond %u blocks",
						relpath(reln->smgr_rlocator, forknum).str,
						InvalidBlockNumber)));

	while (remblocks > 0)
	{
		BlockNumber segstartblock = curblocknum % ((BlockNumber) RELSEG_SIZE);
		pgoff_t		seekpos = (pgoff_t) BLCKSZ * segstartblock;
		int			numblocks;

		if (segstartblock + remblocks > RELSEG_SIZE)
			numblocks = RELSEG_SIZE - segstartblock;
		else
			numblocks = remblocks;

		v = _mdfd_getseg(reln, forknum, curblocknum, skipFsync, EXTENSION_CREATE);

		Assert(segstartblock < RELSEG_SIZE);
		Assert(segstartblock + numblocks <= RELSEG_SIZE);

		/*
		 * If available and useful, use posix_fallocate() (via
		 * FileFallocate()) to extend the relation. That's often more
		 * efficient than using write(), as it commonly won't cause the kernel
		 * to allocate page cache space for the extended pages.
		 *
		 * However, we don't use FileFallocate() for small extensions, as it
		 * defeats delayed allocation on some filesystems. Not clear where
		 * that decision should be made though? For now just use a cutoff of
		 * 8, anything between 4 and 8 worked OK in some local testing.
		 */
		if (numblocks > 8 &&
			file_extend_method != FILE_EXTEND_METHOD_WRITE_ZEROS)
		{
			int			ret = 0;

#ifdef HAVE_POSIX_FALLOCATE
			if (file_extend_method == FILE_EXTEND_METHOD_POSIX_FALLOCATE)
			{
				ret = FileFallocate(v->mdfd_vfd,
									seekpos, (pgoff_t) BLCKSZ * numblocks,
									WAIT_EVENT_DATA_FILE_EXTEND);
			}
			else
#endif
			{
				elog(ERROR, "unsupported file_extend_method: %d",
					 file_extend_method);
			}
			if (ret != 0)
			{
				ereport(ERROR,
						errcode_for_file_access(),
						errmsg("could not extend file \"%s\" with FileFallocate(): %m",
							   FilePathName(v->mdfd_vfd)),
						errhint("Check free disk space."));
			}
		}
		else
		{
			int			ret;

			/*
			 * Even if we don't want to use fallocate, we can still extend a
			 * bit more efficiently than writing each 8kB block individually.
			 * pg_pwrite_zeros() (via FileZero()) uses pg_pwritev_with_retry()
			 * to avoid multiple writes or needing a zeroed buffer for the
			 * whole length of the extension.
			 */
			ret = FileZero(v->mdfd_vfd,
						   seekpos, (pgoff_t) BLCKSZ * numblocks,
						   WAIT_EVENT_DATA_FILE_EXTEND);
			if (ret < 0)
				ereport(ERROR,
						errcode_for_file_access(),
						errmsg("could not extend file \"%s\": %m",
							   FilePathName(v->mdfd_vfd)),
						errhint("Check free disk space."));
		}

		if (!skipFsync && !SmgrIsTemp(reln))
			register_dirty_segment(reln, forknum, v);

		Assert(_mdnblocks(reln, forknum, v) <= ((BlockNumber) RELSEG_SIZE));

		remblocks -= numblocks;
		curblocknum += numblocks;
	}
}

/*
 * mdopenfork (中文)打开一个关系的指定 fork(只打开首段)
 *
 * 【作用】为 fork 打开首段文件(注意:多段关系也只在首次访问时打开
 * 首段,其余段由 _mdfd_getseg 惰性打开),并把首段登记进
 * md_seg_fds[forknum][0]。若首段缺失:按 behavior 决定是报错
 * (EXTENSION_FAIL/EXTENSION_CREATE)还是返回 NULL(EXTENSION_RETURN_NULL,
 * 且错误码属于"文件可能被删"时才返回 NULL)。已打开时直接返回现有
 * 首段,不做任何事。
 *
 * 【参数】
 *   reln —— 目标关系;forknum —— fork;
 *   behavior —— EXTENSION_* 位组合(见宏定义处)。
 * 【返回值】首段的 MdfdVec 指针;或 NULL(仅当 behavior 允许)。
 *
 * mdopenfork() -- Open one fork of the specified relation.
 *
 * Note we only open the first segment, when there are multiple segments.
 *
 * If first segment is not present, either ereport or return NULL according
 * to "behavior".  We treat EXTENSION_CREATE the same as EXTENSION_FAIL;
 * EXTENSION_CREATE means it's OK to extend an existing relation, not to
 * invent one out of whole cloth.
 */
static MdfdVec *
mdopenfork(SMgrRelation reln, ForkNumber forknum, int behavior)
{
	MdfdVec    *mdfd;
	RelPathStr	path;
	File		fd;

	/* No work if already open */
	if (reln->md_num_open_segs[forknum] > 0)
		return &reln->md_seg_fds[forknum][0];

	path = relpath(reln->smgr_rlocator, forknum);

	fd = PathNameOpenFile(path.str, _mdfd_open_flags());

	if (fd < 0)
	{
		if ((behavior & EXTENSION_RETURN_NULL) &&
			FILE_POSSIBLY_DELETED(errno))
			return NULL;
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not open file \"%s\": %m", path.str)));
	}

	_fdvec_resize(reln, forknum, 1);
	mdfd = &reln->md_seg_fds[forknum][0];
	mdfd->mdfd_vfd = fd;
	mdfd->mdfd_segno = 0;

	Assert(_mdnblocks(reln, forknum, mdfd) <= ((BlockNumber) RELSEG_SIZE));

	return mdfd;
}

/*
 * mdopen (中文)初始化"新打开"的关系(所有 fork 标记为未打开)
 *
 * 【作用】smgr_open 的 md 实现:把各 fork 的 md_num_open_segs 清零,
 * 表示"尚未打开任何段"。真正的文件打开推迟到首次访问(惰性打开)。
 *
 * 【参数】reln —— 目标关系。
 * 【返回值】无。
 *
 * mdopen() -- Initialize newly-opened relation.
 */
void
mdopen(SMgrRelation reln)
{
	/* mark it not open */
	for (int forknum = 0; forknum <= MAX_FORKNUM; forknum++)
		reln->md_num_open_segs[forknum] = 0;
}

/*
 * mdclose (中文)关闭指定 fork 已打开的全部段文件
 *
 * 【作用】从数组末尾向前逐个 FileClose() 并收缩数组(_fdvec_resize),
 * 直至全部关闭。从后往前关闭使数组收缩始终发生在"尾部",与数组增长
 * 方向一致,内存管理最省事。已关闭时直接返回。
 *
 * 【参数】
 *   reln —— 目标关系;forknum —— fork。
 * 【返回值】无。
 *
 * mdclose() -- Close the specified relation, if it isn't closed already.
 */
void
mdclose(SMgrRelation reln, ForkNumber forknum)
{
	int			nopensegs = reln->md_num_open_segs[forknum];

	/* No work if already closed */
	if (nopensegs == 0)
		return;

	/* close segments starting from the end */
	while (nopensegs > 0)
	{
		MdfdVec    *v = &reln->md_seg_fds[forknum][nopensegs - 1];

		FileClose(v->mdfd_vfd);
		_fdvec_resize(reln, forknum, nopensegs - 1);
		nopensegs--;
	}
}

/*
 * mdprefetch (中文)对指定块区间发起预读(异步,尽力而为)
 *
 * 【作用】对 [blocknum, blocknum+nblocks) 逐段调用 FilePrefetch(),让
 * 内核提前把数据载入页缓存,后续正式读页时命中。仅当构建支持
 * (USE_PREFETCH)时有效,否则直接返回 true。直接 I/O 模式下断言不可用。
 *
 * 【返回值语义】范围超出 MaxBlockNumber+1 时返回 false;恢复期间目标
 * 段可能已被删除(EXTENSION_RETURN_NULL 返回 NULL)也返回 false——
 * 调用方应把 false 理解为"预读无意义/不可能",而非错误。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块;nblocks —— 块数。
 * 【返回值】是否成功发起(范围合法且文件存在)。
 *
 * mdprefetch() -- Initiate asynchronous read of the specified blocks of a relation
 */
bool
mdprefetch(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		   int nblocks)
{
#ifdef USE_PREFETCH

	Assert((io_direct_flags & IO_DIRECT_DATA) == 0);

	if ((uint64) blocknum + nblocks > (uint64) MaxBlockNumber + 1)
		return false;

	while (nblocks > 0)
	{
		pgoff_t		seekpos;
		MdfdVec    *v;
		int			nblocks_this_segment;

		v = _mdfd_getseg(reln, forknum, blocknum, false,
						 InRecovery ? EXTENSION_RETURN_NULL : EXTENSION_FAIL);
		if (v == NULL)
			return false;

		seekpos = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

		Assert(seekpos < (pgoff_t) BLCKSZ * RELSEG_SIZE);

		nblocks_this_segment =
			Min(nblocks,
				RELSEG_SIZE - (blocknum % ((BlockNumber) RELSEG_SIZE)));

		(void) FilePrefetch(v->mdfd_vfd, seekpos, BLCKSZ * nblocks_this_segment,
							WAIT_EVENT_DATA_FILE_PREFETCH);

		blocknum += nblocks_this_segment;
		nblocks -= nblocks_this_segment;
	}
#endif							/* USE_PREFETCH */

	return true;
}

/*
 * buffers_to_iovec (中文)把缓冲地址数组折叠成 iovec 数组
 *
 * 【作用】mdreadv/mdwritev 的前置处理:检查 nblocks 个缓冲在内存中
 * 是否彼此连续,把相邻的合并成同一个 iovec 项(整块连续时 iovcnt==1,
 * 内核可直接当作一次普通非向量 IO 处理),返回实际使用的 iovec 数。
 * 同时为直接 I/O 构建做对齐断言。
 *
 * 【参数】
 *   iov     —— 输出数组,必须能容纳至多 nblocks 项;
 *   buffers —— 输入缓冲指针数组(每项 BLCKSZ 字节);
 *   nblocks —— 块数(>= 1)。
 * 【返回值】生成的 iovec 项数(1 ~ nblocks)。
 *
 * Convert an array of buffer address into an array of iovec objects, and
 * return the number that were required.  'iov' must have enough space for up
 * to 'nblocks' elements, but the number used may be less depending on
 * merging.  In the case of a run of fully contiguous buffers, a single iovec
 * will be populated that can be handled as a plain non-vectored I/O.
 */
static int
buffers_to_iovec(struct iovec *iov, void **buffers, int nblocks)
{
	struct iovec *iovp;
	int			iovcnt;

	Assert(nblocks >= 1);

	/* If this build supports direct I/O, buffers must be I/O aligned. */
	for (int i = 0; i < nblocks; ++i)
	{
		if (PG_O_DIRECT != 0 && PG_IO_ALIGN_SIZE <= BLCKSZ)
			Assert((uintptr_t) buffers[i] ==
				   TYPEALIGN(PG_IO_ALIGN_SIZE, buffers[i]));
	}

	/* Start the first iovec off with the first buffer. */
	iovp = &iov[0];
	iovp->iov_base = buffers[0];
	iovp->iov_len = BLCKSZ;
	iovcnt = 1;

	/* Try to merge the rest. */
	for (int i = 1; i < nblocks; ++i)
	{
		void	   *buffer = buffers[i];

		if (((char *) iovp->iov_base + iovp->iov_len) == buffer)
		{
			/* Contiguous with the last iovec. */
			iovp->iov_len += BLCKSZ;
		}
		else
		{
			/* Need a new iovec. */
			iovp++;
			iovp->iov_base = buffer;
			iovp->iov_len = BLCKSZ;
			iovcnt++;
		}
	}

	return iovcnt;
}

/*
 * mdmaxcombine (中文)返回从 blocknum 起最多能合并进一次 IO 的块数
 *
 * 【作用】md 的合并上限只受段边界限制:一次 IO 不能跨段(段是独立
 * 文件)。因此返回"到本段末尾还有多少块"
 * = RELSEG_SIZE - (blocknum % RELSEG_SIZE),含 blocknum 本身。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork(此处未实际使用);
 *   blocknum —— 起始块号。
 * 【返回值】可合并块数。
 *
 * mdmaxcombine() -- Return the maximum number of total blocks that can be
 *				 combined with an IO starting at blocknum.
 */
uint32
mdmaxcombine(SMgrRelation reln, ForkNumber forknum,
			 BlockNumber blocknum)
{
	BlockNumber segoff;

	segoff = blocknum % ((BlockNumber) RELSEG_SIZE);

	return RELSEG_SIZE - segoff;
}

/*
 * mdreadv (中文)从关系同步读取连续块到给定缓冲
 *
 * 【作用】把 [blocknum, blocknum+nblocks) 读入 buffers 数组。按段切分
 * 循环处理(单次读不跨越段边界);每段内先 buffers_to_iovec 合并连续
 * 内存,再用 FileReadV 读取;内部循环处理短读(继续读到 EOF,而非假定
 * "短读即文件尾")。命中 EOF 或读到不完整的末块:
 * - 若 zero_damaged_pages 或 InRecovery:把不足部分清零后继续(注意
 *   断言 Assert(false):作者认为该路径在恢复下本不可达、计划移除,
 *   详见英文注释);
 * - 否则报 ERRCODE_DATA_CORRUPTED。
 *
 * 【设计思想】"以块为单位的接口,字节细节藏在实现里":上层永远看到
 * 整块语义;短读在 md 层循环补齐,尽量不让调用方感知。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块;buffers —— 输出缓冲数组;nblocks —— 块数。
 * 【返回值】无(失败报 ERROR)。
 *
 * mdreadv() -- Read the specified blocks from a relation.
 */
void
mdreadv(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		void **buffers, BlockNumber nblocks)
{
	while (nblocks > 0)
	{
		struct iovec iov[PG_IOV_MAX];
		int			iovcnt;
		pgoff_t		seekpos;
		ssize_t		nbytes;
		MdfdVec    *v;
		BlockNumber nblocks_this_segment;
		size_t		transferred_this_segment;
		size_t		size_this_segment;

		v = _mdfd_getseg(reln, forknum, blocknum, false,
						 EXTENSION_FAIL | EXTENSION_CREATE_RECOVERY);

		seekpos = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

		Assert(seekpos < (pgoff_t) BLCKSZ * RELSEG_SIZE);

		nblocks_this_segment =
			Min(nblocks,
				RELSEG_SIZE - (blocknum % ((BlockNumber) RELSEG_SIZE)));
		nblocks_this_segment = Min(nblocks_this_segment, lengthof(iov));

		if (nblocks_this_segment != nblocks)
			elog(ERROR, "read crosses segment boundary");

		iovcnt = buffers_to_iovec(iov, buffers, nblocks_this_segment);
		size_this_segment = nblocks_this_segment * BLCKSZ;
		transferred_this_segment = 0;

		/*
		 * Inner loop to continue after a short read.  We'll keep going until
		 * we hit EOF rather than assuming that a short read means we hit the
		 * end.
		 */
		for (;;)
		{
			TRACE_POSTGRESQL_SMGR_MD_READ_START(forknum, blocknum,
												reln->smgr_rlocator.locator.spcOid,
												reln->smgr_rlocator.locator.dbOid,
												reln->smgr_rlocator.locator.relNumber,
												reln->smgr_rlocator.backend);
			nbytes = FileReadV(v->mdfd_vfd, iov, iovcnt, seekpos,
							   WAIT_EVENT_DATA_FILE_READ);
			TRACE_POSTGRESQL_SMGR_MD_READ_DONE(forknum, blocknum,
											   reln->smgr_rlocator.locator.spcOid,
											   reln->smgr_rlocator.locator.dbOid,
											   reln->smgr_rlocator.locator.relNumber,
											   reln->smgr_rlocator.backend,
											   nbytes,
											   size_this_segment - transferred_this_segment);

#ifdef SIMULATE_SHORT_READ
			nbytes = Min(nbytes, 4096);
#endif

			if (nbytes < 0)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not read blocks %u..%u in file \"%s\": %m",
								blocknum,
								blocknum + nblocks_this_segment - 1,
								FilePathName(v->mdfd_vfd))));

			if (nbytes == 0)
			{
				/*
				 * We are at or past EOF, or we read a partial block at EOF.
				 * Normally this is an error; upper levels should never try to
				 * read a nonexistent block.  However, if zero_damaged_pages
				 * is ON or we are InRecovery, we should instead return zeroes
				 * without complaining.  This allows, for example, the case of
				 * trying to update a block that was later truncated away.
				 *
				 * NB: We think that this codepath is unreachable in recovery
				 * and incomplete with zero_damaged_pages, as missing segments
				 * are not created. Putting blocks into the buffer-pool that
				 * do not exist on disk is rather problematic, as it will not
				 * be found by scans that rely on smgrnblocks(), as they are
				 * beyond EOF. It also can cause weird problems with relation
				 * extension, as relation extension does not expect blocks
				 * beyond EOF to exist.
				 *
				 * Therefore we do not want to copy the logic into
				 * mdstartreadv(), where it would have to be more complicated
				 * due to potential differences in the zero_damaged_pages
				 * setting between the definer and completor of IO.
				 *
				 * For PG 18, we are putting an Assert(false) in mdreadv()
				 * (triggering failures in assertion-enabled builds, but
				 * continuing to work in production builds). Afterwards we
				 * plan to remove this code entirely.
				 */
				if (zero_damaged_pages || InRecovery)
				{
					Assert(false);	/* see comment above */

					for (BlockNumber i = transferred_this_segment / BLCKSZ;
						 i < nblocks_this_segment;
						 ++i)
						memset(buffers[i], 0, BLCKSZ);
					break;
				}
				else
					ereport(ERROR,
							(errcode(ERRCODE_DATA_CORRUPTED),
							 errmsg("could not read blocks %u..%u in file \"%s\": read only %zu of %zu bytes",
									blocknum,
									blocknum + nblocks_this_segment - 1,
									FilePathName(v->mdfd_vfd),
									transferred_this_segment,
									size_this_segment)));
			}

			/* One loop should usually be enough. */
			transferred_this_segment += nbytes;
			Assert(transferred_this_segment <= size_this_segment);
			if (transferred_this_segment == size_this_segment)
				break;

			/* Adjust position and vectors after a short read. */
			seekpos += nbytes;
			iovcnt = compute_remaining_iovec(iov, iov, iovcnt, nbytes);
		}

		nblocks -= nblocks_this_segment;
		buffers += nblocks_this_segment;
		blocknum += nblocks_this_segment;
	}
}

/*
 * mdstartreadv (中文)mdreadv() 的异步版本(配合 AIO 框架)
 *
 * 【作用】发起异步读:定位段(段必须存在,与 mdreadv 相同的 behavior),
 * 折叠 iovec,把 IO 目标设为 smgr(pgaio_io_set_target_smgr,便于 IO 在
 * 其他进程执行时重开文件),注册 md_readv_cb 回调,最后 FileStartReadV()
 * 提交 IO。数据到达后的错误检查在 md_readv_complete() 中完成。
 *
 * 【与同步版的差异】不实现 zero_damaged_pages 逻辑(该逻辑本身有争议、
 * 计划移除,且异步下"定义者/完成者"的该 GUC 可能不一致,实现会更
 * 复杂)。部分读与错误的最终处理由上层负责(见 smgrstartreadv 注释)。
 *
 * 【参数】
 *   ioh —— AIO 句柄;其余与 mdreadv() 相同。
 * 【返回值】无(发起失败报 ERROR)。
 *
 * mdstartreadv() -- Asynchronous version of mdreadv().
 */
void
mdstartreadv(PgAioHandle *ioh,
			 SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
			 void **buffers, BlockNumber nblocks)
{
	pgoff_t		seekpos;
	MdfdVec    *v;
	BlockNumber nblocks_this_segment;
	struct iovec *iov;
	int			iovcnt;
	int			ret;

	v = _mdfd_getseg(reln, forknum, blocknum, false,
					 EXTENSION_FAIL | EXTENSION_CREATE_RECOVERY);

	seekpos = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

	Assert(seekpos < (pgoff_t) BLCKSZ * RELSEG_SIZE);

	nblocks_this_segment =
		Min(nblocks,
			RELSEG_SIZE - (blocknum % ((BlockNumber) RELSEG_SIZE)));

	if (nblocks_this_segment != nblocks)
		elog(ERROR, "read crossing segment boundary");

	iovcnt = pgaio_io_get_iovec(ioh, &iov);

	Assert(nblocks <= iovcnt);

	iovcnt = buffers_to_iovec(iov, buffers, nblocks_this_segment);

	Assert(iovcnt <= nblocks_this_segment);

	if (!(io_direct_flags & IO_DIRECT_DATA))
		pgaio_io_set_flag(ioh, PGAIO_HF_BUFFERED);

	pgaio_io_set_target_smgr(ioh,
							 reln,
							 forknum,
							 blocknum,
							 nblocks,
							 false);
	pgaio_io_register_callbacks(ioh, PGAIO_HCB_MD_READV, 0);

	ret = FileStartReadV(ioh, v->mdfd_vfd, iovcnt, seekpos, WAIT_EVENT_DATA_FILE_READ);
	if (ret != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not start reading blocks %u..%u in file \"%s\": %m",
						blocknum,
						blocknum + nblocks_this_segment - 1,
						FilePathName(v->mdfd_vfd))));

	/*
	 * The error checks corresponding to the post-read checks in mdreadv() are
	 * in md_readv_complete().
	 *
	 * However we chose, at least for now, to not implement the
	 * zero_damaged_pages logic present in mdreadv(). As outlined in mdreadv()
	 * that logic is rather problematic, and we want to get rid of it. Here
	 * equivalent logic would have to be more complicated due to potential
	 * differences in the zero_damaged_pages setting between the definer and
	 * completor of IO.
	 */
}

/*
 * mdwritev (中文)把缓冲数组写到关系的指定位置(仅限已存在的块)
 *
 * 【作用】mdreadv 的写镜像:按段切分,iovec 合并连续缓冲,FileWriteV
 * 循环处理短写(短写多为磁盘满,下次尝试会从内核拿到 ENOSPC)。整段
 * 写完后,若非 skipFsync 且非临时关系,register_dirty_segment() 登记
 * 检查点 fsync。CHECK_WRITE_VS_EXTEND 构建会断言写入范围不超过当前
 * 大小(扩展必须走 mdextend)。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块;buffers —— 待写缓冲数组;nblocks —— 块数;
 *   skipFsync —— 跳过检查点 fsync 登记。
 * 【返回值】无。
 *
 * mdwritev() -- Write the supplied blocks at the appropriate location.
 *
 * This is to be used only for updating already-existing blocks of a
 * relation (ie, those before the current EOF).  To extend a relation,
 * use mdextend().
 */
void
mdwritev(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum,
		 const void **buffers, BlockNumber nblocks, bool skipFsync)
{
	/* This assert is too expensive to have on normally ... */
#ifdef CHECK_WRITE_VS_EXTEND
	Assert((uint64) blocknum + (uint64) nblocks <= (uint64) mdnblocks(reln, forknum));
#endif

	while (nblocks > 0)
	{
		struct iovec iov[PG_IOV_MAX];
		int			iovcnt;
		pgoff_t		seekpos;
		ssize_t		nbytes;
		MdfdVec    *v;
		BlockNumber nblocks_this_segment;
		size_t		transferred_this_segment;
		size_t		size_this_segment;

		v = _mdfd_getseg(reln, forknum, blocknum, skipFsync,
						 EXTENSION_FAIL | EXTENSION_CREATE_RECOVERY);

		seekpos = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

		Assert(seekpos < (pgoff_t) BLCKSZ * RELSEG_SIZE);

		nblocks_this_segment =
			Min(nblocks,
				RELSEG_SIZE - (blocknum % ((BlockNumber) RELSEG_SIZE)));
		nblocks_this_segment = Min(nblocks_this_segment, lengthof(iov));

		if (nblocks_this_segment != nblocks)
			elog(ERROR, "write crosses segment boundary");

		iovcnt = buffers_to_iovec(iov, (void **) buffers, nblocks_this_segment);
		size_this_segment = nblocks_this_segment * BLCKSZ;
		transferred_this_segment = 0;

		/*
		 * Inner loop to continue after a short write.  If the reason is that
		 * we're out of disk space, a future attempt should get an ENOSPC
		 * error from the kernel.
		 */
		for (;;)
		{
			TRACE_POSTGRESQL_SMGR_MD_WRITE_START(forknum, blocknum,
												 reln->smgr_rlocator.locator.spcOid,
												 reln->smgr_rlocator.locator.dbOid,
												 reln->smgr_rlocator.locator.relNumber,
												 reln->smgr_rlocator.backend);
			nbytes = FileWriteV(v->mdfd_vfd, iov, iovcnt, seekpos,
								WAIT_EVENT_DATA_FILE_WRITE);
			TRACE_POSTGRESQL_SMGR_MD_WRITE_DONE(forknum, blocknum,
												reln->smgr_rlocator.locator.spcOid,
												reln->smgr_rlocator.locator.dbOid,
												reln->smgr_rlocator.locator.relNumber,
												reln->smgr_rlocator.backend,
												nbytes,
												size_this_segment - transferred_this_segment);

#ifdef SIMULATE_SHORT_WRITE
			nbytes = Min(nbytes, 4096);
#endif

			if (nbytes < 0)
			{
				bool		enospc = errno == ENOSPC;

				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not write blocks %u..%u in file \"%s\": %m",
								blocknum,
								blocknum + nblocks_this_segment - 1,
								FilePathName(v->mdfd_vfd)),
						 enospc ? errhint("Check free disk space.") : 0));
			}

			/* One loop should usually be enough. */
			transferred_this_segment += nbytes;
			Assert(transferred_this_segment <= size_this_segment);
			if (transferred_this_segment == size_this_segment)
				break;

			/* Adjust position and iovecs after a short write. */
			seekpos += nbytes;
			iovcnt = compute_remaining_iovec(iov, iov, iovcnt, nbytes);
		}

		if (!skipFsync && !SmgrIsTemp(reln))
			register_dirty_segment(reln, forknum, v);

		nblocks -= nblocks_this_segment;
		buffers += nblocks_this_segment;
		blocknum += nblocks_this_segment;
	}
}


/*
 * mdwriteback (中文)通知内核把指定块区间写回磁盘
 *
 * 【作用】对 [blocknum, blocknum+nblocks) 调 FileWriteback()(异步回写,
 * 不等待完成)。按段切分,尽量少发请求。使用 EXTENSION_DONT_OPEN:目标
 * 段若尚未打开(说明最近没有写过它),直接忽略返回——正在写已删除关系
 * 的缓冲也没关系,无需重新打开,以免与 PROCSIGNAL_BARRIER_SMGRRELEASE
 * 竞态,拿到一个"即将被 unlink 的文件"的描述符。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blocknum —— 起始块;nblocks —— 块数。
 * 【返回值】无。
 *
 * mdwriteback() -- Tell the kernel to write pages back to storage.
 *
 * This accepts a range of blocks because flushing several pages at once is
 * considerably more efficient than doing so individually.
 */
void
mdwriteback(SMgrRelation reln, ForkNumber forknum,
			BlockNumber blocknum, BlockNumber nblocks)
{
	Assert((io_direct_flags & IO_DIRECT_DATA) == 0);

	/*
	 * Issue flush requests in as few requests as possible; have to split at
	 * segment boundaries though, since those are actually separate files.
	 */
	while (nblocks > 0)
	{
		BlockNumber nflush = nblocks;
		pgoff_t		seekpos;
		MdfdVec    *v;
		int			segnum_start,
					segnum_end;

		v = _mdfd_getseg(reln, forknum, blocknum, true /* not used */ ,
						 EXTENSION_DONT_OPEN);

		/*
		 * We might be flushing buffers of already removed relations, that's
		 * ok, just ignore that case.  If the segment file wasn't open already
		 * (ie from a recent mdwrite()), then we don't want to re-open it, to
		 * avoid a race with PROCSIGNAL_BARRIER_SMGRRELEASE that might leave
		 * us with a descriptor to a file that is about to be unlinked.
		 */
		if (!v)
			return;

		/* compute offset inside the current segment */
		segnum_start = blocknum / RELSEG_SIZE;

		/* compute number of desired writes within the current segment */
		segnum_end = (blocknum + nblocks - 1) / RELSEG_SIZE;
		if (segnum_start != segnum_end)
			nflush = RELSEG_SIZE - (blocknum % ((BlockNumber) RELSEG_SIZE));

		Assert(nflush >= 1);
		Assert(nflush <= nblocks);

		seekpos = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

		FileWriteback(v->mdfd_vfd, seekpos, (pgoff_t) BLCKSZ * nflush, WAIT_EVENT_DATA_FILE_FLUSH);

		nblocks -= nflush;
		blocknum += nflush;
	}
}

/*
 * mdnblocks (中文)计算关系某个 fork 的块数
 *
 * 【作用】先 mdopenfork 打开首段,再从"最后一个已打开的段"起向高段
 * 推进:已打开段默认满(RELSEG_SIZE,此前验证过,避免重复 seek);每段
 * 用 _mdnblocks 测大小,未满即停止,返回 segno*RELSEG_SIZE+nblocks;
 * 满段则打开下一段继续(_mdfd_openseg,失败/不存在即返回当前累计大小)。
 *
 * 【重要副作用】调用后所有活动段都被打开并加入 md_seg_fds;若从未
 * 调用过,数组里只有"实际访问到的那几个段"。
 *
 * 【一致性假设】"已打开段恰好满"的前提只在"其他后端截断了关系"时被
 * 打破;上层通过 relcache 失效关闭并重开 md fd 处理该场景(checkpointer
 * 不参与 relcache 失效,可能持有非活动段,但它从不需要计算关系大小)。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】块数。
 *
 * mdnblocks() -- Get the number of blocks stored in a relation.
 *
 * Important side effect: all active segments of the relation are opened
 * and added to the md_seg_fds array.  If this routine has not been
 * called, then only segments up to the last one actually touched
 * are present in the array.
 */
BlockNumber
mdnblocks(SMgrRelation reln, ForkNumber forknum)
{
	MdfdVec    *v;
	BlockNumber nblocks;
	BlockNumber segno;

	mdopenfork(reln, forknum, EXTENSION_FAIL);

	/* mdopen has opened the first segment */
	Assert(reln->md_num_open_segs[forknum] > 0);

	/*
	 * Start from the last open segments, to avoid redundant seeks.  We have
	 * previously verified that these segments are exactly RELSEG_SIZE long,
	 * and it's useless to recheck that each time.
	 *
	 * NOTE: this assumption could only be wrong if another backend has
	 * truncated the relation.  We rely on higher code levels to handle that
	 * scenario by closing and re-opening the md fd, which is handled via
	 * relcache flush.  (Since the checkpointer doesn't participate in
	 * relcache flush, it could have segment entries for inactive segments;
	 * that's OK because the checkpointer never needs to compute relation
	 * size.)
	 */
	segno = reln->md_num_open_segs[forknum] - 1;
	v = &reln->md_seg_fds[forknum][segno];

	for (;;)
	{
		nblocks = _mdnblocks(reln, forknum, v);
		if (nblocks > ((BlockNumber) RELSEG_SIZE))
			elog(FATAL, "segment too big");
		if (nblocks < ((BlockNumber) RELSEG_SIZE))
			return (segno * ((BlockNumber) RELSEG_SIZE)) + nblocks;

		/*
		 * If segment is exactly RELSEG_SIZE, advance to next one.
		 */
		segno++;

		/*
		 * We used to pass O_CREAT here, but that has the disadvantage that it
		 * might create a segment which has vanished through some operating
		 * system misadventure.  In such a case, creating the segment here
		 * undermines _mdfd_getseg's attempts to notice and report an error
		 * upon access to a missing segment.
		 */
		v = _mdfd_openseg(reln, forknum, segno, 0);
		if (v == NULL)
			return segno * ((BlockNumber) RELSEG_SIZE);
	}
}

/*
 * mdtruncate (中文)把关系截断到指定块数
 *
 * 【作用】从最后一个打开的段往前处理:
 * - 段起始块号 >= 目标:整段作废——FileTruncate(0) 截成空文件但不
 *   unlink(原因见文件头注释:别的后端/checkpointer 可能持有其 fd,且
 *   截断后关系还可能再扩展回来复用此文件),登记 fsync,关闭 fd 并收缩
 *   数组(首段除外,永不丢弃);
 * - 段跨越目标边界:这是要保留的末段,截到目标大小(若目标恰好是
 *   RELSEG_SIZE 的整数倍,会把"第 K+1 段"截成 0 长度但保留,以维持
 *   "满段 + 一个部分段"的磁盘不变量);
 * - 段完全在目标之前:无需处理,直接结束。
 *
 * 【约束】保证不分配内存(因此可安全用于临界区)!调用前提:调用方
 * 先持锁调用 smgrnblocks 取得当前大小、期间不得使用该关系的 smgr
 * 函数或处理中断(保证所有活动段都已打开、截断循环能见全)。
 * nblocks > curnblk(荒唐请求):恢复期间静默忽略,否则 ERROR。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   curnblk —— 当前大小;nblocks —— 目标大小。
 * 【返回值】无。
 *
 * mdtruncate() -- Truncate relation to specified number of blocks.
 *
 * Guaranteed not to allocate memory, so it can be used in a critical section.
 * Caller must have called smgrnblocks() to obtain curnblk while holding a
 * sufficient lock to prevent a change in relation size, and not used any smgr
 * functions for this relation or handled interrupts in between.  This makes
 * sure we have opened all active segments, so that truncate loop will get
 * them all!
 *
 * If nblocks > curnblk, the request is ignored when we are InRecovery,
 * otherwise, an error is raised.
 */
void
mdtruncate(SMgrRelation reln, ForkNumber forknum,
		   BlockNumber curnblk, BlockNumber nblocks)
{
	BlockNumber priorblocks;
	int			curopensegs;

	if (nblocks > curnblk)
	{
		/* Bogus request ... but no complaint if InRecovery */
		if (InRecovery)
			return;
		ereport(ERROR,
				(errmsg("could not truncate file \"%s\" to %u blocks: it's only %u blocks now",
						relpath(reln->smgr_rlocator, forknum).str,
						nblocks, curnblk)));
	}
	if (nblocks == curnblk)
		return;					/* no work */

	/*
	 * Truncate segments, starting at the last one. Starting at the end makes
	 * managing the memory for the fd array easier, should there be errors.
	 */
	curopensegs = reln->md_num_open_segs[forknum];
	while (curopensegs > 0)
	{
		MdfdVec    *v;

		priorblocks = (curopensegs - 1) * RELSEG_SIZE;

		v = &reln->md_seg_fds[forknum][curopensegs - 1];

		if (priorblocks > nblocks)
		{
			/*
			 * This segment is no longer active. We truncate the file, but do
			 * not delete it, for reasons explained in the header comments.
			 */
			if (FileTruncate(v->mdfd_vfd, 0, WAIT_EVENT_DATA_FILE_TRUNCATE) < 0)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not truncate file \"%s\": %m",
								FilePathName(v->mdfd_vfd))));

			if (!SmgrIsTemp(reln))
				register_dirty_segment(reln, forknum, v);

			/* we never drop the 1st segment */
			Assert(v != &reln->md_seg_fds[forknum][0]);

			FileClose(v->mdfd_vfd);
			_fdvec_resize(reln, forknum, curopensegs - 1);
		}
		else if (priorblocks + ((BlockNumber) RELSEG_SIZE) > nblocks)
		{
			/*
			 * This is the last segment we want to keep. Truncate the file to
			 * the right length. NOTE: if nblocks is exactly a multiple K of
			 * RELSEG_SIZE, we will truncate the K+1st segment to 0 length but
			 * keep it. This adheres to the invariant given in the header
			 * comments.
			 */
			BlockNumber lastsegblocks = nblocks - priorblocks;

			if (FileTruncate(v->mdfd_vfd, (pgoff_t) lastsegblocks * BLCKSZ, WAIT_EVENT_DATA_FILE_TRUNCATE) < 0)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not truncate file \"%s\" to %u blocks: %m",
								FilePathName(v->mdfd_vfd),
								nblocks)));
			if (!SmgrIsTemp(reln))
				register_dirty_segment(reln, forknum, v);
		}
		else
		{
			/*
			 * We still need this segment, so nothing to do for this and any
			 * earlier segment.
			 */
			break;
		}
		curopensegs--;
	}
}

/*
 * mdregistersync (中文)把整个关系(含非活动段)登记为"检查点时需 fsync"
 *
 * 【作用】先 mdnblocks() 确保所有活动段已打开,再临时打开所有非活动
 * 段(存在的话,它们是空文件),把每一段(活动 + 非活动)逐个
 * register_dirty_segment() 登记;非活动段登记后立即关闭。必须连非活动
 * 段一起登记的原因见 mdimmedsync 的注释(截断后被遗忘的段可能在崩溃
 * 恢复后残留旧数据)。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】无。
 *
 * mdregistersync() -- Mark whole relation as needing fsync
 */
void
mdregistersync(SMgrRelation reln, ForkNumber forknum)
{
	int			segno;
	int			min_inactive_seg;

	/*
	 * NOTE: mdnblocks makes sure we have opened all active segments, so that
	 * the loop below will get them all!
	 */
	mdnblocks(reln, forknum);

	min_inactive_seg = segno = reln->md_num_open_segs[forknum];

	/*
	 * Temporarily open inactive segments, then close them after sync.  There
	 * may be some inactive segments left opened after error, but that is
	 * harmless.  We don't bother to clean them up and take a risk of further
	 * trouble.  The next mdclose() will soon close them.
	 */
	while (_mdfd_openseg(reln, forknum, segno, 0) != NULL)
		segno++;

	while (segno > 0)
	{
		MdfdVec    *v = &reln->md_seg_fds[forknum][segno - 1];

		register_dirty_segment(reln, forknum, v);

		/* Close inactive segments immediately */
		if (segno > min_inactive_seg)
		{
			FileClose(v->mdfd_vfd);
			_fdvec_resize(reln, forknum, segno - 1);
		}

		segno--;
	}
}

/*
 * mdimmedsync (中文)立即把关系(含非活动段)同步到稳定存储
 *
 * 【作用】对每一段(活动段 + 临时打开的非活动段)执行 FileSync(fsync),
 * 非活动段同步后立即关闭。只同步"已经发出"的写;对缓冲池里尚未写回
 * 的脏页一无所知(那是 FlushRelationBuffers 的职责)。同步请求处理
 * 路径依赖"非活动段也被同步"这一性质:考虑一个跳过 WAL 的关系——
 * 检查点同步了某段后,mdtruncate() 把它变成非活动段;若下次检查点前
 * 崩溃,该段未被重新同步就会在恢复后存活,把不该有的旧数据带回表里。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork。
 * 【返回值】无(失败按 data_sync_elevel 报错)。
 *
 * mdimmedsync() -- Immediately sync a relation to stable storage.
 *
 * Note that only writes already issued are synced; this routine knows
 * nothing of dirty buffers that may exist inside the buffer manager.  We
 * sync active and inactive segments; smgrDoPendingSyncs() relies on this.
 * Consider a relation skipping WAL.  Suppose a checkpoint syncs blocks of
 * some segment, then mdtruncate() renders that segment inactive.  If we
 * crash before the next checkpoint syncs the newly-inactive segment, that
 * segment may survive recovery, reintroducing unwanted data into the table.
 */
void
mdimmedsync(SMgrRelation reln, ForkNumber forknum)
{
	int			segno;
	int			min_inactive_seg;

	/*
	 * NOTE: mdnblocks makes sure we have opened all active segments, so that
	 * the loop below will get them all!
	 */
	mdnblocks(reln, forknum);

	min_inactive_seg = segno = reln->md_num_open_segs[forknum];

	/*
	 * Temporarily open inactive segments, then close them after sync.  There
	 * may be some inactive segments left opened after fsync() error, but that
	 * is harmless.  We don't bother to clean them up and take a risk of
	 * further trouble.  The next mdclose() will soon close them.
	 */
	while (_mdfd_openseg(reln, forknum, segno, 0) != NULL)
		segno++;

	while (segno > 0)
	{
		MdfdVec    *v = &reln->md_seg_fds[forknum][segno - 1];

		/*
		 * fsyncs done through mdimmedsync() should be tracked in a separate
		 * IOContext than those done through mdsyncfiletag() to differentiate
		 * between unavoidable client backend fsyncs (e.g. those done during
		 * index build) and those which ideally would have been done by the
		 * checkpointer. Since other IO operations bypassing the buffer
		 * manager could also be tracked in such an IOContext, wait until
		 * these are also tracked to track immediate fsyncs.
		 */
		if (FileSync(v->mdfd_vfd, WAIT_EVENT_DATA_FILE_IMMEDIATE_SYNC) < 0)
			ereport(data_sync_elevel(ERROR),
					(errcode_for_file_access(),
					 errmsg("could not fsync file \"%s\": %m",
							FilePathName(v->mdfd_vfd))));

		/* Close inactive segments immediately */
		if (segno > min_inactive_seg)
		{
			FileClose(v->mdfd_vfd);
			_fdvec_resize(reln, forknum, segno - 1);
		}

		segno--;
	}
}

/*
 * mdfd (中文)返回指定块所在段文件的原始内核文件描述符
 *
 * 【作用】供 AIO 框架在"其他进程执行 IO"的场景使用(smgr_aio_reopen
 * 里调用):保证目标段已打开,计算出块在段内的字节偏移(写入 *off),
 * 返回底层真实 fd(绕过 fd.c 的 VFD 抽象,因为跨进程不能共享 VFD)。
 *
 * 【参数】
 *   reln, forknum, blocknum —— 目标关系、fork 与块号;
 *   off —— 输出:块在段内的字节偏移。
 * 【返回值】原始 fd(失败报 ERROR)。
 */
int
mdfd(SMgrRelation reln, ForkNumber forknum, BlockNumber blocknum, uint32 *off)
{
	MdfdVec    *v = mdopenfork(reln, forknum, EXTENSION_FAIL);

	v = _mdfd_getseg(reln, forknum, blocknum, false,
					 EXTENSION_FAIL);

	*off = (pgoff_t) BLCKSZ * (blocknum % ((BlockNumber) RELSEG_SIZE));

	Assert(*off < (pgoff_t) BLCKSZ * RELSEG_SIZE);

	return FileGetRawDesc(v->mdfd_vfd);
}

/*
 * register_dirty_segment (中文)登记某段文件需要被 fsync(待检查点)
 *
 * 【作用】写页/建段/截断等修改文件的操作在"需要 fsync"时调用:
 * 构造该段的 FileTag,通过 RegisterSyncRequest(SYNC_REQUEST) 投递到
 * checkpointer 的请求队列,由它在下次检查点统一 fsync。若队列已满
 * (retryOnError=false,返回 false):退化方案是"本进程立即自己 fsync"
 * (记 DEBUG1),保证可靠性不因队列满而打折扣。临时关系绝不进入本函数
 * (断言)。
 *
 * 【参数】
 *   reln —— 目标关系;forknum —— fork;seg —— 段描述。
 * 【返回值】无。
 *
 * register_dirty_segment() -- Mark a relation segment as needing fsync
 *
 * If there is a local pending-ops table, just make an entry in it for
 * ProcessSyncRequests to process later.  Otherwise, try to pass off the
 * fsync request to the checkpointer process.  If that fails, just do the
 * fsync locally before returning (we hope this will not happen often
 * enough to be a performance problem).
 */
static void
register_dirty_segment(SMgrRelation reln, ForkNumber forknum, MdfdVec *seg)
{
	FileTag		tag;

	INIT_MD_FILETAG(tag, reln->smgr_rlocator.locator, forknum, seg->mdfd_segno);

	/* Temp relations should never be fsync'd */
	Assert(!SmgrIsTemp(reln));

	if (!RegisterSyncRequest(&tag, SYNC_REQUEST, false /* retryOnError */ ))
	{
		instr_time	io_start;

		ereport(DEBUG1,
				(errmsg_internal("could not forward fsync request because request queue is full")));

		io_start = pgstat_prepare_io_time(track_io_timing);

		if (FileSync(seg->mdfd_vfd, WAIT_EVENT_DATA_FILE_SYNC) < 0)
			ereport(data_sync_elevel(ERROR),
					(errcode_for_file_access(),
					 errmsg("could not fsync file \"%s\": %m",
							FilePathName(seg->mdfd_vfd))));

		/*
		 * We have no way of knowing if the current IOContext is
		 * IOCONTEXT_NORMAL or IOCONTEXT_[BULKREAD, BULKWRITE, VACUUM] at this
		 * point, so count the fsync as being in the IOCONTEXT_NORMAL
		 * IOContext. This is probably okay, because the number of backend
		 * fsyncs doesn't say anything about the efficacy of the
		 * BufferAccessStrategy. And counting both fsyncs done in
		 * IOCONTEXT_NORMAL and IOCONTEXT_[BULKREAD, BULKWRITE, VACUUM] under
		 * IOCONTEXT_NORMAL is likely clearer when investigating the number of
		 * backend fsyncs.
		 */
		pgstat_count_io_op_time(IOOBJECT_RELATION, IOCONTEXT_NORMAL,
								IOOP_FSYNC, io_start, 1, 0);
	}
}

/*
 * register_unlink_tombstone (中文)登记"墓碑文件"在下次检查点后删除
 *
 * 【作用】mdunlink 留下的"空首段"(tombstone)不能马上删:要等下一个
 * 检查点之后,确保所有后端都已放弃对旧 relfilenumber 的引用(机制
 * 见 mdunlink 注释)。把任务以 SYNC_UNLINK_REQUEST 交给 checkpointer
 * 处理。仅用于非临时关系的主 fork 首段(断言保证)。
 *
 * 【参数】rlocator —— 关系定位。
 * 【返回值】无。
 *
 * register_unlink_tombstone() -- Schedule a tombstone file to be deleted
 *
 * A tombstone file is an empty first segment of a relation that has already
 * been dropped (see mdunlink()).  This function schedules it to be deleted
 * after the next checkpoint.
 */
static void
register_unlink_tombstone(RelFileLocatorBackend rlocator)
{
	FileTag		tag;

	INIT_MD_FILETAG(tag, rlocator.locator, MAIN_FORKNUM, 0);

	/* Should never be used with temp relations */
	Assert(!RelFileLocatorBackendIsTemp(rlocator));

	RegisterSyncRequest(&tag, SYNC_UNLINK_REQUEST, true /* retryOnError */ );
}

/*
 * register_forget_request (中文)撤销某段的待执行同步请求
 *
 * 【作用】文件即将被删除/失效前调用:把该段的 fsync 请求从检查点
 * 队列中撤掉(SYNC_FORGET_REQUEST),避免对已删文件做无谓甚至出错的
 * fsync。删除路径(如 mdunlinkfork)在真正 unlink 之前调用。
 *
 * 【参数】
 *   rlocator —— 关系定位;forknum —— fork;segno —— 段号。
 * 【返回值】无。
 *
 * register_forget_request() -- forget any fsyncs for a relation fork's segment
 */
static void
register_forget_request(RelFileLocatorBackend rlocator, ForkNumber forknum,
						BlockNumber segno)
{
	FileTag		tag;

	INIT_MD_FILETAG(tag, rlocator.locator, forknum, segno);

	RegisterSyncRequest(&tag, SYNC_FORGET_REQUEST, true /* retryOnError */ );
}

/*
 * ForgetDatabaseSyncRequests (中文)撤销整个数据库的所有同步/删除请求
 *
 * 【作用】DROP DATABASE 时调用:以"数据库 OID 过滤"请求
 * (SYNC_FILTER_REQUEST)把该库全部待执行 fsync/删除登记一次性撤销,
 * 防止 checkpointer 继续处理已经消失的库的文件。
 *
 * 【参数】dbid —— 目标数据库 OID。
 * 【返回值】无。
 *
 * ForgetDatabaseSyncRequests -- forget any fsyncs and unlinks for a DB
 */
void
ForgetDatabaseSyncRequests(Oid dbid)
{
	FileTag		tag;
	RelFileLocator rlocator;

	rlocator.dbOid = dbid;
	rlocator.spcOid = 0;
	rlocator.relNumber = 0;

	INIT_MD_FILETAG(tag, rlocator, InvalidForkNumber, InvalidBlockNumber);

	RegisterSyncRequest(&tag, SYNC_FILTER_REQUEST, true /* retryOnError */ );
}

/*
 * DropRelationFiles (中文)批量删除一批关系的所有文件
 *
 * 【作用】删除关系文件的便捷入口(如 DROP TABLE 提交后的清理):对每个
 * locator 打开 SMgrRelation(重放时先为每个 fork 发 XLogDropRelation
 * 记录,让 WAL 重放时知道这些文件已删),再统一交给
 * smgrdounlinkall() 执行删除,最后 smgrclose() 关闭并释放临时数组。
 *
 * 【参数】
 *   delrels —— 待删关系 locator 数组;ndelrels —— 数量;
 *   isRedo  —— 重放模式(允许文件已不存在)。
 * 【返回值】无。
 *
 * DropRelationFiles -- drop files of all given relations
 */
void
DropRelationFiles(RelFileLocator *delrels, int ndelrels, bool isRedo)
{
	SMgrRelation *srels;
	int			i;

	srels = palloc_array(SMgrRelation, ndelrels);
	for (i = 0; i < ndelrels; i++)
	{
		SMgrRelation srel = smgropen(delrels[i], INVALID_PROC_NUMBER);

		if (isRedo)
		{
			ForkNumber	fork;

			for (fork = 0; fork <= MAX_FORKNUM; fork++)
				XLogDropRelation(delrels[i], fork);
		}
		srels[i] = srel;
	}

	smgrdounlinkall(srels, ndelrels, isRedo);

	for (i = 0; i < ndelrels; i++)
		smgrclose(srels[i]);
	pfree(srels);
}


/*
 * _fdvec_resize (中文)调整 fork 的已打开段数组大小
 *
 * 【作用】把 md_seg_fds[forknum] 数组(长度记录于 md_num_open_segs)
 * 调整到 nseg 项,支持:清空(pfree 置 NULL)、首次分配(MdCxt 中
 * palloc)、扩大(repalloc)。**绝不缩小**已扩大的数组,保证
 * mdtruncate() "不分配内存"的承诺(它只减 md_num_open_segs,不动
 * 内存),从而允许在临界区中使用。
 *
 * 【设计思想】扩大的 repalloc 不做摊销:它比 open/close 文件便宜得
 * 多,不值得为摊销复杂化代码。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;nseg —— 新数组长度。
 * 【返回值】无。
 *
 * _fdvec_resize() -- Resize the fork's open segments array
 */
static void
_fdvec_resize(SMgrRelation reln,
			  ForkNumber forknum,
			  int nseg)
{
	if (nseg == 0)
	{
		if (reln->md_num_open_segs[forknum] > 0)
		{
			pfree(reln->md_seg_fds[forknum]);
			reln->md_seg_fds[forknum] = NULL;
		}
	}
	else if (reln->md_num_open_segs[forknum] == 0)
	{
		reln->md_seg_fds[forknum] =
			MemoryContextAlloc(MdCxt, sizeof(MdfdVec) * nseg);
	}
	else if (nseg > reln->md_num_open_segs[forknum])
	{
		/*
		 * It doesn't seem worthwhile complicating the code to amortize
		 * repalloc() calls.  Those are far faster than PathNameOpenFile() or
		 * FileClose(), and the memory context internally will sometimes avoid
		 * doing an actual reallocation.
		 */
		reln->md_seg_fds[forknum] =
			repalloc(reln->md_seg_fds[forknum],
					 sizeof(MdfdVec) * nseg);
	}
	else
	{
		/*
		 * We don't reallocate a smaller array, because we want mdtruncate()
		 * to be able to promise that it won't allocate memory, so that it is
		 * allowed in a critical section.  This means that a bit of space in
		 * the array is now wasted, until the next time we add a segment and
		 * reallocate.
		 */
	}

	reln->md_num_open_segs[forknum] = nseg;
}

/*
 * _mdfd_segpath (中文)构造指定段的文件路径
 *
 * 【作用】段 0 就是基础路径;段 n>0 为 "基础路径.段号"。返回定长
 * MdPathStr(按值返回,整个结构拷贝,无指针泄漏问题)。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;segno —— 段号。
 * 【返回值】段文件完整路径。
 *
 * Return the filename for the specified segment of the relation. The
 * returned string is palloc'd.
 */
static MdPathStr
_mdfd_segpath(SMgrRelation reln, ForkNumber forknum, BlockNumber segno)
{
	RelPathStr	path;
	MdPathStr	fullpath;

	path = relpath(reln->smgr_rlocator, forknum);

	if (segno > 0)
		sprintf(fullpath.str, "%s.%u", path.str, segno);
	else
		strcpy(fullpath.str, path.str);

	return fullpath;
}

/*
 * _mdfd_openseg (中文)打开指定段文件并登记段描述,失败返回 NULL
 *
 * 【作用】按 _mdfd_segpath 的路径打开文件(附带 oflags,如 O_CREAT),
 * 成功则断言"总是按段号升序追加",_fdvec_resize(segno+1) 扩容后填入
 * MdfdVec 并返回。打开失败(文件不存在等)返回 NULL 而不报错——由
 * 调用方按自己的 behavior 决定如何处理。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   segno —— 段号;oflags —— 附加 open 标志(可为 0 或 O_CREAT)。
 * 【返回值】新段的 MdfdVec 指针;失败 NULL。
 *
 * Open the specified segment of the relation,
 * and make a MdfdVec object for it.  Returns NULL on failure.
 */
static MdfdVec *
_mdfd_openseg(SMgrRelation reln, ForkNumber forknum, BlockNumber segno,
			  int oflags)
{
	MdfdVec    *v;
	File		fd;
	MdPathStr	fullpath;

	fullpath = _mdfd_segpath(reln, forknum, segno);

	/* open the file */
	fd = PathNameOpenFile(fullpath.str, _mdfd_open_flags() | oflags);

	if (fd < 0)
		return NULL;

	/*
	 * Segments are always opened in order from lowest to highest, so we must
	 * be adding a new one at the end.
	 */
	Assert(segno == reln->md_num_open_segs[forknum]);

	_fdvec_resize(reln, forknum, segno + 1);

	/* fill the entry */
	v = &reln->md_seg_fds[forknum][segno];
	v->mdfd_vfd = fd;
	v->mdfd_segno = segno;

	Assert(_mdnblocks(reln, forknum, v) <= ((BlockNumber) RELSEG_SIZE));

	/* all done */
	return v;
}

/*
 * _mdfd_getseg (中文)找到(必要时创建)包含指定块的段
 *
 * 【作用】md 读写路径的核心定位函数:计算 blkno 所在段号 targetseg,
 * 若已打开直接返回;未打开则从"最后打开的段"(或首段)逐个向后推进
 * _mdfd_openseg 直到 targetseg,过程中按 behavior 处理"缺失段":
 * - EXTENSION_CREATE(或恢复期 EXTENSION_CREATE_RECOVERY):允许创建——
 *   若前一段未满,先把它补满(mdextend 垫零,维持"末段之前的段必须
 *   恰好 RELSEG_SIZE"的不变量;恢复或跳跃式扩展时会遇到),再用
 *   O_CREAT 打开新段;
 * - 前一段未满却要求继续:非创建路径下,按 behavior 返回 NULL
 *   (EXTENSION_RETURN_NULL,并置 errno=ENOENT 供调用方区分原因)或
 *   直接报错;
 * - 打开失败:EXTENSION_RETURN_NULL 且 FILE_POSSIBLY_DELETED(errno)
 *   时返回 NULL,否则报错。
 * EXTENSION_DONT_OPEN 时,目标段未打开则直接返回 NULL(绝不开文件)。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork;
 *   blkno —— 目标块号;skipFsync —— 仅在创建新段、垫零扩展时使用;
 *   behavior —— EXTENSION_* 位组合。
 * 【返回值】目标段描述;可能为 NULL(由 behavior 决定)。
 *
 * _mdfd_getseg() -- Find the segment of the relation holding the
 *					 specified block.
 *
 * If the segment doesn't exist, we ereport, return NULL, or create the
 * segment, according to "behavior".  Note: skipFsync is only used in the
 * EXTENSION_CREATE case.
 */
static MdfdVec *
_mdfd_getseg(SMgrRelation reln, ForkNumber forknum, BlockNumber blkno,
			 bool skipFsync, int behavior)
{
	MdfdVec    *v;
	BlockNumber targetseg;
	BlockNumber nextsegno;

	/* some way to handle non-existent segments needs to be specified */
	Assert(behavior &
		   (EXTENSION_FAIL | EXTENSION_CREATE | EXTENSION_RETURN_NULL |
			EXTENSION_DONT_OPEN));

	targetseg = blkno / ((BlockNumber) RELSEG_SIZE);

	/* if an existing and opened segment, we're done */
	if (targetseg < reln->md_num_open_segs[forknum])
	{
		v = &reln->md_seg_fds[forknum][targetseg];
		return v;
	}

	/* The caller only wants the segment if we already had it open. */
	if (behavior & EXTENSION_DONT_OPEN)
		return NULL;

	/*
	 * The target segment is not yet open. Iterate over all the segments
	 * between the last opened and the target segment. This way missing
	 * segments either raise an error, or get created (according to
	 * 'behavior'). Start with either the last opened, or the first segment if
	 * none was opened before.
	 */
	if (reln->md_num_open_segs[forknum] > 0)
		v = &reln->md_seg_fds[forknum][reln->md_num_open_segs[forknum] - 1];
	else
	{
		v = mdopenfork(reln, forknum, behavior);
		if (!v)
			return NULL;		/* if behavior & EXTENSION_RETURN_NULL */
	}

	for (nextsegno = reln->md_num_open_segs[forknum];
		 nextsegno <= targetseg; nextsegno++)
	{
		BlockNumber nblocks = _mdnblocks(reln, forknum, v);
		int			flags = 0;

		Assert(nextsegno == v->mdfd_segno + 1);

		if (nblocks > ((BlockNumber) RELSEG_SIZE))
			elog(FATAL, "segment too big");

		if ((behavior & EXTENSION_CREATE) ||
			(InRecovery && (behavior & EXTENSION_CREATE_RECOVERY)))
		{
			/*
			 * Normally we will create new segments only if authorized by the
			 * caller (i.e., we are doing mdextend()).  But when doing WAL
			 * recovery, create segments anyway; this allows cases such as
			 * replaying WAL data that has a write into a high-numbered
			 * segment of a relation that was later deleted. We want to go
			 * ahead and create the segments so we can finish out the replay.
			 *
			 * We have to maintain the invariant that segments before the last
			 * active segment are of size RELSEG_SIZE; therefore, if
			 * extending, pad them out with zeroes if needed.  (This only
			 * matters if in recovery, or if the caller is extending the
			 * relation discontiguously, but that can happen in hash indexes.)
			 */
			if (nblocks < ((BlockNumber) RELSEG_SIZE))
			{
				char	   *zerobuf = palloc_aligned(BLCKSZ, PG_IO_ALIGN_SIZE,
													 MCXT_ALLOC_ZERO);

				mdextend(reln, forknum,
						 nextsegno * ((BlockNumber) RELSEG_SIZE) - 1,
						 zerobuf, skipFsync);
				pfree(zerobuf);
			}
			flags = O_CREAT;
		}
		else if (nblocks < ((BlockNumber) RELSEG_SIZE))
		{
			/*
			 * When not extending, only open the next segment if the current
			 * one is exactly RELSEG_SIZE.  If not (this branch), either
			 * return NULL or fail.
			 */
			if (behavior & EXTENSION_RETURN_NULL)
			{
				/*
				 * Some callers discern between reasons for _mdfd_getseg()
				 * returning NULL based on errno. As there's no failing
				 * syscall involved in this case, explicitly set errno to
				 * ENOENT, as that seems the closest interpretation.
				 */
				errno = ENOENT;
				return NULL;
			}

			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\" (target block %u): previous segment is only %u blocks",
							_mdfd_segpath(reln, forknum, nextsegno).str,
							blkno, nblocks)));
		}

		v = _mdfd_openseg(reln, forknum, nextsegno, flags);

		if (v == NULL)
		{
			if ((behavior & EXTENSION_RETURN_NULL) &&
				FILE_POSSIBLY_DELETED(errno))
				return NULL;
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\" (target block %u): %m",
							_mdfd_segpath(reln, forknum, nextsegno).str,
							blkno)));
		}
	}

	return v;
}

/*
 * _mdnblocks (中文)返回单个段文件当前的块数
 *
 * 【作用】用 FileSize 取文件字节长度除以 BLCKSZ,得到整块数(忽略
 * EOF 处的部分块)。FileSize 失败(如文件被截断的竞态)报 ERROR。
 *
 * 【参数】
 *   reln, forknum —— 目标关系与 fork(仅用于报错信息);
 *   seg —— 目标段描述。
 * 【返回值】段内块数。
 *
 * Get number of blocks present in a single disk file
 */
static BlockNumber
_mdnblocks(SMgrRelation reln, ForkNumber forknum, MdfdVec *seg)
{
	pgoff_t		len;

	len = FileSize(seg->mdfd_vfd);
	if (len < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not seek to end of file \"%s\": %m",
						FilePathName(seg->mdfd_vfd))));
	/* note that this calculation will ignore any partial block at EOF */
	return (BlockNumber) (len / BLCKSZ);
}

/*
 * mdsyncfiletag (中文)按文件标签执行 fsync(sync 框架回调)
 *
 * 【作用】checkpointer 处理同步请求队列时、或后端从队列取回请求自刷
 * 时调用:给定描述某 md 段文件的 FileTag,打开(或复用已打开的)该文件
 * 并 FileSync()。路径写入 path 输出缓冲,供调用方在错误消息中引用。
 *
 * 【返回值语义】0 成功;-1 失败(errno 保留)。注意:复用 reln 已打开
 * 的 fd 时无需关闭;临时打开的文件必须用完即关。
 *
 * 【参数】
 *   ftag —— 目标段文件标签;path —— 输出:文件路径(MAXPGPATH)。
 * 【返回值】见上。
 *
 * Sync a file to disk, given a file tag.  Write the path into an output
 * buffer so the caller can use it in error messages.
 *
 * Return 0 on success, -1 on failure, with errno set.
 */
int
mdsyncfiletag(const FileTag *ftag, char *path)
{
	SMgrRelation reln = smgropen(ftag->rlocator, INVALID_PROC_NUMBER);
	File		file;
	instr_time	io_start;
	bool		need_to_close;
	int			result,
				save_errno;

	/* See if we already have the file open, or need to open it. */
	if (ftag->segno < reln->md_num_open_segs[ftag->forknum])
	{
		file = reln->md_seg_fds[ftag->forknum][ftag->segno].mdfd_vfd;
		strlcpy(path, FilePathName(file), MAXPGPATH);
		need_to_close = false;
	}
	else
	{
		MdPathStr	p;

		p = _mdfd_segpath(reln, ftag->forknum, ftag->segno);
		strlcpy(path, p.str, MD_PATH_STR_MAXLEN);

		file = PathNameOpenFile(path, _mdfd_open_flags());
		if (file < 0)
			return -1;
		need_to_close = true;
	}

	io_start = pgstat_prepare_io_time(track_io_timing);

	/* Sync the file. */
	result = FileSync(file, WAIT_EVENT_DATA_FILE_SYNC);
	save_errno = errno;

	if (need_to_close)
		FileClose(file);

	pgstat_count_io_op_time(IOOBJECT_RELATION, IOCONTEXT_NORMAL,
							IOOP_FSYNC, io_start, 1, 0);

	errno = save_errno;
	return result;
}

/*
 * mdunlinkfiletag (中文)按文件标签删除文件(仅用于墓碑文件)
 *
 * 【作用】checkpointer 处理 SYNC_UNLINK_REQUEST 时调用:删除 mdunlink
 * 留下的空首段(tombstone)。断言只处理主 fork 首段;路径由 relpathperm
 * 构造;直接 unlink,失败返回 -1 并保留 errno。
 *
 * 【参数】
 *   ftag —— 目标文件标签;path —— 输出:文件路径。
 * 【返回值】0 成功;-1 失败(errno 已设置)。
 *
 * Unlink a file, given a file tag.  Write the path into an output
 * buffer so the caller can use it in error messages.
 *
 * Return 0 on success, -1 on failure, with errno set.
 */
int
mdunlinkfiletag(const FileTag *ftag, char *path)
{
	RelPathStr	p;

	/* We only unlink tombstone files through this mechanism */
	Assert(ftag->forknum == MAIN_FORKNUM && ftag->segno == 0);

	/* Compute the path. */
	p = relpathperm(ftag->rlocator, MAIN_FORKNUM);
	strlcpy(path, p.str, MAXPGPATH);

	/* Try to unlink the file. */
	return unlink(path);
}

/*
 * mdfiletagmatches (中文)SYNC_FILTER_REQUEST 的匹配回调
 *
 * 【作用】处理"过滤"请求时,对队列中每个待处理请求调用:返回 true
 * 表示该请求应被遗忘。当前实现只比较数据库 OID(只用于 DROP DATABASE
 * 时撤销某库的全部待处理回调)。
 *
 * 【参数】
 *   ftag —— 过滤请求的标签;candidate —— 队列中的候选请求标签。
 * 【返回值】是否匹配(匹配则遗忘候选)。
 *
 * Check if a given candidate request matches a given tag, when processing
 * a SYNC_FILTER_REQUEST request.  This will be called for all pending
 * requests to find out whether to forget them.
 */
bool
mdfiletagmatches(const FileTag *ftag, const FileTag *candidate)
{
	/*
	 * For now we only use filter requests as a way to drop all scheduled
	 * callbacks relating to a given database, when dropping the database.
	 * We'll return true for all candidates that have the same database OID as
	 * the ftag from the SYNC_FILTER_REQUEST request, so they're forgotten.
	 */
	return ftag->rlocator.dbOid == candidate->rlocator.dbOid;
}

/*
 * md_readv_complete (中文)异步读的完成回调
 *
 * 【作用】mdstartreadv 提交的 IO 完成时由 AIO 框架调用,把内核返回的
 * "字节数"换算成 smgr 层的"块数",并归类结果:
 * - 硬错误(结果 < 0):置 PGAIO_RS_ERROR,把 errno 记录到 error_data,
 *   立即向服务器日志(LOG_SERVER_ONLY)输出(发起者可能忙于处理其他
 *   工作,或已被取消/因其他 IO 失败而报错,不能指望它及时看到);上层
 *   处理结果时会把它转成 ERROR;
 * - 读到 0 块:视为失败(同上);
 * - 块数不足:标记 PGAIO_RS_PARTIAL,由上层对未读部分重发 IO。
 * 注意本回调不实现 zero_damaged_pages 逻辑(理由见 mdstartreadv)。
 *
 * 【参数】
 *   ioh —— AIO 句柄;prior_result —— 底层 IO 结果;cb_data —— 回调
 *   数据(此处 0,未使用)。
 * 【返回值】换算/归类后的结果。
 *
 * AIO completion callback for mdstartreadv().
 */
static PgAioResult
md_readv_complete(PgAioHandle *ioh, PgAioResult prior_result, uint8 cb_data)
{
	PgAioTargetData *td = pgaio_io_get_target_data(ioh);
	PgAioResult result = prior_result;

	if (prior_result.result < 0)
	{
		result.status = PGAIO_RS_ERROR;
		result.id = PGAIO_HCB_MD_READV;
		/* For "hard" errors, track the error number in error_data */
		result.error_data = -prior_result.result;
		result.result = 0;

		/*
		 * Immediately log a message about the IO error, but only to the
		 * server log. The reason to do so immediately is that the originator
		 * might not process the query result immediately (because it is busy
		 * doing another part of query processing) or at all (e.g. if it was
		 * cancelled or errored out due to another IO also failing).  The
		 * definer of the IO will emit an ERROR when processing the IO's
		 * results
		 */
		pgaio_result_report(result, td, LOG_SERVER_ONLY);

		return result;
	}

	/*
	 * As explained above smgrstartreadv(), the smgr API operates on the level
	 * of blocks, rather than bytes. Convert.
	 */
	result.result /= BLCKSZ;

	Assert(result.result <= td->smgr.nblocks);

	if (result.result == 0)
	{
		/* consider 0 blocks read a failure */
		result.status = PGAIO_RS_ERROR;
		result.id = PGAIO_HCB_MD_READV;
		result.error_data = 0;

		/* see comment above the "hard error" case */
		pgaio_result_report(result, td, LOG_SERVER_ONLY);

		return result;
	}

	if (result.status != PGAIO_RS_ERROR &&
		result.result < td->smgr.nblocks)
	{
		/* partial reads should be retried at upper level */
		result.status = PGAIO_RS_PARTIAL;
		result.id = PGAIO_HCB_MD_READV;
	}

	return result;
}

/*
 * md_readv_report (中文)异步读的错误报告回调
 *
 * 【作用】pgaio_result_report() 最终输出错误消息时调用,把 IO 结果转
 * 成可读的 PostgreSQL 日志/错误文本:error_data != 0 时按对应 errno
 * 生成"读取失败"消息;否则生成"只读了部分字节"消息(通常是调试级别)。
 * 路径按临时/普通关系分别构造。
 *
 * 【参数】
 *   result —— 要报告的 IO 结果;td —— IO 目标数据;elevel —— 消息级别。
 * 【返回值】无。
 *
 * AIO error reporting callback for mdstartreadv().
 *
 * Errors are encoded as follows:
 * - PgAioResult.error_data != 0 encodes IO that failed with that errno
 * - PgAioResult.error_data == 0 encodes IO that didn't read all data
 */
static void
md_readv_report(PgAioResult result, const PgAioTargetData *td, int elevel)
{
	RelPathStr	path;

	path = relpathbackend(td->smgr.rlocator,
						  td->smgr.is_temp ? MyProcNumber : INVALID_PROC_NUMBER,
						  td->smgr.forkNum);

	if (result.error_data != 0)
	{
		/* for errcode_for_file_access() and %m */
		errno = result.error_data;

		ereport(elevel,
				errcode_for_file_access(),
				errmsg("could not read blocks %u..%u in file \"%s\": %m",
					   td->smgr.blockNum,
					   td->smgr.blockNum + td->smgr.nblocks - 1,
					   path.str));
	}
	else
	{
		/*
		 * NB: This will typically only be output in debug messages, while
		 * retrying a partial IO.
		 */
		ereport(elevel,
				errcode(ERRCODE_DATA_CORRUPTED),
				errmsg("could not read blocks %u..%u in file \"%s\": read only %zu of %zu bytes",
					   td->smgr.blockNum,
					   td->smgr.blockNum + td->smgr.nblocks - 1,
					   path.str,
					   result.result * (size_t) BLCKSZ,
					   td->smgr.nblocks * (size_t) BLCKSZ));
	}
}
