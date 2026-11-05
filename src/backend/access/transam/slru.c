/*-------------------------------------------------------------------------
 *
 * slru.c
 *		Simple LRU buffering for wrap-around-able permanent metadata
 *
 * This module is used to maintain various pieces of transaction status
 * indexed by TransactionId (such as commit status, parent transaction ID,
 * commit timestamp), as well as storage for multixacts, serializable
 * isolation locks and NOTIFY traffic.  Extensions can define their own
 * SLRUs, too.
 *
 * Under ordinary circumstances we expect that write traffic will occur
 * mostly to the latest page (and to the just-prior page, soon after a
 * page transition).  Read traffic will probably touch a larger span of
 * pages, but a relatively small number of buffers should be sufficient.
 *
 * We use a simple least-recently-used scheme to manage a pool of shared
 * page buffers, split in banks by the lowest bits of the page number, and
 * the management algorithm only processes the bank to which the desired
 * page belongs, so a linear search is sufficient; there's no need for a
 * hashtable or anything fancy.  The algorithm is straight LRU except that
 * we will never swap out the latest page (since we know it's going to be
 * hit again eventually).
 *
 * We use per-bank control LWLocks to protect the shared data structures,
 * plus per-buffer LWLocks that synchronize I/O for each buffer.  The
 * bank's control lock must be held to examine or modify any of the bank's
 * shared state.  A process that is reading in or writing out a page
 * buffer does not hold the control lock, only the per-buffer lock for the
 * buffer it is working on.  One exception is latest_page_number, which is
 * read and written using atomic ops.
 *
 * "Holding the bank control lock" means exclusive lock in all cases
 * except for SimpleLruReadPage_ReadOnly(); see comments for
 * SlruRecentlyUsed() for the implications of that.
 *
 * When initiating I/O on a buffer, we acquire the per-buffer lock exclusively
 * before releasing the control lock.  The per-buffer lock is released after
 * completing the I/O, re-acquiring the control lock, and updating the shared
 * state.  (Deadlock is not possible here, because we never try to initiate
 * I/O when someone else is already doing I/O on the same buffer.)
 * To wait for I/O to complete, release the control lock, acquire the
 * per-buffer lock in shared mode, immediately release the per-buffer lock,
 * reacquire the control lock, and then recheck state (since arbitrary things
 * could have happened while we didn't have the lock).
 *
 * As with the regular buffer manager, it is possible for another process
 * to re-dirty a page that is currently being written out.  This is handled
 * by re-setting the page's page_dirty flag.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/access/transam/slru.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件实现 PostgreSQL 的 SLRU（Simple LRU）通用缓存机制：一组按页号随机
 * 访问的定长磁盘页面，通过共享内存中的有限缓冲池和 LRU 淘汰策略，为多种
 * “按 32 位事务标识/序号索引的元数据”提供低延迟、可并发、可截断的持久化
 * 存储。SLRU 本身不解释页面内容，页面内条目的布局、页号与键值的换算完全由
 * 各使用者定义。
 *
 * 一、使用者与典型布局
 *   - pg_xact（CLOG）：每个事务 2 bit，一页可容纳 BLCKSZ*4 个事务；使用
 *     group_lsn[] 记录异步提交 LSN，写页前必须 flush 对应 WAL；
 *   - pg_subtrans：每个子事务 4 字节父 XID，一页 BLCKSZ/4 个条目；
 *   - pg_multixact/offsets 与 pg_multixact/members：分别保存 MultiXact 成员
 *     偏移和成员数组，条目大小不同，因此各自有独立的页号换算和 PagePrecedes；
 *   - pg_commit_ts：每个已提交事务保存 8 字节时间戳 + 2 字节复制源；
 *   - pg_serial（可串行化谓词锁）、pg_notify（LISTEN/NOTIFY 队列）以及扩展
 *     通过 SimpleLruRequest() 注册的自定义 SLRU，也复用本文件。
 *
 * 二、页面与 segment 布局
 *   - 一页固定为 BLCKSZ（通常 8KB），一个 segment 固定包含
 *     SLRU_PAGES_PER_SEGMENT（默认 32）页；文件按 segment 组织，文件名是
 *     segment 号的十六进制表示（短名 4~6 位，或 long_segment_names 为 15 位）。
 *   - 全局页号 pageno 与物理位置的关系：
 *         segno   = pageno / SLRU_PAGES_PER_SEGMENT
 *         rpageno = pageno % SLRU_PAGES_PER_SEGMENT
 *         offset  = rpageno * BLCKSZ
 *     segment 内不保存页头，整页都是调用方的数据；页号可以随 32 位键空间回卷。
 *
 * 三、bank 与锁
 *   - 缓冲槽按槽号每 SLRU_BANK_SIZE（16）个分为一个 bank。访问页 pageno 时，
 *     先按 bankno = pageno % nbanks 找到该页所属 bank，再取该 bank 的
 *     LWLock：普通访问用排他锁，SimpleLruReadPage_ReadOnly() 的快路径用共享锁。
 *   - bank 控制锁保护该 bank 内的 page_status/page_dirty/page_number/
 *     page_lru_count/bank_cur_lru_count 等共享数组；latest_page_number 单独
 *     用原子操作读写，因为它只用于“不要淘汰最新页”的启发式判断。
 *   - 每个 buffer 另有一把 LWLock，用于串行化该槽上的物理 I/O。发起 I/O 时
 *     先持有 buffer 锁再释放 bank 锁；等待 I/O 时释放 bank 锁，以共享模式
 *     获取并立即释放 buffer 锁，然后重新获取 bank 锁并复查状态（见文件头英文
 *     注释与 SimpleLruWaitIO()）。
 *
 * 四、buffer 状态机
 *   - EMPTY：槽未使用；READ_IN_PROGRESS：正在从磁盘读入；
 *     VALID：页内容有效且当前没有写 I/O；WRITE_IN_PROGRESS：正在写盘。
 *   - page_dirty 只在 VALID/WRITE_IN_PROGRESS 有意义。开始写时先清 dirty、
 *     置 WRITE_IN_PROGRESS；写盘期间其他进程可以再次弄脏该页，写完后若失败
 *     或已被重新弄脏，dirty 会保持/恢复为 true，因此一次写不保证页变干净。
 *   - 读入失败的槽回到 EMPTY；写入失败的槽回到 VALID 并重新标脏；I/O 失败
 *     不能立即 ereport，因为调用方已在共享内存中改了状态，必须先恢复状态，
 *     再由 SlruReportIOError() 统一报错。
 *
 * 五、优先级、回卷与截断
 *   - LRU 计数按 bank 维护：page_lru_count[slot] 越大表示越新；淘汰时选择
 *     “当前计数 - 页计数”最大者，并永不淘汰 latest_page_number 指向的页。
 *   - 页号来自 32 位键空间时会回卷，因此新旧比较不能用普通大小关系，而由
 *     使用者的 PagePrecedes 回调按模运算语义判断；LRU 平局时也用它选择更老的
 *     页，截断时用它判断 segment 是否整体早于 cutoffPage。
 *   - 只有 segment 的首页和末页都严格早于 cutoffPage 才能删除；若 cutoff 或
 *     回卷点落在 segment 内部，则整个 segment 保留。SimpleLruTruncate() 还会
 *     检查 latest_page_number，防止因回卷 bug 删除当前端点。
 *
 * 六、checkpoint、WAL 与崩溃恢复
 *   - 普通页写入不产生 WAL；新页清零、截断等语义由各使用者负责记录 WAL。
 *     slru.c 只在写页前检查 group_lsn[]（目前仅 pg_xact 使用），把该页所有
 *     LSN 组的上界 XLogFlush，满足“先写 WAL、后写数据”规则。
 *   - SimpleLruWriteAll() 在 checkpoint/关闭时扫描所有 bank 写出脏页，并通过
 *     sync_handler 把 fsync 请求交给 checkpointer 批量处理；它自身只 fsync
 *     目录，确保新建 segment 的目录项落盘。
 *   - 恢复期间允许读取不存在的 segment 并当作全零页（崩溃后可能重放已截断
 *     段上的旧事务状态更新）；写页时也允许按需创建 segment 文件，且不能用
 *     O_EXCL/O_TRUNC，因为多个后端可能同时创建同一个文件。
 *
 * 七、设计思想
 *   - 用“小 bank + 线性扫描”代替哈希表：每 bank 仅 16 个槽，查找和淘汰都在
 *     一个 cache line 友好的小数组内完成，锁竞争也被分散到多个 bank。
 *   - 页大小与普通 buffer 一致，便于复用 I/O、校验和与统计基础设施；不在页内
 *     放头部，避免浪费空间并让调用方自由定义条目格式。
 *   - 延迟 fsync：写入只把脏页交给 OS 并登记 sync request，由 checkpointer
 *     统一 fsync，减少提交/检查点路径上的同步 I/O。
 *   - 通过“最新页常驻 + 近似 LRU + PagePrecedes 回卷语义”在极简实现下同时
 *     满足性能、正确性和可截断性。
 */
#include "postgres.h"

#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

#include "access/slru.h"
#include "access/transam.h"
#include "access/xlog.h"
#include "access/xlogutils.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "storage/fd.h"
#include "storage/shmem.h"
#include "storage/shmem_internal.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/wait_event.h"

/*
 * Converts segment number to the filename of the segment.
 *
 * "path" should point to a buffer at least MAXPGPATH characters long.
 *
 * If ctl->long_segment_names is true, segno can be in the range [0, 2^60-1].
 * The resulting file name is made of 15 characters, e.g. dir/123456789ABCDEF.
 *
 * If ctl->long_segment_names is false, segno can be in the range [0, 2^24-1].
 * The resulting file name is made of 4 to 6 characters, as of:
 *
 *  dir/1234   for [0, 2^16-1]
 *  dir/12345  for [2^16, 2^20-1]
 *  dir/123456 for [2^20, 2^24-1]
 */
/*
 * 中文注释：
 * 把 segment 号转换为相对于数据目录的完整文件名，写入调用方提供的
 * MAXPGPATH 缓冲区。长名模式使用 15 位大写十六进制（如 dir/123456789ABCDEF），
 * 短名模式使用 "%04X"（至少 4 位，最多 6 位，如 dir/1234、dir/12345、
 * dir/123456）；短名模式通过 Assert 把 segno 限制在 24 位内，保证不会超过
 * SlruCorrectSegmentFilenameLength() 认可的 4~6 位长度。
 *
 * 返回值是 snprintf() 的返回值（不含结尾 NUL 的应有长度），调用方通常忽略；
 * 本函数不会 ereport，也不做目录存在性检查。它只做纯字符串格式化，不访问
 * 共享内存，因此无需加锁。文件名格式必须与 SlruScanDirectory() 的解析逻辑
 * 以及 SlruCorrectSegmentFilenameLength() 保持一致，否则旧的 segment 文件
 * 将无法被识别、截断或 fsync。
 */
static inline int
SlruFileName(SlruDesc *ctl, char *path, int64 segno)
{
	if (ctl->options.long_segment_names)
	{
		/*
		 * We could use 16 characters here but the disadvantage would be that
		 * the SLRU segments will be hard to distinguish from WAL segments.
		 *
		 * For this reason we use 15 characters. It is enough but also means
		 * that in the future we can't decrease SLRU_PAGES_PER_SEGMENT easily.
		 */
		Assert(segno >= 0 && segno <= INT64CONST(0xFFFFFFFFFFFFFFF));
		return snprintf(path, MAXPGPATH, "%s/%015" PRIX64, ctl->options.Dir, segno);
	}
	else
	{
		/*
		 * Despite the fact that %04X format string is used up to 24 bit
		 * integers are allowed. See SlruCorrectSegmentFilenameLength()
		 */
		Assert(segno >= 0 && segno <= INT64CONST(0xFFFFFF));
		return snprintf(path, MAXPGPATH, "%s/%04X", (ctl)->options.Dir,
						(unsigned int) segno);
	}
}

/*
 * During SimpleLruWriteAll(), we will usually not need to write more than one
 * or two physical files, but we may need to write several pages per file.  We
 * can consolidate the I/O requests by leaving files open until control returns
 * to SimpleLruWriteAll().  This data structure remembers which files are open.
 */
/*
 * 中文注释：
 * SimpleLruWriteAll() 在一次 flush 中通常只涉及一两个 segment 文件，但每个
 * 文件可能有很多脏页。为避免每页都 open/close，本结构最多缓存
 * MAX_WRITEALL_BUFFERS（16）个已打开文件的 fd 和 segment 号，把同一文件的
 * 多次写入合并为一组 pwrite。fdata 是 SimpleLruWriteAll() 栈上的临时对象，
 * 只在该次 flush 中有效；超过 16 个文件时退化为逐页独立打开/关闭。
 * num_files 是当前已缓存的文件数，fd[]/segno[] 一一对应。该结构不跨进程
 * 共享，也不需要在 bank 锁之外额外保护。
 */
#define MAX_WRITEALL_BUFFERS	16

typedef struct SlruWriteAllData
{
	int			num_files;		/* # files actually open */
	int			fd[MAX_WRITEALL_BUFFERS];	/* their FD's */
	int64		segno[MAX_WRITEALL_BUFFERS];	/* their log seg#s */
} SlruWriteAllData;

typedef struct SlruWriteAllData *SlruWriteAll;


/*
 * Bank size for the slot array.  Pages are assigned a bank according to their
 * page number, with each bank being this size.  We want a power of 2 so that
 * we can determine the bank number for a page with just bit shifting; we also
 * want to keep the bank size small so that LRU victim search is fast.  16
 * buffers per bank seems a good number.
 */
/*
 * 中文注释：
 * SLRU 缓冲池按 bank 划分，每个 bank 固定 SLRU_BANK_SIZE = 16 个槽。
 * 取 2 的幂是为了用右移快速由槽号得到 bank 号（SlotGetBankNumber），同时让
 * 单个 bank 的线性 LRU 扫描足够便宜；bank 数 = nslots / 16，nslots 必须是
 * 16 的倍数（由 check_slru_buffers() 和 shmem 初始化断言保证）。
 * 注意：页到 bank 的映射使用的是 pageno % nbanks（见 SimpleLruGetBankLock），
 * 而不是这里的槽号右移；SlotGetBankNumber 只用于已知槽号时反查其所属 bank。
 */
#define SLRU_BANK_BITSHIFT		4
#define SLRU_BANK_SIZE			(1 << SLRU_BANK_BITSHIFT)

/*
 * Macro to get the bank number to which the slot belongs.
 */
#define SlotGetBankNumber(slotno)	((slotno) >> SLRU_BANK_BITSHIFT)


/*
 * Populate a file tag describing a segment file.  We only use the segment
 * number, since we can derive everything else we need by having separate
 * sync handler functions for clog, multixact etc.
 */
/*
 * 中文注释：
 * 构造用于 sync request 的 FileTag：先把整个结构清零，再填入该 SLRU 的
 * sync_handler 和 segment 号。SLRU 文件没有普通关系表的 relfilenode/fork
 * 概念，checkpointer 只需根据 handler 找到对应 SLRU 的同步回调，再由回调
 * 借助 segno 和该 SLRU 的目录拼出路径；因此其余字段必须保持为零。
 * 该宏只做内存填充，可在任意上下文调用；调用方需保证 a 是 FileTag 左值。
 */
#define INIT_SLRUFILETAG(a,xx_handler,xx_segno) \
( \
	memset(&(a), 0, sizeof(FileTag)), \
	(a).handler = (xx_handler), \
	(a).segno = (xx_segno) \
)

/* Saved info for SlruReportIOError */
/*
 * 中文注释：
 * SlruPhysicalReadPage()/SlruPhysicalWritePage() 在失败时不能直接
 * ereport(ERROR)，因为此时调用方已经修改了共享内存中的槽状态，必须先把
 * 状态恢复一致再报错。这两个 backend-private 静态变量暂存失败原因和 errno，
 * 由调用方在恢复共享状态后调用 SlruReportIOError() 统一生成错误消息。
 * 取值分别对应 open/lseek/read/write/fsync/close 失败；slru_errno 保存
 * 发生失败时的 errno（短读/短写时为 0），供报告区分“系统调用失败”和
 * “字节数不足”。每个后端单线程执行，因此不需要锁；但一次失败信息只在下一次
 * I/O 失败前有效，不能被跨错误边界复用。
 */
typedef enum
{
	SLRU_OPEN_FAILED,
	SLRU_SEEK_FAILED,
	SLRU_READ_FAILED,
	SLRU_WRITE_FAILED,
	SLRU_FSYNC_FAILED,
	SLRU_CLOSE_FAILED,
} SlruErrorCause;

static SlruErrorCause slru_errcause;
static int	slru_errno;


/*
 * 中文注释：
 * 本文件内部 static 辅助函数的前置声明，按“LSN 维护、I/O 等待、物理读写、
 * 错误报告、LRU 淘汰、目录扫描与删除”分层。它们都假定调用方已按约定持有
 * 相应的 bank/buffer 锁；具体锁要求见各函数定义处的中文注释。
 */
static void SimpleLruZeroLSNs(SlruDesc *ctl, int slotno);
static void SimpleLruWaitIO(SlruDesc *ctl, int slotno);
static void SlruInternalWritePage(SlruDesc *ctl, int slotno, SlruWriteAll fdata);
static bool SlruPhysicalReadPage(SlruDesc *ctl, int64 pageno, int slotno);
static bool SlruPhysicalWritePage(SlruDesc *ctl, int64 pageno, int slotno,
								  SlruWriteAll fdata);
static void SlruReportIOError(SlruDesc *ctl, int64 pageno,
							  const void *opaque_data);
static int	SlruSelectLRUPage(SlruDesc *ctl, int64 pageno);

static bool SlruScanDirCbDeleteCutoff(SlruDesc *ctl, char *filename,
									  int64 segpage, void *data);
static void SlruInternalDeleteSegment(SlruDesc *ctl, int64 segno);
static inline void SlruRecentlyUsed(SlruShared shared, int slotno);


/*
 * Initialization of shared memory
 */

/*
 * 中文注释：
 * 计算一个 SLRU 在共享内存中需要的总字节数，供 SimpleLruRequestWithOpts()
 * 在 shmem 请求阶段登记大小。布局依次为：SlruSharedData 本体、每槽的
 * page_buffer 指针数组、page_status/page_dirty/page_number/page_lru_count
 * 数组、每槽 buffer 锁、每 bank 的 bank 锁与 bank_cur_lru_count；若 nlsns>0，
 * 再加上每槽 nlsns 个 XLogRecPtr 的 group_lsn[]。所有数组按 MAXALIGN 对齐，
 * 页数据区按 BUFFERALIGN 对齐，最后附加 nslots * BLCKSZ 的页缓冲区。
 *
 * 参数 nslots 必须是 SLRU_BANK_SIZE 的整数倍且不超过
 * SLRU_MAX_ALLOWED_BUFFERS；nlsns 为每页 LSN 组数，0 表示不需要 WAL 顺序
 * 保护。函数无副作用，不初始化内存；其计算结果必须与 shmem_slru_init() 的
 * 指针切分逻辑严格一致，否则会越界或浪费空间。注释中假设 nslots 不会大到
 * 使乘法溢出 Size。
 */
static Size
SimpleLruShmemSize(int nslots, int nlsns)
{
	int			nbanks = nslots / SLRU_BANK_SIZE;
	Size		sz;

	Assert(nslots <= SLRU_MAX_ALLOWED_BUFFERS);
	Assert(nslots % SLRU_BANK_SIZE == 0);

	/* we assume nslots isn't so large as to risk overflow */
	sz = MAXALIGN(sizeof(SlruSharedData));
	sz += MAXALIGN(nslots * sizeof(char *));	/* page_buffer[] */
	sz += MAXALIGN(nslots * sizeof(SlruPageStatus));	/* page_status[] */
	sz += MAXALIGN(nslots * sizeof(bool));	/* page_dirty[] */
	sz += MAXALIGN(nslots * sizeof(int64)); /* page_number[] */
	sz += MAXALIGN(nslots * sizeof(int));	/* page_lru_count[] */
	sz += MAXALIGN(nslots * sizeof(LWLockPadded));	/* buffer_locks[] */
	sz += MAXALIGN(nbanks * sizeof(LWLockPadded));	/* bank_locks[] */
	sz += MAXALIGN(nbanks * sizeof(int));	/* bank_cur_lru_count[] */

	if (nlsns > 0)
		sz += MAXALIGN(nslots * nlsns * sizeof(XLogRecPtr));	/* group_lsn[] */

	return BUFFERALIGN(sz) + BLCKSZ * nslots;
}

/*
 * Determine a number of SLRU buffers to use.
 *
 * We simply divide shared_buffers by the divisor given and cap
 * that at the maximum given; but always at least SLRU_BANK_SIZE.
 * Round down to the nearest multiple of SLRU_BANK_SIZE.
 */
/*
 * 中文注释：
 * 根据 shared_buffers（NBuffers）自动推算某个 SLRU 的缓冲槽数，供各模块在
 * 对应 GUC（如 transaction_buffers、subtransaction_buffers）为 0 时使用。
 * 规则是 NBuffers/divisor 向下取整到 SLRU_BANK_SIZE 的倍数，再限制在
 * [SLRU_BANK_SIZE, max 向下取整后的值] 区间内；整数除法先减余数保证不会
 * 超过 max，同时保证结果为 bank 大小的整数倍。divisor/max 由调用方按 SLRU
 * 的访问特征选择（常见为 512/1024）。纯函数，无副作用；NBuffers 在
 * postmaster 启动时已确定。
 */
int
SimpleLruAutotuneBuffers(int divisor, int max)
{
	return Min(max - (max % SLRU_BANK_SIZE),
			   Max(SLRU_BANK_SIZE,
				   NBuffers / divisor - (NBuffers / divisor) % SLRU_BANK_SIZE));
}

/*
 * Register a simple LRU cache in shared memory.
 */
/*
 * 中文注释：
 * 在 postmaster 启动、共享内存尚未分配时登记一个 SLRU：把调用方传入的
 * SlruOpts 复制到 TopMemoryContext（调用方常常传入复合字面量或栈上结构，
 * 不能长期引用），计算共享内存大小，然后通过 ShmemRequestInternal() 以
 * SHMEM_KIND_SLRU 加入 shmem 请求队列。真正的共享内存初始化由
 * shmem_slru_init() 完成，每个后端的挂接由 shmem_slru_attach() 完成。
 *
 * 必须满足：name 非空、nslots>0、PagePrecedes 和 errdetail_for_io_error
 * 回调非空。options 是浅拷贝：name 字符串和 desc 指针仍指向调用方的对象，
 * 调用方必须保证它们在进程生命周期内有效（通常是静态全局变量/字符串常量）。
 * 本函数只能在 shmem 请求阶段调用，不能在后端运行期动态注册；它不加锁，
 * 也不访问共享内存。
 */
void
SimpleLruRequestWithOpts(const SlruOpts *options)
{
	SlruOpts   *options_copy;

	Assert(options->name != NULL);
	Assert(options->nslots > 0);
	Assert(options->PagePrecedes != NULL);
	Assert(options->errdetail_for_io_error != NULL);

	options_copy = MemoryContextAlloc(TopMemoryContext,
									  sizeof(SlruOpts));
	memcpy(options_copy, options, sizeof(SlruOpts));

	options_copy->base.name = options->name;
	options_copy->base.size = SimpleLruShmemSize(options_copy->nslots, options_copy->nlsns);

	ShmemRequestInternal(&options_copy->base, SHMEM_KIND_SLRU);
}

/* Initialize locks and shared memory area */
/*
 * 中文注释：
 * shmem 框架的初始化回调：在 postmaster 完成共享内存分配后，把
 * location 处的原始内存切分为 SlruSharedData 及其后随数组，并初始化锁、
 * 槽状态和统计索引。它同时把 desc->shared 指向共享区、desc->nbanks 设为
 * nslots/SLRU_BANK_SIZE、复制一份 options 到 desc，使后端可以通过
 * SlruDesc 访问共享状态。
 *
 * 具体工作：若未指定 tranche id，则为 buffer 锁和 bank 锁各申请一个命名
 * tranche；清零整个共享结构；设置 num_slots/lsn_groups_per_page、原子变量
 * latest_page_number、统计索引；按与 SimpleLruShmemSize() 完全一致的顺序
 * 摆放各数组；初始化每槽 buffer 锁、页指针和 EMPTY/clean/LRU=0 状态；初始化
 * 每个 bank 的锁和 bank_cur_lru_count；最后用 Assert 检查切分未超出预算。
 *
 * 该函数只在启动时由单一进程执行，之后共享内存对所有后端可见，因此不需要
 * 额外加锁；但布局/对齐必须与 SimpleLruShmemSize() 同步修改。页缓冲区按
 * BUFFERALIGN 对齐，可满足直接 I/O 或页级校验和等对对齐的要求。
 */
void
shmem_slru_init(void *location, ShmemStructOpts *base_options)
{
	SlruOpts   *options = (SlruOpts *) base_options;
	SlruDesc   *desc = (SlruDesc *) options->desc;
	char		namebuf[NAMEDATALEN];
	SlruShared	shared;
	int			nslots = options->nslots;
	int			nbanks = nslots / SLRU_BANK_SIZE;
	int			nlsns = options->nlsns;
	char	   *ptr;
	Size		offset;

	shared = (SlruShared) location;
	desc->shared = shared;
	desc->nbanks = nbanks;
	memcpy(&desc->options, options, sizeof(SlruOpts));

	/* assign new tranche IDs, if not given */
	if (desc->options.buffer_tranche_id == 0)
	{
		snprintf(namebuf, sizeof(namebuf), "%s buffer", desc->options.name);
		desc->options.buffer_tranche_id = LWLockNewTrancheId(namebuf);
	}
	if (desc->options.bank_tranche_id == 0)
	{
		snprintf(namebuf, sizeof(namebuf), "%s bank", desc->options.name);
		desc->options.bank_tranche_id = LWLockNewTrancheId(namebuf);
	}

	Assert(nslots <= SLRU_MAX_ALLOWED_BUFFERS);

	memset(shared, 0, sizeof(SlruSharedData));

	shared->num_slots = nslots;
	shared->lsn_groups_per_page = nlsns;

	pg_atomic_init_u64(&shared->latest_page_number, 0);

	shared->slru_stats_idx = pgstat_get_slru_index(desc->options.name);

	ptr = (char *) shared;
	offset = MAXALIGN(sizeof(SlruSharedData));
	shared->page_buffer = (char **) (ptr + offset);
	offset += MAXALIGN(nslots * sizeof(char *));
	shared->page_status = (SlruPageStatus *) (ptr + offset);
	offset += MAXALIGN(nslots * sizeof(SlruPageStatus));
	shared->page_dirty = (bool *) (ptr + offset);
	offset += MAXALIGN(nslots * sizeof(bool));
	shared->page_number = (int64 *) (ptr + offset);
	offset += MAXALIGN(nslots * sizeof(int64));
	shared->page_lru_count = (int *) (ptr + offset);
	offset += MAXALIGN(nslots * sizeof(int));

	/* Initialize LWLocks */
	shared->buffer_locks = (LWLockPadded *) (ptr + offset);
	offset += MAXALIGN(nslots * sizeof(LWLockPadded));
	shared->bank_locks = (LWLockPadded *) (ptr + offset);
	offset += MAXALIGN(nbanks * sizeof(LWLockPadded));
	shared->bank_cur_lru_count = (int *) (ptr + offset);
	offset += MAXALIGN(nbanks * sizeof(int));

	if (nlsns > 0)
	{
		shared->group_lsn = (XLogRecPtr *) (ptr + offset);
		offset += MAXALIGN(nslots * nlsns * sizeof(XLogRecPtr));
	}

	ptr += BUFFERALIGN(offset);
	for (int slotno = 0; slotno < nslots; slotno++)
	{
		LWLockInitialize(&shared->buffer_locks[slotno].lock,
						 desc->options.buffer_tranche_id);

		shared->page_buffer[slotno] = ptr;
		shared->page_status[slotno] = SLRU_PAGE_EMPTY;
		shared->page_dirty[slotno] = false;
		shared->page_lru_count[slotno] = 0;
		ptr += BLCKSZ;
	}

	/* Initialize the slot banks. */
	for (int bankno = 0; bankno < nbanks; bankno++)
	{
		LWLockInitialize(&shared->bank_locks[bankno].lock, desc->options.bank_tranche_id);
		shared->bank_cur_lru_count[bankno] = 0;
	}

	/* Should fit to estimated shmem size */
	Assert(ptr - (char *) shared <= SimpleLruShmemSize(nslots, nlsns));
}

/*
 * 中文注释：
 * shmem 挂接回调：后端（或 EXEC_BACKEND 下的新进程）映射共享内存后，用它
 * 把本进程的 SlruDesc 重新指向映射地址，并恢复 nbanks 与 options 副本。
 * 共享内存内容已由 shmem_slru_init() 初始化，这里绝不能再次 memset 或重置
 * 锁/槽状态，否则会破坏其他后端的数据。函数只写进程私有的 desc，不加锁，
 * 也不做 I/O；nslots 必须与初始化时一致。
 */
void
shmem_slru_attach(void *location, ShmemStructOpts *base_options)
{
	SlruOpts   *options = (SlruOpts *) base_options;
	SlruDesc   *desc = (SlruDesc *) options->desc;
	int			nslots = options->nslots;
	int			nbanks = nslots / SLRU_BANK_SIZE;

	desc->shared = (SlruShared) location;
	desc->nbanks = nbanks;
	memcpy(&desc->options, options, sizeof(SlruOpts));
}


/*
 * Helper function for GUC check_hook to check whether slru buffers are in
 * multiples of SLRU_BANK_SIZE.
 */
/*
 * 中文注释：
 * SLRU 缓冲数 GUC 的 check_hook：要求新值必须是 SLRU_BANK_SIZE（16）的
 * 整数倍，否则通过 GUC_check_errdetail() 给出详细原因并返回 false，让 GUC
 * 机制拒绝该值。这样可保证每个 bank 恰好 16 个槽、nbanks 为整数，避免
 * shmem 布局和 bank 映射出现余数。该函数在配置解析/启动阶段调用，无副作用，
 * 不访问共享内存；name 仅用于错误消息。
 */
bool
check_slru_buffers(const char *name, int *newval)
{
	/* Valid values are multiples of SLRU_BANK_SIZE */
	if (*newval % SLRU_BANK_SIZE == 0)
		return true;

	GUC_check_errdetail("\"%s\" must be a multiple of %d.", name,
						SLRU_BANK_SIZE);
	return false;
}

/*
 * Initialize (or reinitialize) a page to zeroes.
 *
 * The page is not actually written, just set up in shared memory.
 * The slot number of the new page is returned.
 *
 * Bank lock must be held at entry, and will be held at exit.
 */
/*
 * 中文注释：
 * 在共享缓冲池中创建（或重新初始化）一个页，把 BLCKSZ 字节清零并标记为
 * VALID + dirty，返回占用该页的槽号；真正的落盘由后续写页或 checkpoint
 * 完成。调用方必须已持有该页所属 bank 的排他锁，函数返回时仍持有该锁。
 *
 * 步骤：用 SlruSelectLRUPage() 找到目标页已存在的槽，或一个可回收的槽
 * （EMPTY 或干净的 VALID；若选中的脏页会先被写出）；断言槽状态符合预期；
 * 设置 page_number/page_status/dirty；调用 SlruRecentlyUsed() 标记 MRU；
 * 清零页缓冲；清零该槽的 group_lsn[]；原子地更新 latest_page_number 为本页；
 * 增加“清零页”统计。
 *
 * 并发/恢复：整个操作在 bank 锁内完成，且 SlruSelectLRUPage() 同样在 bank
 * 锁内，所以不会与“选中同一槽进行淘汰”并发，latest_page_number 的更新
 * 无需额外内存屏障。调用方通常还要写一条“新页清零”的 WAL 记录（如
 * CLOG_ZEROPAGE），以保证崩溃恢复后页内容可重建；本函数本身不写 WAL，
 * 也不 fsync。
 */
int
SimpleLruZeroPage(SlruDesc *ctl, int64 pageno)
{
	SlruShared	shared = ctl->shared;
	int			slotno;

	Assert(LWLockHeldByMeInMode(SimpleLruGetBankLock(ctl, pageno), LW_EXCLUSIVE));

	/* Find a suitable buffer slot for the page */
	slotno = SlruSelectLRUPage(ctl, pageno);
	Assert(shared->page_status[slotno] == SLRU_PAGE_EMPTY ||
		   (shared->page_status[slotno] == SLRU_PAGE_VALID &&
			!shared->page_dirty[slotno]) ||
		   shared->page_number[slotno] == pageno);

	/* Mark the slot as containing this page */
	shared->page_number[slotno] = pageno;
	shared->page_status[slotno] = SLRU_PAGE_VALID;
	shared->page_dirty[slotno] = true;
	SlruRecentlyUsed(shared, slotno);

	/* Set the buffer to zeroes */
	MemSet(shared->page_buffer[slotno], 0, BLCKSZ);

	/* Set the LSNs for this new page to zero */
	SimpleLruZeroLSNs(ctl, slotno);

	/*
	 * Assume this page is now the latest active page.
	 *
	 * Note that because both this routine and SlruSelectLRUPage run with a
	 * SLRU bank lock held, it is not possible for this to be zeroing a page
	 * that SlruSelectLRUPage is going to evict simultaneously.  Therefore,
	 * there's no memory barrier here.
	 */
	pg_atomic_write_u64(&shared->latest_page_number, pageno);

	/* update the stats counter of zeroed pages */
	pgstat_count_slru_blocks_zeroed(shared->slru_stats_idx);

	return slotno;
}

/*
 * Zero all the LSNs we store for this slru page.
 *
 * This should be called each time we create a new page, and each time we read
 * in a page from disk into an existing buffer.  (Such an old page cannot
 * have any interesting LSNs, since we'd have flushed them before writing
 * the page in the first place.)
 *
 * This assumes that InvalidXLogRecPtr is bitwise-all-0.
 */
/*
 * 中文注释：
 * 把某个槽对应的所有 group_lsn[] 条目清零，表示该页当前没有任何“必须先
 * flush 的 WAL”约束。新建页时必须调用；从磁盘读入一个被淘汰过的旧页时也
 * 必须调用，因为该页原先的 LSN 组在写盘前已经 flush 并失去意义。函数假设
 * InvalidXLogRecPtr 的位模式全为 0，因此直接用 MemSet；nlsns==0 时什么也
 * 不做。
 *
 * 调用者必须确保自己独占该槽：SimpleLruZeroPage() 在 bank 锁内调用；
 * SlruPhysicalReadPage() 之后由 SimpleLruReadPage() 在槽处于
 * READ_IN_PROGRESS 且持有 buffer 锁时调用。不要在其他进程可能读写
 * group_lsn[] 时调用。
 */
static void
SimpleLruZeroLSNs(SlruDesc *ctl, int slotno)
{
	SlruShared	shared = ctl->shared;

	if (shared->lsn_groups_per_page > 0)
		MemSet(&shared->group_lsn[slotno * shared->lsn_groups_per_page], 0,
			   shared->lsn_groups_per_page * sizeof(XLogRecPtr));
}

/*
 * This is a convenience wrapper for the common case of zeroing a page and
 * immediately flushing it to disk.
 *
 * SLRU bank lock is acquired and released here.
 */
/*
 * 中文注释：
 * “清零一个页并立即写盘”的便捷封装，供需要确保页在磁盘上存在且内容为零的
 * 场景使用（例如 CLOG/commit_ts 的 zeropage WAL 重放和启动初始化）。它自行
 * 获取目标页所属 bank 的排他锁，调用 SimpleLruZeroPage() 建页，再调用
 * SimpleLruWritePage() 立即写出，最后断言页已不再 dirty 并释放锁。
 *
 * 与 SimpleLruZeroPage() 不同，调用方无需预先持锁；但本函数会做同步 I/O，
 * 只适合启动/恢复/低频路径。写失败时 SimpleLruWritePage() 会恢复共享状态并
 * 通过 SlruReportIOError() 抛错；若发生错误长跳转，已持有的 LWLock 会按
 * PostgreSQL 的错误清理规则释放。本函数不写 WAL，也不等待 checkpointer 的
 * 延迟 fsync。
 */
void
SimpleLruZeroAndWritePage(SlruDesc *ctl, int64 pageno)
{
	int			slotno;
	LWLock	   *lock;

	lock = SimpleLruGetBankLock(ctl, pageno);
	LWLockAcquire(lock, LW_EXCLUSIVE);

	/* Create and zero the page */
	slotno = SimpleLruZeroPage(ctl, pageno);

	/* Make sure it's written out */
	SimpleLruWritePage(ctl, slotno);
	Assert(!ctl->shared->page_dirty[slotno]);

	LWLockRelease(lock);
}

/*
 * Wait for any active I/O on a page slot to finish.  (This does not
 * guarantee that new I/O hasn't been started before we return, though.
 * In fact the slot might not even contain the same page anymore.)
 *
 * Bank lock must be held at entry, and will be held at exit.
 */
/*
 * 中文注释：
 * 等待某个槽上正在进行的读/写 I/O 完成。调用时 bank 锁必须已持有，返回时
 * 仍持有（重新获取为排他模式）。实现遵循文件头的锁协议：先释放 bank 锁，
 * 再以共享模式获取并立即释放该槽的 buffer 锁（若写者/读者持有排他锁，这里
 * 会阻塞到 I/O 结束），最后重新获取 bank 锁。
 *
 * 返回时并不保证槽仍包含原来的页，甚至不保证 I/O 已成功：其他进程可能在
 * 间隙中完成了旧 I/O 并发起新 I/O，或者失败路径没有恢复状态。因此函数在
 * 重新持锁后检查：若状态仍是 READ_IN_PROGRESS/WRITE_IN_PROGRESS，说明要么
 * 有新 I/O，要么之前的 I/O 失败且未复位；此时尝试条件获取 buffer 锁，
 * 成功则判定为失败残留：读失败把槽置 EMPTY，写失败置 VALID 并重新标脏，
 * 然后释放 buffer 锁。调用者必须重新检查槽状态/页号后再使用。
 *
 * 该函数不报错、不写 WAL；它只修复共享状态，真正的 I/O 错误由原发起者
 * 通过 SlruReportIOError() 报告。参数 slotno 必须属于当前 bank。
 */
static void
SimpleLruWaitIO(SlruDesc *ctl, int slotno)
{
	SlruShared	shared = ctl->shared;
	int			bankno = SlotGetBankNumber(slotno);

	Assert(shared->page_status[slotno] != SLRU_PAGE_EMPTY);

	/* See notes at top of file */
	LWLockRelease(&shared->bank_locks[bankno].lock);
	LWLockAcquire(&shared->buffer_locks[slotno].lock, LW_SHARED);
	LWLockRelease(&shared->buffer_locks[slotno].lock);
	LWLockAcquire(&shared->bank_locks[bankno].lock, LW_EXCLUSIVE);

	/*
	 * If the slot is still in an io-in-progress state, then either someone
	 * already started a new I/O on the slot, or a previous I/O failed and
	 * neglected to reset the page state.  That shouldn't happen, really, but
	 * it seems worth a few extra cycles to check and recover from it. We can
	 * cheaply test for failure by seeing if the buffer lock is still held (we
	 * assume that transaction abort would release the lock).
	 */
	if (shared->page_status[slotno] == SLRU_PAGE_READ_IN_PROGRESS ||
		shared->page_status[slotno] == SLRU_PAGE_WRITE_IN_PROGRESS)
	{
		if (LWLockConditionalAcquire(&shared->buffer_locks[slotno].lock, LW_SHARED))
		{
			/* indeed, the I/O must have failed */
			if (shared->page_status[slotno] == SLRU_PAGE_READ_IN_PROGRESS)
				shared->page_status[slotno] = SLRU_PAGE_EMPTY;
			else				/* write_in_progress */
			{
				shared->page_status[slotno] = SLRU_PAGE_VALID;
				shared->page_dirty[slotno] = true;
			}
			LWLockRelease(&shared->buffer_locks[slotno].lock);
		}
	}
}

/*
 * Find a page in a shared buffer, reading it in if necessary.
 * The page number must correspond to an already-initialized page.
 *
 * If write_ok is true then it is OK to return a page that is in
 * WRITE_IN_PROGRESS state; it is the caller's responsibility to be sure
 * that modification of the page is safe.  If write_ok is false then we
 * will not return the page until it is not undergoing active I/O.
 *
 * On error, the passed-in 'opaque_data' is passed to the
 * 'errdetail_for_io_error' callback, to provide details on the operation that
 * failed.  It is only used for error reporting.
 *
 * Return value is the shared-buffer slot number now holding the page.
 * The buffer's LRU access info is updated.
 *
 * The correct bank lock must be held at entry, and will be held at exit.
 */
/*
 * 中文注释：
 * 从共享缓冲池读取指定页，必要时从磁盘读入；返回持有该页的槽号。调用方
 * 必须已持有该页所属 bank 的排他锁，返回时仍持有；在释放 bank 锁前，调用方
 * 可以安全地读写该槽的页内容。页号必须对应已经初始化（存在或允许按需创建）
 * 的页；本函数不会创建全零页，创建请用 SimpleLruZeroPage()。
 *
 * 流程：循环调用 SlruSelectLRUPage() 查找/选择槽。若槽中已经是目标页：遇到
 * READ_IN_PROGRESS 必须等待；遇到 WRITE_IN_PROGRESS 且 write_ok=false 也要
 * 等待（调用方要修改页时必须等写完成）；否则标记 MRU、统计 hit 并返回。
 * 若未命中，选中的必须是 EMPTY 或干净 VALID 槽；设置 page_number、
 * READ_IN_PROGRESS、dirty=false，获取 buffer 排他锁，释放 bank 锁后调用
 * SlruPhysicalReadPage()，清零 group_lsn[]，再重新获取 bank 锁；根据结果把
 * 状态置 VALID 或 EMPTY，释放 buffer 锁；失败时在状态恢复后调用
 * SlruReportIOError() 抛错；成功则标记 MRU、统计 read 并返回。
 *
 * write_ok 为 true 表示允许返回正在写出的页（读旧内容对只读访问安全）；
 * 为 false 时会等待写完成。opaque_data 只用于 I/O 错误时向
 * errdetail_for_io_error 回调提供上下文，不参与缓存逻辑。I/O 期间释放 bank
 * 锁是为了不让慢磁盘阻塞同一 bank 的其他页访问；buffer 锁保证同一槽不会
 * 同时被两个 I/O 操作使用。
 */
int
SimpleLruReadPage(SlruDesc *ctl, int64 pageno, bool write_ok,
				  const void *opaque_data)
{
	SlruShared	shared = ctl->shared;
	LWLock	   *banklock = SimpleLruGetBankLock(ctl, pageno);

	Assert(LWLockHeldByMeInMode(banklock, LW_EXCLUSIVE));

	/* Outer loop handles restart if we must wait for someone else's I/O */
	for (;;)
	{
		int			slotno;
		bool		ok;

		/* See if page already is in memory; if not, pick victim slot */
		slotno = SlruSelectLRUPage(ctl, pageno);

		/* Did we find the page in memory? */
		if (shared->page_status[slotno] != SLRU_PAGE_EMPTY &&
			shared->page_number[slotno] == pageno)
		{
			/*
			 * If page is still being read in, we must wait for I/O.  Likewise
			 * if the page is being written and the caller said that's not OK.
			 */
			if (shared->page_status[slotno] == SLRU_PAGE_READ_IN_PROGRESS ||
				(shared->page_status[slotno] == SLRU_PAGE_WRITE_IN_PROGRESS &&
				 !write_ok))
			{
				SimpleLruWaitIO(ctl, slotno);
				/* Now we must recheck state from the top */
				continue;
			}
			/* Otherwise, it's ready to use */
			SlruRecentlyUsed(shared, slotno);

			/* update the stats counter of pages found in the SLRU */
			pgstat_count_slru_blocks_hit(shared->slru_stats_idx);

			return slotno;
		}

		/* We found no match; assert we selected a freeable slot */
		Assert(shared->page_status[slotno] == SLRU_PAGE_EMPTY ||
			   (shared->page_status[slotno] == SLRU_PAGE_VALID &&
				!shared->page_dirty[slotno]));

		/* Mark the slot read-busy */
		shared->page_number[slotno] = pageno;
		shared->page_status[slotno] = SLRU_PAGE_READ_IN_PROGRESS;
		shared->page_dirty[slotno] = false;

		/* Acquire per-buffer lock (cannot deadlock, see notes at top) */
		LWLockAcquire(&shared->buffer_locks[slotno].lock, LW_EXCLUSIVE);

		/* Release bank lock while doing I/O */
		LWLockRelease(banklock);

		/* Do the read */
		ok = SlruPhysicalReadPage(ctl, pageno, slotno);

		/* Set the LSNs for this newly read-in page to zero */
		SimpleLruZeroLSNs(ctl, slotno);

		/* Re-acquire bank control lock and update page state */
		LWLockAcquire(banklock, LW_EXCLUSIVE);

		Assert(shared->page_number[slotno] == pageno &&
			   shared->page_status[slotno] == SLRU_PAGE_READ_IN_PROGRESS &&
			   !shared->page_dirty[slotno]);

		shared->page_status[slotno] = ok ? SLRU_PAGE_VALID : SLRU_PAGE_EMPTY;

		LWLockRelease(&shared->buffer_locks[slotno].lock);

		/* Now it's okay to ereport if we failed */
		if (!ok)
			SlruReportIOError(ctl, pageno, opaque_data);

		SlruRecentlyUsed(shared, slotno);

		/* update the stats counter of pages not found in SLRU */
		pgstat_count_slru_blocks_read(shared->slru_stats_idx);

		return slotno;
	}
}

/*
 * Find a page in a shared buffer, reading it in if necessary.
 * The page number must correspond to an already-initialized page.
 * The caller must intend only read-only access to the page.
 *
 * On error, the passed-in 'opaque_data' is passed to the
 * 'errdetail_for_io_error' callback, to provide details on the operation that
 * failed.  It is only used for error reporting.
 *
 * Return value is the shared-buffer slot number now holding the page.
 * The buffer's LRU access info is updated.
 *
 * Bank control lock must NOT be held at entry, but will be held at exit.
 * It is unspecified whether the lock will be shared or exclusive.
 */
/*
 * 中文注释：
 * 只读访问的优化入口：先只持 bank 共享锁，在该 bank 的 16 个槽中线性查找
 * 目标页；若页已在内存且不处于 READ_IN_PROGRESS，则标记 MRU、统计 hit 并
 * 直接返回槽号。返回时 bank 锁仍被持有，但可能是共享锁也可能是排他锁，
 * 调用方必须用 SimpleLruGetBankLock() 取得同一把锁并释放，不能假设锁模式。
 *
 * 若快路径未命中，释放共享锁、改取排他锁，再调用 SimpleLruReadPage() 走
 * 常规的磁盘读入/淘汰路径；因此慢路径返回时持有排他锁。快路径允许返回
 * WRITE_IN_PROGRESS 的页：写 I/O 不会修改页缓冲区内容，只读访问看到的仍是
 * 一致旧内容。多个进程可同时在共享锁下执行 SlruRecentlyUsed()，其近似计数
 * 更新是刻意允许的（见该函数注释）。
 *
 * opaque_data 仅用于 I/O 错误详情；本函数不修改页内容，也不写 WAL。
 */
int
SimpleLruReadPage_ReadOnly(SlruDesc *ctl, int64 pageno, const void *opaque_data)
{
	SlruShared	shared = ctl->shared;
	LWLock	   *banklock = SimpleLruGetBankLock(ctl, pageno);
	int			bankno = pageno % ctl->nbanks;
	int			bankstart = bankno * SLRU_BANK_SIZE;
	int			bankend = bankstart + SLRU_BANK_SIZE;

	/* Try to find the page while holding only shared lock */
	LWLockAcquire(banklock, LW_SHARED);

	/* See if page is already in a buffer */
	for (int slotno = bankstart; slotno < bankend; slotno++)
	{
		if (shared->page_status[slotno] != SLRU_PAGE_EMPTY &&
			shared->page_number[slotno] == pageno &&
			shared->page_status[slotno] != SLRU_PAGE_READ_IN_PROGRESS)
		{
			/* See comments for SlruRecentlyUsed() */
			SlruRecentlyUsed(shared, slotno);

			/* update the stats counter of pages found in the SLRU */
			pgstat_count_slru_blocks_hit(shared->slru_stats_idx);

			return slotno;
		}
	}

	/* No luck, so switch to normal exclusive lock and do regular read */
	LWLockRelease(banklock);
	LWLockAcquire(banklock, LW_EXCLUSIVE);

	return SimpleLruReadPage(ctl, pageno, true, opaque_data);
}

/*
 * Write a page from a shared buffer, if necessary.
 * Does nothing if the specified slot is not dirty.
 *
 * NOTE: only one write attempt is made here.  Hence, it is possible that
 * the page is still dirty at exit (if someone else re-dirtied it during
 * the write).  However, we *do* attempt a fresh write even if the page
 * is already being written; this is for checkpoints.
 *
 * Bank lock must be held at entry, and will be held at exit.
 */
/*
 * 中文注释：
 * 把一个脏的共享缓冲槽写出到磁盘。调用方必须已持有该页所属 bank 的排他锁，
 * 返回时仍持有。fdata 为 NULL 表示独立写；非 NULL 时表示这是
 * SimpleLruWriteAll() 的批量写，可复用 fdata 中已打开的文件描述符，并在
 * 写失败时关闭这些缓存 fd。
 *
 * 步骤：若该槽正在 WRITE_IN_PROGRESS 且页号未变，先调用 SimpleLruWaitIO()
 * 等待（等待会暂时释放 bank 锁）；随后重新检查：页不脏、不是 VALID 或页号
 * 已变则直接返回（可能已被别人写干净或淘汰）。否则置 WRITE_IN_PROGRESS、
 * 清 dirty，获取 buffer 排他锁，释放 bank 锁，调用 SlruPhysicalWritePage()；
 * 失败且处于批量模式时关闭 fdata 中所有 fd；重新获取 bank 锁，断言页号与
 * 状态未变；失败则重新置 dirty，最后置回 VALID，释放 buffer 锁；失败时在
 * 状态恢复后调用 SlruReportIOError() 抛错。
 *
 * 注意：本函数只尝试写一次，且写前清 dirty，因此写盘期间其他后端可以再次
 * 弄脏该页；函数返回时页可能仍是脏的（若失败或被重新弄脏），调用者不能
 * 假设一次写就持久化。fdata 非 NULL 时还会累加 checkpoint 的 SLRU 写统计。
 * 写 I/O 期间不持 bank 锁，避免阻塞同 bank 其他页。
 */
static void
SlruInternalWritePage(SlruDesc *ctl, int slotno, SlruWriteAll fdata)
{
	SlruShared	shared = ctl->shared;
	int64		pageno = shared->page_number[slotno];
	int			bankno = SlotGetBankNumber(slotno);
	bool		ok;

	Assert(shared->page_status[slotno] != SLRU_PAGE_EMPTY);
	Assert(LWLockHeldByMeInMode(SimpleLruGetBankLock(ctl, pageno), LW_EXCLUSIVE));

	/* If a write is in progress, wait for it to finish */
	while (shared->page_status[slotno] == SLRU_PAGE_WRITE_IN_PROGRESS &&
		   shared->page_number[slotno] == pageno)
	{
		SimpleLruWaitIO(ctl, slotno);
	}

	/*
	 * Do nothing if page is not dirty, or if buffer no longer contains the
	 * same page we were called for.
	 */
	if (!shared->page_dirty[slotno] ||
		shared->page_status[slotno] != SLRU_PAGE_VALID ||
		shared->page_number[slotno] != pageno)
		return;

	/*
	 * Mark the slot write-busy, and clear the dirtybit.  After this point, a
	 * transaction status update on this page will mark it dirty again.
	 */
	shared->page_status[slotno] = SLRU_PAGE_WRITE_IN_PROGRESS;
	shared->page_dirty[slotno] = false;

	/* Acquire per-buffer lock (cannot deadlock, see notes at top) */
	LWLockAcquire(&shared->buffer_locks[slotno].lock, LW_EXCLUSIVE);

	/* Release bank lock while doing I/O */
	LWLockRelease(&shared->bank_locks[bankno].lock);

	/* Do the write */
	ok = SlruPhysicalWritePage(ctl, pageno, slotno, fdata);

	/* If we failed, and we're in a flush, better close the files */
	if (!ok && fdata)
	{
		for (int i = 0; i < fdata->num_files; i++)
			CloseTransientFile(fdata->fd[i]);
	}

	/* Re-acquire bank lock and update page state */
	LWLockAcquire(&shared->bank_locks[bankno].lock, LW_EXCLUSIVE);

	Assert(shared->page_number[slotno] == pageno &&
		   shared->page_status[slotno] == SLRU_PAGE_WRITE_IN_PROGRESS);

	/* If we failed to write, mark the page dirty again */
	if (!ok)
		shared->page_dirty[slotno] = true;

	shared->page_status[slotno] = SLRU_PAGE_VALID;

	LWLockRelease(&shared->buffer_locks[slotno].lock);

	/* Now it's okay to ereport if we failed */
	if (!ok)
		SlruReportIOError(ctl, pageno, NULL);

	/* If part of a checkpoint, count this as a SLRU buffer written. */
	if (fdata)
	{
		CheckpointStats.ckpt_slru_written++;
		PendingCheckpointerStats.slru_written++;
	}
}

/*
 * Wrapper of SlruInternalWritePage, for external callers.
 * fdata is always passed a NULL here.
 */
/*
 * 中文注释：
 * 对外暴露的“写出单个槽”封装：调用方必须已持有该槽所属 bank 的排他锁
 * （内部 SlruInternalWritePage() 会断言），且槽不能是 EMPTY。它总是以
 * fdata=NULL 调用内部实现，即独立打开/关闭文件、不参与 SimpleLruWriteAll()
 * 的批量 fd 缓存。若槽不脏则什么也不做；若正被写出则先等待再复查。常用于
 * 刚修改完页后立即持久化（例如 zeropage 重放、NOTIFY 队列推进）以及
 * truncate/delete 前清空缓冲。
 */
void
SimpleLruWritePage(SlruDesc *ctl, int slotno)
{
	Assert(ctl->shared->page_status[slotno] != SLRU_PAGE_EMPTY);

	SlruInternalWritePage(ctl, slotno, NULL);
}

/*
 * Return whether the given page exists on disk.
 *
 * A false return means that either the file does not exist, or that it's not
 * large enough to contain the given page.
 */
/*
 * 中文注释：
 * 判断某个页在磁盘上是否真实存在且文件足够大以覆盖该页。它只检查物理
 * 文件，不读共享缓冲、不加 bank 锁、不修改任何状态；结果是一个可能过期的
 * 快照（其他进程可能同时创建/截断文件），调用方只能把它当作优化/决策
 * 提示，不能用于需要强一致性的判断。
 *
 * 计算 segno/rpageno/offset 后拼接路径，用 OpenTransientFile(O_RDONLY) 打开；
 * ENOENT 直接返回 false（这是正常情况），其他打开错误通过 SlruReportIOError()
 * 报错。用 lseek(SEEK_END) 取文件长度，只有 endpos >= offset+BLCKSZ 才算
 * 存在；lseek 失败同样报错。最后关闭文件，关闭失败时记录错误原因并返回
 * false（此路径不会调用 SlruReportIOError()）。函数会增加“检查页存在”的
 * 统计计数。pg_commit_ts 用它在写入前决定是否需要先清零创建页。
 */
bool
SimpleLruDoesPhysicalPageExist(SlruDesc *ctl, int64 pageno)
{
	int64		segno = pageno / SLRU_PAGES_PER_SEGMENT;
	int			rpageno = pageno % SLRU_PAGES_PER_SEGMENT;
	int			offset = rpageno * BLCKSZ;
	char		path[MAXPGPATH];
	int			fd;
	bool		result;
	off_t		endpos;

	/* update the stats counter of checked pages */
	pgstat_count_slru_blocks_exists(ctl->shared->slru_stats_idx);

	SlruFileName(ctl, path, segno);

	fd = OpenTransientFile(path, O_RDONLY | PG_BINARY);
	if (fd < 0)
	{
		/* expected: file doesn't exist */
		if (errno == ENOENT)
			return false;

		/* report error normally */
		slru_errcause = SLRU_OPEN_FAILED;
		slru_errno = errno;
		SlruReportIOError(ctl, pageno, NULL);
	}

	if ((endpos = lseek(fd, 0, SEEK_END)) < 0)
	{
		slru_errcause = SLRU_SEEK_FAILED;
		slru_errno = errno;
		SlruReportIOError(ctl, pageno, NULL);
	}

	result = endpos >= (off_t) (offset + BLCKSZ);

	if (CloseTransientFile(fd) != 0)
	{
		slru_errcause = SLRU_CLOSE_FAILED;
		slru_errno = errno;
		return false;
	}

	return result;
}

/*
 * Physical read of a (previously existing) page into a buffer slot
 *
 * On failure, we cannot just ereport(ERROR) since caller has put state in
 * shared memory that must be undone.  So, we return false and save enough
 * info in static variables to let SlruReportIOError make the report.
 *
 * For now, assume it's not worth keeping a file pointer open across
 * read/write operations.  We could cache one virtual file pointer ...
 */
/*
 * 中文注释：
 * 物理读：把指定页从 segment 文件的 offset 处读入 shared->page_buffer[slotno]。
 * 调用方必须已持有该槽的 buffer 锁（通常还已释放 bank 锁），这样同一槽不会
 * 有并发 I/O；函数不接触 bank 共享状态，也不加其他锁。成功返回 true；
 * 失败返回 false，并把原因/errno 存入 slru_errcause/slru_errno，由调用方
 * 在恢复共享状态后调用 SlruReportIOError()。
 *
 * 特殊恢复语义：若文件不存在且当前处于 InRecovery，则记录 LOG 并把缓冲区
 * 清零后返回 true。原因是崩溃后可能从较早的 checkpoint 重放，REDO 会要求
 * 更新已经被 truncate 掉的 segment 中的事务状态；把缺失页当作全零
 * （IN_PROGRESS）是安全且幂等的。非恢复期文件缺失则是真实错误。
 *
 * 使用 pg_pread() 从固定偏移读取，避免共享文件偏移；读取不足 BLCKSZ 视为
 * 失败（errno 可能为 0，报告时会说明 read too few bytes）。读取前后设置
 * WAIT_EVENT_SLRU_READ 等待事件，便于 pg_stat_activity 观察。关闭失败也会
 * 返回 false。函数不报告 ERROR、不写 WAL，失败时页缓冲区内容未定义。
 */
static bool
SlruPhysicalReadPage(SlruDesc *ctl, int64 pageno, int slotno)
{
	SlruShared	shared = ctl->shared;
	int64		segno = pageno / SLRU_PAGES_PER_SEGMENT;
	int			rpageno = pageno % SLRU_PAGES_PER_SEGMENT;
	off_t		offset = rpageno * BLCKSZ;
	char		path[MAXPGPATH];
	int			fd;

	SlruFileName(ctl, path, segno);

	/*
	 * In a crash-and-restart situation, it's possible for us to receive
	 * commands to set the commit status of transactions whose bits are in
	 * already-truncated segments of the commit log (see notes in
	 * SlruPhysicalWritePage).  Hence, if we are InRecovery, allow the case
	 * where the file doesn't exist, and return zeroes instead.
	 */
	fd = OpenTransientFile(path, O_RDONLY | PG_BINARY);
	if (fd < 0)
	{
		if (errno != ENOENT || !InRecovery)
		{
			slru_errcause = SLRU_OPEN_FAILED;
			slru_errno = errno;
			return false;
		}

		ereport(LOG,
				(errmsg("file \"%s\" doesn't exist, reading as zeroes",
						path)));
		MemSet(shared->page_buffer[slotno], 0, BLCKSZ);
		return true;
	}

	errno = 0;
	pgstat_report_wait_start(WAIT_EVENT_SLRU_READ);
	if (pg_pread(fd, shared->page_buffer[slotno], BLCKSZ, offset) != BLCKSZ)
	{
		pgstat_report_wait_end();
		slru_errcause = SLRU_READ_FAILED;
		slru_errno = errno;
		CloseTransientFile(fd);
		return false;
	}
	pgstat_report_wait_end();

	if (CloseTransientFile(fd) != 0)
	{
		slru_errcause = SLRU_CLOSE_FAILED;
		slru_errno = errno;
		return false;
	}

	return true;
}

/*
 * Physical write of a page from a buffer slot
 *
 * On failure, we cannot just ereport(ERROR) since caller has put state in
 * shared memory that must be undone.  So, we return false and save enough
 * info in static variables to let SlruReportIOError make the report.
 *
 * For now, assume it's not worth keeping a file pointer open across
 * independent read/write operations.  We do batch operations during
 * SimpleLruWriteAll, though.
 *
 * fdata is NULL for a standalone write, pointer to open-file info during
 * SimpleLruWriteAll.
 */
/*
 * 中文注释：
 * 物理写：把 shared->page_buffer[slotno] 写到指定页对应的文件偏移。调用方
 * 必须已持有该槽的 buffer 锁且已释放 bank 锁；成功返回 true，失败返回
 * false 并在 slru_errcause/slru_errno 中留下原因，由上层恢复共享状态后
 * 统一报错。
 *
 * WAL 规则：若 shared->group_lsn 非空（目前只有 pg_xact），先扫描该页所有
 * LSN 组取最大值；若有效，则在临界区内调用 XLogFlush(max_lsn)。这里不能用
 * elog(ERROR)，因为调用方已在共享内存中把页标为 WRITE_IN_PROGRESS 并清了
 * dirty，若 XLogFlush 失败只能 PANIC，避免留下不一致状态。
 *
 * 文件管理：fdata 非空时先在其中查找已打开的同一 segment fd；否则按需
 * O_RDWR|O_CREAT 打开/创建文件（不能用 O_EXCL/O_TRUNC：多个后端可能同时为
 * 同一文件的不同页创建它，而且恢复时可能写入非首页）。打开后若 fdata 还有
 * 空位就缓存 fd，超过 MAX_WRITEALL_BUFFERS 则退回独立写。用 pg_pwrite()
 * 写入固定偏移；短写且 errno==0 时按 ENOSPC 处理。写成功后通过
 * sync_handler 向 checkpointer 登记 fsync 请求（SYNC_REQUEST）；若队列已满，
 * 则退化为本进程同步 pg_fsync()。独立写最后关闭文件；批量写把 fd 留给
 * SimpleLruWriteAll() 统一关闭。
 *
 * 本函数会增加“写页”统计；不直接 ereport，不删除旧 segment；写失败时
 * 批量模式由调用方关闭所有缓存 fd。
 */
static bool
SlruPhysicalWritePage(SlruDesc *ctl, int64 pageno, int slotno, SlruWriteAll fdata)
{
	SlruShared	shared = ctl->shared;
	int64		segno = pageno / SLRU_PAGES_PER_SEGMENT;
	int			rpageno = pageno % SLRU_PAGES_PER_SEGMENT;
	off_t		offset = rpageno * BLCKSZ;
	char		path[MAXPGPATH];
	int			fd = -1;

	/* update the stats counter of written pages */
	pgstat_count_slru_blocks_written(shared->slru_stats_idx);

	/*
	 * Honor the write-WAL-before-data rule, if appropriate, so that we do not
	 * write out data before associated WAL records.  This is the same action
	 * performed during FlushBuffer() in the main buffer manager.
	 */
	if (shared->group_lsn != NULL)
	{
		/*
		 * We must determine the largest async-commit LSN for the page. This
		 * is a bit tedious, but since this entire function is a slow path
		 * anyway, it seems better to do this here than to maintain a per-page
		 * LSN variable (which'd need an extra comparison in the
		 * transaction-commit path).
		 */
		XLogRecPtr	max_lsn;
		int			lsnindex;

		lsnindex = slotno * shared->lsn_groups_per_page;
		max_lsn = shared->group_lsn[lsnindex++];
		for (int lsnoff = 1; lsnoff < shared->lsn_groups_per_page; lsnoff++)
		{
			XLogRecPtr	this_lsn = shared->group_lsn[lsnindex++];

			if (max_lsn < this_lsn)
				max_lsn = this_lsn;
		}

		if (XLogRecPtrIsValid(max_lsn))
		{
			/*
			 * As noted above, elog(ERROR) is not acceptable here, so if
			 * XLogFlush were to fail, we must PANIC.  This isn't much of a
			 * restriction because XLogFlush is just about all critical
			 * section anyway, but let's make sure.
			 */
			START_CRIT_SECTION();
			XLogFlush(max_lsn);
			END_CRIT_SECTION();
		}
	}

	/*
	 * During a SimpleLruWriteAll, we may already have the desired file open.
	 */
	if (fdata)
	{
		for (int i = 0; i < fdata->num_files; i++)
		{
			if (fdata->segno[i] == segno)
			{
				fd = fdata->fd[i];
				break;
			}
		}
	}

	if (fd < 0)
	{
		/*
		 * If the file doesn't already exist, we should create it.  It is
		 * possible for this to need to happen when writing a page that's not
		 * first in its segment; we assume the OS can cope with that. (Note:
		 * it might seem that it'd be okay to create files only when
		 * SimpleLruZeroPage is called for the first page of a segment.
		 * However, if after a crash and restart the REDO logic elects to
		 * replay the log from a checkpoint before the latest one, then it's
		 * possible that we will get commands to set transaction status of
		 * transactions that have already been truncated from the commit log.
		 * Easiest way to deal with that is to accept references to
		 * nonexistent files here and in SlruPhysicalReadPage.)
		 *
		 * Note: it is possible for more than one backend to be executing this
		 * code simultaneously for different pages of the same file. Hence,
		 * don't use O_EXCL or O_TRUNC or anything like that.
		 */
		SlruFileName(ctl, path, segno);
		fd = OpenTransientFile(path, O_RDWR | O_CREAT | PG_BINARY);
		if (fd < 0)
		{
			slru_errcause = SLRU_OPEN_FAILED;
			slru_errno = errno;
			return false;
		}

		if (fdata)
		{
			if (fdata->num_files < MAX_WRITEALL_BUFFERS)
			{
				fdata->fd[fdata->num_files] = fd;
				fdata->segno[fdata->num_files] = segno;
				fdata->num_files++;
			}
			else
			{
				/*
				 * In the unlikely event that we exceed MAX_WRITEALL_BUFFERS,
				 * fall back to treating it as a standalone write.
				 */
				fdata = NULL;
			}
		}
	}

	errno = 0;
	pgstat_report_wait_start(WAIT_EVENT_SLRU_WRITE);
	if (pg_pwrite(fd, shared->page_buffer[slotno], BLCKSZ, offset) != BLCKSZ)
	{
		pgstat_report_wait_end();
		/* if write didn't set errno, assume problem is no disk space */
		if (errno == 0)
			errno = ENOSPC;
		slru_errcause = SLRU_WRITE_FAILED;
		slru_errno = errno;
		if (!fdata)
			CloseTransientFile(fd);
		return false;
	}
	pgstat_report_wait_end();

	/* Queue up a sync request for the checkpointer. */
	if (ctl->options.sync_handler != SYNC_HANDLER_NONE)
	{
		FileTag		tag;

		INIT_SLRUFILETAG(tag, ctl->options.sync_handler, segno);
		if (!RegisterSyncRequest(&tag, SYNC_REQUEST, false))
		{
			/* No space to enqueue sync request.  Do it synchronously. */
			pgstat_report_wait_start(WAIT_EVENT_SLRU_SYNC);
			if (pg_fsync(fd) != 0)
			{
				pgstat_report_wait_end();
				slru_errcause = SLRU_FSYNC_FAILED;
				slru_errno = errno;
				CloseTransientFile(fd);
				return false;
			}
			pgstat_report_wait_end();
		}
	}

	/* Close file, unless part of flush request. */
	if (!fdata)
	{
		if (CloseTransientFile(fd) != 0)
		{
			slru_errcause = SLRU_CLOSE_FAILED;
			slru_errno = errno;
			return false;
		}
	}

	return true;
}

/*
 * Issue the error message after failure of SlruPhysicalReadPage or
 * SlruPhysicalWritePage.  Call this after cleaning up shared-memory state.
 */
/*
 * 中文注释：
 * 把 SLRU 物理读/写失败的底层错误转换成用户可读的 ERROR 报告。
 *
 * SlruPhysicalReadPage/SlruPhysicalWritePage 在失败时只记录全局的 slru_errcause
 * 和 slru_errno，并清理共享内存状态；本函数根据错误原因（open/seek/read/write/
 * fsync/close）生成对应的错误消息，包含段文件路径、段内偏移和可选的对象信息。
 * opaque_data 由具体 SLRU 的 errdetail_for_io_error 回调解释（例如 XID、MultiXact
 * 成员等），从而在不污染通用 SLRU 层的前提下给出业务语义。必须在释放相关锁之后
 * 调用，因为 ereport(ERROR) 会进行长跳转。
 */
static void
SlruReportIOError(SlruDesc *ctl, int64 pageno, const void *opaque_data)
{
	int64		segno = pageno / SLRU_PAGES_PER_SEGMENT;
	int			rpageno = pageno % SLRU_PAGES_PER_SEGMENT;
	int			offset = rpageno * BLCKSZ;
	char		path[MAXPGPATH];

	SlruFileName(ctl, path, segno);
	errno = slru_errno;
	switch (slru_errcause)
	{
		case SLRU_OPEN_FAILED:
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\": %m", path),
					 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			break;
		case SLRU_SEEK_FAILED:
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not seek in file \"%s\" to offset %d: %m",
							path, offset),
					 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			break;
		case SLRU_READ_FAILED:
			if (errno)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("could not read from file \"%s\" at offset %d: %m",
								path, offset),
						 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			else
				ereport(ERROR,
						(errmsg("could not read from file \"%s\" at offset %d: read too few bytes",
								path, offset),
						 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			break;
		case SLRU_WRITE_FAILED:
			if (errno)
				ereport(ERROR,
						(errcode_for_file_access(),
						 errmsg("Could not write to file \"%s\" at offset %d: %m",
								path, offset),
						 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			else
				ereport(ERROR,
						(errmsg("Could not write to file \"%s\" at offset %d: wrote too few bytes.",
								path, offset),
						 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			break;
		case SLRU_FSYNC_FAILED:
			ereport(data_sync_elevel(ERROR),
					(errcode_for_file_access(),
					 errmsg("could not fsync file \"%s\": %m",
							path),
					 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			break;
		case SLRU_CLOSE_FAILED:
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not close file \"%s\": %m",
							path),
					 opaque_data ? ctl->options.errdetail_for_io_error(opaque_data) : 0));
			break;
		default:
			/* can't get here, we trust */
			elog(ERROR, "unrecognized SimpleLru error cause: %d",
				 (int) slru_errcause);
			break;
	}
}

/*
 * Mark a buffer slot "most recently used".
 */
/*
 * 中文注释：
 * 把一个 buffer 槽标记为“最近使用”，用于 SLRU 的近似 LRU 淘汰。
 *
 * 每个 bank 维护一个单调递增的 bank_cur_lru_count，页槽保存自己最后一次被访问时
 * 的计数；计数越大表示越新。这里不是简单地每次加一，而是仅当页槽计数与当前计数
 * 不同时才更新，避免对同一热页的连续访问快速耗尽计数空间、造成回绕后“旧页变新页”。
 * SimpleLruReadPage_ReadOnly 允许多个进程并发调用本函数，因此读改写不是原子的；
 * 最坏情况只是计数暂时偏小或淘汰选择不够优，不会破坏正确性。
 */
static inline void
SlruRecentlyUsed(SlruShared shared, int slotno)
{
	int			bankno = SlotGetBankNumber(slotno);
	int			new_lru_count = shared->bank_cur_lru_count[bankno];

	Assert(shared->page_status[slotno] != SLRU_PAGE_EMPTY);

	/*
	 * The reason for the if-test is that there are often many consecutive
	 * accesses to the same page (particularly the latest page).  By
	 * suppressing useless increments of bank_cur_lru_count, we reduce the
	 * probability that old pages' counts will "wrap around" and make them
	 * appear recently used.
	 *
	 * We allow this code to be executed concurrently by multiple processes
	 * within SimpleLruReadPage_ReadOnly().  As long as int reads and writes
	 * are atomic, this should not cause any completely-bogus values to enter
	 * the computation.  However, it is possible for either bank_cur_lru_count
	 * or individual page_lru_count entries to be "reset" to lower values than
	 * they should have, in case a process is delayed while it executes this
	 * function.  With care in SlruSelectLRUPage(), this does little harm, and
	 * in any case the absolute worst possible consequence is a nonoptimal
	 * choice of page to evict.  The gain from allowing concurrent reads of
	 * SLRU pages seems worth it.
	 */
	if (new_lru_count != shared->page_lru_count[slotno])
	{
		shared->bank_cur_lru_count[bankno] = ++new_lru_count;
		shared->page_lru_count[slotno] = new_lru_count;
	}
}

/*
 * Select the slot to re-use when we need a free slot for the given page.
 *
 * The target page number is passed not only because we need to know the
 * correct bank to use, but also because we need to consider the possibility
 * that some other process reads in the target page while we are doing I/O to
 * free a slot.  Hence, check or recheck to see if any slot already holds the
 * target page, and return that slot if so.  Thus, the returned slot is
 * *either* a slot already holding the pageno (could be any state except
 * EMPTY), *or* a freeable slot (state EMPTY or CLEAN).
 *
 * The correct bank lock must be held at entry, and will be held at exit.
 */
/*
 * 中文注释：
 * 为指定页号选择一个可用的 buffer 槽，是 SLRU 缓存淘汰策略的核心。
 *
 * 调用者必须持有该页所属 bank 的锁。函数先检查目标页是否已经在某个槽中（可能被
 * 其他进程刚刚读入），有则直接返回；否则寻找 EMPTY 槽。若没有空槽，则在
 * SLRU_PAGE_VALID（干净或脏）的页中选择 LRU 受害者，但永不淘汰
 * latest_page_number（最近分配的页，通常是正在增长的最新页）。若所有候选都在
 * I/O 中，则等待最久未使用的 I/O 槽完成，然后重新扫描；若选中的受害者是脏页，
 * 先写回再重试。并发下多个页可能有相同 lru_count，此时用 PagePrecedes 选择更靠后
 * 的页作为平局裁决。返回值要么是已持有目标页的槽，要么是可回收的 EMPTY/CLEAN 槽。
 */
static int
SlruSelectLRUPage(SlruDesc *ctl, int64 pageno)
{
	SlruShared	shared = ctl->shared;

	/* Outer loop handles restart after I/O */
	for (;;)
	{
		int			cur_count;
		int			bestvalidslot = 0;	/* keep compiler quiet */
		int			best_valid_delta = -1;
		int64		best_valid_page_number = 0; /* keep compiler quiet */
		int			bestinvalidslot = 0;	/* keep compiler quiet */
		int			best_invalid_delta = -1;
		int64		best_invalid_page_number = 0;	/* keep compiler quiet */
		int			bankno = pageno % ctl->nbanks;
		int			bankstart = bankno * SLRU_BANK_SIZE;
		int			bankend = bankstart + SLRU_BANK_SIZE;

		Assert(LWLockHeldByMe(SimpleLruGetBankLock(ctl, pageno)));

		/* See if page already has a buffer assigned */
		for (int slotno = bankstart; slotno < bankend; slotno++)
		{
			if (shared->page_status[slotno] != SLRU_PAGE_EMPTY &&
				shared->page_number[slotno] == pageno)
				return slotno;
		}

		/*
		 * If we find any EMPTY slot, just select that one. Else choose a
		 * victim page to replace.  We normally take the least recently used
		 * valid page, but we will never take the slot containing
		 * latest_page_number, even if it appears least recently used.  We
		 * will select a slot that is already I/O busy only if there is no
		 * other choice: a read-busy slot will not be least recently used once
		 * the read finishes, and waiting for an I/O on a write-busy slot is
		 * inferior to just picking some other slot.  Testing shows the slot
		 * we pick instead will often be clean, allowing us to begin a read at
		 * once.
		 *
		 * Normally the page_lru_count values will all be different and so
		 * there will be a well-defined LRU page.  But since we allow
		 * concurrent execution of SlruRecentlyUsed() within
		 * SimpleLruReadPage_ReadOnly(), it is possible that multiple pages
		 * acquire the same lru_count values.  In that case we break ties by
		 * choosing the furthest-back page.
		 *
		 * Notice that this next line forcibly advances cur_lru_count to a
		 * value that is certainly beyond any value that will be in the
		 * page_lru_count array after the loop finishes.  This ensures that
		 * the next execution of SlruRecentlyUsed will mark the page newly
		 * used, even if it's for a page that has the current counter value.
		 * That gets us back on the path to having good data when there are
		 * multiple pages with the same lru_count.
		 */
		cur_count = (shared->bank_cur_lru_count[bankno])++;
		for (int slotno = bankstart; slotno < bankend; slotno++)
		{
			int			this_delta;
			int64		this_page_number;

			if (shared->page_status[slotno] == SLRU_PAGE_EMPTY)
				return slotno;

			this_delta = cur_count - shared->page_lru_count[slotno];
			if (this_delta < 0)
			{
				/*
				 * Clean up in case shared updates have caused cur_count
				 * increments to get "lost".  We back off the page counts,
				 * rather than trying to increase cur_count, to avoid any
				 * question of infinite loops or failure in the presence of
				 * wrapped-around counts.
				 */
				shared->page_lru_count[slotno] = cur_count;
				this_delta = 0;
			}

			/*
			 * If this page is the one most recently zeroed, don't consider it
			 * an eviction candidate. See comments in SimpleLruZeroPage for an
			 * explanation about the lack of a memory barrier here.
			 */
			this_page_number = shared->page_number[slotno];
			if (this_page_number ==
				pg_atomic_read_u64(&shared->latest_page_number))
				continue;

			if (shared->page_status[slotno] == SLRU_PAGE_VALID)
			{
				if (this_delta > best_valid_delta ||
					(this_delta == best_valid_delta &&
					 ctl->options.PagePrecedes(this_page_number,
											   best_valid_page_number)))
				{
					bestvalidslot = slotno;
					best_valid_delta = this_delta;
					best_valid_page_number = this_page_number;
				}
			}
			else
			{
				if (this_delta > best_invalid_delta ||
					(this_delta == best_invalid_delta &&
					 ctl->options.PagePrecedes(this_page_number,
											   best_invalid_page_number)))
				{
					bestinvalidslot = slotno;
					best_invalid_delta = this_delta;
					best_invalid_page_number = this_page_number;
				}
			}
		}

		/*
		 * If all pages (except possibly the latest one) are I/O busy, we'll
		 * have to wait for an I/O to complete and then retry.  In that
		 * unhappy case, we choose to wait for the I/O on the least recently
		 * used slot, on the assumption that it was likely initiated first of
		 * all the I/Os in progress and may therefore finish first.
		 */
		if (best_valid_delta < 0)
		{
			SimpleLruWaitIO(ctl, bestinvalidslot);
			continue;
		}

		/*
		 * If the selected page is clean, we're set.
		 */
		if (!shared->page_dirty[bestvalidslot])
			return bestvalidslot;

		/*
		 * Write the page.
		 */
		SlruInternalWritePage(ctl, bestvalidslot, NULL);

		/*
		 * Now loop back and try again.  This is the easiest way of dealing
		 * with corner cases such as the victim page being re-dirtied while we
		 * wrote it.
		 */
	}
}

/*
 * Write dirty pages to disk during checkpoint or database shutdown.  Flushing
 * is deferred until the next call to ProcessSyncRequests(), though we do fsync
 * the containing directory here to make sure that newly created directory
 * entries are on disk.
 */
/*
 * 中文注释：
 * 在 checkpoint 或数据库关闭时把某个 SLRU 的所有脏页写回磁盘。
 *
 * 函数按 bank 逐个加排他锁，遍历所有槽并调用 SlruInternalWritePage；为了减少
 * fsync 次数，写文件句柄会收集到 SlruWriteAllData 中，最后统一关闭并交给
 * checkpointer 的同步请求机制处理。allow_redirtied 允许在写回过程中其他进程再次
 * 弄脏页面（checkpoint 场景常见），因此不能断言所有槽最终都是干净的。最后对目录
 * 执行 fsync，确保新建段文件的目录项也持久化。该函数不负责删除旧段。
 */
void
SimpleLruWriteAll(SlruDesc *ctl, bool allow_redirtied)
{
	SlruShared	shared = ctl->shared;
	SlruWriteAllData fdata;
	int64		pageno = 0;
	int			prevbank = SlotGetBankNumber(0);
	bool		ok;

	/* update the stats counter of flushes */
	pgstat_count_slru_flush(shared->slru_stats_idx);

	/*
	 * Find and write dirty pages
	 */
	fdata.num_files = 0;

	LWLockAcquire(&shared->bank_locks[prevbank].lock, LW_EXCLUSIVE);

	for (int slotno = 0; slotno < shared->num_slots; slotno++)
	{
		int			curbank = SlotGetBankNumber(slotno);

		/*
		 * If the current bank lock is not same as the previous bank lock then
		 * release the previous lock and acquire the new lock.
		 */
		if (curbank != prevbank)
		{
			LWLockRelease(&shared->bank_locks[prevbank].lock);
			LWLockAcquire(&shared->bank_locks[curbank].lock, LW_EXCLUSIVE);
			prevbank = curbank;
		}

		/* Do nothing if slot is unused */
		if (shared->page_status[slotno] == SLRU_PAGE_EMPTY)
			continue;

		SlruInternalWritePage(ctl, slotno, &fdata);

		/*
		 * In some places (e.g. checkpoints), we cannot assert that the slot
		 * is clean now, since another process might have re-dirtied it
		 * already.  That's okay.
		 */
		Assert(allow_redirtied ||
			   shared->page_status[slotno] == SLRU_PAGE_EMPTY ||
			   (shared->page_status[slotno] == SLRU_PAGE_VALID &&
				!shared->page_dirty[slotno]));
	}

	LWLockRelease(&shared->bank_locks[prevbank].lock);

	/*
	 * Now close any files that were open
	 */
	ok = true;
	for (int i = 0; i < fdata.num_files; i++)
	{
		if (CloseTransientFile(fdata.fd[i]) != 0)
		{
			slru_errcause = SLRU_CLOSE_FAILED;
			slru_errno = errno;
			pageno = fdata.segno[i] * SLRU_PAGES_PER_SEGMENT;
			ok = false;
		}
	}
	if (!ok)
		SlruReportIOError(ctl, pageno, NULL);

	/* Ensure that directory entries for new files are on disk. */
	if (ctl->options.sync_handler != SYNC_HANDLER_NONE)
		fsync_fname(ctl->options.Dir, true);
}

/*
 * Remove all segments before the one holding the passed page number
 *
 * All SLRUs prevent concurrent calls to this function, either with an LWLock
 * or by calling it only as part of a checkpoint.  Mutual exclusion must begin
 * before computing cutoffPage.  Mutual exclusion must end after any limit
 * update that would permit other backends to write fresh data into the
 * segment immediately preceding the one containing cutoffPage.  Otherwise,
 * when the SLRU is quite full, SimpleLruTruncate() might delete that segment
 * after it has accrued freshly-written data.
 */
/*
 * 中文注释：
 * 删除 cutoffPage 之前的所有 SLRU 段文件，并清理共享内存中对应的页。
 *
 * 调用者必须保证同一 SLRU 的截断互斥（通常用 LWLock 或在 checkpoint 中串行调用），
 * 且互斥范围要覆盖“计算 cutoffPage -> 清理缓存 -> 删除文件 -> 更新限制”的全过程，
 * 否则可能删掉刚被其他后端写入新数据的段。
 *
 * 流程：
 *   1. 安全检查 latest_page_number 不能先于 cutoffPage，防止回绕错误导致误删；
 *   2. 逐 bank 扫描槽：cutoff 之前的干净页直接置 EMPTY；脏页先写回；正在 I/O 的
 *      页等待完成；由于 I/O 会释放锁，处理后需要 restart 重新扫描；
 *   3. 缓存清理完后，用 SlruScanDirectory 删除满足条件的旧段。
 * 这里的“之前”由具体 SLRU 的 PagePrecedes 回调定义，必须正确处理 32 位回绕。
 */
void
SimpleLruTruncate(SlruDesc *ctl, int64 cutoffPage)
{
	SlruShared	shared = ctl->shared;
	int			prevbank;

	/* update the stats counter of truncates */
	pgstat_count_slru_truncate(shared->slru_stats_idx);

	/*
	 * Scan shared memory and remove any pages preceding the cutoff page, to
	 * ensure we won't rewrite them later.  (Since this is normally called in
	 * or just after a checkpoint, any dirty pages should have been flushed
	 * already ... we're just being extra careful here.)
	 */
restart:

	/*
	 * An important safety check: the current endpoint page must not be
	 * eligible for removal.  This check is just a backstop against wraparound
	 * bugs elsewhere in SLRU handling, so we don't care if we read a slightly
	 * outdated value; therefore we don't add a memory barrier.
	 */
	if (ctl->options.PagePrecedes(pg_atomic_read_u64(&shared->latest_page_number),
								  cutoffPage))
	{
		ereport(LOG,
				(errmsg("could not truncate directory \"%s\": apparent wraparound",
						ctl->options.Dir)));
		return;
	}

	prevbank = SlotGetBankNumber(0);
	LWLockAcquire(&shared->bank_locks[prevbank].lock, LW_EXCLUSIVE);
	for (int slotno = 0; slotno < shared->num_slots; slotno++)
	{
		int			curbank = SlotGetBankNumber(slotno);

		/*
		 * If the current bank lock is not same as the previous bank lock then
		 * release the previous lock and acquire the new lock.
		 */
		if (curbank != prevbank)
		{
			LWLockRelease(&shared->bank_locks[prevbank].lock);
			LWLockAcquire(&shared->bank_locks[curbank].lock, LW_EXCLUSIVE);
			prevbank = curbank;
		}

		if (shared->page_status[slotno] == SLRU_PAGE_EMPTY)
			continue;
		if (!ctl->options.PagePrecedes(shared->page_number[slotno], cutoffPage))
			continue;

		/*
		 * If page is clean, just change state to EMPTY (expected case).
		 */
		if (shared->page_status[slotno] == SLRU_PAGE_VALID &&
			!shared->page_dirty[slotno])
		{
			shared->page_status[slotno] = SLRU_PAGE_EMPTY;
			continue;
		}

		/*
		 * Hmm, we have (or may have) I/O operations acting on the page, so
		 * we've got to wait for them to finish and then start again. This is
		 * the same logic as in SlruSelectLRUPage.  (XXX if page is dirty,
		 * wouldn't it be OK to just discard it without writing it?
		 * SlruMayDeleteSegment() uses a stricter qualification, so we might
		 * not delete this page in the end; even if we don't delete it, we
		 * won't have cause to read its data again.  For now, keep the logic
		 * the same as it was.)
		 */
		if (shared->page_status[slotno] == SLRU_PAGE_VALID)
			SlruInternalWritePage(ctl, slotno, NULL);
		else
			SimpleLruWaitIO(ctl, slotno);

		LWLockRelease(&shared->bank_locks[prevbank].lock);
		goto restart;
	}

	LWLockRelease(&shared->bank_locks[prevbank].lock);

	/* Now we can remove the old segment(s) */
	(void) SlruScanDirectory(ctl, SlruScanDirCbDeleteCutoff, &cutoffPage);
}

/*
 * Delete an individual SLRU segment.
 *
 * NB: This does not touch the SLRU buffers themselves, callers have to ensure
 * they either can't yet contain anything, or have already been cleaned out.
 */
/*
 * 中文注释：
 * 删除单个 SLRU 段文件（按段号），不触碰共享内存中的 buffer。
 *
 * 调用者必须确保该段对应的页已经不可能再被访问，或已经被清理/写回；本函数只做两件
 * 事：向 sync 机制注销该段的待同步请求（避免 checkpointer 之后又去 fsync 一个已删除
 * 的文件），然后 unlink 段文件。路径由 SlruFileName 按具体 SLRU 的目录和命名规则
 * 生成。删除失败只记 DEBUG2，因为文件可能已被其他路径删除。
 */
static void
SlruInternalDeleteSegment(SlruDesc *ctl, int64 segno)
{
	char		path[MAXPGPATH];

	/* Forget any fsync requests queued for this segment. */
	if (ctl->options.sync_handler != SYNC_HANDLER_NONE)
	{
		FileTag		tag;

		INIT_SLRUFILETAG(tag, ctl->options.sync_handler, segno);
		RegisterSyncRequest(&tag, SYNC_FORGET_REQUEST, true);
	}

	/* Unlink the file. */
	SlruFileName(ctl, path, segno);
	ereport(DEBUG2, (errmsg_internal("removing file \"%s\"", path)));
	unlink(path);
}

/*
 * Delete an individual SLRU segment, identified by the segment number.
 */
/*
 * 中文注释：
 * 安全删除一个指定段号的 SLRU 段：先清理共享内存中的相关页，再删除文件。
 *
 * 与 SlruInternalDeleteSegment 不同，本函数可以被外部调用（例如两阶段提交清理）。
 * 它逐 bank 加排他锁扫描所有槽，找出属于目标段的页：干净页直接置 EMPTY；脏页写回；
 * 正在 I/O 的页等待完成。由于 I/O 函数会临时释放 bank 锁，期间可能有新页被读入，
 * 因此只要本轮处理过任何页（did_write）就 restart 再扫描一遍，直到确认没有残留。
 * 最后调用 SlruInternalDeleteSegment 删除文件并释放锁。
 */
void
SlruDeleteSegment(SlruDesc *ctl, int64 segno)
{
	SlruShared	shared = ctl->shared;
	int			prevbank = SlotGetBankNumber(0);
	bool		did_write;

	/* Clean out any possibly existing references to the segment. */
	LWLockAcquire(&shared->bank_locks[prevbank].lock, LW_EXCLUSIVE);
restart:
	did_write = false;
	for (int slotno = 0; slotno < shared->num_slots; slotno++)
	{
		int64		pagesegno;
		int			curbank = SlotGetBankNumber(slotno);

		/*
		 * If the current bank lock is not same as the previous bank lock then
		 * release the previous lock and acquire the new lock.
		 */
		if (curbank != prevbank)
		{
			LWLockRelease(&shared->bank_locks[prevbank].lock);
			LWLockAcquire(&shared->bank_locks[curbank].lock, LW_EXCLUSIVE);
			prevbank = curbank;
		}

		if (shared->page_status[slotno] == SLRU_PAGE_EMPTY)
			continue;

		pagesegno = shared->page_number[slotno] / SLRU_PAGES_PER_SEGMENT;
		/* not the segment we're looking for */
		if (pagesegno != segno)
			continue;

		/* If page is clean, just change state to EMPTY (expected case). */
		if (shared->page_status[slotno] == SLRU_PAGE_VALID &&
			!shared->page_dirty[slotno])
		{
			shared->page_status[slotno] = SLRU_PAGE_EMPTY;
			continue;
		}

		/* Same logic as SimpleLruTruncate() */
		if (shared->page_status[slotno] == SLRU_PAGE_VALID)
			SlruInternalWritePage(ctl, slotno, NULL);
		else
			SimpleLruWaitIO(ctl, slotno);

		did_write = true;
	}

	/*
	 * Be extra careful and re-check. The IO functions release the control
	 * lock, so new pages could have been read in.
	 */
	if (did_write)
		goto restart;

	SlruInternalDeleteSegment(ctl, segno);

	LWLockRelease(&shared->bank_locks[prevbank].lock);
}

/*
 * Determine whether a segment is okay to delete.
 *
 * segpage is the first page of the segment, and cutoffPage is the oldest (in
 * PagePrecedes order) page in the SLRU containing still-useful data.  Since
 * every core PagePrecedes callback implements "wrap around", check the
 * segment's first and last pages:
 *
 * first<cutoff  && last<cutoff:  yes
 * first<cutoff  && last>=cutoff: no; cutoff falls inside this segment
 * first>=cutoff && last<cutoff:  no; wrap point falls inside this segment
 * first>=cutoff && last>=cutoff: no; every page of this segment is too young
 */
/*
 * 中文注释：
 * 判断一个 SLRU 段是否可以安全删除。
 *
 * segpage 是段的第一页，cutoffPage 是仍含有有用数据的最老页（按 PagePrecedes 顺序）。
 * 由于核心 SLRU 的 PagePrecedes 都实现了 32 位回绕，不能只比较段首：必须同时满足
 * 段首页和段末页都先于 cutoffPage，才能保证整个段都在 cutoff 之前。否则要么 cutoff
 * 落在段内部，要么回绕点落在段内部，删除都会丢失仍需要的数据。该函数是
 * SlruScanDirCbDeleteCutoff 和 SlruScanDirCbReportPresence 的共同判据。
 */
static bool
SlruMayDeleteSegment(SlruDesc *ctl, int64 segpage, int64 cutoffPage)
{
	int64		seg_last_page = segpage + SLRU_PAGES_PER_SEGMENT - 1;

	Assert(segpage % SLRU_PAGES_PER_SEGMENT == 0);

	return (ctl->options.PagePrecedes(segpage, cutoffPage) &&
			ctl->options.PagePrecedes(seg_last_page, cutoffPage));
}

#ifdef USE_ASSERT_CHECKING
/*
 * 中文注释：
 * PagePrecedes 回调的单元测试辅助函数，针对页内某个偏移量验证回绕比较逻辑。
 *
 * 测试构造一对在 32 位 XID 空间中“互为前后”的值（相差 2^31），验证具体 SLRU 的
 * PagePrecedes 在回绕点附近仍能给出正确顺序；然后构造“最新 XID 位于某段最后一页/
 * 第一页”的边界场景，确认 SlruMayDeleteSegment 不会误删仍含有效数据的段。per_page
 * 表示每页容纳多少个键，offset 是该页内的偏移。仅在 USE_ASSERT_CHECKING 构建中
 * 编译，用于启动时自检各 SLRU 的页优先级实现。
 */
static void
SlruPagePrecedesTestOffset(SlruDesc *ctl, int per_page, uint32 offset)
{
	TransactionId lhs,
				rhs;
	int64		newestPage,
				oldestPage;
	TransactionId newestXact,
				oldestXact;

	/* This must be called after the Slru has been initialized */
	Assert(ctl->options.PagePrecedes);

	/*
	 * Compare an XID pair having undefined order (see RFC 1982), a pair at
	 * "opposite ends" of the XID space.  TransactionIdPrecedes() treats each
	 * as preceding the other.  If RHS is oldestXact, LHS is the first XID we
	 * must not assign.
	 */
	lhs = per_page + offset;	/* skip first page to avoid non-normal XIDs */
	rhs = lhs + (1U << 31);
	Assert(TransactionIdPrecedes(lhs, rhs));
	Assert(TransactionIdPrecedes(rhs, lhs));
	Assert(!TransactionIdPrecedes(lhs - 1, rhs));
	Assert(TransactionIdPrecedes(rhs, lhs - 1));
	Assert(TransactionIdPrecedes(lhs + 1, rhs));
	Assert(!TransactionIdPrecedes(rhs, lhs + 1));
	Assert(!TransactionIdFollowsOrEquals(lhs, rhs));
	Assert(!TransactionIdFollowsOrEquals(rhs, lhs));
	Assert(!ctl->options.PagePrecedes(lhs / per_page, lhs / per_page));
	Assert(!ctl->options.PagePrecedes(lhs / per_page, rhs / per_page));
	Assert(!ctl->options.PagePrecedes(rhs / per_page, lhs / per_page));
	Assert(!ctl->options.PagePrecedes((lhs - per_page) / per_page, rhs / per_page));
	Assert(ctl->options.PagePrecedes(rhs / per_page, (lhs - 3 * per_page) / per_page));
	Assert(ctl->options.PagePrecedes(rhs / per_page, (lhs - 2 * per_page) / per_page));
	Assert(ctl->options.PagePrecedes(rhs / per_page, (lhs - 1 * per_page) / per_page)
		   || (1U << 31) % per_page != 0);	/* See CommitTsPagePrecedes() */
	Assert(ctl->options.PagePrecedes((lhs + 1 * per_page) / per_page, rhs / per_page)
		   || (1U << 31) % per_page != 0);
	Assert(ctl->options.PagePrecedes((lhs + 2 * per_page) / per_page, rhs / per_page));
	Assert(ctl->options.PagePrecedes((lhs + 3 * per_page) / per_page, rhs / per_page));
	Assert(!ctl->options.PagePrecedes(rhs / per_page, (lhs + per_page) / per_page));

	/*
	 * GetNewTransactionId() has assigned the last XID it can safely use, and
	 * that XID is in the *LAST* page of the second segment.  We must not
	 * delete that segment.
	 */
	newestPage = 2 * SLRU_PAGES_PER_SEGMENT - 1;
	newestXact = newestPage * per_page + offset;
	Assert(newestXact / per_page == newestPage);
	oldestXact = newestXact + 1;
	oldestXact -= 1U << 31;
	oldestPage = oldestXact / per_page;
	Assert(!SlruMayDeleteSegment(ctl,
								 (newestPage -
								  newestPage % SLRU_PAGES_PER_SEGMENT),
								 oldestPage));

	/*
	 * GetNewTransactionId() has assigned the last XID it can safely use, and
	 * that XID is in the *FIRST* page of the second segment.  We must not
	 * delete that segment.
	 */
	newestPage = SLRU_PAGES_PER_SEGMENT;
	newestXact = newestPage * per_page + offset;
	Assert(newestXact / per_page == newestPage);
	oldestXact = newestXact + 1;
	oldestXact -= 1U << 31;
	oldestPage = oldestXact / per_page;
	Assert(!SlruMayDeleteSegment(ctl,
								 (newestPage -
								  newestPage % SLRU_PAGES_PER_SEGMENT),
								 oldestPage));
}

/*
 * Unit-test a PagePrecedes function.
 *
 * This assumes every uint32 >= FirstNormalTransactionId is a valid key.  It
 * assumes each value occupies a contiguous, fixed-size region of SLRU bytes.
 * (MultiXactMemberCtl separates flags from XIDs.  NotifyCtl has
 * variable-length entries, no keys, and no random access.  These unit tests
 * do not apply to them.)
 */
/*
 * 中文注释：
 * 对某个 SLRU 的 PagePrecedes 回调运行一组单元测试。
 *
 * 分别取每页的第一个、中间和最后一个键作为偏移，调用
 * SlruPagePrecedesTestOffset 验证回绕边界。适用于“每个 uint32 键占固定大小、可随机
 * 访问”的 SLRU（如 CLOG、SUBTRANS、COMMIT_TS、MULTIXACT）；不适用于 MultiXact
 * 成员（flags 与 XID 分离）和 Notify（变长、无键）等特殊 SLRU。
 */
void
SlruPagePrecedesUnitTests(SlruDesc *ctl, int per_page)
{
	/* Test first, middle and last entries of a page. */
	SlruPagePrecedesTestOffset(ctl, per_page, 0);
	SlruPagePrecedesTestOffset(ctl, per_page, per_page / 2);
	SlruPagePrecedesTestOffset(ctl, per_page, per_page - 1);
}
#endif

/*
 * SlruScanDirectory callback
 *		This callback reports true if there's any segment wholly prior to the
 *		one containing the page passed as "data".
 */
/*
 * 中文注释：
 * SlruScanDirectory 的回调：只要发现一个完全位于 cutoffPage 之前的段，就返回 true。
 *
 * data 指向调用者传入的 cutoffPage。返回 true 会让目录扫描提前停止，因此该回调
 * 适合用于“是否存在可删除的旧段”的快速判断，而不会实际删除任何文件。
 */
bool
SlruScanDirCbReportPresence(SlruDesc *ctl, char *filename, int64 segpage,
							void *data)
{
	int64		cutoffPage = *(int64 *) data;

	if (SlruMayDeleteSegment(ctl, segpage, cutoffPage))
		return true;			/* found one; don't iterate any more */

	return false;				/* keep going */
}

/*
 * SlruScanDirectory callback.
 *		This callback deletes segments prior to the one passed in as "data".
 */
/*
 * 中文注释：
 * SlruScanDirectory 的回调：删除所有完全位于 cutoffPage 之前的段。
 *
 * 对每个段用 SlruMayDeleteSegment 做回绕安全判断，满足条件就调用
 * SlruInternalDeleteSegment 删除；始终返回 false 以继续扫描。data 指向 cutoffPage。
 * 调用者需保证共享内存中这些段的页已经被清理（SimpleLruTruncate 会先做这一步）。
 */
static bool
SlruScanDirCbDeleteCutoff(SlruDesc *ctl, char *filename, int64 segpage,
						  void *data)
{
	int64		cutoffPage = *(int64 *) data;

	if (SlruMayDeleteSegment(ctl, segpage, cutoffPage))
		SlruInternalDeleteSegment(ctl, segpage / SLRU_PAGES_PER_SEGMENT);

	return false;				/* keep going */
}

/*
 * SlruScanDirectory callback.
 *		This callback deletes all segments.
 */
/*
 * 中文注释：
 * SlruScanDirectory 的回调：删除目录中所有合法的 SLRU 段文件。
 *
 * 不做 cutoff 判断，直接按段号删除；始终返回 false 以继续扫描。通常用于重建或
 * 彻底清理某个 SLRU 的场景。调用者仍需自行保证没有其他进程正在访问这些段。
 */
bool
SlruScanDirCbDeleteAll(SlruDesc *ctl, char *filename, int64 segpage, void *data)
{
	SlruInternalDeleteSegment(ctl, segpage / SLRU_PAGES_PER_SEGMENT);

	return false;				/* keep going */
}

/*
 * An internal function used by SlruScanDirectory().
 *
 * Returns true if a file with a name of a given length may be a correct
 * SLRU segment.
 */
/*
 * 中文注释：
 * 判断目录项文件名长度是否符合当前 SLRU 的段文件命名规则。
 *
 * 新式 64 位段号使用 15 个十六进制字符；旧式 32 位段号历史上允许 4、5、6 个字符
 * （分别对应不同阶段的文件名格式），代码仍兼容读取。长度不符的文件（如临时文件、
 * 备份文件、无关文件）会被 SlruScanDirectory 忽略，避免误删。最终所有 SLRU 计划
 * 迁移到 64 位页号和 15 字符文件名。
 */
static inline bool
SlruCorrectSegmentFilenameLength(SlruDesc *ctl, size_t len)
{
	if (ctl->options.long_segment_names)
		return (len == 15);		/* see SlruFileName() */
	else

		/*
		 * Commit 638cf09e76d allowed 5-character lengths. Later commit
		 * 73c986adde5 allowed 6-character length.
		 *
		 * Note: There is an ongoing plan to migrate all SLRUs to 64-bit page
		 * numbers, and the corresponding 15-character file names, which may
		 * eventually deprecate the support for 4, 5, and 6-character names.
		 */
		return (len == 4 || len == 5 || len == 6);
}

/*
 * Scan the SimpleLru directory and apply a callback to each file found in it.
 *
 * If the callback returns true, the scan is stopped.  The last return value
 * from the callback is returned.
 *
 * The callback receives the following arguments: 1. the SlruCtl struct for the
 * slru being truncated; 2. the filename being considered; 3. the page number
 * for the first page of that file; 4. a pointer to the opaque data given to us
 * by the caller.
 *
 * Note that the ordering in which the directory is scanned is not guaranteed.
 *
 * Note that no locking is applied.
 */
/*
 * 中文注释：
 * 扫描某个 SLRU 的目录，对每个合法的段文件调用回调。
 *
 * 只处理“长度符合命名规则且全部由十六进制字符组成”的文件，解析段号并换算成该段
 * 第一页的页号，然后调用 callback(ctl, filename, segpage, data)。回调返回 true 时
 * 提前停止，函数返回该 true；否则扫描完返回 false。目录扫描顺序不做保证，且本函数
 * 不获取任何 SLRU 锁，因此调用者必须根据用途自行保证互斥（例如截断时持有相应锁）。
 */
bool
SlruScanDirectory(SlruDesc *ctl, SlruScanCallback callback, void *data)
{
	bool		retval = false;
	DIR		   *cldir;
	struct dirent *clde;
	int64		segno;
	int64		segpage;

	cldir = AllocateDir(ctl->options.Dir);
	while ((clde = ReadDir(cldir, ctl->options.Dir)) != NULL)
	{
		size_t		len;

		len = strlen(clde->d_name);

		if (SlruCorrectSegmentFilenameLength(ctl, len) &&
			strspn(clde->d_name, "0123456789ABCDEF") == len)
		{
			segno = strtoi64(clde->d_name, NULL, 16);
			segpage = segno * SLRU_PAGES_PER_SEGMENT;

			elog(DEBUG2, "SlruScanDirectory invoking callback on %s/%s",
				 ctl->options.Dir, clde->d_name);
			retval = callback(ctl, clde->d_name, segpage, data);
			if (retval)
				break;
		}
	}
	FreeDir(cldir);

	return retval;
}

/*
 * Individual SLRUs (clog, ...) have to provide a sync.c handler function so
 * that they can provide the correct "SlruCtl" (otherwise we don't know how to
 * build the path), but they just forward to this common implementation that
 * performs the fsync.
 */
/*
 * 中文注释：
 * 各 SLRU 通用的 sync.c 文件同步处理器。
 *
 * 每个具体 SLRU 都需要向 sync 机制注册一个 handler，但真正 fsync 的逻辑相同，
 * 于是统一转发到这里。函数根据 FileTag 中的段号构造完整路径，以 O_RDWR 打开，
 * 调用 pg_fsync，然后关闭文件；返回 fsync 的结果，并保留 errno 供上层报告。
 * 打开失败返回 -1。等待事件标记为 WAIT_EVENT_SLRU_FLUSH_SYNC，便于统计同步 I/O。
 */
int
SlruSyncFileTag(SlruDesc *ctl, const FileTag *ftag, char *path)
{
	int			fd;
	int			save_errno;
	int			result;

	SlruFileName(ctl, path, ftag->segno);

	fd = OpenTransientFile(path, O_RDWR | PG_BINARY);
	if (fd < 0)
		return -1;

	pgstat_report_wait_start(WAIT_EVENT_SLRU_FLUSH_SYNC);
	result = pg_fsync(fd);
	pgstat_report_wait_end();
	save_errno = errno;

	CloseTransientFile(fd);

	errno = save_errno;
	return result;
}
