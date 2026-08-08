/*-------------------------------------------------------------------------
 *
 * shm_toc.c
 *	  shared memory segment table of contents
 *
 * 【模块总览(中文)】
 * 本文件实现"共享内存目录表"(Table of Contents,TOC):在一块动态共享
 * 内存段(DSM)内把若干"命名条目"登记成一张目录,其他进程凭 64 位 key
 * 找到条目。这是并行查询中"每个 worker 如何找到自己的工作区"的基础:
 * leader 进程创建 DSM 段后,用 shm_toc_create 初始化目录、用
 * shm_toc_allocate 从段里划分出各工作区结构、再用约定的 key 经
 * shm_toc_insert 登记;worker 进程 attach 到同一 DSM 段后,用相同的 key
 * 调用 shm_toc_lookup 即可拿到工作区地址。
 *
 * 【布局与设计思想】
 * - 目录条目数组从段头"向前"增长,而数据块从段尾"向后"分配,两者互不
 *   干扰,直到把整段耗尽;shm_toc_allocate 不提供释放、不做合并,只是
 *   一个廉价的"把一段内存切成逻辑块"的手段;
 * - 条目里保存的是相对 TOC 起始地址的字节偏移,而不是绝对指针:同一
 *   DSM 段在不同后端进程可能映射到不同地址,只有相对偏移是进程无关的;
 * - 写方在持自旋锁 toc_mutex 时更新条目与计数,并在递增 toc_nentry 前
 *   插入写屏障,使读方 shm_toc_lookup 可以完全不取锁、只用读屏障安全
 *   读取——多个 worker 常常几乎同时查阅同一目录,免锁能显著降低争用;
 * - 使用协议:建立方先 create/allocate/insert 全部完成,再通过其他机制
 *   (bgworker 参数、shm_mq 等)把 DSM 段句柄交给使用方,因此建立方不会
 *   在登记完成前就被查到。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/storage/ipc/shm_toc.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "port/atomics.h"
#include "storage/shm_toc.h"
#include "storage/spin.h"

/* 目录表条目:
 * key —— 任意的 64 位标识符,由使用 TOC 的各方事先约定(通常是一个
 *         "众所周知的整数",见 shm_toc_insert 的说明);
 * offset —— 条目所指数据块相对于 TOC 起始地址的字节偏移。存偏移而非
 *            绝对指针:DSM 段在不同进程里可能映射到不同地址。 */
typedef struct shm_toc_entry
{
	uint64		key;			/* Arbitrary identifier */
	Size		offset;			/* Offset, in bytes, from TOC start */
} shm_toc_entry;

/* 共享内存目录表控制结构:
 * toc_magic            —— 魔数,用于识别"这块内存确实是 TOC",防止错 attach;
 * toc_mutex            —— 自旋锁,保护下列计数与条目数组的并发更新
 *                          (只有写方持锁;读方走"无锁 + 内存屏障"路径);
 * toc_total_bytes      —— 本 TOC 管理的总字节数(创建时向下 BUFFERALIGN,
 *                          保证 shm_toc_allocate 的对齐假设成立);
 * toc_allocated_bytes  —— 已从段尾"向后"分配出去的数据块字节数;
 * toc_nentry           —— 已登记的条目个数;
 * toc_entry[]          —— 条目数组(柔性数组成员),从段头"向前"增长。 */
struct shm_toc
{
	uint64		toc_magic;		/* Magic number identifying this TOC */
	slock_t		toc_mutex;		/* Spinlock for mutual exclusion */
	Size		toc_total_bytes;	/* Bytes managed by this TOC */
	Size		toc_allocated_bytes;	/* Bytes allocated of those managed */
	uint32		toc_nentry;		/* Number of entries in TOC */
	shm_toc_entry toc_entry[FLEXIBLE_ARRAY_MEMBER];
};

/*
 * Initialize a region of shared memory with a table of contents.
 */
/*
 * shm_toc_create - (中文)把一段共享内存初始化成带目录表的 TOC
 *
 * 【作用】"建立方"在创建 DSM 段后调用:把 address 起的 nbytes 字节变成
 * 一个空 TOC(魔数、自旋锁、计数全部置初值),之后可在其上分配数据块并
 * 登记条目。调用时机必须先于任何其他进程 attach 同一段。
 *
 * 【设计思想】toc_total_bytes 用 BUFFERALIGN_DOWN 向下对齐,因为
 * shm_toc_allocate 假定"起始值按缓冲区对齐",这样才能保证它返回的每个
 * 数据块都满足 BUFFERALIGN 对齐(原子操作、DSA 指针等要求较宽的对齐)。
 *
 * 【参数】
 *   magic   —— 调用方约定的魔数,后续 attach 时用来校验;
 *   address —— DSM 段的起始地址;
 *   nbytes  —— 段的总字节数。
 * 【返回值】指向已初始化的 shm_toc 结构(即 address 本身)。
 */
shm_toc *
shm_toc_create(uint64 magic, void *address, Size nbytes)
{
	shm_toc    *toc = (shm_toc *) address;

	Assert(nbytes > offsetof(shm_toc, toc_entry));
	toc->toc_magic = magic;
	SpinLockInit(&toc->toc_mutex);

	/*
	 * The alignment code in shm_toc_allocate() assumes that the starting
	 * value is buffer-aligned.
	 */
	toc->toc_total_bytes = BUFFERALIGN_DOWN(nbytes);
	toc->toc_allocated_bytes = 0;
	toc->toc_nentry = 0;

	return toc;
}

/*
 * Attach to an existing table of contents.  If the magic number found at
 * the target address doesn't match our expectations, return NULL.
 */
/*
 * shm_toc_attach - (中文)附着到一个已存在的 TOC
 *
 * 【作用】"使用者"attach 到 DSM 段后调用:校验地址处的魔数与创建时一致,
 * 一致则返回 TOC 指针,不一致返回 NULL(说明这块内存不是预期的 TOC)。
 *
 * 【设计思想】只做两件近乎免费的事——比较魔数 + 断言计数自洽,不修改
 * 任何共享状态。魔数是 shm_toc_create 最先写入的字段,因此读方可以放心
 * 地在"建立方尚未完全初始化"时安全失败而不是读到垃圾。
 *
 * 【参数】
 *   magic   —— 创建时用的同一个魔数;
 *   address —— DSM 段的起始地址。
 * 【返回值】TOC 指针;魔数不匹配时返回 NULL。
 */
shm_toc *
shm_toc_attach(uint64 magic, void *address)
{
	shm_toc    *toc = (shm_toc *) address;

	if (toc->toc_magic != magic)
		return NULL;

	Assert(toc->toc_total_bytes >= toc->toc_allocated_bytes);
	Assert(toc->toc_total_bytes > offsetof(shm_toc, toc_entry));

	return toc;
}

/*
 * Allocate shared memory from a segment managed by a table of contents.
 *
 * This is not a full-blown allocator; there's no way to free memory.  It's
 * just a way of dividing a single physical shared memory segment into logical
 * chunks that may be used for different purposes.
 *
 * We allocate backwards from the end of the segment, so that the TOC entries
 * can grow forward from the start of the segment.
 */
/*
 * shm_toc_allocate - (中文)从 TOC 管理的段内分配一块数据
 *
 * 【作用】"建立方"使用:从段尾向"前"切出 nbytes(内部已按 BUFFERALIGN
 * 对齐)字节返回给调用方存放任意数据结构。调用方拿到地址后通常还会用
 * shm_toc_insert 把它登记下来,供其他进程查找。
 *
 * 【设计思想】这是一个极简分配器:没有 free、不做合并,只是一把"把物理
 * 段切分成逻辑块"的尺子。方向选择很关键——数据块从段尾向后分配、条目
 * 数组从段头向前增长,两者互不覆盖,而且插入新条目不会移动已有数据块的
 * 地址。对齐用 BUFFERALIGN 而非 MAXALIGN:原子操作(如 pg_atomic_uint64、
 * DSA 指针)可能需要比 MAXALIGN 更宽的对齐,BUFFERALIGN 足以覆盖。
 * 持锁期间检查"已用字节数 + 请求数"是否超限或算术回绕,超限直接报
 * ERRCODE_OUT_OF_MEMORY(共享内存耗尽)。
 *
 * 【参数】
 *   toc    —— TOC 指针;
 *   nbytes —— 请求的字节数(返回值实际可用大小可能更大,因已对齐)。
 * 【返回值】数据块在段内的地址;空间不足时报 ERROR。
 */
void *
shm_toc_allocate(shm_toc *toc, Size nbytes)
{
	Size		total_bytes;
	Size		allocated_bytes;
	Size		nentry;
	Size		toc_bytes;

	/*
	 * Make sure request is well-aligned.  XXX: MAXALIGN is not enough,
	 * because atomic ops might need a wider alignment.  We don't have a
	 * proper definition for the minimum to make atomic ops safe, but
	 * BUFFERALIGN ought to be enough.
	 */
	nbytes = BUFFERALIGN(nbytes);

	SpinLockAcquire(&toc->toc_mutex);

	total_bytes = toc->toc_total_bytes;
	allocated_bytes = toc->toc_allocated_bytes;
	nentry = toc->toc_nentry;
	toc_bytes = offsetof(shm_toc, toc_entry) + nentry * sizeof(shm_toc_entry)
		+ allocated_bytes;

	/* Check for memory exhaustion and overflow. */
	if (toc_bytes + nbytes > total_bytes || toc_bytes + nbytes < toc_bytes)
	{
		SpinLockRelease(&toc->toc_mutex);
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory")));
	}
	toc->toc_allocated_bytes += nbytes;

	SpinLockRelease(&toc->toc_mutex);

	return ((char *) toc) + (total_bytes - allocated_bytes - nbytes);
}

/*
 * Return the number of bytes that can still be allocated.
 */
/*
 * shm_toc_freespace - (中文)查询 TOC 还可分配的字节数
 *
 * 【作用】估算剩余空间:总字节数减去"已分配数据块 + 条目数组占用的
 * 空间"。建立方常用来决定还能往段里塞多少结构。
 *
 * 【设计思想】持锁读取三个计数以取得一致快照,随后在锁外用
 * BUFFERALIGN(toc_bytes) 把条目数组向上对齐——条目区与数据块的边界
 * 必须对齐,这是 shm_toc_allocate 计算可用空间的前提(有断言验证)。
 *
 * 【参数】toc —— TOC 指针。
 * 【返回值】还能分配的字节数(含对齐损耗的估算)。
 */
Size
shm_toc_freespace(shm_toc *toc)
{
	Size		total_bytes;
	Size		allocated_bytes;
	Size		nentry;
	Size		toc_bytes;

	SpinLockAcquire(&toc->toc_mutex);
	total_bytes = toc->toc_total_bytes;
	allocated_bytes = toc->toc_allocated_bytes;
	nentry = toc->toc_nentry;
	SpinLockRelease(&toc->toc_mutex);

	toc_bytes = offsetof(shm_toc, toc_entry) + nentry * sizeof(shm_toc_entry);
	Assert(allocated_bytes + BUFFERALIGN(toc_bytes) <= total_bytes);
	return total_bytes - (allocated_bytes + BUFFERALIGN(toc_bytes));
}

/*
 * Insert a TOC entry.
 *
 * The idea here is that the process setting up the shared memory segment will
 * register the addresses of data structures within the segment using this
 * function.  Each data structure will be identified using a 64-bit key, which
 * is assumed to be a well-known or discoverable integer.  Other processes
 * accessing the shared memory segment can pass the same key to
 * shm_toc_lookup() to discover the addresses of those data structures.
 *
 * Since the shared memory segment may be mapped at different addresses within
 * different backends, we store relative rather than absolute pointers.
 *
 * This won't scale well to a large number of keys.  Hopefully, that isn't
 * necessary; if it proves to be, we might need to provide a more sophisticated
 * data structure here.  But the real idea here is just to give someone mapping
 * a dynamic shared memory the ability to find the bare minimum number of
 * pointers that they need to bootstrap.  If you're storing a lot of stuff in
 * the TOC, you're doing it wrong.
 */
/*
 * shm_toc_insert - (中文)把 key 与某数据块地址的对应关系登记进 TOC
 *
 * 【作用】"建立方"在 shm_toc_allocate 拿到数据块后调用,把
 * "key → 块内偏移"登记为一条目录条目;其他进程随后可用同一 key 经
 * shm_toc_lookup 找到该数据块。
 *
 * 【设计思想】
 * - 地址先"相对化"成偏移再存储,因为不同进程映射 DSM 段的位置不同;
 * - 条目数组线性扫描(断言检查重复 key)。条目数设计上就很少(只登记
 *   启动所需的最少指针),所以线性查找可以接受;若要在 TOC 里存大量
 *   东西,那是用法不对——真正的数据结构应放在 TOC 之外,只把它的入口
 *   指针登记进来;
 * - 关键的内存序设计:先把 (key, offset) 写入条目槽,再执行
 *   pg_write_barrier() 写屏障,最后才递增 toc_nentry 并释放自旋锁。
 *   这样无锁的读方只要"先读 nentry、再读屏障",就不会看到半初始化的
 *   条目;
 * - 插入前同样做溢出/回绕检查,条目总数不能超过 PG_UINT32_MAX。
 *
 * 【参数】
 *   toc     —— TOC 指针;
 *   key     —— 调用方约定的 64 位标识符(不得与已有条目重复);
 *   address —— 段内某数据块的地址(必须是本段内的地址)。
 * 【返回值】无;空间不足时报 ERROR。
 */
void
shm_toc_insert(shm_toc *toc, uint64 key, void *address)
{
	Size		total_bytes;
	Size		allocated_bytes;
	Size		nentry;
	Size		toc_bytes;
	Size		offset;

	/* Relativize pointer. */
	Assert(address > (void *) toc);
	offset = ((char *) address) - (char *) toc;

	SpinLockAcquire(&toc->toc_mutex);

	total_bytes = toc->toc_total_bytes;
	allocated_bytes = toc->toc_allocated_bytes;
	nentry = toc->toc_nentry;

#ifdef USE_ASSERT_CHECKING
	/* Verify no duplicate keys */
	for (Size i = 0; i < nentry; i++)
		Assert(toc->toc_entry[i].key != key);
#endif

	toc_bytes = offsetof(shm_toc, toc_entry) + nentry * sizeof(shm_toc_entry)
		+ allocated_bytes;

	/* Check for memory exhaustion and overflow. */
	if (toc_bytes + sizeof(shm_toc_entry) > total_bytes ||
		toc_bytes + sizeof(shm_toc_entry) < toc_bytes ||
		nentry >= PG_UINT32_MAX)
	{
		SpinLockRelease(&toc->toc_mutex);
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory")));
	}

	Assert(offset < total_bytes);
	toc->toc_entry[nentry].key = key;
	toc->toc_entry[nentry].offset = offset;

	/*
	 * By placing a write barrier after filling in the entry and before
	 * updating the number of entries, we make it safe to read the TOC
	 * unlocked.
	 */
	pg_write_barrier();

	toc->toc_nentry++;

	SpinLockRelease(&toc->toc_mutex);
}

/*
 * Look up a TOC entry.
 *
 * If the key is not found, returns NULL if noError is true, otherwise
 * throws elog(ERROR).
 *
 * Unlike the other functions in this file, this operation acquires no lock;
 * it uses only barriers.  It probably wouldn't hurt concurrency very much even
 * if it did get a lock, but since it's reasonably likely that a group of
 * worker processes could each read a series of entries from the same TOC
 * right around the same time, there seems to be some value in avoiding it.
 */
/*
 * shm_toc_lookup - (中文)按 key 在 TOC 中查找数据块地址
 *
 * 【作用】"使用者"调用:遍历条目数组,返回与 key 匹配的条目所指数据块
 * 的地址(已把相对偏移换算回本进程的绝对地址)。
 *
 * 【设计思想】这是全文件唯一的"无锁读"路径:先原子读 toc_nentry(假设
 * 读 uint32 是原子的),再 pg_read_barrier() 读屏障,然后线性扫描。
 * 与 shm_toc_insert 中"先写条目、写屏障、再递增 nentry"的顺序配对,
 * 保证"读到 nentry = N 时,前 N 个条目必然完整可见"。免锁是有意为之:
 * 多个 worker 常常几乎同时各读一串条目,自旋锁会让它们排队;屏障的
 * 开销则小得多。
 * 允许 noError = true 时找不到返回 NULL(调用方自己兜底);否则找不到
 * 就 elog(ERROR)——这通常意味着建立方与使用方对 key 的约定不一致,
 * 属于编程错误。
 *
 * 【参数】
 *   toc     —— TOC 指针;
 *   key     —— 要查找的 64 位标识符;
 *   noError —— true 时找不到返回 NULL;false 时找不到抛出 elog(ERROR)。
 * 【返回值】匹配条目对应的数据块地址;找不到时按 noError 返回 NULL 或
 *           报错。
 */
void *
shm_toc_lookup(shm_toc *toc, uint64 key, bool noError)
{
	uint32		nentry;
	uint32		i;

	/*
	 * Read the number of entries before we examine any entry.  We assume that
	 * reading a uint32 is atomic.
	 */
	nentry = toc->toc_nentry;
	pg_read_barrier();

	/* Now search for a matching entry. */
	for (i = 0; i < nentry; ++i)
	{
		if (toc->toc_entry[i].key == key)
			return ((char *) toc) + toc->toc_entry[i].offset;
	}

	/* No matching entry was found. */
	if (!noError)
		elog(ERROR, "could not find key " UINT64_FORMAT " in shm TOC at %p",
			 key, toc);
	return NULL;
}

/*
 * Estimate how much shared memory will be required to store a TOC and its
 * dependent data structures.
 */
/*
 * shm_toc_estimate - (中文)估算创建 TOC 及其数据所需的共享内存总量
 *
 * 【作用】"建立方"在 dsm_create 之前调用:给定计划登记的条目数与数据块
 * 总量,返回需要的总字节数;创建 DSM 段时按此值开段,建完再逐个
 * shm_toc_allocate / shm_toc_insert。
 *
 * 【设计思想】总和 = 头结构 + 条目数 × 单条目大小 + 数据块总字节数,
 * 最后整体 BUFFERALIGN,与 shm_toc_create 的向下对齐语义自洽。
 * add_size / mul_size 是带溢出检查的算术封装,防止条目数巨大时回绕。
 *
 * 【参数】e —— 估算器,含 number_of_keys(条目数)与
 *             space_for_chunks(数据块总字节数)两个字段。
 * 【返回值】TOC 及其数据所需的总字节数(已对齐)。
 */
Size
shm_toc_estimate(shm_toc_estimator *e)
{
	Size		sz;

	sz = offsetof(shm_toc, toc_entry);
	sz = add_size(sz, mul_size(e->number_of_keys, sizeof(shm_toc_entry)));
	sz = add_size(sz, e->space_for_chunks);

	return BUFFERALIGN(sz);
}
