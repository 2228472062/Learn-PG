/*-------------------------------------------------------------------------
 *
 * buf_table.c
 *	  routines for mapping BufferTags to buffer indexes.
 *
 * 【模块总览(中文)】
 * 本文件实现"缓冲区查找表"(Shared Buffer Lookup Table):一张位于共享内存
 * 中的哈希表,用于把"磁盘页标签"(BufferTag)映射到共享缓冲池中的缓冲区编号
 * (buffer id)。
 *
 * 背景知识:PostgreSQL 把每个磁盘页(一个 relation 的一个 fork 的第 n 块)
 * 用一个三元组唯一标识,即 BufferTag = {relation的FileTag, fork编号, 块号}。
 * 当后端进程需要访问某个页时,必须先在共享缓冲池中找到(或调入)该页所在的
 * 缓冲区;本文件就负责完成"页标签 -> 缓冲区"的查询、插入、删除。
 *
 * 设计要点:
 * 1. 本文件所有函数"自身不做任何加锁"!因为锁粒度必须是"按哈希分区"的
 *    (BufMappingLock 被拆成 NUM_BUFFER_PARTITIONS 个,详见 README),
 *    调用者必须自行持有对应分区的锁,并且往往需要在持锁期间修改缓冲区头
 *    字段后才能释放锁,因此无法把加锁逻辑封装进本文件的函数里。
 * 2. 哈希表带分区分桶(HASH_PARTITION),配合分区锁把并发冲突分散到多个锁上,
 *    避免 8.1 之前单一 BufMgrLock 成为系统瓶颈的问题。
 * 3. 表中最大条目数 NBuffers + NUM_BUFFER_PARTITIONS:因为 BufferAlloc()
 *    采用"先插入新条目、后删除旧条目"的顺序,理论上每个分区可同时多出一个
 *    临时条目,因此需要预留这么多空间,保证永不因表满而失败。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/buffer/buf_table.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "storage/buf_internals.h"
#include "storage/subsystems.h"

/* entry for buffer lookup hashtable */
/* 缓冲区查找哈希表的条目结构:
 *   key —— 磁盘页标签(BufferTag),即 (relation 标识, fork 编号, 块号),
 *          用于唯一标识"数据库中的某一个磁盘页";
 *   id  —— 该页在共享缓冲池中的缓冲区编号(数组下标,范围为 [0, NBuffers)),
 *          即 "缓冲区描述符数组 BufferDescriptors[]" 的下标。 */
typedef struct
{
	BufferTag	key;			/* Tag of a disk page */
	int			id;				/* Associated buffer ID */
} BufferLookupEnt;

/* SharedBufHash:指向共享内存中"缓冲区查找哈希表"的句柄。
 * 该表在 postmaster 启动时由 BufTableShmemRequest() 请求分配,之后进程间共享,
 * 每个后端进程通过这个句柄访问同一张表。 */
static HTAB *SharedBufHash;

static void BufTableShmemRequest(void *arg);

/* BufTableShmemCallbacks:向共享内存子系统注册的"启动回调函数表"。
 * 共享内存子系统在初始化阶段会调用注册的 request_fn 来计算并申请所需内存,
 * 这里没有 init_fn,因为哈希表本身在 shmem 创建后即为空,无需额外初始化。 */
const ShmemCallbacks BufTableShmemCallbacks = {
	.request_fn = BufTableShmemRequest,
	/* no special initialization needed, the hash table will start empty */
};

/*
 * BufTableShmemRequest
 *      (中文)申请共享内存,用于创建"缓冲区查找哈希表"
 *
 * 【作用】在 PostgreSQL 启动的共享内存分配阶段被调用,向共享内存子系统
 * 声明:缓冲管理器需要一张哈希表,容量与布局如下,请创建并把表句柄写入
 * 全局变量 SharedBufHash。
 *
 * 【设计思想】PostgreSQL 采用"先统计需求、再一次性分配"的方式管理共享内存:
 * 各子系统在启动早期通过 ShmemRequestHash/ShmemRequest 上报自己需要多少
 * 内存,由上层统一计算总量后一次性分配,避免碎片化与多次系统调用。
 *
 * 【大小选择】表的最大稳态条目数是 NBuffers(每个缓冲区至多对应一个页标签),
 * 但 BufferAlloc() 采用"先插入新条目、再删除被替换的旧条目"的顺序;理论上
 * 各分区可并发进行替换,每个分区最多多出一条临时条目,因此容量取
 * NBuffers + NUM_BUFFER_PARTITIONS,保证任何情况下都不会因表满而失败
 * (哈希表分配失败在 PG 中是致命的,不能容忍)。
 *
 * 【分区分桶】哈希表按标签哈希值的低位分成 NUM_BUFFER_PARTITIONS 个桶分区,
 * 与 BufMappingLock 的分区一一对应,使并发查找/插入落在不同锁上,大幅降低争用。
 *
 * 【参数】arg —— 未使用,保留以匹配回调签名。
 * 【返回值】无(通过全局变量 SharedBufHash 输出表句柄)。
 *
 * Register shmem hash table for mapping buffers.
 *		size is the desired hash table size (possibly more than NBuffers)
 */
void
BufTableShmemRequest(void *arg)
{
	int			size;

	/*
	 * Request the shared buffer lookup hashtable.
	 *
	 * Since we can't tolerate running out of lookup table entries, we must be
	 * sure to specify an adequate table size here.  The maximum steady-state
	 * usage is of course NBuffers entries, but BufferAlloc() tries to insert
	 * a new entry before deleting the old.  In principle this could be
	 * happening in each partition concurrently, so we could need as many as
	 * NBuffers + NUM_BUFFER_PARTITIONS entries.
	 */
	size = NBuffers + NUM_BUFFER_PARTITIONS;

	ShmemRequestHash(.name = "Shared Buffer Lookup Table",
					 .nelems = size,
					 .ptr = &SharedBufHash,
					 .hash_info.keysize = sizeof(BufferTag),
					 .hash_info.entrysize = sizeof(BufferLookupEnt),
					 .hash_info.num_partitions = NUM_BUFFER_PARTITIONS,
					 .hash_flags = HASH_ELEM | HASH_BLOBS | HASH_PARTITION | HASH_FIXED_SIZE,
		);
}

/*
 * BufTableHashCode
 *      (中文)计算 BufferTag 对应的哈希码
 *
 * 【作用】给定一个磁盘页标签,计算并返回它的 32 位哈希码。
 *
 * 【设计思想】调用方(如 BufferAlloc)拿到哈希码后要做两件事:
 *   1) 用哈希码的低位比特确定该标签属于哪个 BufMappingLock 分区,以便加锁;
 *   2) 把哈希码连同标签传给 BufTableLookup/Insert/Delete,让哈希查找
 *      (hash_search_with_hash_value)直接用它定位桶,避免重复计算。
 * 哈希函数 hash_any 计算较慢,若在表操作内部再算一遍,则"锁前一次、锁内一次"
 * 要做两次;由调用者只算一次、多处复用,是典型的计算结果外提优化。
 *
 * 【参数】tagPtr —— 待计算的页标签指针(不能为 NULL)。
 * 【返回值】32 位无符号哈希码。
 *
 * BufTableHashCode
 *		Compute the hash code associated with a BufferTag
 *
 * This must be passed to the lookup/insert/delete routines along with the
 * tag.  We do it like this because the callers need to know the hash code
 * in order to determine which buffer partition to lock, and we don't want
 * to do the hash computation twice (hash_any is a bit slow).
 */
uint32
BufTableHashCode(BufferTag *tagPtr)
{
	return get_hash_value(SharedBufHash, tagPtr);
}

/*
 * BufTableLookup
 *      (中文)在查找表中查询给定页标签,返回其缓冲区编号
 *
 * 【作用】检查"某个磁盘页当前是否已在共享缓冲池中":若在,返回它所在的
 * 缓冲区编号(非负);若不在,返回 -1。
 *
 * 【调用约定/设计思想】调用者必须至少持有该标签所属分区上的 BufMappingLock
 * 共享锁。加锁不能封装在本文件内,原因见文件头注释:调用者找到缓冲区后,
 * 必须在释放锁之前就把该缓冲区的引用计数(pin)加 1,否则锁一放,缓冲区
 * 可能立刻被其他进程回收复用;而修改 pin 属于调用者职责。
 *
 * 【参数】
 *   tagPtr   —— 要查询的页标签;
 *   hashcode —— 该标签的哈希码(必须由 BufTableHashCode 预先算好,且与
 *               调用者所持锁的分区保持一致,二者不可错配)。
 * 【返回值】找到返回缓冲区 id;未找到返回 -1。
 *
 * BufTableLookup
 *		Lookup the given BufferTag; return buffer ID, or -1 if not found
 *
 * Caller must hold at least share lock on BufMappingLock for tag's partition
 */
int
BufTableLookup(BufferTag *tagPtr, uint32 hashcode)
{
	BufferLookupEnt *result;

	result = (BufferLookupEnt *)
		hash_search_with_hash_value(SharedBufHash,
									tagPtr,
									hashcode,
									HASH_FIND,
									NULL);

	if (!result)
		return -1;

	return result->id;
}

/*
 * BufTableInsert
 *      (中文)向查找表插入"标签 -> 缓冲区"映射条目
 *
 * 【作用】把页标签 tagPtr 与缓冲区编号 buf_id 的对应关系登记进哈希表。
 * 成功插入返回 -1;若该标签已存在(说明别的进程已把同一页调入),返回已
 * 存在条目的缓冲区编号,由调用者决定如何处理(例如改用那个缓冲区、释放
 * 自己刚读入的页)。
 *
 * 【设计思想】"插入时若已存在则返回旧值"的语义与缓冲管理器的"加载新页"
 * 流程咬合:BufferAlloc 持分区排他锁插入时若发现被他人抢先,说明两个进程
 * 同时读入了同一页,只需复用已有缓冲区并丢弃自己的拷贝,保证缓冲池中同一
 * 页绝不出现两份。
 *
 * 【调用约定】调用者必须持有该标签所属分区上的 BufMappingLock 排他锁
 * (因为要修改哈希表结构)。
 *
 * 【参数】
 *   tagPtr   —— 页标签(blockNum 不能是 P_NEW 这类"待分配"的伪块号);
 *   hashcode —— 预先算好的哈希码;
 *   buf_id   —— 要登记到表中的缓冲区编号(不能为 -1,-1 是"不在表中"的
 *               保留标记)。
 * 【返回值】-1 表示成功插入;否则返回与标签冲突的既有缓冲区编号。
 *
 * BufTableInsert
 *		Insert a hashtable entry for given tag and buffer ID,
 *		unless an entry already exists for that tag
 *
 * Returns -1 on successful insertion.  If a conflicting entry exists
 * already, returns the buffer ID in that entry.
 *
 * Caller must hold exclusive lock on BufMappingLock for tag's partition
 */
int
BufTableInsert(BufferTag *tagPtr, uint32 hashcode, int buf_id)
{
	BufferLookupEnt *result;
	bool		found;

	Assert(buf_id >= 0);		/* -1 is reserved for not-in-table */
	Assert(tagPtr->blockNum != P_NEW);	/* invalid tag */

	result = (BufferLookupEnt *)
		hash_search_with_hash_value(SharedBufHash,
									tagPtr,
									hashcode,
									HASH_ENTER,
									&found);

	if (found)					/* found something already in the table */
		return result->id;

	result->id = buf_id;

	return -1;
}

/*
 * BufTableDelete
 *      (中文)从查找表中删除给定标签的映射条目
 *
 * 【作用】当某个缓冲区被回收、改用于存放别的页时,必须先删除旧的
 * "标签 -> 缓冲区"映射,否则后续查询会错误地认为该页仍在缓冲池中。
 * 本函数完成该删除操作。
 *
 * 【调用约定】调用者必须持有该标签所属分区上的 BufMappingLock 排他锁。
 *
 * 【异常处理】表中必须已存在该标签(由调用者保证);若不存在,说明哈希表
 * 状态已损坏(如内存越界、并发编程错误),直接抛 ERROR 中止当前事务,
 * 防止带病继续运行造成更严重后果。
 *
 * 【参数】tagPtr —— 要删除的页标签;hashcode —— 对应的哈希码。
 * 【返回值】无。
 *
 * BufTableDelete
 *		Delete the hashtable entry for given tag (which must exist)
 *
 * Caller must hold exclusive lock on BufMappingLock for tag's partition
 */
void
BufTableDelete(BufferTag *tagPtr, uint32 hashcode)
{
	BufferLookupEnt *result;

	result = (BufferLookupEnt *)
		hash_search_with_hash_value(SharedBufHash,
									tagPtr,
									hashcode,
									HASH_REMOVE,
									NULL);

	if (!result)				/* shouldn't happen */
		elog(ERROR, "shared buffer hash table corrupted");
}
