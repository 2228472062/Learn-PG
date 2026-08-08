/*-------------------------------------------------------------------------
 *
 * predicate.c
 *	  POSTGRES predicate locking
 *	  to support full serializable transaction isolation
 *
 *
 * The approach taken is to implement Serializable Snapshot Isolation (SSI)
 * as initially described in this paper:
 *
 *	Michael J. Cahill, Uwe Röhm, and Alan D. Fekete. 2008.
 *	Serializable isolation for snapshot databases.
 *	In SIGMOD '08: Proceedings of the 2008 ACM SIGMOD
 *	international conference on Management of data,
 *	pages 729-738, New York, NY, USA. ACM.
 *	http://doi.acm.org/10.1145/1376616.1376690
 *
 * and further elaborated in Cahill's doctoral thesis:
 *
 *	Michael James Cahill. 2009.
 *	Serializable Isolation for Snapshot Databases.
 *	Sydney Digital Theses.
 *	University of Sydney, School of Information Technologies.
 *	http://hdl.handle.net/2123/5353
 *
 *
 * Predicate locks for Serializable Snapshot Isolation (SSI) are SIREAD
 * locks, which are so different from normal locks that a distinct set of
 * structures is required to handle them.  They are needed to detect
 * rw-conflicts when the read happens before the write.  (When the write
 * occurs first, the reading transaction can check for a conflict by
 * examining the MVCC data.)
 *
 * (1)	Besides tuples actually read, they must cover ranges of tuples
 *		which would have been read based on the predicate.  This will
 *		require modelling the predicates through locks against database
 *		objects such as pages, index ranges, or entire tables.
 *
 * (2)	They must be kept in RAM for quick access.  Because of this, it
 *		isn't possible to always maintain tuple-level granularity -- when
 *		the space allocated to store these approaches exhaustion, a
 *		request for a lock may need to scan for situations where a single
 *		transaction holds many fine-grained locks which can be coalesced
 *		into a single coarser-grained lock.
 *
 * (3)	They never block anything; they are more like flags than locks
 *		in that regard; although they refer to database objects and are
 *		used to identify rw-conflicts with normal write locks.
 *
 * (4)	While they are associated with a transaction, they must survive
 *		a successful COMMIT of that transaction, and remain until all
 *		overlapping transactions complete.  This even means that they
 *		must survive termination of the transaction's process.  If a
 *		top level transaction is rolled back, however, it is immediately
 *		flagged so that it can be ignored, and its SIREAD locks can be
 *		released any time after that.
 *
 * (5)	The only transactions which create SIREAD locks or check for
 *		conflicts with them are serializable transactions.
 *
 * (6)	When a write lock for a top level transaction is found to cover
 *		an existing SIREAD lock for the same transaction, the SIREAD lock
 *		can be deleted.
 *
 * (7)	A write from a serializable transaction must ensure that an xact
 *		record exists for the transaction, with the same lifespan (until
 *		all concurrent transaction complete or the transaction is rolled
 *		back) so that rw-dependencies to that transaction can be
 *		detected.
 *
 * We use an optimization for read-only transactions. Under certain
 * circumstances, a read-only transaction's snapshot can be shown to
 * never have conflicts with other transactions.  This is referred to
 * as a "safe" snapshot (and one known not to be is "unsafe").
 * However, it can't be determined whether a snapshot is safe until
 * all concurrent read/write transactions complete.
 *
 * Once a read-only transaction is known to have a safe snapshot, it
 * can release its predicate locks and exempt itself from further
 * predicate lock tracking. READ ONLY DEFERRABLE transactions run only
 * on safe snapshots, waiting as necessary for one to be available.
 *
 *
 * Lightweight locks to manage access to the predicate locking shared
 * memory objects must be taken in this order, and should be released in
 * reverse order:
 *
 *	SerializableFinishedListLock
 *		- Protects the list of transactions which have completed but which
 *			may yet matter because they overlap still-active transactions.
 *
 *	SerializablePredicateListLock
 *		- Protects the linked list of locks held by a transaction.  Note
 *			that the locks themselves are also covered by the partition
 *			locks of their respective lock targets; this lock only affects
 *			the linked list connecting the locks related to a transaction.
 *		- All transactions share this single lock (with no partitioning).
 *		- There is never a need for a process other than the one running
 *			an active transaction to walk the list of locks held by that
 *			transaction, except parallel query workers sharing the leader's
 *			transaction.  In the parallel case, an extra per-sxact lock is
 *			taken; see below.
 *		- It is relatively infrequent that another process needs to
 *			modify the list for a transaction, but it does happen for such
 *			things as index page splits for pages with predicate locks and
 *			freeing of predicate locked pages by a vacuum process.  When
 *			removing a lock in such cases, the lock itself contains the
 *			pointers needed to remove it from the list.  When adding a
 *			lock in such cases, the lock can be added using the anchor in
 *			the transaction structure.  Neither requires walking the list.
 *		- Cleaning up the list for a terminated transaction is sometimes
 *			not done on a retail basis, in which case no lock is required.
 *		- Due to the above, a process accessing its active transaction's
 *			list always uses a shared lock, regardless of whether it is
 *			walking or maintaining the list.  This improves concurrency
 *			for the common access patterns.
 *		- A process which needs to alter the list of a transaction other
 *			than its own active transaction must acquire an exclusive
 *			lock.
 *
 *	SERIALIZABLEXACT's member 'perXactPredicateListLock'
 *		- Protects the linked list of predicate locks held by a transaction.
 *			Only needed for parallel mode, where multiple backends share the
 *			same SERIALIZABLEXACT object.  Not needed if
 *			SerializablePredicateListLock is held exclusively.
 *
 *	PredicateLockHashPartitionLock(hashcode)
 *		- The same lock protects a target, all locks on that target, and
 *			the linked list of locks on the target.
 *		- When more than one is needed, acquire in ascending address order.
 *		- When all are needed (rare), acquire in ascending index order with
 *			PredicateLockHashPartitionLockByIndex(index).
 *
 *	SerializableXactHashLock
 *		- Protects both PredXact and SerializableXidHash.
 *
 *	SerialControlLock
 *		- Protects SerialControlData members
 *
 *	SLRU per-bank locks
 *		- Protects SerialSlruCtl
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL "可串行化快照隔离"(SSI,Serializable Snapshot
 * Isolation)的完整实现,用于在快照隔离(SI)之上提供真正的
 * SERIALIZABLE 隔离级别。SI 读不阻塞写、写不阻塞读,但存在"写偏斜"
 * 等串行化异常;SSI 的妙处在于:只要监控事务之间"读写冲突"
 * (rw-conflict)构成的依赖图,当图中出现由两条相邻 rw 边构成的
 * "危险结构"(dangerous structure)时让其中一个事务以 SQLSTATE
 * 40001(serialization failure)中止,就能保证任何执行结果都等价于
 * 某种串行执行,同时几乎不损失 SI 的并发性。
 *
 * 危险结构:T_in --rw--> T_pivot --rw--> T_out,且 T_out 先于图中
 * 其他事务提交。rw 边方向是"读者 → 写者":读者因并发看不见写者的
 * 写入,所以读者"看起来先执行"。两条相邻的 rw 边意味着"先读、
 * 后写、又读"的交错使提交顺序与依赖顺序互相矛盾。本文件所有冲突
 * 记录点(FlagRWConflict / OnConflict_CheckForSerializationFailure)
 * 都在检查新边是否补全了这样的结构,一旦发现立即中止合适的
 * 事务(优先中止仍可回滚的"枢轴"事务,保证重试能推进)。
 *
 * 谓词锁(SIREAD 锁)用于跟踪"读",与普通重锁截然不同(见文件头
 * 英文注释的 7 条性质):它从不阻塞任何人,只是"旗标";它必须
 * 覆盖谓词隐含的范围,因此有 表(relation)/页(page)/元组(tuple)
 * 三级粒度,内存紧张时允许把多个细粒度锁提升为单个粗粒度锁;
 * 它随事务提交而保留,直到所有重叠事务结束。写冲突则利用 MVCC
 * 信息直接判定:
 * - 写元组时(CheckForSerializableConflictIn):查看目标上谁持有了
 *   SIREAD 锁,为每个持锁者建立"持锁者 → 写者"的 rw 边;
 * - 读元组时(CheckForSerializableConflictOut):若读到别的并发
 *   事务写入/更新的版本,建立"读者 → 写者"的 rw 边。
 *
 * 【核心数据结构】(全部位于共享内存,定义见
 * src/include/storage/predicate_internals.h)
 * - SERIALIZABLEXACT(PredXact 定长数组):每个参与 SSI 的事务一个,
 *   记录 vxid、prepareSeqNo/commitSeqNo(提交序号)、inConflicts/
 *   outConflicts/possibleUnsafeConflicts 冲突边双向链表、谓词锁
 *   链表、xmin/flags 等;
 * - PREDICATELOCKTARGET / PREDICATELOCK:谓词锁目标(表/页/元组
 *   tag)与"某事务在某目标上的锁";两张哈希表各分为 16 个分区,
 *   目标与其上的所有锁共用同一把分区 LWLock 保护;
 * - RWConflictPool:冲突边对象池(rw 边不复用普通锁表结构);
 * - LocalPredicateLockHash:每后端私有的锁记录表,含父锁的
 *   childLocks 计数,用于粒度提升决策(纯优化,允许轻微漂移);
 * - SerialSlruCtl + SerialControlData:把"早已提交、与当前活动
 *   事务不再重叠"的事务摘要为 commitSeqNo 信息写入 SLRU
 *   (pg_serial),使共享内存占用有上界;
 * - SerCommitSeqNo:提交序号,给所有参与 SSI 的事务一个单调递增
 *   的"提交顺序"刻度,用于判断 T_out 是否先提交、以及只读事务
 *   快照的安全性。
 *
 * 【关键简化】
 * 1. 只追踪 rw 冲突;wr/ww 依赖天然与提交顺序一致,无需监控;
 * 2. rw 边指向的写者若回滚则边作废,故许多冲突的结算/清理被
 *    推迟到提交时刻(ReleasePredicateLocks 等)进行;
 * 3. 只读事务可 "opt out":若所有并发读写事务都不会造成危险
 *    结构(RO_SAFE 判定),就释放谓词锁、停止跟踪;READ ONLY
 *    DEFERRABLE 事务则直接等待安全快照再开始;
 * 4. 内存不足时"优雅退化":提升锁粒度或把老事务摘要进 SLRU,
 *    尽量避免中止无辜事务。
 *
 * 锁顺序约定(自上而下获取、逆序释放):SerializableFinishedListLock
 * → SerializablePredicateListLock → perXactPredicateListLock →
 * 目标分区锁(多个时按地址升序)→ SerializableXactHashLock →
 * SerialControlLock → SLRU bank 锁。违反该顺序可能死锁。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/predicate.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *
 * predicate lock reporting
 *		GetPredicateLockStatusData(void)
 *		PageIsPredicateLocked(Relation relation, BlockNumber blkno)
 *
 * predicate lock maintenance
 *		GetSerializableTransactionSnapshot(Snapshot snapshot)
 *		SetSerializableTransactionSnapshot(Snapshot snapshot,
 *										   VirtualTransactionId *sourcevxid)
 *		RegisterPredicateLockingXid(void)
 *		PredicateLockRelation(Relation relation, Snapshot snapshot)
 *		PredicateLockPage(Relation relation, BlockNumber blkno,
 *						Snapshot snapshot)
 *		PredicateLockTID(Relation relation, const ItemPointerData *tid, Snapshot snapshot,
 *						 TransactionId tuple_xid)
 *		PredicateLockPageSplit(Relation relation, BlockNumber oldblkno,
 *							   BlockNumber newblkno)
 *		PredicateLockPageCombine(Relation relation, BlockNumber oldblkno,
 *								 BlockNumber newblkno)
 *		TransferPredicateLocksToHeapRelation(Relation relation)
 *		ReleasePredicateLocks(bool isCommit, bool isReadOnlySafe)
 *
 * conflict detection (may also trigger rollback)
 *		CheckForSerializableConflictOut(Relation relation, TransactionId xid,
 *										Snapshot snapshot)
 *		CheckForSerializableConflictIn(Relation relation, const ItemPointerData *tid,
 *									   BlockNumber blkno)
 *		CheckTableForSerializableConflictIn(Relation relation)
 *
 * final rollback checking
 *		PreCommit_CheckForSerializationFailure(void)
 *
 * two-phase commit support
 *		AtPrepare_PredicateLocks(void);
 *		PostPrepare_PredicateLocks(TransactionId xid);
 *		PredicateLockTwoPhaseFinish(FullTransactionId fxid, bool isCommit);
 *		predicatelock_twophase_recover(FullTransactionId fxid, uint16 info,
 *									   void *recdata, uint32 len);
 */

#include "postgres.h"

#include "access/parallel.h"
#include "access/slru.h"
#include "access/transam.h"
#include "access/twophase.h"
#include "access/twophase_rmgr.h"
#include "access/xact.h"
#include "access/xlog.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "port/pg_lfind.h"
#include "storage/predicate.h"
#include "storage/predicate_internals.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "storage/shmem.h"
#include "storage/subsystems.h"
#include "utils/guc_hooks.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"
#include "utils/wait_event.h"

/* Uncomment the next line to test the graceful degradation code. */
/* #define TEST_SUMMARIZE_SERIAL */

/*
 * Test the most selective fields first, for performance.
 *
 * a is covered by b if all of the following hold:
 *	1) a.database = b.database
 *	2) a.relation = b.relation
 *	3) b.offset is invalid (b is page-granularity or higher)
 *	4) either of the following:
 *		4a) a.offset is valid (a is tuple-granularity) and a.page = b.page
 *	 or 4b) a.offset is invalid and b.page is invalid (a is
 *			page-granularity and b is relation-granularity
 */
#define TargetTagIsCoveredBy(covered_target, covering_target)			\
	((GET_PREDICATELOCKTARGETTAG_RELATION(covered_target) == /* (2) */	\
	  GET_PREDICATELOCKTARGETTAG_RELATION(covering_target))				\
	 && (GET_PREDICATELOCKTARGETTAG_OFFSET(covering_target) ==			\
		 InvalidOffsetNumber)								 /* (3) */	\
	 && (((GET_PREDICATELOCKTARGETTAG_OFFSET(covered_target) !=			\
		   InvalidOffsetNumber)								 /* (4a) */ \
		  && (GET_PREDICATELOCKTARGETTAG_PAGE(covering_target) ==		\
			  GET_PREDICATELOCKTARGETTAG_PAGE(covered_target)))			\
		 || ((GET_PREDICATELOCKTARGETTAG_PAGE(covering_target) ==		\
			  InvalidBlockNumber)							 /* (4b) */ \
			 && (GET_PREDICATELOCKTARGETTAG_PAGE(covered_target)		\
				 != InvalidBlockNumber)))								\
	 && (GET_PREDICATELOCKTARGETTAG_DB(covered_target) ==	 /* (1) */	\
		 GET_PREDICATELOCKTARGETTAG_DB(covering_target)))
/* (中文)"目标覆盖"判定:covered_target(细粒度)是否被
 * covering_target(粗粒度)的锁所覆盖?判定条件(见英文注释):
 * 两者数据库相同、关系相同;covering 至少是页级(offset 无效);
 * 且 covered 是页内目标(页号相同,covering 为页级或元组被页覆盖),
 * 或者 covering 是表级(页号也无效)。该宏用于删除"被更粗新锁
 * 覆盖"的旧锁(DeleteChildTargetLocks、TransferPredicateLocksToNewTarget
 * 的覆盖判断等)。字段检查顺序刻意把最可能最先失败的"关系号"
 * 放前面,以缩短常见路径。 */


/*
 * The predicate locking target and lock shared hash tables are partitioned to
 * reduce contention.  To determine which partition a given target belongs to,
 * compute the tag's hash code with PredicateLockTargetTagHashCode(), then
 * apply one of these macros.
 * NB: NUM_PREDICATELOCK_PARTITIONS must be a power of 2!
 */
#define PredicateLockHashPartition(hashcode) \
	((hashcode) % NUM_PREDICATELOCK_PARTITIONS)
#define PredicateLockHashPartitionLock(hashcode) \
	(&MainLWLockArray[PREDICATELOCK_MANAGER_LWLOCK_OFFSET + \
		PredicateLockHashPartition(hashcode)].lock)
#define PredicateLockHashPartitionLockByIndex(i) \
	(&MainLWLockArray[PREDICATELOCK_MANAGER_LWLOCK_OFFSET + (i)].lock)
/* (中文)谓词锁共享哈希表的分区机制(与 lock.c 的锁表分区同理):
 * 由 tag 哈希码低 LOG2_NUM_PREDICATELOCK_PARTITIONS 位(取模)得到
 * 分区号,映射到 MainLWLockArray 中一段连续的分区 LWLock。同一把
 * 分区锁同时保护"一个目标、该目标上的全部锁、以及目标上的锁
 * 链表"。需要同时持有多个分区锁时按锁地址升序获取;需要全部
 * 分区锁时按下标升序获取(PredicateLockHashPartitionLockByIndex),
 * 以防死锁。 */

#define NPREDICATELOCKTARGETENTS() \
	mul_size(max_predicate_locks_per_xact, add_size(MaxBackends, max_prepared_xacts))
/* (中文)共享内存中谓词锁"目标"条目总数:每个并发后端(含
 * prepared 事务)预计最多 max_predicate_locks_per_xact 个目标。 */

#define SxactIsOnFinishedList(sxact) (!dlist_node_is_detached(&(sxact)->finishedLink))
/* (中文)判断 sxact 是否仍挂在 FinishedSerializableTransactions
 * (已结束事务)链表上:finishedLink 未脱离即表示在链上。 */


/*
 * Note that a sxact is marked "prepared" once it has passed
 * PreCommit_CheckForSerializationFailure, even if it isn't using
 * 2PC. This is the point at which it can no longer be aborted.
 *
 * The PREPARED flag remains set after commit, so SxactIsCommitted
 * implies SxactIsPrepared.
 */
/* (中文)SERIALIZABLEXACT->flags 各标志位的访问宏(标志位定义见
 * predicate_internals.h 的 SXACT_FLAG_*):
 * - SxactIsCommitted / SxactIsPrepared:已提交 / 已通过提交前检查
 *   (PREPARED 在提交后仍保留,故 Committed 蕴含 Prepared;"prepared"
 *    标志一旦置上事务就不可再被中止,这是危险结构判定中必须
 *    考虑"枢轴已 prepared 则只能自杀"的原因);
 * - SxactIsRolledBack:已回滚(ReleasePredicateLocks 已调用,对象
 *   可被清理,不再参与 SxactGlobalXmin 计算);
 * - SxactIsDoomed:被判定为"注定失败",另一个事务已决定中止它,
 *   它自己在下次冲突检查或提交时报错;已 doomed 的事务不再值得
 *   与它建立冲突边;
 * - SxactIsReadOnly:显式声明或隐式(提交前未写)的只读事务;
 * - SxactHasSummaryConflictIn/Out:与"被摘要进 SLRU 的已提交老
 *   事务"之间存在冲突进/出(细节已丢失,只能做保守假设);
 * - SxactHasConflictOut:存在指向"更早提交事务"的冲突出边,即
 *   本事务可能成为危险结构中的 T_out;
 * - SxactIsDeferrableWaiting:DEFERRABLE 只读事务正在等待安全快照;
 * - SxactIsROSafe / SxactIsROUnsafe:只读事务的快照已被证明安全/
 *   不安全(若 RO_SAFE 则释放谓词锁并整体退出跟踪);
 * - SxactIsPartiallyReleased:共享对象已被部分释放(锁与冲突已
 *   清理),仅为并行 worker 保留着,由 leader 在事务末尾回收。 */
#define SxactIsCommitted(sxact) (((sxact)->flags & SXACT_FLAG_COMMITTED) != 0)
#define SxactIsPrepared(sxact) (((sxact)->flags & SXACT_FLAG_PREPARED) != 0)
#define SxactIsRolledBack(sxact) (((sxact)->flags & SXACT_FLAG_ROLLED_BACK) != 0)
#define SxactIsDoomed(sxact) (((sxact)->flags & SXACT_FLAG_DOOMED) != 0)
#define SxactIsReadOnly(sxact) (((sxact)->flags & SXACT_FLAG_READ_ONLY) != 0)
#define SxactHasSummaryConflictIn(sxact) (((sxact)->flags & SXACT_FLAG_SUMMARY_CONFLICT_IN) != 0)
#define SxactHasSummaryConflictOut(sxact) (((sxact)->flags & SXACT_FLAG_SUMMARY_CONFLICT_OUT) != 0)
/*
 * The following macro actually means that the specified transaction has a
 * conflict out *to a transaction which committed ahead of it*.  It's hard
 * to get that into a name of a reasonable length.
 */
#define SxactHasConflictOut(sxact) (((sxact)->flags & SXACT_FLAG_CONFLICT_OUT) != 0)
#define SxactIsDeferrableWaiting(sxact) (((sxact)->flags & SXACT_FLAG_DEFERRABLE_WAITING) != 0)
#define SxactIsROSafe(sxact) (((sxact)->flags & SXACT_FLAG_RO_SAFE) != 0)
#define SxactIsROUnsafe(sxact) (((sxact)->flags & SXACT_FLAG_RO_UNSAFE) != 0)
#define SxactIsPartiallyReleased(sxact) (((sxact)->flags & SXACT_FLAG_PARTIALLY_RELEASED) != 0)

/*
 * Compute the hash code associated with a PREDICATELOCKTARGETTAG.
 *
 * To avoid unnecessary recomputations of the hash code, we try to do this
 * just once per function, and then pass it around as needed.  Aside from
 * passing the hashcode to hash_search_with_hash_value(), we can extract
 * the lock partition number from the hashcode.
 */
#define PredicateLockTargetTagHashCode(predicatelocktargettag) \
	get_hash_value(PredicateLockTargetHash, predicatelocktargettag)
/* (中文)计算 PREDICATELOCKTARGETTAG 的哈希码。为避免在调用链中
 * 反复重算,惯例是每个函数只算一次,再把结果作为
 * targettaghash 参数传下去(hash_search_with_hash_value 直接使用),
 * 同时由哈希码低 4 位提取分区号。 */

/*
 * Given a predicate lock tag, and the hash for its target,
 * compute the lock hash.
 *
 * To make the hash code also depend on the transaction, we xor the sxid
 * struct's address into the hash code, left-shifted so that the
 * partition-number bits don't change.  Since this is only a hash, we
 * don't care if we lose high-order bits of the address; use an
 * intermediate variable to suppress cast-pointer-to-int warnings.
 */
/* (中文)由"谓词锁 tag"与"目标哈希码"合成谓词锁的哈希码:把持有
 * 事务对象(sxact 结构体地址)左移 LOG2_NUM_PREDICATELOCK_PARTITIONS
 * 位后异或进目标哈希码。左移保证分区号(低 4 位)不变,使"锁"
 * 与其"目标"永远落入同一分区、共用同一把分区锁(见英文注释,
 * dynahash 用哈希码低位取分区);地址高位丢失对哈希均匀性无碍。 */
#define PredicateLockHashCodeFromTargetHashCode(predicatelocktag, targethash) \
	((targethash) ^ ((uint32) PointerGetDatum((predicatelocktag)->myXact)) \
	 << LOG2_NUM_PREDICATELOCK_PARTITIONS)


/*
 * The SLRU buffer area through which we access the old xids.
 */
static bool SerialPagePrecedesLogically(int64 page1, int64 page2);
static int	serial_errdetail_for_io_error(const void *opaque_data);

static SlruDesc SerialSlruDesc;

#define SerialSlruCtl			(&SerialSlruDesc)

#define SERIAL_PAGESIZE			BLCKSZ
#define SERIAL_ENTRYSIZE			sizeof(SerCommitSeqNo)
#define SERIAL_ENTRIESPERPAGE	(SERIAL_PAGESIZE / SERIAL_ENTRYSIZE)

/*
 * Set maximum pages based on the number needed to track all transactions.
 */
#define SERIAL_MAX_PAGE			(MaxTransactionId / SERIAL_ENTRIESPERPAGE)

#define SerialNextPage(page) (((page) >= SERIAL_MAX_PAGE) ? 0 : (page) + 1)

#define SerialValue(slotno, xid) (*((SerCommitSeqNo *) \
	(SerialSlruCtl->shared->page_buffer[slotno] + \
	((((uint32) (xid)) % SERIAL_ENTRIESPERPAGE) * SERIAL_ENTRYSIZE))))

#define SerialPage(xid)	(((uint32) (xid)) / SERIAL_ENTRIESPERPAGE)
/* (中文)Serial SLRU 声明区:用 SLRU 机制(见 slru.h,与 CLOG 同款)
 * 保存"已提交读写事务的摘要信息"——按 xid 索引的一个 SerCommitSeqNo
 * 值(minConflictCommitSeqNo,该事务所有冲突出边指向的最早提交序号),
 * 磁盘目录为 pg_serial。
 * - SERIAL_ENTRYSIZE = 8 字节(一个 SerCommitSeqNo),每页
 *   SERIAL_ENTRIESPERPAGE 个条目;
 * - SerialPage(xid) 由 xid 算页号(整除),SerialValue 由槽号与 xid
 *   取模算页内偏移并取出条目值;
 * - SerialNextPage 循环换页;SERIAL_MAX_PAGE 覆盖整个 xid 空间。 */

typedef struct SerialControlData
{
	int64		headPage;		/* newest initialized page */
	TransactionId headXid;		/* newest valid Xid in the SLRU */
	TransactionId tailXid;		/* oldest xmin we might be interested in */
}			SerialControlData;
/* (中文)Serial SLRU 的全局控制信息(共享内存,由 SerialControlLock
 * 保护):
 * - headPage:最新已初始化的页号(-1 表示 SLRU 完全未启用);
 * - headXid:SLRU 中最新有效的 xid(上界,只增);
 * - tailXid:我们可能感兴趣的最老 xmin(下界);比 tailXid 更老的
 *   xid 不必保存。有效条目位于 [tailXid, headXid] 区间内。 */

typedef struct SerialControlData *SerialControl;

static SerialControl serialControl;

/*
 * When the oldest committed transaction on the "finished" list is moved to
 * SLRU, its predicate locks will be moved to this "dummy" transaction,
 * collapsing duplicate targets.  When a duplicate is found, the later
 * commitSeqNo is used.
 */
/* (中文)"虚拟事务":Finished 链表上最老已提交事务被摘要进 SLRU 时,
 * 它的谓词锁被转移挂到 OldCommittedSxact 名下(见英文注释),多个
 * 老事务在同一目标上的锁合并为一个,commitSeqNo 取较新者。此后
 * 与新事务发生冲突时只能通过 SXACT_FLAG_SUMMARY_CONFLICT_IN/OUT
 * 与 SerialGetMinConflictCommitSeqNo 做保守判定。 */
static SERIALIZABLEXACT *OldCommittedSxact;


/*
 * These configuration variables are used to set the predicate lock table size
 * and to control promotion of predicate locks to coarser granularity in an
 * attempt to degrade performance (mostly as false positive serialization
 * failure) gracefully in the face of memory pressure.
 */
int			max_predicate_locks_per_xact;	/* in guc_tables.c */
int			max_predicate_locks_per_relation;	/* in guc_tables.c */
int			max_predicate_locks_per_page;	/* in guc_tables.c */
/* (中文)三个相关 GUC(注册在 guc_tables.c):
 * - max_predicate_locks_per_xact:每个事务预计持有的谓词锁数量,
 *   决定共享"目标/锁"两张表的大小(NPREDICATELOCKTARGETENTS);
 * - max_predicate_locks_per_relation / _per_page:单个关系/单页的
 *   子锁数量上限(负数表示按每事务上限的几分之一折算,见
 *   MaxPredicateChildLocks);超过上限会把细粒度锁提升为粗粒度锁,
 *   以可能的"误报串行化失败"为代价优雅降级,避免耗尽共享内存。 */

/*
 * This provides a list of objects in order to track transactions
 * participating in predicate locking.  Entries in the list are fixed size,
 * and reside in shared memory.  The memory address of an entry must remain
 * fixed during its lifetime.  The list will be protected from concurrent
 * update externally; no provision is made in this code to manage that.  The
 * number of entries in the list, and the size allowed for each entry is
 * fixed upon creation.
 */
static PredXactList PredXact;
/* (中文)指向共享内存中"参与谓词锁定的全部事务"列表头
 * (PredXactListData,见 predicate_internals.h):含 availableList
 * (空闲槽链表)与 activeList(活动事务链表)两条双向链表、全局
 * 可串行化 xmin 及其计数、可写事务计数、提交序号计数器、
 * 部分清理进度等。槽位(SERIALIZABLEXACT 数组)为定长,地址在
 * 生命周期内固定——冲突边与锁都靠地址引用事务。并发保护由
 * 外部(SerializableXactHashLock 等)负责。 */

static void PredicateLockShmemRequest(void *arg);
static void PredicateLockShmemInit(void *arg);
static void PredicateLockShmemAttach(void *arg);

const ShmemCallbacks PredicateLockShmemCallbacks = {
	.request_fn = PredicateLockShmemRequest,
	.init_fn = PredicateLockShmemInit,
	.attach_fn = PredicateLockShmemAttach,
};
/* (中文)向共享内存子系统注册的回调集:request 阶段登记各哈希表、
 * 列表与 SLRU 的共享内存大小;init 阶段(仅 postmaster 执行)初始化
 * 全部结构;attach 阶段(各后端连接共享内存后)缓存派生指针。 */


/*
 * This provides a pool of RWConflict data elements to use in conflict lists
 * between transactions.
 */
static RWConflictPoolHeader RWConflictPool;
/* (中文)RWConflict 数据元素池(共享内存定长数组,见英文注释):
 * 所有 rw 冲突边对象统一从 availableList 取、用完放回,避免哈希表
 * 式动态分配;SetRWConflict 等函数在池空时报错(建议调大
 * max_connections)。 */

/*
 * The predicate locking hash tables are in shared memory.
 * Each backend keeps pointers to them.
 */
static HTAB *SerializableXidHash;
static HTAB *PredicateLockTargetHash;
static HTAB *PredicateLockHash;
static dlist_head *FinishedSerializableTransactions;
/* (中文)共享内存中的谓词锁哈希表与链表(指针在共享内存初始化时
 * 填入,各后端共享同一实例):
 * - SerializableXidHash:xid → SERIALIZABLEXID(指向所属顶层事务的
 *   SERIALIZABLEXACT),使从元组 MVCC 字段拿到的 xid 能立刻找到
 *   事务对象,即使其会话早已结束;
 * - PredicateLockTargetHash:谓词锁目标(表/页/元组 tag)→
 *   PREDICATELOCKTARGET(含该目标上的锁链表);
 * - PredicateLockHash:(目标, 事务) 二元组 → PREDICATELOCK;
 * - FinishedSerializableTransactions:已提交但可能与活动事务重叠、
 *   尚不能清理的事务链表,按提交顺序排列。 */

/*
 * Tag for a dummy entry in PredicateLockTargetHash. By temporarily removing
 * this entry, you can ensure that there's enough scratch space available for
 * inserting one entry in the hash table. This is an otherwise-invalid tag.
 */
static const PREDICATELOCKTARGETTAG ScratchTargetTag = {0, 0, 0, 0};
static uint32 ScratchTargetTagHash;
static LWLock *ScratchPartitionLock;
/* (中文)PredicateLockTargetHash 里的"占位条目"(见英文注释):
 * 页分裂/合并等必须保证"一定能新建目标"的场景,先临时摘除这个
 * 伪目标腾出空位(RemoveScratchTarget),用完再放回(RestoreScratchTarget);
 * 其哈希码与所在分区锁在共享内存初始化/附加时预计算缓存,避免
 * 每次重算。 */

/*
 * The local hash table used to determine when to combine multiple fine-
 * grained locks into a single courser-grained lock.
 */
static HTAB *LocalPredicateLockHash = NULL;
/* (中文)后端私有的本地哈希表:记录本事务对每个目标的持有状态
 * (LOCALPREDICATELOCK:held + childLocks 孩子计数),用于决定何时把
 * 多个细粒度锁提升为单个粗粒度锁(见 CheckAndPromotePredicateLockRequest)。
 * 仅作优化启发式,允许在个别角落与共享状态轻微漂移(见
 * predicate_internals.h 中英文注释),事务结束时整体销毁。 */

/*
 * Keep a pointer to the currently-running serializable transaction (if any)
 * for quick reference. Also, remember if we have written anything that could
 * cause a rw-conflict.
 */
static SERIALIZABLEXACT *MySerializableXact = InvalidSerializableXact;
static bool MyXactDidWrite = false;
/* (中文)本后端当前参与 SSI 的事务对象快捷指针(InvalidSerializableXact
 * 表示当前不在可串行化模式);MyXactDidWrite 记录本事务是否写过
 * 可能造成 rw 冲突的数据——提交时若为 false 则把事务标记为隐式
 * 只读,享受只读优化。 */

/*
 * The SXACT_FLAG_RO_UNSAFE optimization might lead us to release
 * MySerializableXact early.  If that happens in a parallel query, the leader
 * needs to defer the destruction of the SERIALIZABLEXACT until end of
 * transaction, because the workers still have a reference to it.  In that
 * case, the leader stores it here.
 */
static SERIALIZABLEXACT *SavedSerializableXact = InvalidSerializableXact;
/* (中文)并行查询场景下,RO_UNSAFE 优化可能让 leader 提前部分释放
 * SERIALIZABLEXACT(见英文注释):worker 还引用着它,leader 先把指针
 * 暂存于此,等所有 worker 退出、事务真正结束时再彻底回收
 * (见 ReleasePredicateLocks 的开头恢复逻辑)。 */

static int64 max_serializable_xacts;
/* (中文)共享内存中 SERIALIZABLEXACT 槽位总数(约 (MaxBackends +
 * max_prepared_xacts) * 10,见 PredicateLockShmemRequest):留出冗余
 * 以便在需要把数据摘要进 SLRU 之前先做激进清理。 */

/* local functions */

static SERIALIZABLEXACT *CreatePredXact(void);
static void ReleasePredXact(SERIALIZABLEXACT *sxact);

static bool RWConflictExists(const SERIALIZABLEXACT *reader, const SERIALIZABLEXACT *writer);
static void SetRWConflict(SERIALIZABLEXACT *reader, SERIALIZABLEXACT *writer);
static void SetPossibleUnsafeConflict(SERIALIZABLEXACT *roXact, SERIALIZABLEXACT *activeXact);
static void ReleaseRWConflict(RWConflict conflict);
static void FlagSxactUnsafe(SERIALIZABLEXACT *sxact);

static void SerialAdd(TransactionId xid, SerCommitSeqNo minConflictCommitSeqNo);
static SerCommitSeqNo SerialGetMinConflictCommitSeqNo(TransactionId xid);
static void SerialSetActiveSerXmin(TransactionId xid);

static uint32 predicatelock_hash(const void *key, Size keysize);

static void SummarizeOldestCommittedSxact(void);
static Snapshot GetSafeSnapshot(Snapshot origSnapshot);
static Snapshot GetSerializableTransactionSnapshotInt(Snapshot snapshot,
													  VirtualTransactionId *sourcevxid,
													  int sourcepid);
static bool PredicateLockExists(const PREDICATELOCKTARGETTAG *targettag);
static bool GetParentPredicateLockTag(const PREDICATELOCKTARGETTAG *tag,
									  PREDICATELOCKTARGETTAG *parent);
static bool CoarserLockCovers(const PREDICATELOCKTARGETTAG *newtargettag);
static void RemoveScratchTarget(bool lockheld);
static void RestoreScratchTarget(bool lockheld);
static void RemoveTargetIfNoLongerUsed(PREDICATELOCKTARGET *target,
									   uint32 targettaghash);
static void DeleteChildTargetLocks(const PREDICATELOCKTARGETTAG *newtargettag);
static int	MaxPredicateChildLocks(const PREDICATELOCKTARGETTAG *tag);
static bool CheckAndPromotePredicateLockRequest(const PREDICATELOCKTARGETTAG *reqtag);
static void DecrementParentLocks(const PREDICATELOCKTARGETTAG *targettag);
static void CreatePredicateLock(const PREDICATELOCKTARGETTAG *targettag,
								uint32 targettaghash,
								SERIALIZABLEXACT *sxact);
static void DeleteLockTarget(PREDICATELOCKTARGET *target, uint32 targettaghash);
static bool TransferPredicateLocksToNewTarget(PREDICATELOCKTARGETTAG oldtargettag,
											  PREDICATELOCKTARGETTAG newtargettag,
											  bool removeOld);
static void PredicateLockAcquire(const PREDICATELOCKTARGETTAG *targettag);
static void DropAllPredicateLocksFromTable(Relation relation,
										   bool transfer);
static void SetNewSxactGlobalXmin(void);
static void ClearOldPredicateLocks(void);
static void ReleaseOneSerializableXact(SERIALIZABLEXACT *sxact, bool partial,
									   bool summarize);
static bool XidIsConcurrent(TransactionId xid);
static void CheckTargetForConflictsIn(PREDICATELOCKTARGETTAG *targettag);
static void FlagRWConflict(SERIALIZABLEXACT *reader, SERIALIZABLEXACT *writer);
static void OnConflict_CheckForSerializationFailure(const SERIALIZABLEXACT *reader,
													SERIALIZABLEXACT *writer);
static void CreateLocalPredicateLockHash(void);
static void ReleasePredicateLocksLocal(void);


/*------------------------------------------------------------------------*/

/*
 * Does this relation participate in predicate locking? Temporary and system
 * relations are exempt.
 */
/*
 * PredicateLockingNeededForRelation
 *      (中文)该关系是否参与谓词锁定?
 *
 * 【作用】谓词锁定/冲突检测的"关系级开关":OID 小于
 * FirstUnpinnedObjectId(12000,系统目录等"钉住"对象)或使用本地
 * 缓冲(临时表,见 RelationUsesLocalBuffers)的关系直接豁免。所有
 * 谓词锁接口(读、写、页分裂/合并、DDL 转移等)的第一步都是调用
 * 它做快速返回。
 *
 * 【设计思想】系统目录上的操作不受快照隔离约束,SSI 管不了;
 * 临时表只属于本会话,不可能与别的事务形成依赖环,锁定纯属浪费。
 *
 * 【参数】relation —— 待判定的关系。
 * 【返回值】true = 需要参与谓词锁定;false = 豁免。
 */
static inline bool
PredicateLockingNeededForRelation(Relation relation)
{
	return !(relation->rd_id < FirstUnpinnedObjectId ||
			 RelationUsesLocalBuffers(relation));
}

/*
 * When a public interface method is called for a read, this is the test to
 * see if we should do a quick return.
 *
 * Note: this function has side-effects! If this transaction has been flagged
 * as RO-safe since the last call, we release all predicate locks and reset
 * MySerializableXact. That makes subsequent calls to return quickly.
 *
 * This is marked as 'inline' to eliminate the function call overhead in the
 * common case that serialization is not needed.
 */
/*
 * SerializationNeededForRead
 *      (中文)本次"读"操作是否需要进行 SSI 处理?
 *
 * 【作用】所有读路径公开接口(PredicateLockRelation/Page/TID、
 * CheckForSerializableConflictOut 等)的统一快速返回检查。注意本
 * 函数有副作用:若本事务刚被标记为 RO_SAFE(所有并发读写事务都
 * 已安全提交,本只读事务不可能再成为危险结构的一部分),则立即
 * 释放全部谓词锁并重置 MySerializableXact,让后续调用走快速返回。
 *
 * 【设计思想】把最常见的"无事可做"情形(非可串行化事务、特殊
 * 快照、RO_SAFE、豁免关系)收敛成一次内联函数调用,尽量降低
 * SSI 对常规路径的开销。特殊快照(如 CLUSTER/REINDEX 使用的)不
 * 加锁,它们通过 TransferPredicateLocksToHeapRelation 与
 * CheckTableForSerializableConflictIn 等批量接口参与串行化。
 *
 * 【参数】
 *   relation —— 本次读涉及的关系(用于豁免判定);
 *   snapshot —— 本次读使用的快照(须是 MVCC 快照才需要处理)。
 * 【返回值】true = 需要继续 SSI 处理;false = 快速返回。
 */
static inline bool
SerializationNeededForRead(Relation relation, Snapshot snapshot)
{
	/* Nothing to do if this is not a serializable transaction */
	if (MySerializableXact == InvalidSerializableXact)
		return false;

	/*
	 * Don't acquire locks or conflict when scanning with a special snapshot.
	 * This excludes things like CLUSTER and REINDEX. They use the wholesale
	 * functions TransferPredicateLocksToHeapRelation() and
	 * CheckTableForSerializableConflictIn() to participate in serialization,
	 * but the scans involved don't need serialization.
	 */
	if (!IsMVCCSnapshot(snapshot))
		return false;

	/*
	 * Check if we have just become "RO-safe". If we have, immediately release
	 * all locks as they're not needed anymore. This also resets
	 * MySerializableXact, so that subsequent calls to this function can exit
	 * quickly.
	 *
	 * A transaction is flagged as RO_SAFE if all concurrent R/W transactions
	 * commit without having conflicts out to an earlier snapshot, thus
	 * ensuring that no conflicts are possible for this transaction.
	 */
	if (SxactIsROSafe(MySerializableXact))
	{
		ReleasePredicateLocks(false, true);
		return false;
	}

	/* Check if the relation doesn't participate in predicate locking */
	if (!PredicateLockingNeededForRelation(relation))
		return false;

	return true;				/* no excuse to skip predicate locking */
}

/*
 * Like SerializationNeededForRead(), but called on writes.
 * The logic is the same, but there is no snapshot and we can't be RO-safe.
 */
/*
 * SerializationNeededForWrite
 *      (中文)本次"写"操作是否需要进行 SSI 处理?
 *
 * 【作用】写路径公开接口(CheckForSerializableConflictIn、
 * CheckTableForSerializableConflictIn 等)的统一快速返回检查。与
 * SerializationNeededForRead 不同:写操作没有快照,也永远不会被
 * RO_SAFE 优化豁免(能写就不是只读事务),所以只检查两件事——
 * 是否在可串行化事务中、关系是否豁免。
 *
 * 【参数】relation —— 本次写涉及的关系。
 * 【返回值】true = 需要继续 SSI 处理;false = 快速返回。
 */
static inline bool
SerializationNeededForWrite(Relation relation)
{
	/* Nothing to do if this is not a serializable transaction */
	if (MySerializableXact == InvalidSerializableXact)
		return false;

	/* Check if the relation doesn't participate in predicate locking */
	if (!PredicateLockingNeededForRelation(relation))
		return false;

	return true;				/* no excuse to skip predicate locking */
}


/*------------------------------------------------------------------------*/

/*
 * These functions are a simple implementation of a list for this specific
 * type of struct.  If there is ever a generalized shared memory list, we
 * should probably switch to that.
 */
/*
 * CreatePredXact
 *      (中文)从空闲池取一个 SERIALIZABLEXACT 槽位并挂到活动链表
 *
 * 【作用】为新加入 SSI 的(可串行化)事务分配事务对象。从
 * PredXact->availableList 头部弹出一个槽位,挂到 activeList 尾部
 * 并返回。
 *
 * 【设计思想】PredXact 是共享内存中的定长数组 + 两条双向链表:
 * 分配/释放只是链表节点的移动,不涉及任何内存分配,因此可以在
 * 持锁(SERIALIZABLEXACT 结构本身由 SerializableXactHashLock 保护)
 * 的情况下安全执行。调用者拿到对象后还需自行初始化各字段。
 *
 * 【参数】无。
 * 【返回值】指向新分配的 SERIALIZABLEXACT;若空闲池已空返回 NULL
 * (调用者需通过 SummarizeOldestCommittedSxact 释放旧事务后重试)。
 */
static SERIALIZABLEXACT *
CreatePredXact(void)
{
	SERIALIZABLEXACT *sxact;

	if (dlist_is_empty(&PredXact->availableList))
		return NULL;

	sxact = dlist_container(SERIALIZABLEXACT, xactLink,
							dlist_pop_head_node(&PredXact->availableList));
	dlist_push_tail(&PredXact->activeList, &sxact->xactLink);
	return sxact;
}

static void
ReleasePredXact(SERIALIZABLEXACT *sxact)
{
	Assert(ShmemAddrIsValid(sxact));

	dlist_delete(&sxact->xactLink);
	dlist_push_tail(&PredXact->availableList, &sxact->xactLink);
}
/* (中文)把事务对象归还空闲池:从 activeList 摘下、挂回
 * availableList,即"释放一个 SERIALIZABLEXACT 槽位"。调用者负责
 * 保证该事务的锁、冲突边、xid 记录等已先行清理完毕,并且持有
 * SerializableXactHashLock。 */

/*------------------------------------------------------------------------*/

/*
 * These functions manage primitive access to the RWConflict pool and lists.
 */
/*
 * RWConflictExists
 *      (中文)查询 reader 与 writer 之间是否已存在 rw 冲突边
 *
 * 【作用】沿 reader 的 outConflicts 链表线性查找 sxactIn == writer
 * 的边。若 reader 或 writer 已 doomed(注定回滚),或任一条链表为
 * 空,则直接判定不存在。
 *
 * 【设计思想】冲突边是"读者 → 写者"方向:reader->outConflicts
 * 保存"我读了你写的东西"的边,writer->inConflicts 保存同样一条
 * 边的另一端视角。因为一条边同时挂在两个事务上,只需查一端。
 * 先查两端链表是否为空可快速跳过绝大多数无关调用。
 *
 * 【参数】
 *   reader —— 边起点(读者);
 *   writer —— 边终点(写者)。
 * 【返回值】true = 两者间已有 rw 冲突边(重复边不建立,避免浪费
 * 池元素并防止重复的危险结构判定)。
 */
static bool
RWConflictExists(const SERIALIZABLEXACT *reader, const SERIALIZABLEXACT *writer)
{
	dlist_iter	iter;

	Assert(reader != writer);

	/* Check the ends of the purported conflict first. */
	if (SxactIsDoomed(reader)
		|| SxactIsDoomed(writer)
		|| dlist_is_empty(&reader->outConflicts)
		|| dlist_is_empty(&writer->inConflicts))
		return false;

	/*
	 * A conflict is possible; walk the list to find out.
	 *
	 * The unconstify is needed as we have no const version of
	 * dlist_foreach().
	 */
	dlist_foreach(iter, &unconstify(SERIALIZABLEXACT *, reader)->outConflicts)
	{
		RWConflict	conflict =
			dlist_container(RWConflictData, outLink, iter.cur);

		if (conflict->sxactIn == writer)
			return true;
	}

	/* No conflict found. */
	return false;
}

static void
SetRWConflict(SERIALIZABLEXACT *reader, SERIALIZABLEXACT *writer)
{
	RWConflict	conflict;

	Assert(reader != writer);
	Assert(!RWConflictExists(reader, writer));

	if (dlist_is_empty(&RWConflictPool->availableList))
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("not enough elements in RWConflictPool to record a read/write conflict"),
				 errhint("You might need to run fewer transactions at a time or increase \"max_connections\".")));

	conflict = dlist_head_element(RWConflictData, outLink, &RWConflictPool->availableList);
	dlist_delete(&conflict->outLink);

	conflict->sxactOut = reader;
	conflict->sxactIn = writer;
	dlist_push_tail(&reader->outConflicts, &conflict->outLink);
	dlist_push_tail(&writer->inConflicts, &conflict->inLink);
}
/* (中文)建立一条"reader → writer"的 rw 冲突边:从池中取一个
 * RWConflictData,同时挂到 reader->outConflicts 与
 * writer->inConflicts 两条链表(outLink 属于读者视角,inLink 属于
 * 写者视角)。调用者须已持有 SerializableXactHashLock,并确认边
 * 尚不存在;池空时报错(ERRCODE_OUT_OF_MEMORY),提示减少并发或
 * 增大 max_connections。 */

static void
SetPossibleUnsafeConflict(SERIALIZABLEXACT *roXact,
						  SERIALIZABLEXACT *activeXact)
{
	RWConflict	conflict;

	Assert(roXact != activeXact);
	Assert(SxactIsReadOnly(roXact));
	Assert(!SxactIsReadOnly(activeXact));

	if (dlist_is_empty(&RWConflictPool->availableList))
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("not enough elements in RWConflictPool to record a potential read/write conflict"),
				 errhint("You might need to run fewer transactions at a time or increase \"max_connections\".")));

	conflict = dlist_head_element(RWConflictData, outLink, &RWConflictPool->availableList);
	dlist_delete(&conflict->outLink);

	conflict->sxactOut = activeXact;
	conflict->sxactIn = roXact;
	dlist_push_tail(&activeXact->possibleUnsafeConflicts, &conflict->outLink);
	dlist_push_tail(&roXact->possibleUnsafeConflicts, &conflict->inLink);
}
/* (中文)为只读事务登记一条"潜在不安全"关系:roXact 取快照时与之
 * 重叠的每个未提交读写事务 activeXact 各记一条。与 rw 冲突边同
 * 一个 RWConflictData 结构(方向相反:out = activeXact,in = roXact),
 * 挂在双方的 possibleUnsafeConflicts 链表上。
 *
 * 【设计思想】只读事务要证明自己"永远不会成为危险结构中的
 * T_in"(见 README-SSI),必须等所有重叠的读写事务都提交、并确认
 * 它们没有指向更早事务的冲突出边。这些"可能出问题"的关系先
 * 记下,逐个结算:每条边释放时若发现写者带冲突出边,则把只读
 * 事务标记为 RO_UNSAFE(见 FlagSxactUnsafe);全部安全则标记
 * RO_SAFE,释放全部谓词锁并退出跟踪。 */

static void
ReleaseRWConflict(RWConflict conflict)
{
	dlist_delete(&conflict->inLink);
	dlist_delete(&conflict->outLink);
	dlist_push_tail(&RWConflictPool->availableList, &conflict->outLink);
}
/* (中文)释放一条冲突边(或潜在不安全关系):从两端的链表上摘下,
 * 放回 RWConflictPool 空闲池。调用者须持有保护相关链表的锁
 * (通常是 SerializableXactHashLock)。 */

static void
FlagSxactUnsafe(SERIALIZABLEXACT *sxact)
{
	dlist_mutable_iter iter;

	Assert(SxactIsReadOnly(sxact));
	Assert(!SxactIsROSafe(sxact));

	sxact->flags |= SXACT_FLAG_RO_UNSAFE;

	/*
	 * We know this isn't a safe snapshot, so we can stop looking for other
	 * potential conflicts.
	 */
	dlist_foreach_modify(iter, &sxact->possibleUnsafeConflicts)
	{
		RWConflict	conflict =
			dlist_container(RWConflictData, inLink, iter.cur);

		Assert(!SxactIsReadOnly(conflict->sxactOut));
		Assert(sxact == conflict->sxactIn);

		ReleaseRWConflict(conflict);
	}
}
/* (中文)把只读事务标记为 RO_UNSAFE:其快照已被证明不安全,无法
 * 退出 SSI 跟踪。因为结论已定,剩下的潜在冲突关系不再需要——
 * 全部释放回池,为其他事务腾出 RWConflict 元素。
 *
 * 【触发条件】某重叠读写事务提交时,发现它带有指向"早于该只读
 * 事务快照"提交事务的冲突出边(见 ReleasePredicateLocks),此时
 * 只读事务可能成为危险结构的 T_in,必须中止(其在快照获取后的
 * 首次冲突检查/提交时报 40001,或 DEFERRABLE 事务醒来重试新快照)。
 *
 * 【参数】sxact —— 待标记的只读事务(须已 READ_ONLY 且未标记
 * RO_SAFE)。【返回值】无。
 */

/*------------------------------------------------------------------------*/

/*
 * Decide whether a Serial page number is "older" for truncation purposes.
 * Analogous to CLOGPagePrecedes().
 */
/*
 * SerialPagePrecedesLogically
 *      (中文)判断 Serial 页号 page1 是否"逻辑上早于" page2
 *
 * 【作用】供 SLRU 的截断(SimpleLruTruncate)与新增页判定使用:
 * 判断 page1 是否在 page2 之前(按 xid 语义,而非简单的数值比较)。
 * 与 CLOGPagePrecedes 同理——xid 空间会回绕,必须用 TransactionId
 * 比较。
 *
 * 【设计思想】把页号换算成页内第一个 xid(加 FirstNormalTransactionId
 * + 1 对齐到正常 xid 区间)再比较;要求 page1 的第一个 xid 既早于
 * page2 的第一个 xid、也早于 page2 的最后一个 xid,即整页都早于
 * page2,避免回绕边界上的歧义。返回值在绝大多数正常场景下与
 * 数值大小一致(见 SerialPagePrecedesLogicallyUnitTests 对两个
 * 极端回绕场景的讨论)。
 *
 * 【参数】
 *   page1 —— 待比较的页号;
 *   page2 —— 基准页号。
 * 【返回值】true = page1 逻辑上早于(可被 page2 截断掉);false = 否则。
 */
static bool
SerialPagePrecedesLogically(int64 page1, int64 page2)
{
	TransactionId xid1;
	TransactionId xid2;

	xid1 = ((TransactionId) page1) * SERIAL_ENTRIESPERPAGE;
	xid1 += FirstNormalTransactionId + 1;
	xid2 = ((TransactionId) page2) * SERIAL_ENTRIESPERPAGE;
	xid2 += FirstNormalTransactionId + 1;

	return (TransactionIdPrecedes(xid1, xid2) &&
			TransactionIdPrecedes(xid1, xid2 + SERIAL_ENTRIESPERPAGE - 1));
}

static int
serial_errdetail_for_io_error(const void *opaque_data)
{
	TransactionId xid = *(const TransactionId *) opaque_data;

	return errdetail("Could not access serializable CSN of transaction %u.", xid);
}
/* (中文)Serial SLRU 发生 I/O 错误时的 errdetail 回调(opaque_data
 * 指向 SerialAdd 等传入的 xid):向错误消息附加"无法访问事务 %u
 * 的可串行化提交序号"的详细信息,便于定位是哪个事务的摘要
 * 页读不出来。 */

#ifdef USE_ASSERT_CHECKING
/*
 * SerialPagePrecedesLogicallyUnitTests
 *      (中文)SerialPagePrecedesLogically 的单元测试(仅断言编译期)
 *
 * 【作用】在共享内存注册阶段(PredicateLockShmemRequest)执行:构造
 * 两个逼近 xid 空间回绕边界的极端场景,断言页序判定行为符合预期,
 * 防止截断逻辑在回绕时误删仍需要的页。
 *
 * 【设计思想】详见函数内英文注释:场景一验证"headPage 属于最新
 * 分配的一小段 xid,而 oldestXact 已隔了约 20 亿 xid",此时函数
 * 必须返回 false,避免 SerialAdd 把含其他老 xid 的 tailPage 清零、
 * 报废半个 SLRU;场景二验证"headPage 属于 oldestXact 所在页"时
 * 返回 true。这类极端情况需要烧掉约 20 亿个 xid,几乎不可能在
 * 实际运行中触发,但断言保障了实现的边界安全。
 *
 * 【参数】无。【返回值】无。
 */
static void
SerialPagePrecedesLogicallyUnitTests(void)
{
	int			per_page = SERIAL_ENTRIESPERPAGE,
				offset = per_page / 2;
	int64		newestPage,
				oldestPage,
				headPage,
				targetPage;
	TransactionId newestXact,
				oldestXact;

	/* GetNewTransactionId() has assigned the last XID it can safely use. */
	newestPage = 2 * SLRU_PAGES_PER_SEGMENT - 1;	/* nothing special */
	newestXact = newestPage * per_page + offset;
	Assert(newestXact / per_page == newestPage);
	oldestXact = newestXact + 1;
	oldestXact -= 1U << 31;
	oldestPage = oldestXact / per_page;

	/*
	 * In this scenario, the SLRU headPage pertains to the last ~1000 XIDs
	 * assigned.  oldestXact finishes, ~2B XIDs having elapsed since it
	 * started.  Further transactions cause us to summarize oldestXact to
	 * tailPage.  Function must return false so SerialAdd() doesn't zero
	 * tailPage (which may contain entries for other old, recently-finished
	 * XIDs) and half the SLRU.  Reaching this requires burning ~2B XIDs in
	 * single-user mode, a negligible possibility.
	 */
	headPage = newestPage;
	targetPage = oldestPage;
	Assert(!SerialPagePrecedesLogically(headPage, targetPage));

	/*
	 * In this scenario, the SLRU headPage pertains to oldestXact.  We're
	 * summarizing an XID near newestXact.  (Assume few other XIDs used
	 * SERIALIZABLE, hence the minimal headPage advancement.  Assume
	 * oldestXact was long-running and only recently reached the SLRU.)
	 * Function must return true to make SerialAdd() create targetPage.
	 *
	 * Today's implementation mishandles this case, but it doesn't matter
	 * enough to fix.  Verify that the defect affects just one page by
	 * asserting correct treatment of its prior page.  Reaching this case
	 * requires burning ~2B XIDs in single-user mode, a negligible
	 * possibility.  Moreover, if it does happen, the consequence would be
	 * mild, namely a new transaction failing in SimpleLruReadPage().
	 */
	headPage = oldestPage;
	targetPage = newestPage;
	Assert(SerialPagePrecedesLogically(headPage, targetPage - 1));
#if 0
	Assert(SerialPagePrecedesLogically(headPage, targetPage));
#endif
}
#endif

/*
 * GUC check_hook for serializable_buffers
 */
/*
 * check_serial_buffers
 *      (中文)GUC serializable_buffers 的检查钩子
 *
 * 【作用】当用户设置 serializable_buffers(Serial SLRU 的缓冲页数)
 * 时由 GUC 框架调用,直接委托给通用 SLRU 缓冲检查函数
 * check_slru_buffers(校验取值范围并处理与 shared_buffers 的联动)。
 *
 * 【参数】
 *   newval —— 新值(待校验);
 *   extra  —— GUC 框架使用的额外输出参数(原样传递);
 *   source —— 值的来源(文件/命令行/SQL 等)。
 * 【返回值】true = 接受新值;false = 拒绝(报错)。
 */
bool
check_serial_buffers(int *newval, void **extra, GucSource source)
{
	return check_slru_buffers("serializable_buffers", newval);
}

/*
 * Record a committed read write serializable xid and the minimum
 * commitSeqNo of any transactions to which this xid had a rw-conflict out.
 * An invalid commitSeqNo means that there were no conflicts out from xid.
 */
/*
 * SerialAdd
 *      (中文)把已提交读写事务的摘要写入 Serial SLRU
 *
 * 【作用】事务被摘要(SummarizeOldestCommittedSxact)时调用:在
 * pg_serial 中按 xid 记录一个 SerCommitSeqNo——
 * minConflictCommitSeqNo,即该事务所有冲突出边指向的、最早提交的
 * 那个事务的提交序号(InvalidSerCommitSeqNo 表示没有任何冲突出边)。
 *
 * 【设计思想】这是"共享内存有上界"机制的核心:老事务的 rw 冲突
 * 细节进 SLRU,内存里只留摘要。后来者读元组时若发现写入者已
 * 不在内存(SerialGetMinConflictCommitSeqNo),就与这个摘要比较:
 * 摘要冲突提交序号早于本事务快照,则必须中止(保守但正确)。
 * 函数同时持有 SerialControlLock 与目标页的 SLRU bank 锁,一边
 * 推进 headXid/headPage 一边为新页清零。xid 若已老于 tailXid
 * (全局 xmin 已前进)则直接放弃存储。
 *
 * 【参数】
 *   xid —— 已提交读写事务的顶层 xid;
 *   minConflictCommitSeqNo —— 其所有冲突出边指向的最早提交序号;
 *   InvalidSerCommitSeqNo 表示没有冲突出边。
 * 【返回值】无。
 */
static void
SerialAdd(TransactionId xid, SerCommitSeqNo minConflictCommitSeqNo)
{
	TransactionId tailXid;
	int64		targetPage;
	int			slotno;
	int64		firstZeroPage;
	bool		isNewPage;
	LWLock	   *lock;

	Assert(TransactionIdIsValid(xid));

	targetPage = SerialPage(xid);
	lock = SimpleLruGetBankLock(SerialSlruCtl, targetPage);

	/*
	 * In this routine, we must hold both SerialControlLock and the SLRU bank
	 * lock simultaneously while making the SLRU data catch up with the new
	 * state that we determine.
	 */
	LWLockAcquire(SerialControlLock, LW_EXCLUSIVE);

	/*
	 * If 'xid' is older than the global xmin (== tailXid), there's no need to
	 * store it, after all. This can happen if the oldest transaction holding
	 * back the global xmin just finished, making 'xid' uninteresting, but
	 * ClearOldPredicateLocks() has not yet run.
	 */
	tailXid = serialControl->tailXid;
	if (!TransactionIdIsValid(tailXid) || TransactionIdPrecedes(xid, tailXid))
	{
		LWLockRelease(SerialControlLock);
		return;
	}

	/*
	 * If the SLRU is currently unused, zero out the whole active region from
	 * tailXid to headXid before taking it into use. Otherwise zero out only
	 * any new pages that enter the tailXid-headXid range as we advance
	 * headXid.
	 */
	if (serialControl->headPage < 0)
	{
		firstZeroPage = SerialPage(tailXid);
		isNewPage = true;
	}
	else
	{
		firstZeroPage = SerialNextPage(serialControl->headPage);
		isNewPage = SerialPagePrecedesLogically(serialControl->headPage,
												targetPage);
	}

	if (!TransactionIdIsValid(serialControl->headXid)
		|| TransactionIdFollows(xid, serialControl->headXid))
		serialControl->headXid = xid;
	if (isNewPage)
		serialControl->headPage = targetPage;

	if (isNewPage)
	{
		/* Initialize intervening pages; might involve trading locks */
		for (;;)
		{
			lock = SimpleLruGetBankLock(SerialSlruCtl, firstZeroPage);
			LWLockAcquire(lock, LW_EXCLUSIVE);
			slotno = SimpleLruZeroPage(SerialSlruCtl, firstZeroPage);
			if (firstZeroPage == targetPage)
				break;
			firstZeroPage = SerialNextPage(firstZeroPage);
			LWLockRelease(lock);
		}
	}
	else
	{
		LWLockAcquire(lock, LW_EXCLUSIVE);
		slotno = SimpleLruReadPage(SerialSlruCtl, targetPage, true, &xid);
	}

	SerialValue(slotno, xid) = minConflictCommitSeqNo;
	SerialSlruCtl->shared->page_dirty[slotno] = true;

	LWLockRelease(lock);
	LWLockRelease(SerialControlLock);
}

/*
 * Get the minimum commitSeqNo for any conflict out for the given xid.  For
 * a transaction which exists but has no conflict out, InvalidSerCommitSeqNo
 * will be returned.
 */
/*
 * SerialGetMinConflictCommitSeqNo
 *      (中文)查询某 xid 的"最早冲突出边提交序号"摘要
 *
 * 【作用】CheckForSerializableConflictOut 在内存中找不到目标事务
 * (已摘要)时调用:从 Serial SLRU 读出该 xid 记录的
 * minConflictCommitSeqNo。返回 0 表示该 xid 从未被记录(不是
 * 可串行化事务或已被丢弃);返回 InvalidSerCommitSeqNo 表示记录在
 * 但没有任何冲突出边。
 *
 * 【设计思想】只在 [tailXid, headXid] 有效区间内查找;区间外的
 * xid 一律返回 0(调用方按"无冲突"处理——比 tailXid 更老的 xid
 * 对当前事务不可能有重叠,比 headXid 更新的 xid 必然还活跃在
 * 内存中,不会走到这里)。读页用只读路径
 * SimpleLruReadPage_ReadOnly,拿到的 bank 锁必须由本函数释放。
 *
 * 【参数】xid —— 待查询的顶层事务 xid(须有效)。
 * 【返回值】见上:0 / InvalidSerCommitSeqNo / 具体的提交序号。
 */
static SerCommitSeqNo
SerialGetMinConflictCommitSeqNo(TransactionId xid)
{
	TransactionId headXid;
	TransactionId tailXid;
	SerCommitSeqNo val;
	int			slotno;

	Assert(TransactionIdIsValid(xid));

	LWLockAcquire(SerialControlLock, LW_SHARED);
	headXid = serialControl->headXid;
	tailXid = serialControl->tailXid;
	LWLockRelease(SerialControlLock);

	if (!TransactionIdIsValid(headXid))
		return 0;

	Assert(TransactionIdIsValid(tailXid));

	if (TransactionIdPrecedes(xid, tailXid)
		|| TransactionIdFollows(xid, headXid))
		return 0;

	/*
	 * The following function must be called without holding SLRU bank lock,
	 * but will return with that lock held, which must then be released.
	 */
	slotno = SimpleLruReadPage_ReadOnly(SerialSlruCtl,
										SerialPage(xid), &xid);
	val = SerialValue(slotno, xid);
	LWLockRelease(SimpleLruGetBankLock(SerialSlruCtl, SerialPage(xid)));
	return val;
}

/*
 * Call this whenever there is a new xmin for active serializable
 * transactions.  We don't need to keep information on transactions which
 * precede that.  InvalidTransactionId means none active, so everything in
 * the SLRU can be discarded.
 */
/*
 * SerialSetActiveSerXmin
 *      (中文)更新 Serial SLRU 的下界 tailXid(活动可串行化事务的 xmin)
 *
 * 【作用】每当可串行化事务的全局 xmin(SxactGlobalXmin)变化时
 * (SetNewSxactGlobalXmin / 注册事务时)调用:把 serialControl->
 * tailXid 推进到新的全局 xmin,比它更老的摘要即可丢弃。传
 * InvalidTransactionId 表示当前没有任何活动可串行化事务,此时把
 * tailXid/headXid 置为无效(但保留 headPage,避免反复清零同一页)。
 *
 * 【设计思想】tailXid 是 SLRU 的"清理水位":截断与 SerialAdd 的
 * 快速放弃都依据它。正常推进时断言 tailXid 只前进不后退;唯一
 * 例外是恢复 prepared 事务期间(RecoveryInProgress),此时没有事务
 * 会提交、SLRU 为空,允许 xmin 后退(恢复顺序所致)。
 *
 * 【参数】xid —— 新的活动可串行化事务 xmin;InvalidTransactionId
 * 表示无活动事务。【返回值】无。
 */
static void
SerialSetActiveSerXmin(TransactionId xid)
{
	LWLockAcquire(SerialControlLock, LW_EXCLUSIVE);

	/*
	 * When no sxacts are active, nothing overlaps, set the xid values to
	 * invalid to show that there are no valid entries.  Don't clear headPage,
	 * though.  A new xmin might still land on that page, and we don't want to
	 * repeatedly zero out the same page.
	 */
	if (!TransactionIdIsValid(xid))
	{
		serialControl->tailXid = InvalidTransactionId;
		serialControl->headXid = InvalidTransactionId;
		LWLockRelease(SerialControlLock);
		return;
	}

	/*
	 * When we're recovering prepared transactions, the global xmin might move
	 * backwards depending on the order they're recovered. Normally that's not
	 * OK, but during recovery no serializable transactions will commit, so
	 * the SLRU is empty and we can get away with it.
	 */
	if (RecoveryInProgress())
	{
		Assert(serialControl->headPage < 0);
		if (!TransactionIdIsValid(serialControl->tailXid)
			|| TransactionIdPrecedes(xid, serialControl->tailXid))
		{
			serialControl->tailXid = xid;
		}
		LWLockRelease(SerialControlLock);
		return;
	}

	Assert(!TransactionIdIsValid(serialControl->tailXid)
		   || TransactionIdFollows(xid, serialControl->tailXid));

	serialControl->tailXid = xid;

	LWLockRelease(SerialControlLock);
}

/*
 * Perform a checkpoint --- either during shutdown, or on-the-fly
 *
 * We don't have any data that needs to survive a restart, but this is a
 * convenient place to truncate the SLRU.
 */
/*
 * CheckPointPredicate
 *      (中文)检查点时的 Serial SLRU 截断与落盘
 *
 * 【作用】在检查点(正常关闭或 on-the-fly)时被调用:先确定可以
 * 截断掉的页号(Serial SLRU 不需要跨重启存活,这里纯粹是回收
 * 磁盘空间的时机),然后 SimpleLruTruncate 截断、SimpleLruWriteAll
 * 把脏页写出(仅为调试可读性,非正确性必需)。
 *
 * 【设计思想】截断水位取 tailXid 所在页与 headPage 的较前者:
 * 正常情况下可截到 tailXid 页;若 tailXid 反而"新于" headPage
 * (有事务正在推进 tail 但摘要尚未写入),只能保守截到 headPage;
 * 若已无有效 tailXid(没有活动事务),整个 SLRU 不再需要,截到
 * head 后把 headPage 置 -1 表示停用。英文注释还讨论了 XID 回绕
 * 边界上的极端情形(遗留头页可能被误认为新页),代价仅是一次
 * 罕见的 SimpleLruReadPage 失败,故未修。
 *
 * 【参数】无。【返回值】无。
 */
void
CheckPointPredicate(void)
{
	int64		truncateCutoffPage;

	LWLockAcquire(SerialControlLock, LW_EXCLUSIVE);

	/* Exit quickly if the SLRU is currently not in use. */
	if (serialControl->headPage < 0)
	{
		LWLockRelease(SerialControlLock);
		return;
	}

	if (TransactionIdIsValid(serialControl->tailXid))
	{
		int64		tailPage;

		tailPage = SerialPage(serialControl->tailXid);

		/*
		 * It is possible for the tailXid to be ahead of the headXid.  This
		 * occurs if we checkpoint while there are in-progress serializable
		 * transaction(s) advancing the tail but we are yet to summarize the
		 * transactions.  In this case, we cutoff up to the headPage and the
		 * next summary will advance the headXid.
		 */
		if (SerialPagePrecedesLogically(tailPage, serialControl->headPage))
		{
			/* We can truncate the SLRU up to the page containing tailXid */
			truncateCutoffPage = tailPage;
		}
		else
			truncateCutoffPage = serialControl->headPage;
	}
	else
	{
		/*----------
		 * The SLRU is no longer needed. Truncate to head before we set head
		 * invalid.
		 *
		 * XXX: It's possible that the SLRU is not needed again until XID
		 * wrap-around has happened, so that the segment containing headPage
		 * that we leave behind will appear to be new again. In that case it
		 * won't be removed until XID horizon advances enough to make it
		 * current again.
		 *
		 * XXX: This should happen in vac_truncate_clog(), not in checkpoints.
		 * Consider this scenario, starting from a system with no in-progress
		 * transactions and VACUUM FREEZE having maximized oldestXact:
		 * - Start a SERIALIZABLE transaction.
		 * - Start, finish, and summarize a SERIALIZABLE transaction, creating
		 *   one SLRU page.
		 * - Consume XIDs to reach xidStopLimit.
		 * - Finish all transactions.  Due to the long-running SERIALIZABLE
		 *   transaction, earlier checkpoints did not touch headPage.  The
		 *   next checkpoint will change it, but that checkpoint happens after
		 *   the end of the scenario.
		 * - VACUUM to advance XID limits.
		 * - Consume ~2M XIDs, crossing the former xidWrapLimit.
		 * - Start, finish, and summarize a SERIALIZABLE transaction.
		 *   SerialAdd() declines to create the targetPage, because headPage
		 *   is not regarded as in the past relative to that targetPage.  The
		 *   transaction instigating the summarize fails in
		 *   SimpleLruReadPage().
		 */
		truncateCutoffPage = serialControl->headPage;
		serialControl->headPage = -1;
	}

	LWLockRelease(SerialControlLock);

	/*
	 * Truncate away pages that are no longer required.  Note that no
	 * additional locking is required, because this is only called as part of
	 * a checkpoint, and the validity limits have already been determined.
	 */
	SimpleLruTruncate(SerialSlruCtl, truncateCutoffPage);

	/*
	 * Write dirty SLRU pages to disk
	 *
	 * This is not actually necessary from a correctness point of view. We do
	 * it merely as a debugging aid.
	 *
	 * We're doing this after the truncation to avoid writing pages right
	 * before deleting the file in which they sit, which would be completely
	 * pointless.
	 */
	SimpleLruWriteAll(SerialSlruCtl, true);
}

/*------------------------------------------------------------------------*/

/*
 * PredicateLockShmemRequest -- Register the predicate locking data structures.
 */
/*
 * PredicateLockShmemRequest
 *      (中文)登记谓词锁定所需的全部共享内存结构(大小估算)
 *
 * 【作用】postmaster 启动早期(共享内存尚未实际建立)由共享内存
 * 子系统回调:逐个 ShmemRequestHash / ShmemRequestStruct /
 * SimpleLruRequest 登记本模块需要的哈希表、列表、SLRU 及控制块,
 * 并给出条目规模估算。
 *
 * 【设计思想】估算规则(见各英文注释):目标表按
 * NPREDICATELOCKTARGETENTS(每后端 max_predicate_locks_per_xact);
 * 锁表按目标的 2 倍(平均每目标 2 个事务持锁);事务对象
 * (SERIALIZABLEXACT)按 (MaxBackends + max_prepared_xacts) * 10,
 * 冗余空间用于"先清理再摘要"的弹性;RWConflict 池按事务数的
 * 5 倍。这些估算值决定共享内存总量,一旦确定不能更改。
 * 断言编译期还会顺带运行 SerialPagePrecedesLogicallyUnitTests。
 *
 * 【参数】arg —— ShmemCallbacks 回调框架参数,未使用。
 * 【返回值】无。
 */
static void
PredicateLockShmemRequest(void *arg)
{
	int64		max_predicate_lock_targets;
	int64		max_predicate_locks;
	int64		max_rw_conflicts;

	/*
	 * Register hash table for PREDICATELOCKTARGET structs.  This stores
	 * per-predicate-lock-target information.
	 */
	max_predicate_lock_targets = NPREDICATELOCKTARGETENTS();

	ShmemRequestHash(.name = "PREDICATELOCKTARGET hash",
					 .nelems = max_predicate_lock_targets,
					 .ptr = &PredicateLockTargetHash,
					 .hash_info.keysize = sizeof(PREDICATELOCKTARGETTAG),
					 .hash_info.entrysize = sizeof(PREDICATELOCKTARGET),
					 .hash_info.num_partitions = NUM_PREDICATELOCK_PARTITIONS,
					 .hash_flags = HASH_ELEM | HASH_BLOBS | HASH_PARTITION | HASH_FIXED_SIZE,
		);

	/*
	 * Allocate hash table for PREDICATELOCK structs.  This stores per
	 * xact-lock-of-a-target information.
	 *
	 * Assume an average of 2 xacts per target.
	 */
	max_predicate_locks = max_predicate_lock_targets * 2;

	ShmemRequestHash(.name = "PREDICATELOCK hash",
					 .nelems = max_predicate_locks,
					 .ptr = &PredicateLockHash,
					 .hash_info.keysize = sizeof(PREDICATELOCKTAG),
					 .hash_info.entrysize = sizeof(PREDICATELOCK),
					 .hash_info.hash = predicatelock_hash,
					 .hash_info.num_partitions = NUM_PREDICATELOCK_PARTITIONS,
					 .hash_flags = HASH_ELEM | HASH_FUNCTION | HASH_PARTITION | HASH_FIXED_SIZE,
		);

	/*
	 * Compute size for serializable transaction hashtable.
	 *
	 * Assume an average of 10 predicate locking transactions per backend.
	 * This allows aggressive cleanup while detail is present before data must
	 * be summarized for storage in SLRU and the "dummy" transaction.
	 */
	max_serializable_xacts = (MaxBackends + max_prepared_xacts) * 10;

	/*
	 * Register a list to hold information on transactions participating in
	 * predicate locking.
	 */
	ShmemRequestStruct(.name = "PredXactList",
					   .size = add_size(PredXactListDataSize,
										(mul_size((Size) max_serializable_xacts,
												  sizeof(SERIALIZABLEXACT)))),
					   .ptr = (void **) &PredXact,
		);

	/*
	 * Register hash table for SERIALIZABLEXID structs.  This stores per-xid
	 * information for serializable transactions which have accessed data.
	 */
	ShmemRequestHash(.name = "SERIALIZABLEXID hash",
					 .nelems = max_serializable_xacts,
					 .ptr = &SerializableXidHash,
					 .hash_info.keysize = sizeof(SERIALIZABLEXIDTAG),
					 .hash_info.entrysize = sizeof(SERIALIZABLEXID),
					 .hash_flags = HASH_ELEM | HASH_BLOBS | HASH_FIXED_SIZE,
		);

	/*
	 * Allocate space for tracking rw-conflicts in lists attached to the
	 * transactions.
	 *
	 * Assume an average of 5 conflicts per transaction.  Calculations suggest
	 * that this will prevent resource exhaustion in even the most pessimal
	 * loads up to max_connections = 200 with all 200 connections pounding the
	 * database with serializable transactions.  Beyond that, there may be
	 * occasional transactions canceled when trying to flag conflicts. That's
	 * probably OK.
	 */
	max_rw_conflicts = max_serializable_xacts * 5;

	ShmemRequestStruct(.name = "RWConflictPool",
					   .size = RWConflictPoolHeaderDataSize + mul_size((Size) max_rw_conflicts,
																	   RWConflictDataSize),
					   .ptr = (void **) &RWConflictPool,
		);

	ShmemRequestStruct(.name = "FinishedSerializableTransactions",
					   .size = sizeof(dlist_head),
					   .ptr = (void **) &FinishedSerializableTransactions,
		);

	/*
	 * Initialize the SLRU storage for old committed serializable
	 * transactions.
	 */
	SimpleLruRequest(.desc = &SerialSlruDesc,
					 .name = "serializable",
					 .Dir = "pg_serial",
					 .long_segment_names = false,

					 .nslots = serializable_buffers,

					 .sync_handler = SYNC_HANDLER_NONE,
					 .PagePrecedes = SerialPagePrecedesLogically,
					 .errdetail_for_io_error = serial_errdetail_for_io_error,

					 .buffer_tranche_id = LWTRANCHE_SERIAL_BUFFER,
					 .bank_tranche_id = LWTRANCHE_SERIAL_SLRU,
		);
#ifdef USE_ASSERT_CHECKING
	SerialPagePrecedesLogicallyUnitTests();
#endif

	ShmemRequestStruct(.name = "SerialControlData",
					   .size = sizeof(SerialControlData),
					   .ptr = (void **) &serialControl,
		);
}

/*
 * PredicateLockShmemInit
 *      (中文)初始化谓词锁定的全部共享内存结构(仅 postmaster 执行)
 *
 * 【作用】共享内存建立后由子系统回调一次:在目标哈希表中预置
 * ScratchTargetTag 占位条目(保证后续分页/合并必有空位,见英文
 * 注释,否则可能中止一个非可串行化事务);初始化 PredXact 的
 * 空闲/活动链表并把所有 SERIALIZABLEXACT 槽位挂入空闲链;创建
 * OldCommittedSxact 虚拟事务并置好其 flags(COMMITTED);初始化
 * RWConflict 池、Finished 链表、Serial 控制块(空 SLRU 状态);
 * 最后缓存 OldCommittedSxact、ScratchTargetTagHash 与分区锁。
 *
 * 【设计思想】OldCommittedSxact 特意从普通池里取一个槽位并永远
 * 占着(commitSeqNo = 0,不参与任何活动事务判定),它是所有被
 * 摘要事务的谓词锁"归宿"。初始化顺序与锁层次一致,避免在
 * 尚未就绪时被并发访问。
 *
 * 【参数】arg —— ShmemCallbacks 回调框架参数,未使用。
 * 【返回值】无。
 */
static void
PredicateLockShmemInit(void *arg)
{
	int			max_rw_conflicts;
	bool		found;

	/*
	 * Reserve a dummy entry in the hash table; we use it to make sure there's
	 * always one entry available when we need to split or combine a page,
	 * because running out of space there could mean aborting a
	 * non-serializable transaction.
	 */
	(void) hash_search(PredicateLockTargetHash, &ScratchTargetTag,
					   HASH_ENTER, &found);
	Assert(!found);

	dlist_init(&PredXact->availableList);
	dlist_init(&PredXact->activeList);
	PredXact->SxactGlobalXmin = InvalidTransactionId;
	PredXact->SxactGlobalXminCount = 0;
	PredXact->WritableSxactCount = 0;
	PredXact->LastSxactCommitSeqNo = FirstNormalSerCommitSeqNo - 1;
	PredXact->CanPartialClearThrough = 0;
	PredXact->HavePartialClearedThrough = 0;
	PredXact->element
		= (SERIALIZABLEXACT *) ((char *) PredXact + PredXactListDataSize);
	/* Add all elements to available list, clean. */
	for (int i = 0; i < max_serializable_xacts; i++)
	{
		LWLockInitialize(&PredXact->element[i].perXactPredicateListLock,
						 LWTRANCHE_PER_XACT_PREDICATE_LIST);
		dlist_push_tail(&PredXact->availableList, &PredXact->element[i].xactLink);
	}
	PredXact->OldCommittedSxact = CreatePredXact();
	SetInvalidVirtualTransactionId(PredXact->OldCommittedSxact->vxid);
	PredXact->OldCommittedSxact->prepareSeqNo = 0;
	PredXact->OldCommittedSxact->commitSeqNo = 0;
	PredXact->OldCommittedSxact->SeqNo.lastCommitBeforeSnapshot = 0;
	dlist_init(&PredXact->OldCommittedSxact->outConflicts);
	dlist_init(&PredXact->OldCommittedSxact->inConflicts);
	dlist_init(&PredXact->OldCommittedSxact->predicateLocks);
	dlist_node_init(&PredXact->OldCommittedSxact->finishedLink);
	dlist_init(&PredXact->OldCommittedSxact->possibleUnsafeConflicts);
	PredXact->OldCommittedSxact->topXid = InvalidTransactionId;
	PredXact->OldCommittedSxact->finishedBefore = InvalidTransactionId;
	PredXact->OldCommittedSxact->xmin = InvalidTransactionId;
	PredXact->OldCommittedSxact->flags = SXACT_FLAG_COMMITTED;
	PredXact->OldCommittedSxact->pid = 0;
	PredXact->OldCommittedSxact->pgprocno = INVALID_PROC_NUMBER;

	/* Initialize the rw-conflict pool */
	dlist_init(&RWConflictPool->availableList);
	RWConflictPool->element = (RWConflict) ((char *) RWConflictPool +
											RWConflictPoolHeaderDataSize);

	max_rw_conflicts = max_serializable_xacts * 5;

	/* Add all elements to available list, clean. */
	for (int i = 0; i < max_rw_conflicts; i++)
	{
		dlist_push_tail(&RWConflictPool->availableList,
						&RWConflictPool->element[i].outLink);
	}

	/* Initialize the list of finished serializable transactions */
	dlist_init(FinishedSerializableTransactions);

	/* Initialize SerialControl to reflect empty SLRU. */
	LWLockAcquire(SerialControlLock, LW_EXCLUSIVE);
	serialControl->headPage = -1;
	serialControl->headXid = InvalidTransactionId;
	serialControl->tailXid = InvalidTransactionId;
	LWLockRelease(SerialControlLock);

	SlruPagePrecedesUnitTests(SerialSlruCtl, SERIAL_ENTRIESPERPAGE);

	/* This never changes, so let's keep a local copy. */
	OldCommittedSxact = PredXact->OldCommittedSxact;

	/* Pre-calculate the hash and partition lock of the scratch entry */
	ScratchTargetTagHash = PredicateLockTargetTagHashCode(&ScratchTargetTag);
	ScratchPartitionLock = PredicateLockHashPartitionLock(ScratchTargetTagHash);
}
/* (中文)各后端(包括 postmaster 之外的进程)附加到共享内存后调用:
 * 缓存从共享结构派生、且永不改变的本地副本——OldCommittedSxact
 * 指针、占位条目的哈希码与分区锁,避免每次使用时重算。 */

static void
PredicateLockShmemAttach(void *arg)
{
	/* This never changes, so let's keep a local copy. */
	OldCommittedSxact = PredXact->OldCommittedSxact;

	/* Pre-calculate the hash and partition lock of the scratch entry */
	ScratchTargetTagHash = PredicateLockTargetTagHashCode(&ScratchTargetTag);
	ScratchPartitionLock = PredicateLockHashPartitionLock(ScratchTargetTagHash);
}

/*
 * Compute the hash code associated with a PREDICATELOCKTAG.
 *
 * Because we want to use just one set of partition locks for both the
 * PREDICATELOCKTARGET and PREDICATELOCK hash tables, we have to make sure
 * that PREDICATELOCKs fall into the same partition number as their
 * associated PREDICATELOCKTARGETs.  dynahash.c expects the partition number
 * to be the low-order bits of the hash code, and therefore a
 * PREDICATELOCKTAG's hash code must have the same low-order bits as the
 * associated PREDICATELOCKTARGETTAG's hash code.  We achieve this with this
 * specialized hash function.
 */
/*
 * predicatelock_hash
 *      (中文)PREDICATELOCK 表专用的哈希函数
 *
 * 【作用】PredicateLockHash 的 hash 回调:取该锁指向的目标
 * (tag.myTarget)的 tag 计算目标哈希码,再用
 * PredicateLockHashCodeFromTargetHashCode 把持有事务的地址异或
 * 进去,得到锁的哈希码。
 *
 * 【设计思想】目标哈希码与锁哈希码的低 LOG2_NUM_PREDICATELOCK_
 * PARTITIONS 位相同(见英文注释),因此"锁"与"目标"永远落在
 * 同一分区、由同一把分区锁保护——一把分区锁即可安全维护
 * "目标 + 目标上的锁链表",这是本文件大量代码的前提。
 *
 * 【参数】
 *   key —— 指向 PREDICATELOCKTAG 的指针;
 *   keysize —— 键大小(断言为 sizeof(PREDICATELOCKTAG))。
 * 【返回值】锁条目的哈希码。
 */
static uint32
predicatelock_hash(const void *key, Size keysize)
{
	const PREDICATELOCKTAG *predicatelocktag = (const PREDICATELOCKTAG *) key;
	uint32		targethash;

	Assert(keysize == sizeof(PREDICATELOCKTAG));

	/* Look into the associated target object, and compute its hash code */
	targethash = PredicateLockTargetTagHashCode(&predicatelocktag->myTarget->tag);

	return PredicateLockHashCodeFromTargetHashCode(predicatelocktag, targethash);
}


/*
 * GetPredicateLockStatusData
 *		Return a table containing the internal state of the predicate
 *		lock manager for use in pg_lock_status.
 *
 * Like GetLockStatusData, this function tries to hold the partition LWLocks
 * for as short a time as possible by returning two arrays that simply
 * contain the PREDICATELOCKTARGETTAG and SERIALIZABLEXACT for each lock
 * table entry. Multiple copies of the same PREDICATELOCKTARGETTAG and
 * SERIALIZABLEXACT will likely appear.
 */
/*
 * GetPredicateLockStatusData
 *      (中文)导出谓词锁管理器内部状态(供 pg_locks 视图)
 *
 * 【作用】pg_lock_status / pg_locks 显示谓词锁时调用:按
 * PredicateLockHash 当前内容生成两个并行的输出数组——每个锁
 * 条目的目标 tag 与持有事务的 SERIALIZABLEXACT 副本。同一目标
 * 或同一事务可能重复出现多次(每把锁各一份)。
 *
 * 【设计思想】与 GetLockStatusData 类似:先按下标升序一次性获取
 * 全部分区锁,再取 SerializableXactHashLock,得到一个一致的快照;
 * 之后只做拷贝,不持有锁进行复杂操作,尽量缩短锁占用时间。
 * 输出在调用者的内存上下文里 palloc。
 *
 * 【参数】无。
 * 【返回值】PredicateLockData 结构(nelements + locktags[] +
 * xacts[]),由调用者负责释放。
 */
PredicateLockData *
GetPredicateLockStatusData(void)
{
	PredicateLockData *data;
	int			i;
	int			els,
				el;
	HASH_SEQ_STATUS seqstat;
	PREDICATELOCK *predlock;

	data = palloc_object(PredicateLockData);

	/*
	 * To ensure consistency, take simultaneous locks on all partition locks
	 * in ascending order, then SerializableXactHashLock.
	 */
	for (i = 0; i < NUM_PREDICATELOCK_PARTITIONS; i++)
		LWLockAcquire(PredicateLockHashPartitionLockByIndex(i), LW_SHARED);
	LWLockAcquire(SerializableXactHashLock, LW_SHARED);

	/* Get number of locks and allocate appropriately-sized arrays. */
	els = hash_get_num_entries(PredicateLockHash);
	data->nelements = els;
	data->locktags = palloc_array(PREDICATELOCKTARGETTAG, els);
	data->xacts = palloc_array(SERIALIZABLEXACT, els);


	/* Scan through PredicateLockHash and copy contents */
	hash_seq_init(&seqstat, PredicateLockHash);

	el = 0;

	while ((predlock = (PREDICATELOCK *) hash_seq_search(&seqstat)))
	{
		data->locktags[el] = predlock->tag.myTarget->tag;
		data->xacts[el] = *predlock->tag.myXact;
		el++;
	}

	Assert(el == els);

	/* Release locks in reverse order */
	LWLockRelease(SerializableXactHashLock);
	for (i = NUM_PREDICATELOCK_PARTITIONS - 1; i >= 0; i--)
		LWLockRelease(PredicateLockHashPartitionLockByIndex(i));

	return data;
}

/*
 * Free up shared memory structures by pushing the oldest sxact (the one at
 * the front of the SummarizeOldestCommittedSxact queue) into summary form.
 * Each call will free exactly one SERIALIZABLEXACT structure and may also
 * free one or more of these structures: SERIALIZABLEXID, PREDICATELOCK,
 * PREDICATELOCKTARGET, RWConflictData.
 */
/*
 * SummarizeOldestCommittedSxact
 *      (中文)把最老的已提交事务摘要进 SLRU,腾出一个事务槽位
 *
 * 【作用】当事务对象池(availableList)为空、无法为新事务分配
 * SERIALIZABLEXACT 时,由 GetSerializableTransactionSnapshotInt 循环
 * 调用:从 FinishedSerializableTransactions(按提交顺序)头部取下
 * 最老已提交事务,把其冲突摘要写进 Serial SLRU
 * (SerialAdd),再释放其全部细节结构(谓词锁转交虚拟事务、
 * 冲突边与 xid 记录删除、槽位归还),从而腾出共享内存。
 *
 * 【设计思想】这是共享内存上界机制的另一半:内存里的细节
 * (锁、冲突边)与磁盘上的摘要(SLRU)互为取舍。摘要只关心
 * "该事务是否带冲突出边、最早指向哪次提交",足够后续做保守
 * 的冲突判定。注意并发竞争:另一个后端可能已抢先把链上事务
 * 清理干净(释放了槽位),此时本函数直接返回,调用者重试分配
 * 即可。
 *
 * 【参数】无。
 * 【返回值】无(不一定真的释放了槽位,调用者要循环重试)。
 */
static void
SummarizeOldestCommittedSxact(void)
{
	SERIALIZABLEXACT *sxact;

	LWLockAcquire(SerializableFinishedListLock, LW_EXCLUSIVE);

	/*
	 * This function is only called if there are no sxact slots available.
	 * Some of them must belong to old, already-finished transactions, so
	 * there should be something in FinishedSerializableTransactions list that
	 * we can summarize. However, there's a race condition: while we were not
	 * holding any locks, a transaction might have ended and cleaned up all
	 * the finished sxact entries already, freeing up their sxact slots. In
	 * that case, we have nothing to do here. The caller will find one of the
	 * slots released by the other backend when it retries.
	 */
	if (dlist_is_empty(FinishedSerializableTransactions))
	{
		LWLockRelease(SerializableFinishedListLock);
		return;
	}

	/*
	 * Grab the first sxact off the finished list -- this will be the earliest
	 * commit.  Remove it from the list.
	 */
	sxact = dlist_head_element(SERIALIZABLEXACT, finishedLink,
							   FinishedSerializableTransactions);
	dlist_delete_thoroughly(&sxact->finishedLink);

	/* Add to SLRU summary information. */
	if (TransactionIdIsValid(sxact->topXid) && !SxactIsReadOnly(sxact))
		SerialAdd(sxact->topXid, SxactHasConflictOut(sxact)
				  ? sxact->SeqNo.earliestOutConflictCommit : InvalidSerCommitSeqNo);

	/* Summarize and release the detail. */
	ReleaseOneSerializableXact(sxact, false, true);

	LWLockRelease(SerializableFinishedListLock);
}

/*
 * GetSafeSnapshot
 *		Obtain and register a snapshot for a READ ONLY DEFERRABLE
 *		transaction. Ensures that the snapshot is "safe", i.e. a
 *		read-only transaction running on it can execute serializably
 *		without further checks. This requires waiting for concurrent
 *		transactions to complete, and retrying with a new snapshot if
 *		one of them could possibly create a conflict.
 *
 *		As with GetSerializableTransactionSnapshot (which this is a subroutine
 *		for), the passed-in Snapshot pointer should reference a static data
 *		area that can safely be passed to GetSnapshotData.
 */
/*
 * GetSafeSnapshot
 *      (中文)为 READ ONLY DEFERRABLE 事务获取"安全快照"
 *
 * 【作用】SERIALIZABLE READ ONLY DEFERRABLE 事务取快照时调用:
 * 循环获取快照并注册事务,等待所有与之重叠的读写事务结束。
 * 若其中任何写者提交时带有早于本快照的冲突出边(快照被判
 * RO_UNSAFE),丢弃本次快照、重试新快照;直到拿到被证明安全
 * (RO_SAFE)的快照为止——拿到后即可释放全部谓词锁、以零 SSI
 * 开销运行。
 *
 * 【设计思想】快照安全性要到"所有重叠读写事务都提交"才能
 * 判定。DEFERRABLE 事务为此愿意等待:等待期间置
 * SXACT_FLAG_DEFERRABLE_WAITING 标志,写者提交时
 * (ReleasePredicateLocks)若判定其安全/不安全会 ProcSendSignal
 * 唤醒;被唤醒后重查条件(possibleUnsafeConflicts 清空 = 安全,
 * RO_UNSAFE = 不安全需重试)。DEBUG2 日志记录重试以便诊断。
 *
 * 【参数】origSnapshot —— 调用者提供的静态快照存储区(原样传给
 * GetSerializableTransactionSnapshotInt 供 GetSnapshotData 使用)。
 * 【返回值】安全的 Snapshot 指针(即传入的那块存储区);若当时
 * 没有任何并发读写事务,第一次循环就安全返回。
 */
static Snapshot
GetSafeSnapshot(Snapshot origSnapshot)
{
	Snapshot	snapshot;

	Assert(XactReadOnly && XactDeferrable);

	while (true)
	{
		/*
		 * GetSerializableTransactionSnapshotInt is going to call
		 * GetSnapshotData, so we need to provide it the static snapshot area
		 * our caller passed to us.  The pointer returned is actually the same
		 * one passed to it, but we avoid assuming that here.
		 */
		snapshot = GetSerializableTransactionSnapshotInt(origSnapshot,
														 NULL, InvalidPid);

		if (MySerializableXact == InvalidSerializableXact)
			return snapshot;	/* no concurrent r/w xacts; it's safe */

		LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

		/*
		 * Wait for concurrent transactions to finish. Stop early if one of
		 * them marked us as conflicted.
		 */
		MySerializableXact->flags |= SXACT_FLAG_DEFERRABLE_WAITING;
		while (!(dlist_is_empty(&MySerializableXact->possibleUnsafeConflicts) ||
				 SxactIsROUnsafe(MySerializableXact)))
		{
			LWLockRelease(SerializableXactHashLock);
			ProcWaitForSignal(WAIT_EVENT_SAFE_SNAPSHOT);
			LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);
		}
		MySerializableXact->flags &= ~SXACT_FLAG_DEFERRABLE_WAITING;

		if (!SxactIsROUnsafe(MySerializableXact))
		{
			LWLockRelease(SerializableXactHashLock);
			break;				/* success */
		}

		LWLockRelease(SerializableXactHashLock);

		/* else, need to retry... */
		ereport(DEBUG2,
				(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
				 errmsg_internal("deferrable snapshot was unsafe; trying a new one")));
		ReleasePredicateLocks(false, false);
	}

	/*
	 * Now we have a safe snapshot, so we don't need to do any further checks.
	 */
	Assert(SxactIsROSafe(MySerializableXact));
	ReleasePredicateLocks(false, true);

	return snapshot;
}

/*
 * GetSafeSnapshotBlockingPids
 *		If the specified process is currently blocked in GetSafeSnapshot,
 *		write the process IDs of all processes that it is blocked by
 *		into the caller-supplied buffer output[].  The list is truncated at
 *		output_size, and the number of PIDs written into the buffer is
 *		returned.  Returns zero if the given PID is not currently blocked
 *		in GetSafeSnapshot.
 */
/*
 * GetSafeSnapshotBlockingPids
 *      (中文)报告阻塞在 GetSafeSnapshot 中的进程被谁"挡着"
 *
 * 【作用】pg_blocking_pids 等诊断功能使用:若指定 PID 的进程当前
 * 正作为 DEFERRABLE 只读事务等待安全快照,则把"可能让它不安全"
 * 的并发读写事务所在进程的 PID 写入输出缓冲区(截断到
 * output_size),返回写入了几个。
 *
 * 【设计思想】等待者被"阻塞"的语义不是持锁,而是必须等所有
 * 重叠读写事务提交结算;因此把 possibleUnsafeConflicts 链表上
 * 各写者的 pid 当作阻塞者上报,让 DBA 能看到等待原因。
 *
 * 【参数】
 *   blocked_pid —— 待查询的进程号;
 *   output —— 输出缓冲区;
 *   output_size —— 缓冲区容量。
 * 【返回值】写入的 PID 个数;该进程不在等待则返回 0。
 */
int
GetSafeSnapshotBlockingPids(int blocked_pid, int *output, int output_size)
{
	int			num_written = 0;
	dlist_iter	iter;
	SERIALIZABLEXACT *blocking_sxact = NULL;

	LWLockAcquire(SerializableXactHashLock, LW_SHARED);

	/* Find blocked_pid's SERIALIZABLEXACT by linear search. */
	dlist_foreach(iter, &PredXact->activeList)
	{
		SERIALIZABLEXACT *sxact =
			dlist_container(SERIALIZABLEXACT, xactLink, iter.cur);

		if (sxact->pid == blocked_pid)
		{
			blocking_sxact = sxact;
			break;
		}
	}

	/* Did we find it, and is it currently waiting in GetSafeSnapshot? */
	if (blocking_sxact != NULL && SxactIsDeferrableWaiting(blocking_sxact))
	{
		/* Traverse the list of possible unsafe conflicts collecting PIDs. */
		dlist_foreach(iter, &blocking_sxact->possibleUnsafeConflicts)
		{
			RWConflict	possibleUnsafeConflict =
				dlist_container(RWConflictData, inLink, iter.cur);

			output[num_written++] = possibleUnsafeConflict->sxactOut->pid;

			if (num_written >= output_size)
				break;
		}
	}

	LWLockRelease(SerializableXactHashLock);

	return num_written;
}

/*
 * Acquire a snapshot that can be used for the current transaction.
 *
 * Make sure we have a SERIALIZABLEXACT reference in MySerializableXact.
 * It should be current for this process and be contained in PredXact.
 *
 * The passed-in Snapshot pointer should reference a static data area that
 * can safely be passed to GetSnapshotData.  The return value is actually
 * always this same pointer; no new snapshot data structure is allocated
 * within this function.
 */
/*
 * GetSerializableTransactionSnapshot
 *      (中文)为当前事务获取可用于可串行化隔离的快照
 *
 * 【作用】可串行化事务开始(获取第一个快照)时由 snapmgr 调用:
 * 保证 MySerializableXact 就位(创建/注册 SERIALIZABLEXACT),返回
 * 可用于本事务的快照。READ ONLY DEFERRABLE 事务走 GetSafeSnapshot
 * 等待安全快照;其余直接走 GetSerializableTransactionSnapshotInt。
 * hot standby(恢复中)禁止使用 SERIALIZABLE(SSI 的共享结构在
 * standby 不工作),直接报错并给出改默认隔离级别的提示。
 *
 * 【设计思想】一个可串行化事务的所有部分必须共用同一快照,因此
 * 该函数整个生命周期只应调用一次(在第一个快照请求时)。
 * DEFERRABLE 优化把"等待 + 验证安全"合并到取快照阶段,换取
 * 之后零 SSI 开销。
 *
 * 【参数】snapshot —— 调用者提供的静态快照存储区(供
 * GetSnapshotData 填充)。
 * 【返回值】同一指针;未分配新结构。
 */
Snapshot
GetSerializableTransactionSnapshot(Snapshot snapshot)
{
	Assert(IsolationIsSerializable());

	/*
	 * Can't use serializable mode while recovery is still active, as it is,
	 * for example, on a hot standby.  We could get here despite the check in
	 * check_transaction_isolation() if default_transaction_isolation is set
	 * to serializable, so phrase the hint accordingly.
	 */
	if (RecoveryInProgress())
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("cannot use serializable mode in a hot standby"),
				 errdetail("\"default_transaction_isolation\" is set to \"serializable\"."),
				 errhint("You can use \"SET default_transaction_isolation = 'repeatable read'\" to change the default.")));

	/*
	 * A special optimization is available for SERIALIZABLE READ ONLY
	 * DEFERRABLE transactions -- we can wait for a suitable snapshot and
	 * thereby avoid all SSI overhead once it's running.
	 */
	if (XactReadOnly && XactDeferrable)
		return GetSafeSnapshot(snapshot);

	return GetSerializableTransactionSnapshotInt(snapshot,
												 NULL, InvalidPid);
}

/*
 * Import a snapshot to be used for the current transaction.
 *
 * This is nearly the same as GetSerializableTransactionSnapshot, except that
 * we don't take a new snapshot, but rather use the data we're handed.
 *
 * The caller must have verified that the snapshot came from a serializable
 * transaction; and if we're read-write, the source transaction must not be
 * read-only.
 */
/*
 * SetSerializableTransactionSnapshot
 *      (中文)导入一个快照供当前事务使用(并行 worker / 快照导入)
 *
 * 【作用】与 GetSerializableTransactionSnapshot 几乎相同,但不新取
 * 快照,而是采用调用方传入的快照内容(来自另一个可串行化事务)。
 * 调用方须已验证:快照来自可串行化事务;若本事务可写,源事务
 * 必须也是可写的(否则会破坏 SSI 的读写对称性)。
 *
 * 【设计思想】并行 worker 直接返回,不创建事务对象——leader 的
 * SERIALIZABLEXACT 稍后经 AttachSerializableXact 安装,同时
 * DEFERRABLE 也不在此处拒绝(leader 已确认快照安全)。普通
 * 后端导入快照时,READ ONLY DEFERRABLE 组合被禁止(没有机会等待
 * 安全快照,详见英文注释的 XXX 讨论)。真正的工作交给
 * GetSerializableTransactionSnapshotInt(其内部会校验源事务是否
 * 仍存活)。
 *
 * 【参数】
 *   snapshot —— 导入的快照(其 xmin 等已填好);
 *   sourcevxid —— 源事务的 vxid(用于存活校验);
 *   sourcepid —— 源进程 PID(仅用于错误提示)。
 * 【返回值】无。
 */
void
SetSerializableTransactionSnapshot(Snapshot snapshot,
								   VirtualTransactionId *sourcevxid,
								   int sourcepid)
{
	Assert(IsolationIsSerializable());

	/*
	 * If this is called by parallel.c in a parallel worker, we don't want to
	 * create a SERIALIZABLEXACT just yet because the leader's
	 * SERIALIZABLEXACT will be installed with AttachSerializableXact().  We
	 * also don't want to reject SERIALIZABLE READ ONLY DEFERRABLE in this
	 * case, because the leader has already determined that the snapshot it
	 * has passed us is safe.  So there is nothing for us to do.
	 */
	if (IsParallelWorker())
		return;

	/*
	 * We do not allow SERIALIZABLE READ ONLY DEFERRABLE transactions to
	 * import snapshots, since there's no way to wait for a safe snapshot when
	 * we're using the snap we're told to.  (XXX instead of throwing an error,
	 * we could just ignore the XactDeferrable flag?)
	 */
	if (XactReadOnly && XactDeferrable)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("a snapshot-importing transaction must not be READ ONLY DEFERRABLE")));

	(void) GetSerializableTransactionSnapshotInt(snapshot, sourcevxid,
												 sourcepid);
}

/*
 * Guts of GetSerializableTransactionSnapshot
 *
 * If sourcevxid is valid, this is actually an import operation and we should
 * skip calling GetSnapshotData, because the snapshot contents are already
 * loaded up.  HOWEVER: to avoid race conditions, we must check that the
 * source xact is still running after we acquire SerializableXactHashLock.
 * We do that by calling ProcArrayInstallImportedXmin.
 */
/*
 * GetSerializableTransactionSnapshotInt
 *      (中文)获取/导入可串行化快照的核心实现
 *
 * 【作用】分配并初始化本事务的 SERIALIZABLEXACT 对象,取快照
 * (或校验导入快照),登记只读事务的"潜在不安全"关系或递增
 * 可写事务计数,维护 SxactGlobalXmin 与 Serial SLRU 下界,最后
 * 建立本地谓词锁表并设置 MySerializableXact。
 *
 * 【执行流程】
 * 1. 在 SerializableXactHashLock 下 CreatePredXact 分配槽位;池空
 *    则释放锁、SummarizeOldestCommittedSxact、重新取锁重试;
 * 2. 无 sourcevxid 时调用 GetSnapshotData;有则用
 *    ProcArrayInstallImportedXmin 校验源事务仍存活(失败则放弃
 *    槽位并报错);
 * 3. 优化:只读事务且当前没有任何活动读写事务
 *    (WritableSxactCount == 0)时,直接放弃槽位返回——不会有任何
 *    事务能与之构成危险结构(见英文注释的论证);
 * 4. 初始化字段;只读事务为每个未提交读写事务记一条
 *    SetPossibleUnsafeConflict(全为 doomed 则同样直接 opt out);
 *    读写事务递增 WritableSxactCount;
 * 5. 维护 SxactGlobalXmin 计数与 SerialSetActiveSerXmin;
 * 6. 设置 MySerializableXact,CreateLocalPredicateLockHash。
 *
 * 【设计思想】必须在持 SerializableXactHashLock 时取快照,理由
 * 与 GetSnapshotData 持 ProcArrayLock 相同(快照与事务注册须
 * 原子可见),这导致"先分配槽位再取快照"的顺序(英文注释
 * 承认 procarray 报错可能泄漏槽位,等待重构)。
 *
 * 【参数】
 *   snapshot —— 静态快照存储区;导入模式(sourcevxid 有效)时
 *   xmin 已填好,否则由 GetSnapshotData 填充;
 *   sourcevxid —— 导入模式的源事务 vxid,NULL 表示普通取快照;
 *   sourcepid —— 源进程 PID(仅错误提示用)。
 * 【返回值】填充好的 Snapshot 指针(即传入的存储区)。
 */
static Snapshot
GetSerializableTransactionSnapshotInt(Snapshot snapshot,
									  VirtualTransactionId *sourcevxid,
									  int sourcepid)
{
	PGPROC	   *proc;
	VirtualTransactionId vxid;
	SERIALIZABLEXACT *sxact,
			   *othersxact;

	/* We only do this for serializable transactions.  Once. */
	Assert(MySerializableXact == InvalidSerializableXact);

	Assert(!RecoveryInProgress());

	/*
	 * Since all parts of a serializable transaction must use the same
	 * snapshot, it is too late to establish one after a parallel operation
	 * has begun.
	 */
	if (IsInParallelMode())
		elog(ERROR, "cannot establish serializable snapshot during a parallel operation");

	proc = MyProc;
	Assert(proc != NULL);
	GET_VXID_FROM_PGPROC(vxid, *proc);

	/*
	 * First we get the sxact structure, which may involve looping and access
	 * to the "finished" list to free a structure for use.
	 *
	 * We must hold SerializableXactHashLock when taking/checking the snapshot
	 * to avoid race conditions, for much the same reasons that
	 * GetSnapshotData takes the ProcArrayLock.  Since we might have to
	 * release SerializableXactHashLock to call SummarizeOldestCommittedSxact,
	 * this means we have to create the sxact first, which is a bit annoying
	 * (in particular, an elog(ERROR) in procarray.c would cause us to leak
	 * the sxact).  Consider refactoring to avoid this.
	 */
#ifdef TEST_SUMMARIZE_SERIAL
	SummarizeOldestCommittedSxact();
#endif
	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);
	do
	{
		sxact = CreatePredXact();
		/* If null, push out committed sxact to SLRU summary & retry. */
		if (!sxact)
		{
			LWLockRelease(SerializableXactHashLock);
			SummarizeOldestCommittedSxact();
			LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);
		}
	} while (!sxact);

	/* Get the snapshot, or check that it's safe to use */
	if (!sourcevxid)
		snapshot = GetSnapshotData(snapshot);
	else if (!ProcArrayInstallImportedXmin(snapshot->xmin, sourcevxid))
	{
		ReleasePredXact(sxact);
		LWLockRelease(SerializableXactHashLock);
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("could not import the requested snapshot"),
				 errdetail("The source process with PID %d is not running anymore.",
						   sourcepid)));
	}

	/*
	 * If there are no serializable transactions which are not read-only, we
	 * can "opt out" of predicate locking and conflict checking for a
	 * read-only transaction.
	 *
	 * The reason this is safe is that a read-only transaction can only become
	 * part of a dangerous structure if it overlaps a writable transaction
	 * which in turn overlaps a writable transaction which committed before
	 * the read-only transaction started.  A new writable transaction can
	 * overlap this one, but it can't meet the other condition of overlapping
	 * a transaction which committed before this one started.
	 */
	if (XactReadOnly && PredXact->WritableSxactCount == 0)
	{
		ReleasePredXact(sxact);
		LWLockRelease(SerializableXactHashLock);
		return snapshot;
	}

	/* Initialize the structure. */
	sxact->vxid = vxid;
	sxact->SeqNo.lastCommitBeforeSnapshot = PredXact->LastSxactCommitSeqNo;
	sxact->prepareSeqNo = InvalidSerCommitSeqNo;
	sxact->commitSeqNo = InvalidSerCommitSeqNo;
	dlist_init(&(sxact->outConflicts));
	dlist_init(&(sxact->inConflicts));
	dlist_init(&(sxact->possibleUnsafeConflicts));
	sxact->topXid = GetTopTransactionIdIfAny();
	sxact->finishedBefore = InvalidTransactionId;
	sxact->xmin = snapshot->xmin;
	sxact->pid = MyProcPid;
	sxact->pgprocno = MyProcNumber;
	dlist_init(&sxact->predicateLocks);
	dlist_node_init(&sxact->finishedLink);
	sxact->flags = 0;
	if (XactReadOnly)
	{
		dlist_iter	iter;

		sxact->flags |= SXACT_FLAG_READ_ONLY;

		/*
		 * Register all concurrent r/w transactions as possible conflicts; if
		 * all of them commit without any outgoing conflicts to earlier
		 * transactions then this snapshot can be deemed safe (and we can run
		 * without tracking predicate locks).
		 */
		dlist_foreach(iter, &PredXact->activeList)
		{
			othersxact = dlist_container(SERIALIZABLEXACT, xactLink, iter.cur);

			if (!SxactIsCommitted(othersxact)
				&& !SxactIsDoomed(othersxact)
				&& !SxactIsReadOnly(othersxact))
			{
				SetPossibleUnsafeConflict(sxact, othersxact);
			}
		}

		/*
		 * If we didn't find any possibly unsafe conflicts because every
		 * uncommitted writable transaction turned out to be doomed, then we
		 * can "opt out" immediately.  See comments above the earlier check
		 * for PredXact->WritableSxactCount == 0.
		 */
		if (dlist_is_empty(&sxact->possibleUnsafeConflicts))
		{
			ReleasePredXact(sxact);
			LWLockRelease(SerializableXactHashLock);
			return snapshot;
		}
	}
	else
	{
		++(PredXact->WritableSxactCount);
		Assert(PredXact->WritableSxactCount <=
			   (MaxBackends + max_prepared_xacts));
	}

	/* Maintain serializable global xmin info. */
	if (!TransactionIdIsValid(PredXact->SxactGlobalXmin))
	{
		Assert(PredXact->SxactGlobalXminCount == 0);
		PredXact->SxactGlobalXmin = snapshot->xmin;
		PredXact->SxactGlobalXminCount = 1;
		SerialSetActiveSerXmin(snapshot->xmin);
	}
	else if (TransactionIdEquals(snapshot->xmin, PredXact->SxactGlobalXmin))
	{
		Assert(PredXact->SxactGlobalXminCount > 0);
		PredXact->SxactGlobalXminCount++;
	}
	else
	{
		Assert(TransactionIdFollows(snapshot->xmin, PredXact->SxactGlobalXmin));
	}

	MySerializableXact = sxact;
	MyXactDidWrite = false;		/* haven't written anything yet */

	LWLockRelease(SerializableXactHashLock);

	CreateLocalPredicateLockHash();

	return snapshot;
}

/* (中文)创建后端本地的谓词锁记账表(进程私有内存):键为目标
 * tag,值为 LOCALPREDICATELOCK(held + childLocks)。每次可串行化
 * 事务取快照后调用一次,事务结束时整体销毁(ReleasePredicateLocksLocal)。
 * 它用于快速判断"某锁是否已持有/被更粗锁覆盖",并统计父锁的
 * 孩子数以便粒度提升;纯优化数据结构,允许漂移(见英文注释)。 */

static void
CreateLocalPredicateLockHash(void)
{
	HASHCTL		hash_ctl;

	/* Initialize the backend-local hash table of parent locks */
	Assert(LocalPredicateLockHash == NULL);
	hash_ctl.keysize = sizeof(PREDICATELOCKTARGETTAG);
	hash_ctl.entrysize = sizeof(LOCALPREDICATELOCK);
	LocalPredicateLockHash = hash_create("Local predicate lock",
										 max_predicate_locks_per_xact,
										 &hash_ctl,
										 HASH_ELEM | HASH_BLOBS);
}

/*
 * Register the top level XID in SerializableXidHash.
 * Also store it for easy reference in MySerializableXact.
 */
/*
 * RegisterPredicateLockingXid
 *      (中文)注册顶层 XID 到 SerializableXidHash
 *
 * 【作用】本事务第一次拿到顶层 xid 时(GetNewTransactionId 路径)
 * 调用:把 xid 与 MySerializableXact 的对应关系记入
 * SerializableXidHash,并把 xid 存进 MySerializableXact->topXid。
 * 此后任何进程(甚至事务结束后)都能从元组里的 xid 反查事务
 * 对象。
 *
 * 【设计思想】PostgreSQL 事务直到第一次写才分配 xid,而 SSI 的
 * 读锁登记在取快照时就已开始,所以"xid → 事务"映射的建立
 * 被推迟到此刻;只读事务可能永远不调用本函数(topXid 保持
 * InvalidTransactionId)。只允许每个事务调用一次。
 *
 * 【参数】xid —— 本事务的顶层事务号(须有效)。
 * 【返回值】无。
 */
void
RegisterPredicateLockingXid(TransactionId xid)
{
	SERIALIZABLEXIDTAG sxidtag;
	SERIALIZABLEXID *sxid;
	bool		found;

	/*
	 * If we're not tracking predicate lock data for this transaction, we
	 * should ignore the request and return quickly.
	 */
	if (MySerializableXact == InvalidSerializableXact)
		return;

	/* We should have a valid XID and be at the top level. */
	Assert(TransactionIdIsValid(xid));

	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	/* This should only be done once per transaction. */
	Assert(MySerializableXact->topXid == InvalidTransactionId);

	MySerializableXact->topXid = xid;

	sxidtag.xid = xid;
	sxid = (SERIALIZABLEXID *) hash_search(SerializableXidHash,
										   &sxidtag,
										   HASH_ENTER, &found);
	Assert(!found);

	/* Initialize the structure. */
	sxid->myXact = MySerializableXact;
	LWLockRelease(SerializableXactHashLock);
}


/*
 * Check whether there are any predicate locks held by any transaction
 * for the page at the given block number.
 *
 * Note that the transaction may be completed but not yet subject to
 * cleanup due to overlapping serializable transactions.  This must
 * return valid information regardless of transaction isolation level.
 *
 * Also note that this doesn't check for a conflicting relation lock,
 * just a lock specifically on the given page.
 *
 * One use is to support proper behavior during GiST index vacuum.
 */
/*
 * PageIsPredicateLocked
 *      (中文)指定页上是否存在任何事务持有的谓词锁
 *
 * 【作用】查询共享目标表:某关系的某页是否被"任何事务"(包括
 * 已提交但尚未清理的)加了页级谓词锁。GiST 索引 VACUUM 用它
 * 决定是否需要对页做特殊处理。
 *
 * 【设计思想】只查页级目标本身,不检查更粗的关系级锁(调用方
 * 需要精确的"页级锁存在与否"语义);结果与调用方隔离级别
 * 无关,因为已提交事务的锁要保留到所有重叠事务结束。共享
 * 分区锁仅短暂持有(查完即放)。
 *
 * 【参数】
 *   relation —— 待查询的关系;
 *   blkno —— 页号。
 * 【返回值】true = 该页存在页级谓词锁;false = 没有。
 */
bool
PageIsPredicateLocked(Relation relation, BlockNumber blkno)
{
	PREDICATELOCKTARGETTAG targettag;
	uint32		targettaghash;
	LWLock	   *partitionLock;
	PREDICATELOCKTARGET *target;

	SET_PREDICATELOCKTARGETTAG_PAGE(targettag,
									relation->rd_locator.dbOid,
									relation->rd_id,
									blkno);

	targettaghash = PredicateLockTargetTagHashCode(&targettag);
	partitionLock = PredicateLockHashPartitionLock(targettaghash);
	LWLockAcquire(partitionLock, LW_SHARED);
	target = (PREDICATELOCKTARGET *)
		hash_search_with_hash_value(PredicateLockTargetHash,
									&targettag, targettaghash,
									HASH_FIND, NULL);
	LWLockRelease(partitionLock);

	return (target != NULL);
}


/*
 * Check whether a particular lock is held by this transaction.
 *
 * Important note: this function may return false even if the lock is
 * being held, because it uses the local lock table which is not
 * updated if another transaction modifies our lock list (e.g. to
 * split an index page). It can also return true when a coarser
 * granularity lock that covers this target is being held. Be careful
 * to only use this function in circumstances where such errors are
 * acceptable!
 */
/*
 * PredicateLockExists
 *      (中文)本事务是否已持有(或被覆盖)指定目标的谓词锁?
 *
 * 【作用】在本地锁表(LocalPredicateLockHash)中按目标 tag 查找。
 * 返回 false 并不保证锁真的不存在——本地表不随"其他进程替
 * 我们改锁"而更新(如索引页分裂把锁转移走);返回 true 也可能
 * 是持有的是覆盖该目标的更粗锁。英文注释警告:只允许在
 * 能容忍这种误差的场景使用。
 *
 * 【设计思想】本地表是免锁的优化缓存:held 字段区分"真持有"
 * 与"只是父锁被登记"(子锁的父节点以 held = false 存在,用于
 * 统计 childLocks)。
 *
 * 【参数】targettag —— 待查询的目标。
 * 【返回值】true = 本地记录显示已持有或被子锁覆盖。
 */
static bool
PredicateLockExists(const PREDICATELOCKTARGETTAG *targettag)
{
	LOCALPREDICATELOCK *lock;

	/* check local hash table */
	lock = (LOCALPREDICATELOCK *) hash_search(LocalPredicateLockHash,
											  targettag,
											  HASH_FIND, NULL);

	if (!lock)
		return false;

	/*
	 * Found entry in the table, but still need to check whether it's actually
	 * held -- it could just be a parent of some held lock.
	 */
	return lock->held;
}

/*
 * Return the parent lock tag in the lock hierarchy: the next coarser
 * lock that covers the provided tag.
 *
 * Returns true and sets *parent to the parent tag if one exists,
 * returns false if none exists.
 */
/*
 * GetParentPredicateLockTag
 *      (中文)求锁层次中"下一级更粗"的父目标 tag
 *
 * 【作用】给定目标 tag,返回覆盖它的、更粗一级的锁目标:
 * 元组 → 所在页;页 → 所在表;表没有父级(返回 false)。
 *
 * 【设计思想】层次结构 表 ⊇ 页 ⊇ 元组 是粒度提升/覆盖判断的
 * 骨架:PredicateLockAcquire 沿它逐级上溯寻找已持有的粗锁
 * (CoarserLockCovers),CheckAndPromotePredicateLockRequest 沿它
 * 递增父锁的孩子计数。tag 的类型由 GET_PREDICATELOCKTARGETTAG_TYPE
 * 按 field3/field4 是否为无效值推断。
 *
 * 【参数】
 *   tag —— 当前目标;
 *   parent —— 输出参数,收到父目标的 tag(仅返回 true 时有效)。
 * 【返回值】true = 存在父级且已填入;false = 已是最高级(表锁)。
 */
static bool
GetParentPredicateLockTag(const PREDICATELOCKTARGETTAG *tag,
						  PREDICATELOCKTARGETTAG *parent)
{
	switch (GET_PREDICATELOCKTARGETTAG_TYPE(*tag))
	{
		case PREDLOCKTAG_RELATION:
			/* relation locks have no parent lock */
			return false;

		case PREDLOCKTAG_PAGE:
			/* parent lock is relation lock */
			SET_PREDICATELOCKTARGETTAG_RELATION(*parent,
												GET_PREDICATELOCKTARGETTAG_DB(*tag),
												GET_PREDICATELOCKTARGETTAG_RELATION(*tag));

			return true;

		case PREDLOCKTAG_TUPLE:
			/* parent lock is page lock */
			SET_PREDICATELOCKTARGETTAG_PAGE(*parent,
											GET_PREDICATELOCKTARGETTAG_DB(*tag),
											GET_PREDICATELOCKTARGETTAG_RELATION(*tag),
											GET_PREDICATELOCKTARGETTAG_PAGE(*tag));
			return true;
	}

	/* not reachable */
	Assert(false);
	return false;
}

/*
 * Check whether the lock we are considering is already covered by a
 * coarser lock for our transaction.
 *
 * Like PredicateLockExists, this function might return a false
 * negative, but it will never return a false positive.
 */
/*
 * CoarserLockCovers
 *      (中文)更粗粒度的锁是否已覆盖待加的目标?
 *
 * 【作用】PredicateLockAcquire 的快速检查之一:沿锁层次向上
 * (元组→页→表)逐级查本地表,任何一级已持有即表示无需再加
 * 新锁(粗锁的语义已覆盖细目标)。
 *
 * 【设计思想】与 PredicateLockExists 同源(基于本地锁表),因此
 * 可能漏报(假阴性)——但绝无假阳性:本地表只有"实际持有或
 * 被转移"的信息,不会凭空多出锁。漏报的后果只是多加点冗余
 * 细锁,共享层会去重(CreatePredicateLock 幂等),不影响正确性。
 *
 * 【参数】newtargettag —— 准备加锁的目标。
 * 【返回值】true = 已被更粗锁覆盖,无需加锁;false = 未覆盖。
 */
static bool
CoarserLockCovers(const PREDICATELOCKTARGETTAG *newtargettag)
{
	PREDICATELOCKTARGETTAG targettag,
				parenttag;

	targettag = *newtargettag;

	/* check parents iteratively until no more */
	while (GetParentPredicateLockTag(&targettag, &parenttag))
	{
		targettag = parenttag;
		if (PredicateLockExists(&targettag))
			return true;
	}

	/* no more parents to check; lock is not covered */
	return false;
}

/*
 * Remove the dummy entry from the predicate lock target hash, to free up some
 * scratch space. The caller must be holding SerializablePredicateListLock,
 * and must restore the entry with RestoreScratchTarget() before releasing the
 * lock.
 *
 * If lockheld is true, the caller is already holding the partition lock
 * of the partition containing the scratch entry.
 */
/*
 * RemoveScratchTarget
 *      (中文)临时摘除哈希表中的占位条目以腾出插入空间
 *
 * 【作用】TransferPredicateLocksToNewTarget(removeOld 模式)等
 * "必须成功新建目标"的操作,先调用本函数把 ScratchTargetTag
 * 条目从 PredicateLockTargetHash 删除,保证哈希表一定有空位。
 * 完成后调用者必须调用 RestoreScratchTarget 放回。
 *
 * 【设计思想】哈希表(固定大小)满员时 HASH_ENTER 会失败,而
 * 页分裂等操作失败会危及非可串行化事务;占位条目像"保底空位"
 * 一样被预留,临时挪走即可腾出恰好一个槽。调用者必须持有
 * SerializablePredicateListLock(断言);若 lockheld 为 false,函数
 * 自己获取/释放占位条目的分区锁。
 *
 * 【参数】lockheld —— 调用者是否已持有占位条目所在的分区锁。
 * 【返回值】无。
 */
static void
RemoveScratchTarget(bool lockheld)
{
	bool		found;

	Assert(LWLockHeldByMe(SerializablePredicateListLock));

	if (!lockheld)
		LWLockAcquire(ScratchPartitionLock, LW_EXCLUSIVE);
	hash_search_with_hash_value(PredicateLockTargetHash,
								&ScratchTargetTag,
								ScratchTargetTagHash,
								HASH_REMOVE, &found);
	Assert(found);
	if (!lockheld)
		LWLockRelease(ScratchPartitionLock);
}

/*
 * Re-insert the dummy entry in predicate lock target hash.
 */
/*
 * RestoreScratchTarget
 *      (中文)把占位条目重新插回目标哈希表
 *
 * 【作用】RemoveScratchTarget 的逆操作:用完腾出的空位后,把
 * ScratchTargetTag 放回 PredicateLockTargetHash。锁约定同
 * RemoveScratchTarget(须持有 SerializablePredicateListLock;
 * lockheld 表示调用者已持分区锁)。
 *
 * 【参数】lockheld —— 调用者是否已持有占位条目所在的分区锁。
 * 【返回值】无。
 */
static void
RestoreScratchTarget(bool lockheld)
{
	bool		found;

	Assert(LWLockHeldByMe(SerializablePredicateListLock));

	if (!lockheld)
		LWLockAcquire(ScratchPartitionLock, LW_EXCLUSIVE);
	hash_search_with_hash_value(PredicateLockTargetHash,
								&ScratchTargetTag,
								ScratchTargetTagHash,
								HASH_ENTER, &found);
	Assert(!found);
	if (!lockheld)
		LWLockRelease(ScratchPartitionLock);
}

/*
 * Check whether the list of related predicate locks is empty for a
 * predicate lock target, and remove the target if it is.
 */
/*
 * RemoveTargetIfNoLongerUsed
 *      (中文)若目标上已无任何锁,则从哈希表删除该目标
 *
 * 【作用】在删除某把锁之后调用:若目标->predicateLocks 链表已
 * 空,把目标条目从 PredicateLockTargetHash 移除。所有"删除锁"
 * 的路径(DeleteChildTargetLocks、DeleteLockTarget、释放锁等)
 * 都靠它保持目标表无垃圾。
 *
 * 【设计思想】目标条目与锁共享同一把分区锁,删除操作必须
 * 在锁保护下进行;断言要求调用者持有
 * SerializablePredicateListLock(与目标表一致性约定)。
 *
 * 【参数】
 *   target —— 待检查的目标;
 *   targettaghash —— 其预计算的哈希码。
 * 【返回值】无。
 */
static void
RemoveTargetIfNoLongerUsed(PREDICATELOCKTARGET *target, uint32 targettaghash)
{
	PREDICATELOCKTARGET *rmtarget PG_USED_FOR_ASSERTS_ONLY;

	Assert(LWLockHeldByMe(SerializablePredicateListLock));

	/* Can't remove it until no locks at this target. */
	if (!dlist_is_empty(&target->predicateLocks))
		return;

	/* Actually remove the target. */
	rmtarget = hash_search_with_hash_value(PredicateLockTargetHash,
										   &target->tag,
										   targettaghash,
										   HASH_REMOVE, NULL);
	Assert(rmtarget == target);
}

/*
 * Delete child target locks owned by this process.
 * This implementation is assuming that the usage of each target tag field
 * is uniform.  No need to make this hard if we don't have to.
 *
 * We acquire an LWLock in the case of parallel mode, because worker
 * backends have access to the leader's SERIALIZABLEXACT.  Otherwise,
 * we aren't acquiring LWLocks for the predicate lock or lock
 * target structures associated with this transaction unless we're going
 * to modify them, because no other process is permitted to modify our
 * locks.
 */
/*
 * DeleteChildTargetLocks
 *      (中文)删除被新锁覆盖的、本事务持有的全部细粒度锁
 *
 * 【作用】加锁成功后(PredicateLockAcquire 的非提升分支),遍历
 * 本事务的谓词锁链表,把被新目标覆盖(TargetTagIsCoveredBy)的
 * 旧锁逐一删除:从锁表删除锁条目、从目标表删除空目标、并在
 * 本地表递减父锁计数(DecrementParentLocks)。
 *
 * 【设计思想】粗锁的获得意味着细锁冗余:新锁的语义已覆盖它们,
 * 留着只会浪费共享内存并增加误报。删除时按"旧目标分区锁 +
 * 链表锁"的顺序获取;并行模式下 worker 可访问 leader 的
 * SERIALIZABLEXACT,须额外取 perXactPredicateListLock。
 *
 * 【参数】newtargettag —— 刚获得的新锁目标(被其覆盖的旧锁
 * 将被删除)。【返回值】无。
 */
static void
DeleteChildTargetLocks(const PREDICATELOCKTARGETTAG *newtargettag)
{
	SERIALIZABLEXACT *sxact;
	PREDICATELOCK *predlock;
	dlist_mutable_iter iter;

	LWLockAcquire(SerializablePredicateListLock, LW_SHARED);
	sxact = MySerializableXact;
	if (IsInParallelMode())
		LWLockAcquire(&sxact->perXactPredicateListLock, LW_EXCLUSIVE);

	dlist_foreach_modify(iter, &sxact->predicateLocks)
	{
		PREDICATELOCKTAG oldlocktag;
		PREDICATELOCKTARGET *oldtarget;
		PREDICATELOCKTARGETTAG oldtargettag;

		predlock = dlist_container(PREDICATELOCK, xactLink, iter.cur);

		oldlocktag = predlock->tag;
		Assert(oldlocktag.myXact == sxact);
		oldtarget = oldlocktag.myTarget;
		oldtargettag = oldtarget->tag;

		if (TargetTagIsCoveredBy(oldtargettag, *newtargettag))
		{
			uint32		oldtargettaghash;
			LWLock	   *partitionLock;
			PREDICATELOCK *rmpredlock PG_USED_FOR_ASSERTS_ONLY;

			oldtargettaghash = PredicateLockTargetTagHashCode(&oldtargettag);
			partitionLock = PredicateLockHashPartitionLock(oldtargettaghash);

			LWLockAcquire(partitionLock, LW_EXCLUSIVE);

			dlist_delete(&predlock->xactLink);
			dlist_delete(&predlock->targetLink);
			rmpredlock = hash_search_with_hash_value
				(PredicateLockHash,
				 &oldlocktag,
				 PredicateLockHashCodeFromTargetHashCode(&oldlocktag,
														 oldtargettaghash),
				 HASH_REMOVE, NULL);
			Assert(rmpredlock == predlock);

			RemoveTargetIfNoLongerUsed(oldtarget, oldtargettaghash);

			LWLockRelease(partitionLock);

			DecrementParentLocks(&oldtargettag);
		}
	}
	if (IsInParallelMode())
		LWLockRelease(&sxact->perXactPredicateListLock);
	LWLockRelease(SerializablePredicateListLock);
}

/*
 * Returns the promotion limit for a given predicate lock target.  This is the
 * max number of descendant locks allowed before promoting to the specified
 * tag. Note that the limit includes non-direct descendants (e.g., both tuples
 * and pages for a relation lock).
 *
 * Currently the default limit is 2 for a page lock, and half of the value of
 * max_pred_locks_per_transaction - 1 for a relation lock, to match behavior
 * of earlier releases when upgrading.
 *
 * TODO SSI: We should probably add additional GUCs to allow a maximum ratio
 * of page and tuple locks based on the pages in a relation, and the maximum
 * ratio of tuple locks to tuples in a page.  This would provide more
 * generally "balanced" allocation of locks to where they are most useful,
 * while still allowing the absolute numbers to prevent one relation from
 * tying up all predicate lock resources.
 */
/*
 * MaxPredicateChildLocks
 *      (中文)某目标的"孩子锁数量上限"(触发粒度提升的阈值)
 *
 * 【作用】返回允许在指定目标下登记的子孙锁(含间接子孙)数量
 * 上限,超过即触发提升到该目标粒度。页锁上限是
 * max_predicate_locks_per_page;表锁上限是
 * max_predicate_locks_per_relation,为负时按"每事务上限除以
 * 绝对值再减 1"折算(兼容旧版本行为)。元组是最细粒度,永远
 * 不应作为提升目标(断言不可达)。
 *
 * 【设计思想】见英文注释的 TODO:理想是按关系页数/每页元组数
 * 动态配比,但绝对数量上限已足以防止单关系耗尽全部锁资源。
 *
 * 【参数】tag —— 目标(决定返回哪种上限)。
 * 【返回值】孩子锁数量上限。
 */
static int
MaxPredicateChildLocks(const PREDICATELOCKTARGETTAG *tag)
{
	switch (GET_PREDICATELOCKTARGETTAG_TYPE(*tag))
	{
		case PREDLOCKTAG_RELATION:
			return max_predicate_locks_per_relation < 0
				? (max_predicate_locks_per_xact
				   / (-max_predicate_locks_per_relation)) - 1
				: max_predicate_locks_per_relation;

		case PREDLOCKTAG_PAGE:
			return max_predicate_locks_per_page;

		case PREDLOCKTAG_TUPLE:

			/*
			 * not reachable: nothing is finer-granularity than a tuple, so we
			 * should never try to promote to it.
			 */
			Assert(false);
			return 0;
	}

	/* not reachable */
	Assert(false);
	return 0;
}

/*
 * For all ancestors of a newly-acquired predicate lock, increment
 * their child count in the parent hash table. If any of them have
 * more descendants than their promotion threshold, acquire the
 * coarsest such lock.
 *
 * Returns true if a parent lock was acquired and false otherwise.
 */
/*
 * CheckAndPromotePredicateLockRequest
 *      (中文)登记父锁计数,必要时把请求提升为更粗粒度的锁
 *
 * 【作用】每次成功加细锁后调用:沿锁层次逐级向上,在本地表为
 * 每个父目标登记/递增 childLocks;一旦某级父锁的孩子数超过其
 * 上限(MaxPredicateChildLocks),记下该级为候选提升目标,并继续
 * 向上检查(更粗的父可能也需要提升)。最后若存在候选,直接对
 * 最粗候选调用 PredicateLockAcquire 加粗锁。
 *
 * 【设计思想】提升是内存压力的"压力阀":细锁太多就合并成粗锁,
 * 宁可误报冲突也不耗尽共享内存。提升获得的粗锁会反过来删除
 * 所有被其覆盖的细锁(见 PredicateLockAcquire 的分支处理)。
 *
 * 【参数】reqtag —— 刚获得的目标(以其为子孙起点)。
 * 【返回值】true = 已提升并获得父锁(调用者可结束);false =
 * 未提升。
 */
static bool
CheckAndPromotePredicateLockRequest(const PREDICATELOCKTARGETTAG *reqtag)
{
	PREDICATELOCKTARGETTAG targettag,
				nexttag,
				promotiontag;
	LOCALPREDICATELOCK *parentlock;
	bool		found,
				promote;

	promote = false;

	targettag = *reqtag;

	/* check parents iteratively */
	while (GetParentPredicateLockTag(&targettag, &nexttag))
	{
		targettag = nexttag;
		parentlock = (LOCALPREDICATELOCK *) hash_search(LocalPredicateLockHash,
														&targettag,
														HASH_ENTER,
														&found);
		if (!found)
		{
			parentlock->held = false;
			parentlock->childLocks = 1;
		}
		else
			parentlock->childLocks++;

		if (parentlock->childLocks >
			MaxPredicateChildLocks(&targettag))
		{
			/*
			 * We should promote to this parent lock. Continue to check its
			 * ancestors, however, both to get their child counts right and to
			 * check whether we should just go ahead and promote to one of
			 * them.
			 */
			promotiontag = targettag;
			promote = true;
		}
	}

	if (promote)
	{
		/* acquire coarsest ancestor eligible for promotion */
		PredicateLockAcquire(&promotiontag);
		return true;
	}
	else
		return false;
}

/*
 * When releasing a lock, decrement the child count on all ancestor
 * locks.
 *
 * This is called only when releasing a lock via
 * DeleteChildTargetLocks (i.e. when a lock becomes redundant because
 * we've acquired its parent, possibly due to promotion) or when a new
 * MVCC write lock makes the predicate lock unnecessary. There's no
 * point in calling it when locks are released at transaction end, as
 * this information is no longer needed.
 */
/*
 * DecrementParentLocks
 *      (中文)释放锁时递减其全部祖先的本地孩子计数
 *
 * 【作用】当一把锁被删除(因被更粗锁取代而冗余,或因本事务对
 * 元组获得写锁)时,沿锁层次向上,把本地表中各父锁的
 * childLocks 减 1;减到 0 且父锁本身未被持有,就把该父条目从
 * 本地表移除。
 *
 * 【设计思想】本地表只统计"现存细锁覆盖关系",因此删除细锁
 * 必须同步递减,否则计数虚高会过早触发粒度提升。英文注释
 * 说明两个可容忍的偏差:索引分裂可能让父条目缺失(跳过),
 * 或计数短暂为负(归零即可,前提是持有该父锁)。事务结束时
 * 本地表整体销毁,无需逐条递减。
 *
 * 【参数】targettag —— 被删除锁的目标。【返回值】无。
 */
static void
DecrementParentLocks(const PREDICATELOCKTARGETTAG *targettag)
{
	PREDICATELOCKTARGETTAG parenttag,
				nexttag;

	parenttag = *targettag;

	while (GetParentPredicateLockTag(&parenttag, &nexttag))
	{
		uint32		targettaghash;
		LOCALPREDICATELOCK *parentlock,
				   *rmlock PG_USED_FOR_ASSERTS_ONLY;

		parenttag = nexttag;
		targettaghash = PredicateLockTargetTagHashCode(&parenttag);
		parentlock = (LOCALPREDICATELOCK *)
			hash_search_with_hash_value(LocalPredicateLockHash,
										&parenttag, targettaghash,
										HASH_FIND, NULL);

		/*
		 * There's a small chance the parent lock doesn't exist in the lock
		 * table. This can happen if we prematurely removed it because an
		 * index split caused the child refcount to be off.
		 */
		if (parentlock == NULL)
			continue;

		parentlock->childLocks--;

		/*
		 * Under similar circumstances the parent lock's refcount might be
		 * zero. This only happens if we're holding that lock (otherwise we
		 * would have removed the entry).
		 */
		if (parentlock->childLocks < 0)
		{
			Assert(parentlock->held);
			parentlock->childLocks = 0;
		}

		if ((parentlock->childLocks == 0) && (!parentlock->held))
		{
			rmlock = (LOCALPREDICATELOCK *)
				hash_search_with_hash_value(LocalPredicateLockHash,
											&parenttag, targettaghash,
											HASH_REMOVE, NULL);
			Assert(rmlock == parentlock);
		}
	}
}

/*
 * Indicate that a predicate lock on the given target is held by the
 * specified transaction. Has no effect if the lock is already held.
 *
 * This updates the lock table and the sxact's lock list, and creates
 * the lock target if necessary, but does *not* do anything related to
 * granularity promotion or the local lock table. See
 * PredicateLockAcquire for that.
 */
/*
 * CreatePredicateLock
 *      (中文)在共享锁表登记"某事务持有某目标上的谓词锁"
 *
 * 【作用】核心登记动作:确保目标条目存在(HASH_ENTER_NULL,失败
 * 报"out of shared memory"并提示调大 max_pred_locks_per_transaction),
 * 再按 (目标, 事务) 二元组在 PredicateLockHash 中查/建锁条目;
 * 新建时挂入目标与事务的两条链表并初始化 commitSeqNo。已有锁
 * 时不做任何事(幂等)。
 *
 * 【设计思想】本函数只管共享层登记,不做粒度提升、不做本地表
 * 更新(那是 PredicateLockAcquire 的职责)。锁获取的锁顺序:
 * SerializablePredicateListLock(共享)→(并行时 perXact 锁)→
 * 分区锁(排他)。与 lock.c 不同,谓词锁"从不等待"——锁表查/
 * 建后立刻返回。
 *
 * 【参数】
 *   targettag —— 目标;
 *   targettaghash —— 预计算的目标哈希码;
 *   sxact —— 持有事务。
 * 【返回值】无。
 */
static void
CreatePredicateLock(const PREDICATELOCKTARGETTAG *targettag,
					uint32 targettaghash,
					SERIALIZABLEXACT *sxact)
{
	PREDICATELOCKTARGET *target;
	PREDICATELOCKTAG locktag;
	PREDICATELOCK *lock;
	LWLock	   *partitionLock;
	bool		found;

	partitionLock = PredicateLockHashPartitionLock(targettaghash);

	LWLockAcquire(SerializablePredicateListLock, LW_SHARED);
	if (IsInParallelMode())
		LWLockAcquire(&sxact->perXactPredicateListLock, LW_EXCLUSIVE);
	LWLockAcquire(partitionLock, LW_EXCLUSIVE);

	/* Make sure that the target is represented. */
	target = (PREDICATELOCKTARGET *)
		hash_search_with_hash_value(PredicateLockTargetHash,
									targettag, targettaghash,
									HASH_ENTER_NULL, &found);
	if (!target)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory"),
				 errhint("You might need to increase \"%s\".", "max_pred_locks_per_transaction")));
	if (!found)
		dlist_init(&target->predicateLocks);

	/* We've got the sxact and target, make sure they're joined. */
	locktag.myTarget = target;
	locktag.myXact = sxact;
	lock = (PREDICATELOCK *)
		hash_search_with_hash_value(PredicateLockHash, &locktag,
									PredicateLockHashCodeFromTargetHashCode(&locktag, targettaghash),
									HASH_ENTER_NULL, &found);
	if (!lock)
		ereport(ERROR,
				(errcode(ERRCODE_OUT_OF_MEMORY),
				 errmsg("out of shared memory"),
				 errhint("You might need to increase \"%s\".", "max_pred_locks_per_transaction")));

	if (!found)
	{
		dlist_push_tail(&target->predicateLocks, &lock->targetLink);
		dlist_push_tail(&sxact->predicateLocks, &lock->xactLink);
		lock->commitSeqNo = InvalidSerCommitSeqNo;
	}

	LWLockRelease(partitionLock);
	if (IsInParallelMode())
		LWLockRelease(&sxact->perXactPredicateListLock);
	LWLockRelease(SerializablePredicateListLock);
}

/*
 * Acquire a predicate lock on the specified target for the current
 * connection if not already held. This updates the local lock table
 * and uses it to implement granularity promotion. It will consolidate
 * multiple locks into a coarser lock if warranted, and will release
 * any finer-grained locks covered by the new one.
 */
/*
 * PredicateLockAcquire
 *      (中文)为当前事务获得目标上的谓词锁(含粒度提升/合并)
 *
 * 【作用】所有加锁入口(PredicateLockRelation/Page/TID)的共同
 * 核心:先检查本地表(已持有或被粗锁覆盖则返回),然后在本地
 * 表登记 held = true,调用 CreatePredicateLock 写共享表;最后
 * 调用 CheckAndPromotePredicateLockRequest——若被提升,新粗锁
 * 会删除本锁及其子孙,任务完成;否则删除被本锁覆盖的细锁
 * (元组没有更细的,跳过)。
 *
 * 【设计思想】谓词锁不阻塞、可重复获得,因此加锁是"登记"
 * 而非"请求-等待"。粒度管理是双向的:向上提升(压力阀)与
 * 向下合并(粗锁掩盖细锁后清理)。共享层与本地层通过本函数
 * 保持大致同步。
 *
 * 【参数】targettag —— 待加锁的目标。
 * 【返回值】无。
 */
static void
PredicateLockAcquire(const PREDICATELOCKTARGETTAG *targettag)
{
	uint32		targettaghash;
	bool		found;
	LOCALPREDICATELOCK *locallock;

	/* Do we have the lock already, or a covering lock? */
	if (PredicateLockExists(targettag))
		return;

	if (CoarserLockCovers(targettag))
		return;

	/* the same hash and LW lock apply to the lock target and the local lock. */
	targettaghash = PredicateLockTargetTagHashCode(targettag);

	/* Acquire lock in local table */
	locallock = (LOCALPREDICATELOCK *)
		hash_search_with_hash_value(LocalPredicateLockHash,
									targettag, targettaghash,
									HASH_ENTER, &found);
	locallock->held = true;
	if (!found)
		locallock->childLocks = 0;

	/* Actually create the lock */
	CreatePredicateLock(targettag, targettaghash, MySerializableXact);

	/*
	 * Lock has been acquired. Check whether it should be promoted to a
	 * coarser granularity, or whether there are finer-granularity locks to
	 * clean up.
	 */
	if (CheckAndPromotePredicateLockRequest(targettag))
	{
		/*
		 * Lock request was promoted to a coarser-granularity lock, and that
		 * lock was acquired. It will delete this lock and any of its
		 * children, so we're done.
		 */
	}
	else
	{
		/* Clean up any finer-granularity locks */
		if (GET_PREDICATELOCKTARGETTAG_TYPE(*targettag) != PREDLOCKTAG_TUPLE)
			DeleteChildTargetLocks(targettag);
	}
}


/*
 *		PredicateLockRelation
 *
 * Gets a predicate lock at the relation level.
 * Skip if not in full serializable transaction isolation level.
 * Skip if this is a temporary table.
 * Clear any finer-grained predicate locks this session has on the relation.
 */
/*
 * PredicateLockRelation
 *      (中文)在关系级获得谓词锁(表扫描)
 *
 * 【作用】整表扫描时由 heapam/索引扫描等调用:为本事务在
 * 关系上打 SIREAD 锁,覆盖该扫描可能读到的所有元组。
 * SerializationNeededForRead 快速返回后,构建关系 tag 并交给
 * PredicateLockAcquire(它会自动清理本会话更细粒度的锁)。
 *
 * 【设计思想】表级锁语义上覆盖页/元组锁,获得后旧细锁成为
 * 冗余而被清理(见 PredicateLockAcquire 的 DeleteChildTargetLocks
 * 分支)。
 *
 * 【参数】
 *   relation —— 待锁的关系;
 *   snapshot —— 当前快照(用于豁免判定)。
 * 【返回值】无。
 */
void
PredicateLockRelation(Relation relation, Snapshot snapshot)
{
	PREDICATELOCKTARGETTAG tag;

	if (!SerializationNeededForRead(relation, snapshot))
		return;

	SET_PREDICATELOCKTARGETTAG_RELATION(tag,
										relation->rd_locator.dbOid,
										relation->rd_id);
	PredicateLockAcquire(&tag);
}

/*
 *		PredicateLockPage
 *
 * Gets a predicate lock at the page level.
 * Skip if not in full serializable transaction isolation level.
 * Skip if this is a temporary table.
 * Skip if a coarser predicate lock already covers this page.
 * Clear any finer-grained predicate locks this session has on the relation.
 */
/*
 * PredicateLockPage
 *      (中文)在页级获得谓词锁(索引页扫描)
 *
 * 【作用】按页访问数据(如 B-tree 叶子页扫描)时调用:为本事务
 * 在指定页上打 SIREAD 锁;若已有覆盖该页的关系级锁则无需重复
 * (PredicateLockAcquire 内部处理)。加锁成功后同样清理被覆盖的
 * 元组级细锁。
 *
 * 【参数】
 *   relation —— 关系;
 *   blkno —— 页号;
 *   snapshot —— 当前快照(豁免判定)。
 * 【返回值】无。
 */
void
PredicateLockPage(Relation relation, BlockNumber blkno, Snapshot snapshot)
{
	PREDICATELOCKTARGETTAG tag;

	if (!SerializationNeededForRead(relation, snapshot))
		return;

	SET_PREDICATELOCKTARGETTAG_PAGE(tag,
									relation->rd_locator.dbOid,
									relation->rd_id,
									blkno);
	PredicateLockAcquire(&tag);
}

/*
 *		PredicateLockTID
 *
 * Gets a predicate lock at the tuple level.
 * Skip if not in full serializable transaction isolation level.
 * Skip if this is a temporary table.
 */
/*
 * PredicateLockTID
 *      (中文)在元组级获得谓词锁(堆元组读)
 *
 * 【作用】读取具体堆元组时由 heapam 调用:为本事务在元组
 * (页号 + 槽号)上打 SIREAD 锁。两个快速返回:元组是本事务
 * 自己写的(已有写锁,无需 SIREAD,见 README-SSI 关于写锁消除
 * 的证明);或已持有关系级锁(先做一次"快而不可靠"的关系锁
 * 检查——可能漏报,但随后 PredicateLockAcquire 会再确认)。
 *
 * 【设计思想】heap 元组锁是最细粒度,锁的是"这一行"以及
 * "未来的更新插到这里会冲突"的范围;索引上的插入冲突由
 * 索引页锁覆盖。
 *
 * 【参数】
 *   relation —— 关系;
 *   tid —— 元组标识(页号 + 槽号);
 *   snapshot —— 当前快照;
 *   tuple_xid —— 元组版本的产生/修改事务 xid(用于"自己写的"
 *   判断,只有堆表才有效)。
 * 【返回值】无。
 */
void
PredicateLockTID(Relation relation, const ItemPointerData *tid, Snapshot snapshot,
				 TransactionId tuple_xid)
{
	PREDICATELOCKTARGETTAG tag;

	if (!SerializationNeededForRead(relation, snapshot))
		return;

	/*
	 * Return if this xact wrote it.
	 */
	if (relation->rd_index == NULL)
	{
		/* If we wrote it; we already have a write lock. */
		if (TransactionIdIsCurrentTransactionId(tuple_xid))
			return;
	}

	/*
	 * Do quick-but-not-definitive test for a relation lock first.  This will
	 * never cause a return when the relation is *not* locked, but will
	 * occasionally let the check continue when there really *is* a relation
	 * level lock.
	 */
	SET_PREDICATELOCKTARGETTAG_RELATION(tag,
										relation->rd_locator.dbOid,
										relation->rd_id);
	if (PredicateLockExists(&tag))
		return;

	SET_PREDICATELOCKTARGETTAG_TUPLE(tag,
									 relation->rd_locator.dbOid,
									 relation->rd_id,
									 ItemPointerGetBlockNumber(tid),
									 ItemPointerGetOffsetNumber(tid));
	PredicateLockAcquire(&tag);
}


/*
 *		DeleteLockTarget
 *
 * Remove a predicate lock target along with any locks held for it.
 *
 * Caller must hold SerializablePredicateListLock and the
 * appropriate hash partition lock for the target.
 */
/*
 * DeleteLockTarget
 *      (中文)删除一个谓词锁目标及其上的全部锁
 *
 * 【作用】批量清理一个目标:遍历目标->predicateLocks 链表,把
 * 每把锁从锁表删除并摘出两条链表节点(相应事务的锁链表也被
 * 更新),最后 RemoveTargetIfNoLongerUsed 删除目标本身。由
 * TransferPredicateLocksToNewTarget 在"迁移失败回滚"时调用。
 *
 * 【设计思想】遍历时需修改各事务的锁链表,因此还要拿
 * SerializableXactHashLock(排他);调用者须已持有
 * SerializablePredicateListLock(排他)与目标分区锁。
 *
 * 【参数】
 *   target —— 待删除的目标;
 *   targettaghash —— 其预计算哈希码。
 * 【返回值】无。
 */
static void
DeleteLockTarget(PREDICATELOCKTARGET *target, uint32 targettaghash)
{
	dlist_mutable_iter iter;

	Assert(LWLockHeldByMeInMode(SerializablePredicateListLock,
								LW_EXCLUSIVE));
	Assert(LWLockHeldByMe(PredicateLockHashPartitionLock(targettaghash)));

	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	dlist_foreach_modify(iter, &target->predicateLocks)
	{
		PREDICATELOCK *predlock =
			dlist_container(PREDICATELOCK, targetLink, iter.cur);
		bool		found;

		dlist_delete(&(predlock->xactLink));
		dlist_delete(&(predlock->targetLink));

		hash_search_with_hash_value
			(PredicateLockHash,
			 &predlock->tag,
			 PredicateLockHashCodeFromTargetHashCode(&predlock->tag,
													 targettaghash),
			 HASH_REMOVE, &found);
		Assert(found);
	}
	LWLockRelease(SerializableXactHashLock);

	/* Remove the target itself, if possible. */
	RemoveTargetIfNoLongerUsed(target, targettaghash);
}


/*
 *		TransferPredicateLocksToNewTarget
 *
 * Move or copy all the predicate locks for a lock target, for use by
 * index page splits/combines and other things that create or replace
 * lock targets. If 'removeOld' is true, the old locks and the target
 * will be removed.
 *
 * Returns true on success, or false if we ran out of shared memory to
 * allocate the new target or locks. Guaranteed to always succeed if
 * removeOld is set (by using the scratch entry in PredicateLockTargetHash
 * for scratch space).
 *
 * Warning: the "removeOld" option should be used only with care,
 * because this function does not (indeed, can not) update other
 * backends' LocalPredicateLockHash. If we are only adding new
 * entries, this is not a problem: the local lock table is used only
 * as a hint, so missing entries for locks that are held are
 * OK. Having entries for locks that are no longer held, as can happen
 * when using "removeOld", is not in general OK. We can only use it
 * safely when replacing a lock with a coarser-granularity lock that
 * covers it, or if we are absolutely certain that no one will need to
 * refer to that lock in the future.
 *
 * Caller must hold SerializablePredicateListLock exclusively.
 */
/*
 * TransferPredicateLocksToNewTarget
 *      (中文)把旧目标上的全部谓词锁移动/复制到新目标
 *
 * 【作用】索引页分裂/合并、页 → 关系锁提升等场景的核心工具:
 * 把 oldtargettag 上的每把锁改写为指向 newtargettag 的锁条目
 * (同一事务在两端同时存在时合并,commitSeqNo 取较大者)。
 * removeOld = true 时删除旧锁与旧目标(移动);false 时保留
 * (复制,新锁额外添加)。
 *
 * 【设计思想】
 * - 保证成功:removeOld 模式先 RemoveScratchTarget 腾出占位
 *   槽,确保新目标必然能建(断言不会 outOfShmem);
 * - 锁顺序:新旧目标可能在两个分区,按锁地址升序获取分区锁
 *   (同一分区只取一次),避免死锁;SerializableXactHashLock 在
 *   改写各事务锁链表期间持有;
 * - 风险(见英文注释警告):removeOld 无法同步其他后端本地表,
 *   只允许"换成覆盖它的粗锁"或"确实无人再引用"时使用。
 *
 * 【参数】
 *   oldtargettag / newtargettag —— 新旧目标;
 *   removeOld —— true = 移动(删除旧锁),false = 复制(保留旧锁)。
 * 【返回值】true = 成功;false = 共享内存不足(仅 removeOld = false
 * 可能;此时新目标/部分新锁已建,调用者自行处置)。
 */
static bool
TransferPredicateLocksToNewTarget(PREDICATELOCKTARGETTAG oldtargettag,
								  PREDICATELOCKTARGETTAG newtargettag,
								  bool removeOld)
{
	uint32		oldtargettaghash;
	LWLock	   *oldpartitionLock;
	PREDICATELOCKTARGET *oldtarget;
	uint32		newtargettaghash;
	LWLock	   *newpartitionLock;
	bool		found;
	bool		outOfShmem = false;

	Assert(LWLockHeldByMeInMode(SerializablePredicateListLock,
								LW_EXCLUSIVE));

	oldtargettaghash = PredicateLockTargetTagHashCode(&oldtargettag);
	newtargettaghash = PredicateLockTargetTagHashCode(&newtargettag);
	oldpartitionLock = PredicateLockHashPartitionLock(oldtargettaghash);
	newpartitionLock = PredicateLockHashPartitionLock(newtargettaghash);

	if (removeOld)
	{
		/*
		 * Remove the dummy entry to give us scratch space, so we know we'll
		 * be able to create the new lock target.
		 */
		RemoveScratchTarget(false);
	}

	/*
	 * We must get the partition locks in ascending sequence to avoid
	 * deadlocks. If old and new partitions are the same, we must request the
	 * lock only once.
	 */
	if (oldpartitionLock < newpartitionLock)
	{
		LWLockAcquire(oldpartitionLock,
					  (removeOld ? LW_EXCLUSIVE : LW_SHARED));
		LWLockAcquire(newpartitionLock, LW_EXCLUSIVE);
	}
	else if (oldpartitionLock > newpartitionLock)
	{
		LWLockAcquire(newpartitionLock, LW_EXCLUSIVE);
		LWLockAcquire(oldpartitionLock,
					  (removeOld ? LW_EXCLUSIVE : LW_SHARED));
	}
	else
		LWLockAcquire(newpartitionLock, LW_EXCLUSIVE);

	/*
	 * Look for the old target.  If not found, that's OK; no predicate locks
	 * are affected, so we can just clean up and return. If it does exist,
	 * walk its list of predicate locks and move or copy them to the new
	 * target.
	 */
	oldtarget = hash_search_with_hash_value(PredicateLockTargetHash,
											&oldtargettag,
											oldtargettaghash,
											HASH_FIND, NULL);

	if (oldtarget)
	{
		PREDICATELOCKTARGET *newtarget;
		PREDICATELOCKTAG newpredlocktag;
		dlist_mutable_iter iter;

		newtarget = hash_search_with_hash_value(PredicateLockTargetHash,
												&newtargettag,
												newtargettaghash,
												HASH_ENTER_NULL, &found);

		if (!newtarget)
		{
			/* Failed to allocate due to insufficient shmem */
			outOfShmem = true;
			goto exit;
		}

		/* If we created a new entry, initialize it */
		if (!found)
			dlist_init(&newtarget->predicateLocks);

		newpredlocktag.myTarget = newtarget;

		/*
		 * Loop through all the locks on the old target, replacing them with
		 * locks on the new target.
		 */
		LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

		dlist_foreach_modify(iter, &oldtarget->predicateLocks)
		{
			PREDICATELOCK *oldpredlock =
				dlist_container(PREDICATELOCK, targetLink, iter.cur);
			PREDICATELOCK *newpredlock;
			SerCommitSeqNo oldCommitSeqNo = oldpredlock->commitSeqNo;

			newpredlocktag.myXact = oldpredlock->tag.myXact;

			if (removeOld)
			{
				dlist_delete(&(oldpredlock->xactLink));
				dlist_delete(&(oldpredlock->targetLink));

				hash_search_with_hash_value
					(PredicateLockHash,
					 &oldpredlock->tag,
					 PredicateLockHashCodeFromTargetHashCode(&oldpredlock->tag,
															 oldtargettaghash),
					 HASH_REMOVE, &found);
				Assert(found);
			}

			newpredlock = (PREDICATELOCK *)
				hash_search_with_hash_value(PredicateLockHash,
											&newpredlocktag,
											PredicateLockHashCodeFromTargetHashCode(&newpredlocktag,
																					newtargettaghash),
											HASH_ENTER_NULL,
											&found);
			if (!newpredlock)
			{
				/* Out of shared memory. Undo what we've done so far. */
				LWLockRelease(SerializableXactHashLock);
				DeleteLockTarget(newtarget, newtargettaghash);
				outOfShmem = true;
				goto exit;
			}
			if (!found)
			{
				dlist_push_tail(&(newtarget->predicateLocks),
								&(newpredlock->targetLink));
				dlist_push_tail(&(newpredlocktag.myXact->predicateLocks),
								&(newpredlock->xactLink));
				newpredlock->commitSeqNo = oldCommitSeqNo;
			}
			else
			{
				if (newpredlock->commitSeqNo < oldCommitSeqNo)
					newpredlock->commitSeqNo = oldCommitSeqNo;
			}

			Assert(newpredlock->commitSeqNo != 0);
			Assert((newpredlock->commitSeqNo == InvalidSerCommitSeqNo)
				   || (newpredlock->tag.myXact == OldCommittedSxact));
		}
		LWLockRelease(SerializableXactHashLock);

		if (removeOld)
		{
			Assert(dlist_is_empty(&oldtarget->predicateLocks));
			RemoveTargetIfNoLongerUsed(oldtarget, oldtargettaghash);
		}
	}


exit:
	/* Release partition locks in reverse order of acquisition. */
	if (oldpartitionLock < newpartitionLock)
	{
		LWLockRelease(newpartitionLock);
		LWLockRelease(oldpartitionLock);
	}
	else if (oldpartitionLock > newpartitionLock)
	{
		LWLockRelease(oldpartitionLock);
		LWLockRelease(newpartitionLock);
	}
	else
		LWLockRelease(newpartitionLock);

	if (removeOld)
	{
		/* We shouldn't run out of memory if we're moving locks */
		Assert(!outOfShmem);

		/* Put the scratch entry back */
		RestoreScratchTarget(false);
	}

	return !outOfShmem;
}

/*
 * Drop all predicate locks of any granularity from the specified relation,
 * which can be a heap relation or an index relation.  If 'transfer' is true,
 * acquire a relation lock on the heap for any transactions with any lock(s)
 * on the specified relation.
 *
 * This requires grabbing a lot of LW locks and scanning the entire lock
 * target table for matches.  That makes this more expensive than most
 * predicate lock management functions, but it will only be called for DDL
 * type commands that are expensive anyway, and there are fast returns when
 * no serializable transactions are active or the relation is temporary.
 *
 * We don't use the TransferPredicateLocksToNewTarget function because it
 * acquires its own locks on the partitions of the two targets involved,
 * and we'll already be holding all partition locks.
 *
 * We can't throw an error from here, because the call could be from a
 * transaction which is not serializable.
 *
 * NOTE: This is currently only called with transfer set to true, but that may
 * change.  If we decide to clean up the locks from a table on commit of a
 * transaction which executed DROP TABLE, the false condition will be useful.
 */
/*
 * DropAllPredicateLocksFromTable
 *      (中文)删除某关系(堆/索引)上的全部谓词锁,可选转移到堆关系锁
 *
 * 【作用】TRUNCATE / DROP TABLE 等 DDL 时调用:扫描目标哈希表
 * 找到该关系(数据库 + 关系号匹配)的全部目标,把上面每把锁
 * 删除;transfer = true 时把这些锁改挂到堆关系的关系级目标上
 * (isIndex 时目标关系号换算为堆表 OID)。全部分区锁一次拿齐
 * 后整体扫描,开销大但只在昂贵 DDL 中出现。
 *
 * 【设计思想】不能调用 TransferPredicateLocksToNewTarget,因为
 * 本函数已持有全部分区锁(避免重复获取,且需顺序一致)。允许
 * 报错——调用者可能是非可串行化事务,不能让 SSI 的内存问题
 * 拖垮它(英文注释说明)。当前实际只有 transfer = true 的调用
 * (TransferPredicateLocksToHeapRelation);英文注释推测未来 DROP
 * TABLE 提交时清理锁可能用到 false 分支。
 *
 * 【参数】
 *   relation —— 目标关系(堆或索引);
 *   transfer —— true = 把锁转移到堆关系锁;false = 只删除。
 * 【返回值】无。
 */
static void
DropAllPredicateLocksFromTable(Relation relation, bool transfer)
{
	HASH_SEQ_STATUS seqstat;
	PREDICATELOCKTARGET *oldtarget;
	PREDICATELOCKTARGET *heaptarget;
	Oid			dbId;
	Oid			relId;
	Oid			heapId;
	int			i;
	bool		isIndex;
	bool		found;
	uint32		heaptargettaghash;

	/*
	 * Bail out quickly if there are no serializable transactions running.
	 * It's safe to check this without taking locks because the caller is
	 * holding an ACCESS EXCLUSIVE lock on the relation.  No new locks which
	 * would matter here can be acquired while that is held.
	 */
	if (!TransactionIdIsValid(PredXact->SxactGlobalXmin))
		return;

	if (!PredicateLockingNeededForRelation(relation))
		return;

	dbId = relation->rd_locator.dbOid;
	relId = relation->rd_id;
	if (relation->rd_index == NULL)
	{
		isIndex = false;
		heapId = relId;
	}
	else
	{
		isIndex = true;
		heapId = relation->rd_index->indrelid;
	}
	Assert(heapId != InvalidOid);
	Assert(transfer || !isIndex);	/* index OID only makes sense with
									 * transfer */

	/* Retrieve first time needed, then keep. */
	heaptargettaghash = 0;
	heaptarget = NULL;

	/* Acquire locks on all lock partitions */
	LWLockAcquire(SerializablePredicateListLock, LW_EXCLUSIVE);
	for (i = 0; i < NUM_PREDICATELOCK_PARTITIONS; i++)
		LWLockAcquire(PredicateLockHashPartitionLockByIndex(i), LW_EXCLUSIVE);
	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	/*
	 * Remove the dummy entry to give us scratch space, so we know we'll be
	 * able to create the new lock target.
	 */
	if (transfer)
		RemoveScratchTarget(true);

	/* Scan through target map */
	hash_seq_init(&seqstat, PredicateLockTargetHash);

	while ((oldtarget = (PREDICATELOCKTARGET *) hash_seq_search(&seqstat)))
	{
		dlist_mutable_iter iter;

		/*
		 * Check whether this is a target which needs attention.
		 */
		if (GET_PREDICATELOCKTARGETTAG_RELATION(oldtarget->tag) != relId)
			continue;			/* wrong relation id */
		if (GET_PREDICATELOCKTARGETTAG_DB(oldtarget->tag) != dbId)
			continue;			/* wrong database id */
		if (transfer && !isIndex
			&& GET_PREDICATELOCKTARGETTAG_TYPE(oldtarget->tag) == PREDLOCKTAG_RELATION)
			continue;			/* already the right lock */

		/*
		 * If we made it here, we have work to do.  We make sure the heap
		 * relation lock exists, then we walk the list of predicate locks for
		 * the old target we found, moving all locks to the heap relation lock
		 * -- unless they already hold that.
		 */

		/*
		 * First make sure we have the heap relation target.  We only need to
		 * do this once.
		 */
		if (transfer && heaptarget == NULL)
		{
			PREDICATELOCKTARGETTAG heaptargettag;

			SET_PREDICATELOCKTARGETTAG_RELATION(heaptargettag, dbId, heapId);
			heaptargettaghash = PredicateLockTargetTagHashCode(&heaptargettag);
			heaptarget = hash_search_with_hash_value(PredicateLockTargetHash,
													 &heaptargettag,
													 heaptargettaghash,
													 HASH_ENTER, &found);
			if (!found)
				dlist_init(&heaptarget->predicateLocks);
		}

		/*
		 * Loop through all the locks on the old target, replacing them with
		 * locks on the new target.
		 */
		dlist_foreach_modify(iter, &oldtarget->predicateLocks)
		{
			PREDICATELOCK *oldpredlock =
				dlist_container(PREDICATELOCK, targetLink, iter.cur);
			PREDICATELOCK *newpredlock;
			SerCommitSeqNo oldCommitSeqNo;
			SERIALIZABLEXACT *oldXact;

			/*
			 * Remove the old lock first. This avoids the chance of running
			 * out of lock structure entries for the hash table.
			 */
			oldCommitSeqNo = oldpredlock->commitSeqNo;
			oldXact = oldpredlock->tag.myXact;

			dlist_delete(&(oldpredlock->xactLink));

			/*
			 * No need for retail delete from oldtarget list, we're removing
			 * the whole target anyway.
			 */
			hash_search(PredicateLockHash,
						&oldpredlock->tag,
						HASH_REMOVE, &found);
			Assert(found);

			if (transfer)
			{
				PREDICATELOCKTAG newpredlocktag;

				newpredlocktag.myTarget = heaptarget;
				newpredlocktag.myXact = oldXact;
				newpredlock = (PREDICATELOCK *)
					hash_search_with_hash_value(PredicateLockHash,
												&newpredlocktag,
												PredicateLockHashCodeFromTargetHashCode(&newpredlocktag,
																						heaptargettaghash),
												HASH_ENTER,
												&found);
				if (!found)
				{
					dlist_push_tail(&(heaptarget->predicateLocks),
									&(newpredlock->targetLink));
					dlist_push_tail(&(newpredlocktag.myXact->predicateLocks),
									&(newpredlock->xactLink));
					newpredlock->commitSeqNo = oldCommitSeqNo;
				}
				else
				{
					if (newpredlock->commitSeqNo < oldCommitSeqNo)
						newpredlock->commitSeqNo = oldCommitSeqNo;
				}

				Assert(newpredlock->commitSeqNo != 0);
				Assert((newpredlock->commitSeqNo == InvalidSerCommitSeqNo)
					   || (newpredlock->tag.myXact == OldCommittedSxact));
			}
		}

		hash_search(PredicateLockTargetHash, &oldtarget->tag, HASH_REMOVE,
					&found);
		Assert(found);
	}

	/* Put the scratch entry back */
	if (transfer)
		RestoreScratchTarget(true);

	/* Release locks in reverse order */
	LWLockRelease(SerializableXactHashLock);
	for (i = NUM_PREDICATELOCK_PARTITIONS - 1; i >= 0; i--)
		LWLockRelease(PredicateLockHashPartitionLockByIndex(i));
	LWLockRelease(SerializablePredicateListLock);
}

/*
 * TransferPredicateLocksToHeapRelation
 *		For all transactions, transfer all predicate locks for the given
 *		relation to a single relation lock on the heap.
 */
/*
 * TransferPredicateLocksToHeapRelation
 *      (中文)把给定关系上的所有谓词锁合并为堆关系上的单个关系锁
 *
 * 【作用】CLUSTER / REINDEX / VACUUM FULL 等重写表的操作,在
 * 扫描前把所有事务对该关系(及其索引)的细粒度锁统一提升为
 * 堆关系的关系级锁——重写后页/元组位置全部变化,只有关系级
 * 锁仍有效。直接委托 DropAllPredicateLocksFromTable(relation,
 * true)。
 *
 * 【设计思想】这些操作按新结构重写整个表,旧页级/元组级锁
 * 失去意义;统一提升既保留串行化语义(锁范围变宽,可能误报
 * 但不漏报),又避免在重写过程中维护大量过时锁。
 *
 * 【参数】relation —— 待处理的关系(堆或索引)。
 * 【返回值】无。
 */
void
TransferPredicateLocksToHeapRelation(Relation relation)
{
	DropAllPredicateLocksFromTable(relation, true);
}


/*
 *		PredicateLockPageSplit
 *
 * Copies any predicate locks for the old page to the new page.
 * Skip if this is a temporary table or toast table.
 *
 * NOTE: A page split (or overflow) affects all serializable transactions,
 * even if it occurs in the context of another transaction isolation level.
 *
 * NOTE: This currently leaves the local copy of the locks without
 * information on the new lock which is in shared memory.  This could cause
 * problems if enough page splits occur on locked pages without the processes
 * which hold the locks getting in and noticing.
 */
/*
 * PredicateLockPageSplit
 *      (中文)索引页分裂时复制旧页上的谓词锁到新页
 *
 * 【作用】B-tree/GiST 等索引页分裂(含溢出页)时由索引 AM 调用:
 * 把 oldblkno 页上的全部谓词锁复制(不删除!)到 newblkno 页。
 * 页分裂会影响所有可串行化事务,即使分裂者是其他隔离级别。
 *
 * 【设计思想】分裂后数据分布到两页,谓词锁必须覆盖"所有
 * 可能的插入位置",故旧页锁保留(不能丢:扫描可能再次访问),
 * 新页锁新增。先尝试普通复制;若共享内存不足(不允许失败),
 * 退而求其次把锁提升到关系级(removeOld = true 的转移,粗锁
 * 覆盖两页,损失精度但保证语义)。全程持有
 * SerializablePredicateListLock(排他)。英文注释提醒:本地表
 * 不随新锁更新,反复分裂可能让本地计数失真(仅影响提升
 * 决策,无碍正确性)。
 *
 * 【参数】
 *   relation —— 关系;
 *   oldblkno —— 旧页号;
 *   newblkno —— 新页号。
 * 【返回值】无。
 */
void
PredicateLockPageSplit(Relation relation, BlockNumber oldblkno,
					   BlockNumber newblkno)
{
	PREDICATELOCKTARGETTAG oldtargettag;
	PREDICATELOCKTARGETTAG newtargettag;
	bool		success;

	/*
	 * Bail out quickly if there are no serializable transactions running.
	 *
	 * It's safe to do this check without taking any additional locks. Even if
	 * a serializable transaction starts concurrently, we know it can't take
	 * any SIREAD locks on the page being split because the caller is holding
	 * the associated buffer page lock. Memory reordering isn't an issue; the
	 * memory barrier in the LWLock acquisition guarantees that this read
	 * occurs while the buffer page lock is held.
	 */
	if (!TransactionIdIsValid(PredXact->SxactGlobalXmin))
		return;

	if (!PredicateLockingNeededForRelation(relation))
		return;

	Assert(oldblkno != newblkno);
	Assert(BlockNumberIsValid(oldblkno));
	Assert(BlockNumberIsValid(newblkno));

	SET_PREDICATELOCKTARGETTAG_PAGE(oldtargettag,
									relation->rd_locator.dbOid,
									relation->rd_id,
									oldblkno);
	SET_PREDICATELOCKTARGETTAG_PAGE(newtargettag,
									relation->rd_locator.dbOid,
									relation->rd_id,
									newblkno);

	LWLockAcquire(SerializablePredicateListLock, LW_EXCLUSIVE);

	/*
	 * Try copying the locks over to the new page's tag, creating it if
	 * necessary.
	 */
	success = TransferPredicateLocksToNewTarget(oldtargettag,
												newtargettag,
												false);

	if (!success)
	{
		/*
		 * No more predicate lock entries are available. Failure isn't an
		 * option here, so promote the page lock to a relation lock.
		 */

		/* Get the parent relation lock's lock tag */
		success = GetParentPredicateLockTag(&oldtargettag,
											&newtargettag);
		Assert(success);

		/*
		 * Move the locks to the parent. This shouldn't fail.
		 *
		 * Note that here we are removing locks held by other backends,
		 * leading to a possible inconsistency in their local lock hash table.
		 * This is OK because we're replacing it with a lock that covers the
		 * old one.
		 */
		success = TransferPredicateLocksToNewTarget(oldtargettag,
													newtargettag,
													true);
		Assert(success);
	}

	LWLockRelease(SerializablePredicateListLock);
}

/*
 *		PredicateLockPageCombine
 *
 * Combines predicate locks for two existing pages.
 * Skip if this is a temporary table or toast table.
 *
 * NOTE: A page combine affects all serializable transactions, even if it
 * occurs in the context of another transaction isolation level.
 */
/*
 * PredicateLockPageCombine
 *      (中文)索引页合并时处理谓词锁
 *
 * 【作用】索引页合并(B-tree)时由索引 AM 调用。理想做法是把
 * 旧页锁"移动"到新页;但移动会删除旧锁,其他后端本地表不会
 * 同步(留下"持有着不存在的锁"的脏记录,不可接受),因此实际
 * 与页分裂做同样的工作:新页加锁、旧页保留。
 *
 * 【设计思想】牺牲部分精度换取正确性:旧页 + 新页同时持锁
 * 造成一些误报,但合并事件罕见,误报可接受(英文注释)。
 *
 * 【参数】
 *   relation —— 关系;
 *   oldblkno —— 旧页号(将被合并掉);
 *   newblkno —— 保留页号。
 * 【返回值】无。
 */
void
PredicateLockPageCombine(Relation relation, BlockNumber oldblkno,
						 BlockNumber newblkno)
{
	/*
	 * Page combines differ from page splits in that we ought to be able to
	 * remove the locks on the old page after transferring them to the new
	 * page, instead of duplicating them. However, because we can't edit other
	 * backends' local lock tables, removing the old lock would leave them
	 * with an entry in their LocalPredicateLockHash for a lock they're not
	 * holding, which isn't acceptable. So we wind up having to do the same
	 * work as a page split, acquiring a lock on the new page and keeping the
	 * old page locked too. That can lead to some false positives, but should
	 * be rare in practice.
	 */
	PredicateLockPageSplit(relation, oldblkno, newblkno);
}

/*
 * Walk the list of in-progress serializable transactions and find the new
 * xmin.
 */
/*
 * SetNewSxactGlobalXmin
 *      (中文)重算活动可串行化事务的全局 xmin
 *
 * 【作用】当持有最老 xmin 的事务全部结束时(ReleasePredicateLocks
 * 中 SxactGlobalXminCount 减到 0)调用:遍历 activeList,在
 * "未回滚、未提交、且非虚拟事务"的活动事务中找出最小 xmin 及
 * 使用它的计数,更新 PredXact->SxactGlobalXmin[Count],并同步
 * Serial SLRU 的下界(SerialSetActiveSerXmin)。
 *
 * 【设计思想】SxactGlobalXmin 是"已结束事务可被清理"的水位:
 * 提交早于它的旧事务不再与任何活动事务重叠,其锁/冲突可以
 * 回收(见 ClearOldPredicateLocks 的 finishedBefore 比较)。回滚
 * 事务因马上要被清理而不计入。
 *
 * 【参数】无(操作全局状态;须持有 SerializableXactHashLock)。
 * 【返回值】无。
 */
static void
SetNewSxactGlobalXmin(void)
{
	dlist_iter	iter;

	Assert(LWLockHeldByMe(SerializableXactHashLock));

	PredXact->SxactGlobalXmin = InvalidTransactionId;
	PredXact->SxactGlobalXminCount = 0;

	dlist_foreach(iter, &PredXact->activeList)
	{
		SERIALIZABLEXACT *sxact =
			dlist_container(SERIALIZABLEXACT, xactLink, iter.cur);

		if (!SxactIsRolledBack(sxact)
			&& !SxactIsCommitted(sxact)
			&& sxact != OldCommittedSxact)
		{
			Assert(sxact->xmin != InvalidTransactionId);
			if (!TransactionIdIsValid(PredXact->SxactGlobalXmin)
				|| TransactionIdPrecedes(sxact->xmin,
										 PredXact->SxactGlobalXmin))
			{
				PredXact->SxactGlobalXmin = sxact->xmin;
				PredXact->SxactGlobalXminCount = 1;
			}
			else if (TransactionIdEquals(sxact->xmin,
										 PredXact->SxactGlobalXmin))
				PredXact->SxactGlobalXminCount++;
		}
	}

	SerialSetActiveSerXmin(PredXact->SxactGlobalXmin);
}

/*
 *		ReleasePredicateLocks
 *
 * Releases predicate locks based on completion of the current transaction,
 * whether committed or rolled back.  It can also be called for a read only
 * transaction when it becomes impossible for the transaction to become
 * part of a dangerous structure.
 *
 * We do nothing unless this is a serializable transaction.
 *
 * This method must ensure that shared memory hash tables are cleaned
 * up in some relatively timely fashion.
 *
 * If this transaction is committing and is holding any predicate locks,
 * it must be added to a list of completed serializable transactions still
 * holding locks.
 *
 * If isReadOnlySafe is true, then predicate locks are being released before
 * the end of the transaction because MySerializableXact has been determined
 * to be RO_SAFE.  In non-parallel mode we can release it completely, but it
 * in parallel mode we partially release the SERIALIZABLEXACT and keep it
 * around until the end of the transaction, allowing each backend to clear its
 * MySerializableXact variable and benefit from the optimization in its own
 * time.
 */
/*
 * ReleasePredicateLocks
 *      (中文)事务结束时释放谓词锁与冲突(提交/回滚/RO_SAFE)
 *
 * 【作用】本文件最复杂的状态机,事务提交、回滚、或只读事务被
 * 判定 RO_SAFE 时调用:
 * - 提交:打 COMMITTED 标志、分配 commitSeqNo、把冲突边结算成
 *   earliestOutConflictCommit(对已提交目标的出边,取最早
 *   prepareSeqNo 并置 CONFLICT_OUT)、挂上 Finished 链表;未写
 *   过数据的提交视为隐式只读;
 * - 回滚:打 DOOMED + ROLLED_BACK,所有边、锁即刻清理,事务
 *   对象即刻归还;
 * - RO_SAFE 并行模式:先部分释放(锁与冲突清理、对象保留),
 *   由 leader 在事务末尾彻底回收(见 SavedSerializableXact);
 * - 结算 only-read 事务:对每条 possibleUnsafe 边,若本事务
 *   提交且带早于该只读快照的冲突出边,则 FlagSxactUnsafe
 *   (其醒来后中止/重试);否则释放边,边清空则标 RO_SAFE 并
 *   唤醒等待中的 DEFERRABLE 事务;
 * - 若自己是最后一个持有全局最老 xmin 的事务,重算
 *   SxactGlobalXmin 并触发 ClearOldPredicateLocks。
 *
 * 【设计思想】这是"危险结构只在提交时结算"原则的实现点:
 * 提交瞬间所有信息齐备(谁已提交、谁还活着、提交顺序),按
 * README-SSI 的两条优化(只对 T_out 先提交的结构中止;只读
 * T_in 仅当 T_out 提交早于其快照时才有害)精确过滤。所有
 * 状态切换在 SerializableXactHashLock 保护下完成,Finished
 * 链表另由 SerializableFinishedListLock 保护。
 *
 * 【参数】
 *   isCommit —— true = 提交路径;false = 回滚/RO_SAFE 释放;
 *   isReadOnlySafe —— true = 因 RO_SAFE 提前释放(非事务结束)。
 * 【返回值】无。
 */
void
ReleasePredicateLocks(bool isCommit, bool isReadOnlySafe)
{
	bool		partiallyReleasing = false;
	bool		needToClear;
	SERIALIZABLEXACT *roXact;
	dlist_mutable_iter iter;

	/*
	 * We can't trust XactReadOnly here, because a transaction which started
	 * as READ WRITE can show as READ ONLY later, e.g., within
	 * subtransactions.  We want to flag a transaction as READ ONLY if it
	 * commits without writing so that de facto READ ONLY transactions get the
	 * benefit of some RO optimizations, so we will use this local variable to
	 * get some cleanup logic right which is based on whether the transaction
	 * was declared READ ONLY at the top level.
	 */
	bool		topLevelIsDeclaredReadOnly;

	/* We can't be both committing and releasing early due to RO_SAFE. */
	Assert(!(isCommit && isReadOnlySafe));

	/* Are we at the end of a transaction, that is, a commit or abort? */
	if (!isReadOnlySafe)
	{
		/*
		 * Parallel workers mustn't release predicate locks at the end of
		 * their transaction.  The leader will do that at the end of its
		 * transaction.
		 */
		if (IsParallelWorker())
		{
			ReleasePredicateLocksLocal();
			return;
		}

		/*
		 * By the time the leader in a parallel query reaches end of
		 * transaction, it has waited for all workers to exit.
		 */
		Assert(!ParallelContextActive());

		/*
		 * If the leader in a parallel query earlier stashed a partially
		 * released SERIALIZABLEXACT for final clean-up at end of transaction
		 * (because workers might still have been accessing it), then it's
		 * time to restore it.
		 */
		if (SavedSerializableXact != InvalidSerializableXact)
		{
			Assert(MySerializableXact == InvalidSerializableXact);
			MySerializableXact = SavedSerializableXact;
			SavedSerializableXact = InvalidSerializableXact;
			Assert(SxactIsPartiallyReleased(MySerializableXact));
		}
	}

	if (MySerializableXact == InvalidSerializableXact)
	{
		Assert(LocalPredicateLockHash == NULL);
		return;
	}

	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	/*
	 * If the transaction is committing, but it has been partially released
	 * already, then treat this as a roll back.  It was marked as rolled back.
	 */
	if (isCommit && SxactIsPartiallyReleased(MySerializableXact))
		isCommit = false;

	/*
	 * If we're called in the middle of a transaction because we discovered
	 * that the SXACT_FLAG_RO_SAFE flag was set, then we'll partially release
	 * it (that is, release the predicate locks and conflicts, but not the
	 * SERIALIZABLEXACT itself) if we're the first backend to have noticed.
	 */
	if (isReadOnlySafe && IsInParallelMode())
	{
		/*
		 * The leader needs to stash a pointer to it, so that it can
		 * completely release it at end-of-transaction.
		 */
		if (!IsParallelWorker())
			SavedSerializableXact = MySerializableXact;

		/*
		 * The first backend to reach this condition will partially release
		 * the SERIALIZABLEXACT.  All others will just clear their
		 * backend-local state so that they stop doing SSI checks for the rest
		 * of the transaction.
		 */
		if (SxactIsPartiallyReleased(MySerializableXact))
		{
			LWLockRelease(SerializableXactHashLock);
			ReleasePredicateLocksLocal();
			return;
		}
		else
		{
			MySerializableXact->flags |= SXACT_FLAG_PARTIALLY_RELEASED;
			partiallyReleasing = true;
			/* ... and proceed to perform the partial release below. */
		}
	}
	Assert(!isCommit || SxactIsPrepared(MySerializableXact));
	Assert(!isCommit || !SxactIsDoomed(MySerializableXact));
	Assert(!SxactIsCommitted(MySerializableXact));
	Assert(SxactIsPartiallyReleased(MySerializableXact)
		   || !SxactIsRolledBack(MySerializableXact));

	/* may not be serializable during COMMIT/ROLLBACK PREPARED */
	Assert(MySerializableXact->pid == 0 || IsolationIsSerializable());

	/* We'd better not already be on the cleanup list. */
	Assert(!SxactIsOnFinishedList(MySerializableXact));

	topLevelIsDeclaredReadOnly = SxactIsReadOnly(MySerializableXact);

	/*
	 * We don't hold XidGenLock lock here, assuming that TransactionId is
	 * atomic!
	 *
	 * If this value is changing, we don't care that much whether we get the
	 * old or new value -- it is just used to determine how far
	 * SxactGlobalXmin must advance before this transaction can be fully
	 * cleaned up.  The worst that could happen is we wait for one more
	 * transaction to complete before freeing some RAM; correctness of visible
	 * behavior is not affected.
	 */
	MySerializableXact->finishedBefore = XidFromFullTransactionId(TransamVariables->nextXid);

	/*
	 * If it's not a commit it's either a rollback or a read-only transaction
	 * flagged SXACT_FLAG_RO_SAFE, and we can clear our locks immediately.
	 */
	if (isCommit)
	{
		MySerializableXact->flags |= SXACT_FLAG_COMMITTED;
		MySerializableXact->commitSeqNo = ++(PredXact->LastSxactCommitSeqNo);
		/* Recognize implicit read-only transaction (commit without write). */
		if (!MyXactDidWrite)
			MySerializableXact->flags |= SXACT_FLAG_READ_ONLY;
	}
	else
	{
		/*
		 * The DOOMED flag indicates that we intend to roll back this
		 * transaction and so it should not cause serialization failures for
		 * other transactions that conflict with it. Note that this flag might
		 * already be set, if another backend marked this transaction for
		 * abort.
		 *
		 * The ROLLED_BACK flag further indicates that ReleasePredicateLocks
		 * has been called, and so the SerializableXact is eligible for
		 * cleanup. This means it should not be considered when calculating
		 * SxactGlobalXmin.
		 */
		MySerializableXact->flags |= SXACT_FLAG_DOOMED;
		MySerializableXact->flags |= SXACT_FLAG_ROLLED_BACK;

		/*
		 * If the transaction was previously prepared, but is now failing due
		 * to a ROLLBACK PREPARED or (hopefully very rare) error after the
		 * prepare, clear the prepared flag.  This simplifies conflict
		 * checking.
		 */
		MySerializableXact->flags &= ~SXACT_FLAG_PREPARED;
	}

	if (!topLevelIsDeclaredReadOnly)
	{
		Assert(PredXact->WritableSxactCount > 0);
		if (--(PredXact->WritableSxactCount) == 0)
		{
			/*
			 * Release predicate locks and rw-conflicts in for all committed
			 * transactions.  There are no longer any transactions which might
			 * conflict with the locks and no chance for new transactions to
			 * overlap.  Similarly, existing conflicts in can't cause pivots,
			 * and any conflicts in which could have completed a dangerous
			 * structure would already have caused a rollback, so any
			 * remaining ones must be benign.
			 */
			PredXact->CanPartialClearThrough = PredXact->LastSxactCommitSeqNo;
		}
	}
	else
	{
		/*
		 * Read-only transactions: clear the list of transactions that might
		 * make us unsafe. Note that we use 'inLink' for the iteration as
		 * opposed to 'outLink' for the r/w xacts.
		 */
		dlist_foreach_modify(iter, &MySerializableXact->possibleUnsafeConflicts)
		{
			RWConflict	possibleUnsafeConflict =
				dlist_container(RWConflictData, inLink, iter.cur);

			Assert(!SxactIsReadOnly(possibleUnsafeConflict->sxactOut));
			Assert(MySerializableXact == possibleUnsafeConflict->sxactIn);

			ReleaseRWConflict(possibleUnsafeConflict);
		}
	}

	/* Check for conflict out to old committed transactions. */
	if (isCommit
		&& !SxactIsReadOnly(MySerializableXact)
		&& SxactHasSummaryConflictOut(MySerializableXact))
	{
		/*
		 * we don't know which old committed transaction we conflicted with,
		 * so be conservative and use FirstNormalSerCommitSeqNo here
		 */
		MySerializableXact->SeqNo.earliestOutConflictCommit =
			FirstNormalSerCommitSeqNo;
		MySerializableXact->flags |= SXACT_FLAG_CONFLICT_OUT;
	}

	/*
	 * Release all outConflicts to committed transactions.  If we're rolling
	 * back clear them all.  Set SXACT_FLAG_CONFLICT_OUT if any point to
	 * previously committed transactions.
	 */
	dlist_foreach_modify(iter, &MySerializableXact->outConflicts)
	{
		RWConflict	conflict =
			dlist_container(RWConflictData, outLink, iter.cur);

		if (isCommit
			&& !SxactIsReadOnly(MySerializableXact)
			&& SxactIsCommitted(conflict->sxactIn))
		{
			if ((MySerializableXact->flags & SXACT_FLAG_CONFLICT_OUT) == 0
				|| conflict->sxactIn->prepareSeqNo < MySerializableXact->SeqNo.earliestOutConflictCommit)
				MySerializableXact->SeqNo.earliestOutConflictCommit = conflict->sxactIn->prepareSeqNo;
			MySerializableXact->flags |= SXACT_FLAG_CONFLICT_OUT;
		}

		if (!isCommit
			|| SxactIsCommitted(conflict->sxactIn)
			|| (conflict->sxactIn->SeqNo.lastCommitBeforeSnapshot >= PredXact->LastSxactCommitSeqNo))
			ReleaseRWConflict(conflict);
	}

	/*
	 * Release all inConflicts from committed and read-only transactions. If
	 * we're rolling back, clear them all.
	 */
	dlist_foreach_modify(iter, &MySerializableXact->inConflicts)
	{
		RWConflict	conflict =
			dlist_container(RWConflictData, inLink, iter.cur);

		if (!isCommit
			|| SxactIsCommitted(conflict->sxactOut)
			|| SxactIsReadOnly(conflict->sxactOut))
			ReleaseRWConflict(conflict);
	}

	if (!topLevelIsDeclaredReadOnly)
	{
		/*
		 * Remove ourselves from the list of possible conflicts for concurrent
		 * READ ONLY transactions, flagging them as unsafe if we have a
		 * conflict out. If any are waiting DEFERRABLE transactions, wake them
		 * up if they are known safe or known unsafe.
		 */
		dlist_foreach_modify(iter, &MySerializableXact->possibleUnsafeConflicts)
		{
			RWConflict	possibleUnsafeConflict =
				dlist_container(RWConflictData, outLink, iter.cur);

			roXact = possibleUnsafeConflict->sxactIn;
			Assert(MySerializableXact == possibleUnsafeConflict->sxactOut);
			Assert(SxactIsReadOnly(roXact));

			/* Mark conflicted if necessary. */
			if (isCommit
				&& MyXactDidWrite
				&& SxactHasConflictOut(MySerializableXact)
				&& (MySerializableXact->SeqNo.earliestOutConflictCommit
					<= roXact->SeqNo.lastCommitBeforeSnapshot))
			{
				/*
				 * This releases possibleUnsafeConflict (as well as all other
				 * possible conflicts for roXact)
				 */
				FlagSxactUnsafe(roXact);
			}
			else
			{
				ReleaseRWConflict(possibleUnsafeConflict);

				/*
				 * If we were the last possible conflict, flag it safe. The
				 * transaction can now safely release its predicate locks (but
				 * that transaction's backend has to do that itself).
				 */
				if (dlist_is_empty(&roXact->possibleUnsafeConflicts))
					roXact->flags |= SXACT_FLAG_RO_SAFE;
			}

			/*
			 * Wake up the process for a waiting DEFERRABLE transaction if we
			 * now know it's either safe or conflicted.
			 */
			if (SxactIsDeferrableWaiting(roXact) &&
				(SxactIsROUnsafe(roXact) || SxactIsROSafe(roXact)))
				ProcSendSignal(roXact->pgprocno);
		}
	}

	/*
	 * Check whether it's time to clean up old transactions. This can only be
	 * done when the last serializable transaction with the oldest xmin among
	 * serializable transactions completes.  We then find the "new oldest"
	 * xmin and purge any transactions which finished before this transaction
	 * was launched.
	 *
	 * For parallel queries in read-only transactions, it might run twice. We
	 * only release the reference on the first call.
	 */
	needToClear = false;
	if ((partiallyReleasing ||
		 !SxactIsPartiallyReleased(MySerializableXact)) &&
		TransactionIdEquals(MySerializableXact->xmin,
							PredXact->SxactGlobalXmin))
	{
		Assert(PredXact->SxactGlobalXminCount > 0);
		if (--(PredXact->SxactGlobalXminCount) == 0)
		{
			SetNewSxactGlobalXmin();
			needToClear = true;
		}
	}

	LWLockRelease(SerializableXactHashLock);

	LWLockAcquire(SerializableFinishedListLock, LW_EXCLUSIVE);

	/* Add this to the list of transactions to check for later cleanup. */
	if (isCommit)
		dlist_push_tail(FinishedSerializableTransactions,
						&MySerializableXact->finishedLink);

	/*
	 * If we're releasing a RO_SAFE transaction in parallel mode, we'll only
	 * partially release it.  That's necessary because other backends may have
	 * a reference to it.  The leader will release the SERIALIZABLEXACT itself
	 * at the end of the transaction after workers have stopped running.
	 */
	if (!isCommit)
		ReleaseOneSerializableXact(MySerializableXact,
								   isReadOnlySafe && IsInParallelMode(),
								   false);

	LWLockRelease(SerializableFinishedListLock);

	if (needToClear)
		ClearOldPredicateLocks();

	ReleasePredicateLocksLocal();
}

/* (中文)清空本后端与 SSI 相关的全部本地状态:重置
 * MySerializableXact 与 MyXactDidWrite,销毁本地谓词锁表。
 * 由 ReleasePredicateLocks 在共享侧清理完毕后调用(含并行
 * worker 的提前退出路径,worker 不碰共享结构)。 */

static void
ReleasePredicateLocksLocal(void)
{
	MySerializableXact = InvalidSerializableXact;
	MyXactDidWrite = false;

	/* Delete per-transaction lock table */
	if (LocalPredicateLockHash != NULL)
	{
		hash_destroy(LocalPredicateLockHash);
		LocalPredicateLockHash = NULL;
	}
}

/*
 * Clear old predicate locks, belonging to committed transactions that are no
 * longer interesting to any in-progress transaction.
 */
/*
 * ClearOldPredicateLocks
 *      (中文)清理已不再被任何活动事务关注的已提交事务的锁
 *
 * 【作用】活动事务的全局 xmin 前移后调用:遍历 Finished 链表
 * (按提交序),对每个已结束事务判断:
 * 1. finishedBefore ≤ SxactGlobalXmin:该事务提交于所有活动事务
 *    取快照之前,彻底清理(整对象释放);
 * 2. 否则若其 commitSeqNo 落在 (HavePartialClearedThrough,
 *    CanPartialClearThrough] 区间:没有可写事务与之重叠(只有
 *    只读事务可能参考它),做部分清理——只读事务整对象释放,
 *    读写事务保留对象但释放谓词锁与冲突进边;
 * 3. 再往后的仍"有趣",立即停止(链表有序)。
 * 最后清扫 OldCommittedSxact 名下、commitSeqNo 早于
 * CanPartialClearThrough 的被摘要锁。
 *
 * 【设计思想】CanPartialClearThrough 在最后一个可写事务结束时
 * 前移(见 ReleasePredicateLocks):之后不可能再有新写事务启动
 * 去与旧提交冲突,旧锁留着只会造成误报。两层锁
 * (SerializableFinishedListLock + SerializableXactHashLock)按
 * 既定顺序交替获取。
 *
 * 【参数】无。【返回值】无。
 */
static void
ClearOldPredicateLocks(void)
{
	dlist_mutable_iter iter;

	/*
	 * Loop through finished transactions. They are in commit order, so we can
	 * stop as soon as we find one that's still interesting.
	 */
	LWLockAcquire(SerializableFinishedListLock, LW_EXCLUSIVE);
	LWLockAcquire(SerializableXactHashLock, LW_SHARED);
	dlist_foreach_modify(iter, FinishedSerializableTransactions)
	{
		SERIALIZABLEXACT *finishedSxact =
			dlist_container(SERIALIZABLEXACT, finishedLink, iter.cur);

		if (!TransactionIdIsValid(PredXact->SxactGlobalXmin)
			|| TransactionIdPrecedesOrEquals(finishedSxact->finishedBefore,
											 PredXact->SxactGlobalXmin))
		{
			/*
			 * This transaction committed before any in-progress transaction
			 * took its snapshot. It's no longer interesting.
			 */
			LWLockRelease(SerializableXactHashLock);
			dlist_delete_thoroughly(&finishedSxact->finishedLink);
			ReleaseOneSerializableXact(finishedSxact, false, false);
			LWLockAcquire(SerializableXactHashLock, LW_SHARED);
		}
		else if (finishedSxact->commitSeqNo > PredXact->HavePartialClearedThrough
				 && finishedSxact->commitSeqNo <= PredXact->CanPartialClearThrough)
		{
			/*
			 * Any active transactions that took their snapshot before this
			 * transaction committed are read-only, so we can clear part of
			 * its state.
			 */
			LWLockRelease(SerializableXactHashLock);

			if (SxactIsReadOnly(finishedSxact))
			{
				/* A read-only transaction can be removed entirely */
				dlist_delete_thoroughly(&(finishedSxact->finishedLink));
				ReleaseOneSerializableXact(finishedSxact, false, false);
			}
			else
			{
				/*
				 * A read-write transaction can only be partially cleared. We
				 * need to keep the SERIALIZABLEXACT but can release the
				 * SIREAD locks and conflicts in.
				 */
				ReleaseOneSerializableXact(finishedSxact, true, false);
			}

			PredXact->HavePartialClearedThrough = finishedSxact->commitSeqNo;
			LWLockAcquire(SerializableXactHashLock, LW_SHARED);
		}
		else
		{
			/* Still interesting. */
			break;
		}
	}
	LWLockRelease(SerializableXactHashLock);

	/*
	 * Loop through predicate locks on dummy transaction for summarized data.
	 */
	LWLockAcquire(SerializablePredicateListLock, LW_SHARED);
	dlist_foreach_modify(iter, &OldCommittedSxact->predicateLocks)
	{
		PREDICATELOCK *predlock =
			dlist_container(PREDICATELOCK, xactLink, iter.cur);
		bool		canDoPartialCleanup;

		LWLockAcquire(SerializableXactHashLock, LW_SHARED);
		Assert(predlock->commitSeqNo != 0);
		Assert(predlock->commitSeqNo != InvalidSerCommitSeqNo);
		canDoPartialCleanup = (predlock->commitSeqNo <= PredXact->CanPartialClearThrough);
		LWLockRelease(SerializableXactHashLock);

		/*
		 * If this lock originally belonged to an old enough transaction, we
		 * can release it.
		 */
		if (canDoPartialCleanup)
		{
			PREDICATELOCKTAG tag;
			PREDICATELOCKTARGET *target;
			PREDICATELOCKTARGETTAG targettag;
			uint32		targettaghash;
			LWLock	   *partitionLock;

			tag = predlock->tag;
			target = tag.myTarget;
			targettag = target->tag;
			targettaghash = PredicateLockTargetTagHashCode(&targettag);
			partitionLock = PredicateLockHashPartitionLock(targettaghash);

			LWLockAcquire(partitionLock, LW_EXCLUSIVE);

			dlist_delete(&(predlock->targetLink));
			dlist_delete(&(predlock->xactLink));

			hash_search_with_hash_value(PredicateLockHash, &tag,
										PredicateLockHashCodeFromTargetHashCode(&tag,
																				targettaghash),
										HASH_REMOVE, NULL);
			RemoveTargetIfNoLongerUsed(target, targettaghash);

			LWLockRelease(partitionLock);
		}
	}

	LWLockRelease(SerializablePredicateListLock);
	LWLockRelease(SerializableFinishedListLock);
}

/*
 * This is the normal way to delete anything from any of the predicate
 * locking hash tables.  Given a transaction which we know can be deleted:
 * delete all predicate locks held by that transaction and any predicate
 * lock targets which are now unreferenced by a lock; delete all conflicts
 * for the transaction; delete all xid values for the transaction; then
 * delete the transaction.
 *
 * When the partial flag is set, we can release all predicate locks and
 * in-conflict information -- we've established that there are no longer
 * any overlapping read write transactions for which this transaction could
 * matter -- but keep the transaction entry itself and any outConflicts.
 *
 * When the summarize flag is set, we've run short of room for sxact data
 * and must summarize to the SLRU.  Predicate locks are transferred to a
 * dummy "old" transaction, with duplicate locks on a single target
 * collapsing to a single lock with the "latest" commitSeqNo from among
 * the conflicting locks..
 */
/*
 * ReleaseOneSerializableXact
 *      (中文)彻底/部分/摘要式地删除一个事务的全部谓词锁数据
 *
 * 【作用】"任何谓词锁数据的最终清理入口"(见英文注释):按
 * 三种模式处理一个已结束(提交或回滚)事务:
 * - 默认:删除其全部谓词锁(连同空目标)、全部进出冲突边、
 *   SerializableXidHash 中的 xid 记录,最后归还事务槽位;
 * - partial = true:只释放谓词锁与冲突进边——已证明没有可写
 *   事务再与之重叠,但对象本身与出边必须保留(还有只读事务
 *   或后续结算要看);
 * - summarize = true:谓词锁转交给 OldCommittedSxact(同目标
 *   去重,commitSeqNo 取较大者),冲突双方补
 *   SUMMARY_CONFLICT_IN/OUT 标志,保留冲突信息的最小形态,
 *   槽位归还。
 *
 * 【设计思想】清理顺序与获取顺序相反:先谓词锁(分区锁 +
 * 链表锁),再 SerializableXactHashLock 下的冲突边与 xid 记录。
 * 调用者须持有 SerializableFinishedListLock 且对象不在
 * Finished 链表(partial = true 除外)。
 *
 * 【参数】
 *   sxact —— 待处理事务;
 *   partial —— true = 部分释放(保留对象与出边);
 *   summarize —— true = 摘要式转移(供 SummarizeOldestCommittedSxact)。
 * 【返回值】无。
 */
static void
ReleaseOneSerializableXact(SERIALIZABLEXACT *sxact, bool partial,
						   bool summarize)
{
	SERIALIZABLEXIDTAG sxidtag;
	dlist_mutable_iter iter;

	Assert(sxact != NULL);
	Assert(SxactIsRolledBack(sxact) || SxactIsCommitted(sxact));
	Assert(partial || !SxactIsOnFinishedList(sxact));
	Assert(LWLockHeldByMe(SerializableFinishedListLock));

	/*
	 * First release all the predicate locks held by this xact (or transfer
	 * them to OldCommittedSxact if summarize is true)
	 */
	LWLockAcquire(SerializablePredicateListLock, LW_SHARED);
	if (IsInParallelMode())
		LWLockAcquire(&sxact->perXactPredicateListLock, LW_EXCLUSIVE);
	dlist_foreach_modify(iter, &sxact->predicateLocks)
	{
		PREDICATELOCK *predlock =
			dlist_container(PREDICATELOCK, xactLink, iter.cur);
		PREDICATELOCKTAG tag;
		PREDICATELOCKTARGET *target;
		PREDICATELOCKTARGETTAG targettag;
		uint32		targettaghash;
		LWLock	   *partitionLock;

		tag = predlock->tag;
		target = tag.myTarget;
		targettag = target->tag;
		targettaghash = PredicateLockTargetTagHashCode(&targettag);
		partitionLock = PredicateLockHashPartitionLock(targettaghash);

		LWLockAcquire(partitionLock, LW_EXCLUSIVE);

		dlist_delete(&predlock->targetLink);

		hash_search_with_hash_value(PredicateLockHash, &tag,
									PredicateLockHashCodeFromTargetHashCode(&tag,
																			targettaghash),
									HASH_REMOVE, NULL);
		if (summarize)
		{
			bool		found;

			/* Fold into dummy transaction list. */
			tag.myXact = OldCommittedSxact;
			predlock = hash_search_with_hash_value(PredicateLockHash, &tag,
												   PredicateLockHashCodeFromTargetHashCode(&tag,
																						   targettaghash),
												   HASH_ENTER_NULL, &found);
			if (!predlock)
				ereport(ERROR,
						(errcode(ERRCODE_OUT_OF_MEMORY),
						 errmsg("out of shared memory"),
						 errhint("You might need to increase \"%s\".", "max_pred_locks_per_transaction")));
			if (found)
			{
				Assert(predlock->commitSeqNo != 0);
				Assert(predlock->commitSeqNo != InvalidSerCommitSeqNo);
				if (predlock->commitSeqNo < sxact->commitSeqNo)
					predlock->commitSeqNo = sxact->commitSeqNo;
			}
			else
			{
				dlist_push_tail(&target->predicateLocks,
								&predlock->targetLink);
				dlist_push_tail(&OldCommittedSxact->predicateLocks,
								&predlock->xactLink);
				predlock->commitSeqNo = sxact->commitSeqNo;
			}
		}
		else
			RemoveTargetIfNoLongerUsed(target, targettaghash);

		LWLockRelease(partitionLock);
	}

	/*
	 * Rather than retail removal, just re-init the head after we've run
	 * through the list.
	 */
	dlist_init(&sxact->predicateLocks);

	if (IsInParallelMode())
		LWLockRelease(&sxact->perXactPredicateListLock);
	LWLockRelease(SerializablePredicateListLock);

	sxidtag.xid = sxact->topXid;
	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	/* Release all outConflicts (unless 'partial' is true) */
	if (!partial)
	{
		dlist_foreach_modify(iter, &sxact->outConflicts)
		{
			RWConflict	conflict =
				dlist_container(RWConflictData, outLink, iter.cur);

			if (summarize)
				conflict->sxactIn->flags |= SXACT_FLAG_SUMMARY_CONFLICT_IN;
			ReleaseRWConflict(conflict);
		}
	}

	/* Release all inConflicts. */
	dlist_foreach_modify(iter, &sxact->inConflicts)
	{
		RWConflict	conflict =
			dlist_container(RWConflictData, inLink, iter.cur);

		if (summarize)
			conflict->sxactOut->flags |= SXACT_FLAG_SUMMARY_CONFLICT_OUT;
		ReleaseRWConflict(conflict);
	}

	/* Finally, get rid of the xid and the record of the transaction itself. */
	if (!partial)
	{
		if (sxidtag.xid != InvalidTransactionId)
			hash_search(SerializableXidHash, &sxidtag, HASH_REMOVE, NULL);
		ReleasePredXact(sxact);
	}

	LWLockRelease(SerializableXactHashLock);
}

/*
 * Tests whether the given top level transaction is concurrent with
 * (overlaps) our current transaction.
 *
 * We need to identify the top level transaction for SSI, anyway, so pass
 * that to this function to save the overhead of checking the snapshot's
 * subxip array.
 */
/*
 * XidIsConcurrent
 *      (中文)给定顶层 xid 的事务是否与当前事务并发(重叠)?
 *
 * 【作用】冲突判定前的重要过滤:用当前快照判断写者事务是否
 * 与我们在时间上重叠——xid 晚于快照 xmax 或出现在活动 xip
 * 数组中 = 并发;早于 xmin = 已完结不并发。只有并发事务的
 * 写才能造成 rw 冲突(见 CheckForSerializableConflictOut)。
 *
 * 【设计思想】基于快照的重叠判定快而准;顶层 xid 直接比较
 * 即可,无需查子事务数组(SSI 处处使用顶层 xid,见 README-SSI)。
 *
 * 【参数】xid —— 待测的顶层事务号(有效,且非本事务自身)。
 * 【返回值】true = 与当前事务并发;false = 已完结或尚未开始。
 */
static bool
XidIsConcurrent(TransactionId xid)
{
	Snapshot	snap;

	Assert(TransactionIdIsValid(xid));
	Assert(!TransactionIdEquals(xid, GetTopTransactionIdIfAny()));

	snap = GetTransactionSnapshot();

	if (TransactionIdPrecedes(xid, snap->xmin))
		return false;

	if (TransactionIdFollowsOrEquals(xid, snap->xmax))
		return true;

	return pg_lfind32(xid, snap->xip, snap->xcnt);
}

/*
 * CheckForSerializableConflictOutNeeded
 *      (中文)是否需要走"冲突出"检查?(快速预检)
 *
 * 【作用】表访问方法在"读到被修改过的元组"时先调用本函数预检:
 * 若无需 SSI 处理(SerializationNeededForRead 判定)直接返回
 * false;若本事务已被别人标记 DOOMED(作为危险结构的枢轴被
 * 判死),立即抛 40001。通过则返回 true,调用者继续构造
 * CheckForSerializableConflictOut 所需的参数。
 *
 * 【设计思想】把"读路径上最常见的无事可做"与"已判死"两种
 * 情形提前收敛,避免读路径在非 SSI 场景的开销;DOOMED 的
 * 报错集中在这里与冲突出检查两处,保证判死后很快失败。
 *
 * 【参数】
 *   relation —— 读操作涉及的关系;
 *   snapshot —— 读快照。
 * 【返回值】true = 需要继续冲突出检查;false = 无需处理。
 */
bool
CheckForSerializableConflictOutNeeded(Relation relation, Snapshot snapshot)
{
	if (!SerializationNeededForRead(relation, snapshot))
		return false;

	/* Check if someone else has already decided that we need to die */
	if (SxactIsDoomed(MySerializableXact))
	{
		ereport(ERROR,
				(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
				 errmsg("could not serialize access due to read/write dependencies among transactions"),
				 errdetail_internal("Reason code: Canceled on identification as a pivot, during conflict out checking."),
				 errhint("The transaction might succeed if retried.")));
	}

	return true;
}

/*
 * CheckForSerializableConflictOut
 *		A table AM is reading a tuple that has been modified.  If it determines
 *		that the tuple version it is reading is not visible to us, it should
 *		pass in the top level xid of the transaction that created it.
 *		Otherwise, if it determines that it is visible to us but it has been
 *		deleted or there is a newer version available due to an update, it
 *		should pass in the top level xid of the modifying transaction.
 *
 * This function will check for overlap with our own transaction.  If the given
 * xid is also serializable and the transactions overlap (i.e., they cannot see
 * each other's writes), then we have a conflict out.
 */
/*
 * CheckForSerializableConflictOut
 *      (中文)读元组时的冲突出检查(建立 读者→写者 的 rw 边)
 *
 * 【作用】表 AM 读到被修改过的元组时调用(xid 的语义见英文
 * 注释:不可见版本的产生者,或可见但已删/被更新的修改者):
 * 若写者是并发可串行化事务,登记一条
 * "本事务(读者)→ 写者"的 rw 冲突边(FlagRWConflict 内部会先
 * 做危险结构检查,发现即中止)。已 DOOMED 或写者是本事务自身
 * 时直接忽略。
 *
 * 【主要分支】
 * 1. 写者不在 SerializableXidHash(已提交并摘要):查 SLRU 摘要
 *    (SerialGetMinConflictCommitSeqNo)。摘要冲突提交序号有效且
 *    早于本快照(或本事务可写),说明老枢轴事务先于本快照提交
 *    且带冲突出边 → 必中止;否则只置 SUMMARY_CONFLICT_OUT 标志
 *    记下这笔潜在冲突出,供提交时结算;
 * 2. 写者对象带 SUMMARY_CONFLICT_OUT(它连着一笔已摘要的老
 *    冲突,提交时序不可考):未 prepared 则直接 DOOM 它(它还可
 *    回滚);已 prepared 则中止自己;
 * 3. 只读事务优化:写者已提交且无早于本快照的冲突出边,则本
 *    只读事务"看起来先执行",无冲突;
 * 4. 非并发(写者早于本快照完结):无冲突。
 *
 * 【设计思想】冲突出边 = "写者写的东西我没看见",它是危险
 * 结构判定的另一半(冲入边在 CheckForSerializableConflictIn)。
 * 所有分支在 SerializableXactHashLock(排他)下完成,因为要改
 * 冲突链表。
 *
 * 【参数】
 *   relation —— 读操作的关系;
 *   xid —— 修改该元组的顶层事务号;
 *   snapshot —— 读快照。
 * 【返回值】无(可能抛 40001)。
 */
void
CheckForSerializableConflictOut(Relation relation, TransactionId xid, Snapshot snapshot)
{
	SERIALIZABLEXIDTAG sxidtag;
	SERIALIZABLEXID *sxid;
	SERIALIZABLEXACT *sxact;

	if (!SerializationNeededForRead(relation, snapshot))
		return;

	/* Check if someone else has already decided that we need to die */
	if (SxactIsDoomed(MySerializableXact))
	{
		ereport(ERROR,
				(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
				 errmsg("could not serialize access due to read/write dependencies among transactions"),
				 errdetail_internal("Reason code: Canceled on identification as a pivot, during conflict out checking."),
				 errhint("The transaction might succeed if retried.")));
	}
	Assert(TransactionIdIsValid(xid));

	if (TransactionIdEquals(xid, GetTopTransactionIdIfAny()))
		return;

	/*
	 * Find sxact or summarized info for the top level xid.
	 */
	sxidtag.xid = xid;
	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);
	sxid = (SERIALIZABLEXID *)
		hash_search(SerializableXidHash, &sxidtag, HASH_FIND, NULL);
	if (!sxid)
	{
		/*
		 * Transaction not found in "normal" SSI structures.  Check whether it
		 * got pushed out to SLRU storage for "old committed" transactions.
		 */
		SerCommitSeqNo conflictCommitSeqNo;

		conflictCommitSeqNo = SerialGetMinConflictCommitSeqNo(xid);
		if (conflictCommitSeqNo != 0)
		{
			if (conflictCommitSeqNo != InvalidSerCommitSeqNo
				&& (!SxactIsReadOnly(MySerializableXact)
					|| conflictCommitSeqNo
					<= MySerializableXact->SeqNo.lastCommitBeforeSnapshot))
				ereport(ERROR,
						(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
						 errmsg("could not serialize access due to read/write dependencies among transactions"),
						 errdetail_internal("Reason code: Canceled on conflict out to old pivot %u.", xid),
						 errhint("The transaction might succeed if retried.")));

			if (SxactHasSummaryConflictIn(MySerializableXact)
				|| !dlist_is_empty(&MySerializableXact->inConflicts))
				ereport(ERROR,
						(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
						 errmsg("could not serialize access due to read/write dependencies among transactions"),
						 errdetail_internal("Reason code: Canceled on identification as a pivot, with conflict out to old committed transaction %u.", xid),
						 errhint("The transaction might succeed if retried.")));

			MySerializableXact->flags |= SXACT_FLAG_SUMMARY_CONFLICT_OUT;
		}

		/* It's not serializable or otherwise not important. */
		LWLockRelease(SerializableXactHashLock);
		return;
	}
	sxact = sxid->myXact;
	Assert(TransactionIdEquals(sxact->topXid, xid));
	if (sxact == MySerializableXact || SxactIsDoomed(sxact))
	{
		/* Can't conflict with ourself or a transaction that will roll back. */
		LWLockRelease(SerializableXactHashLock);
		return;
	}

	/*
	 * We have a conflict out to a transaction which has a conflict out to a
	 * summarized transaction.  That summarized transaction must have
	 * committed first, and we can't tell when it committed in relation to our
	 * snapshot acquisition, so something needs to be canceled.
	 */
	if (SxactHasSummaryConflictOut(sxact))
	{
		if (!SxactIsPrepared(sxact))
		{
			sxact->flags |= SXACT_FLAG_DOOMED;
			LWLockRelease(SerializableXactHashLock);
			return;
		}
		else
		{
			LWLockRelease(SerializableXactHashLock);
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("could not serialize access due to read/write dependencies among transactions"),
					 errdetail_internal("Reason code: Canceled on conflict out to old pivot."),
					 errhint("The transaction might succeed if retried.")));
		}
	}

	/*
	 * If this is a read-only transaction and the writing transaction has
	 * committed, and it doesn't have a rw-conflict to a transaction which
	 * committed before it, no conflict.
	 */
	if (SxactIsReadOnly(MySerializableXact)
		&& SxactIsCommitted(sxact)
		&& !SxactHasSummaryConflictOut(sxact)
		&& (!SxactHasConflictOut(sxact)
			|| MySerializableXact->SeqNo.lastCommitBeforeSnapshot < sxact->SeqNo.earliestOutConflictCommit))
	{
		/* Read-only transaction will appear to run first.  No conflict. */
		LWLockRelease(SerializableXactHashLock);
		return;
	}

	if (!XidIsConcurrent(xid))
	{
		/* This write was already in our snapshot; no conflict. */
		LWLockRelease(SerializableXactHashLock);
		return;
	}

	if (RWConflictExists(MySerializableXact, sxact))
	{
		/* We don't want duplicate conflict records in the list. */
		LWLockRelease(SerializableXactHashLock);
		return;
	}

	/*
	 * Flag the conflict.  But first, if this conflict creates a dangerous
	 * structure, ereport an error.
	 */
	FlagRWConflict(MySerializableXact, sxact);
	LWLockRelease(SerializableXactHashLock);
}

/*
 * Check a particular target for rw-dependency conflict in. A subroutine of
 * CheckForSerializableConflictIn().
 */
/*
 * CheckTargetForConflictsIn
 *      (中文)检查单个目标的冲入冲突(写元组路径的核心子程序)
 *
 * 【作用】写操作发生时,对目标上的每把谓词锁做"冲入"结算:
 * - 锁持有者 = 本事务:若本事务不在子事务中且目标是元组级,
 *   记下这把 SIREAD 锁,待循环结束后删除(见英文注释:对本
 *   事务获得写锁的元组,SIREAD 锁冗余;子事务中不能删,因为
 *   子事务回滚会失去顶层保护);
 * - 其他持有者:若其未 doomed 且仍"有趣"(未提交,或提交但
 *   其 finishedBefore 晚于本快照 xmin),且边尚不存在,则
 *   FlagRWConflict(持有者, 本事务)——同时该检查内部会做危险
 *   结构判定。先共享锁快速遍历,需要加边时升级排他并复查
 *   (避免与别人并发加边冲突)。
 *
 * 【设计思想】"读锁持有者 → 写者"的边是冲入边;加边前必须
 * 用 GetTransactionSnapshot()->xmin 与 finishedBefore 过滤掉
 * "提交早于本快照"的持有者(那样读已可见我们的写,无冲突)。
 * 删除自己的元组 SIREAD 锁需要升级分区锁为排他,故延迟到
 * 循环后统一处理(含 RemoveTargetIfNoLongerUsed 与本地表清理)。
 *
 * 【参数】targettag —— 本次写涉及的目标(元组/页/关系)。
 * 【返回值】无。
 */
static void
CheckTargetForConflictsIn(PREDICATELOCKTARGETTAG *targettag)
{
	uint32		targettaghash;
	LWLock	   *partitionLock;
	PREDICATELOCKTARGET *target;
	PREDICATELOCK *mypredlock = NULL;
	PREDICATELOCKTAG mypredlocktag;
	dlist_mutable_iter iter;

	Assert(MySerializableXact != InvalidSerializableXact);

	/*
	 * The same hash and LW lock apply to the lock target and the lock itself.
	 */
	targettaghash = PredicateLockTargetTagHashCode(targettag);
	partitionLock = PredicateLockHashPartitionLock(targettaghash);
	LWLockAcquire(partitionLock, LW_SHARED);
	target = (PREDICATELOCKTARGET *)
		hash_search_with_hash_value(PredicateLockTargetHash,
									targettag, targettaghash,
									HASH_FIND, NULL);
	if (!target)
	{
		/* Nothing has this target locked; we're done here. */
		LWLockRelease(partitionLock);
		return;
	}

	/*
	 * Each lock for an overlapping transaction represents a conflict: a
	 * rw-dependency in to this transaction.
	 */
	LWLockAcquire(SerializableXactHashLock, LW_SHARED);

	dlist_foreach_modify(iter, &target->predicateLocks)
	{
		PREDICATELOCK *predlock =
			dlist_container(PREDICATELOCK, targetLink, iter.cur);
		SERIALIZABLEXACT *sxact = predlock->tag.myXact;

		if (sxact == MySerializableXact)
		{
			/*
			 * If we're getting a write lock on a tuple, we don't need a
			 * predicate (SIREAD) lock on the same tuple. We can safely remove
			 * our SIREAD lock, but we'll defer doing so until after the loop
			 * because that requires upgrading to an exclusive partition lock.
			 *
			 * We can't use this optimization within a subtransaction because
			 * the subtransaction could roll back, and we would be left
			 * without any lock at the top level.
			 */
			if (!IsSubTransaction()
				&& GET_PREDICATELOCKTARGETTAG_OFFSET(*targettag))
			{
				mypredlock = predlock;
				mypredlocktag = predlock->tag;
			}
		}
		else if (!SxactIsDoomed(sxact)
				 && (!SxactIsCommitted(sxact)
					 || TransactionIdPrecedes(GetTransactionSnapshot()->xmin,
											  sxact->finishedBefore))
				 && !RWConflictExists(sxact, MySerializableXact))
		{
			LWLockRelease(SerializableXactHashLock);
			LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

			/*
			 * Re-check after getting exclusive lock because the other
			 * transaction may have flagged a conflict.
			 */
			if (!SxactIsDoomed(sxact)
				&& (!SxactIsCommitted(sxact)
					|| TransactionIdPrecedes(GetTransactionSnapshot()->xmin,
											 sxact->finishedBefore))
				&& !RWConflictExists(sxact, MySerializableXact))
			{
				FlagRWConflict(sxact, MySerializableXact);
			}

			LWLockRelease(SerializableXactHashLock);
			LWLockAcquire(SerializableXactHashLock, LW_SHARED);
		}
	}
	LWLockRelease(SerializableXactHashLock);
	LWLockRelease(partitionLock);

	/*
	 * If we found one of our own SIREAD locks to remove, remove it now.
	 *
	 * At this point our transaction already has a RowExclusiveLock on the
	 * relation, so we are OK to drop the predicate lock on the tuple, if
	 * found, without fearing that another write against the tuple will occur
	 * before the MVCC information makes it to the buffer.
	 */
	if (mypredlock != NULL)
	{
		uint32		predlockhashcode;
		PREDICATELOCK *rmpredlock;

		LWLockAcquire(SerializablePredicateListLock, LW_SHARED);
		if (IsInParallelMode())
			LWLockAcquire(&MySerializableXact->perXactPredicateListLock, LW_EXCLUSIVE);
		LWLockAcquire(partitionLock, LW_EXCLUSIVE);
		LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

		/*
		 * Remove the predicate lock from shared memory, if it wasn't removed
		 * while the locks were released.  One way that could happen is from
		 * autovacuum cleaning up an index.
		 */
		predlockhashcode = PredicateLockHashCodeFromTargetHashCode
			(&mypredlocktag, targettaghash);
		rmpredlock = (PREDICATELOCK *)
			hash_search_with_hash_value(PredicateLockHash,
										&mypredlocktag,
										predlockhashcode,
										HASH_FIND, NULL);
		if (rmpredlock != NULL)
		{
			Assert(rmpredlock == mypredlock);

			dlist_delete(&(mypredlock->targetLink));
			dlist_delete(&(mypredlock->xactLink));

			rmpredlock = (PREDICATELOCK *)
				hash_search_with_hash_value(PredicateLockHash,
											&mypredlocktag,
											predlockhashcode,
											HASH_REMOVE, NULL);
			Assert(rmpredlock == mypredlock);

			RemoveTargetIfNoLongerUsed(target, targettaghash);
		}

		LWLockRelease(SerializableXactHashLock);
		LWLockRelease(partitionLock);
		if (IsInParallelMode())
			LWLockRelease(&MySerializableXact->perXactPredicateListLock);
		LWLockRelease(SerializablePredicateListLock);

		if (rmpredlock != NULL)
		{
			/*
			 * Remove entry in local lock table if it exists. It's OK if it
			 * doesn't exist; that means the lock was transferred to a new
			 * target by a different backend.
			 */
			hash_search_with_hash_value(LocalPredicateLockHash,
										targettag, targettaghash,
										HASH_REMOVE, NULL);

			DecrementParentLocks(targettag);
		}
	}
}

/*
 * CheckForSerializableConflictIn
 *		We are writing the given tuple.  If that indicates a rw-conflict
 *		in from another serializable transaction, take appropriate action.
 *
 * Skip checking for any granularity for which a parameter is missing.
 *
 * A tuple update or delete is in conflict if we have a predicate lock
 * against the relation or page in which the tuple exists, or against the
 * tuple itself.
 */
/*
 * CheckForSerializableConflictIn
 *      (中文)写元组时的冲入检查(建立 读者→写者 的 rw 边)
 *
 * 【作用】堆元组的 UPDATE/DELETE(以及部分插入)前由 heapam 调用:
 * 本事务即将写入,先检查元组/页/关系三级目标上有没有其他事务
 * 的谓词锁——有则产生"持锁者 → 本事务"的冲入冲突(必要时
 * 中止)。同时置 MyXactDidWrite = true,并把检查按"最细到最粗"
 * 的顺序进行(元组 → 页 → 关系,参数可为空表示跳过某级)。
 *
 * 【设计思想】
 * - 顺序很重要:粒度提升发生在加粗锁之后、删细锁之前,按
 *   细→粗检查保证不会漏掉任何一档(英文注释);
 * - 各目标可能落在不同分区,无法一次持锁检查全部,故逐级
 *   单独获取分区锁;
 * - 事务已被判死(DOOMED)时立即报 40001,让失败尽早暴露。
 *
 * 【参数】
 *   relation —— 写操作的关系;
 *   tid —— 元组标识(非 NULL 则检查元组级);
 *   blkno —— 页号(有效则检查页级);关系级总是检查。
 * 【返回值】无(可能抛 40001)。
 */
void
CheckForSerializableConflictIn(Relation relation, const ItemPointerData *tid, BlockNumber blkno)
{
	PREDICATELOCKTARGETTAG targettag;

	if (!SerializationNeededForWrite(relation))
		return;

	/* Check if someone else has already decided that we need to die */
	if (SxactIsDoomed(MySerializableXact))
		ereport(ERROR,
				(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
				 errmsg("could not serialize access due to read/write dependencies among transactions"),
				 errdetail_internal("Reason code: Canceled on identification as a pivot, during conflict in checking."),
				 errhint("The transaction might succeed if retried.")));

	/*
	 * We're doing a write which might cause rw-conflicts now or later.
	 * Memorize that fact.
	 */
	MyXactDidWrite = true;

	/*
	 * It is important that we check for locks from the finest granularity to
	 * the coarsest granularity, so that granularity promotion doesn't cause
	 * us to miss a lock.  The new (coarser) lock will be acquired before the
	 * old (finer) locks are released.
	 *
	 * It is not possible to take and hold a lock across the checks for all
	 * granularities because each target could be in a separate partition.
	 */
	if (tid != NULL)
	{
		SET_PREDICATELOCKTARGETTAG_TUPLE(targettag,
										 relation->rd_locator.dbOid,
										 relation->rd_id,
										 ItemPointerGetBlockNumber(tid),
										 ItemPointerGetOffsetNumber(tid));
		CheckTargetForConflictsIn(&targettag);
	}

	if (blkno != InvalidBlockNumber)
	{
		SET_PREDICATELOCKTARGETTAG_PAGE(targettag,
										relation->rd_locator.dbOid,
										relation->rd_id,
										blkno);
		CheckTargetForConflictsIn(&targettag);
	}

	SET_PREDICATELOCKTARGETTAG_RELATION(targettag,
										relation->rd_locator.dbOid,
										relation->rd_id);
	CheckTargetForConflictsIn(&targettag);
}

/*
 * CheckTableForSerializableConflictIn
 *		The entire table is going through a DDL-style logical mass delete
 *		like TRUNCATE or DROP TABLE.  If that causes a rw-conflict in from
 *		another serializable transaction, take appropriate action.
 *
 * While these operations do not operate entirely within the bounds of
 * snapshot isolation, they can occur inside a serializable transaction, and
 * will logically occur after any reads which saw rows which were destroyed
 * by these operations, so we do what we can to serialize properly under
 * SSI.
 *
 * The relation passed in must be a heap relation. Any predicate lock of any
 * granularity on the heap will cause a rw-conflict in to this transaction.
 * Predicate locks on indexes do not matter because they only exist to guard
 * against conflicting inserts into the index, and this is a mass *delete*.
 * When a table is truncated or dropped, the index will also be truncated
 * or dropped, and we'll deal with locks on the index when that happens.
 *
 * Dropping or truncating a table also needs to drop any existing predicate
 * locks on heap tuples or pages, because they're about to go away. This
 * should be done before altering the predicate locks because the transaction
 * could be rolled back because of a conflict, in which case the lock changes
 * are not needed. (At the moment, we don't actually bother to drop the
 * existing locks on a dropped or truncated table at the moment. That might
 * lead to some false positives, but it doesn't seem worth the trouble.)
 */
/*
 * CheckTableForSerializableConflictIn
 *      (中文)整表 DDL 删除(TRUNCATE/DROP)时的冲入检查
 *
 * 【作用】TRUNCATE、DROP TABLE 等"逻辑上的批量删除"操作由
 * 执行器调用:扫描目标哈希表,对该堆关系(任意粒度)上的全部
 * 谓词锁建立"持锁者 → 本事务"的冲入边(去重后
 * FlagRWConflict)。索引上的锁不参与:索引锁只防插入冲突,而
 * 这是批量删除(见英文注释)。
 *
 * 【设计思想】这些操作虽不严格处于快照隔离内,但发生在
 * 可串行化事务中,逻辑上晚于先前读到被删行的查询,必须纳入
 * SSI 图。调用者持有关系上的 ACCESS EXCLUSIVE 锁,故无锁检查
 * SxactGlobalXmin 也安全;需一次性拿齐全部分区锁(共享)+
 * SerializablePredicateListLock(排他)+ SerializableXactHashLock
 * (排他)后整体扫描,代价高昂但仅限昂贵 DDL。
 *
 * 【参数】relation —— 堆关系(断言非索引)。
 * 【返回值】无(可能抛 40001)。
 */
void
CheckTableForSerializableConflictIn(Relation relation)
{
	HASH_SEQ_STATUS seqstat;
	PREDICATELOCKTARGET *target;
	Oid			dbId;
	Oid			heapId;
	int			i;

	/*
	 * Bail out quickly if there are no serializable transactions running.
	 * It's safe to check this without taking locks because the caller is
	 * holding an ACCESS EXCLUSIVE lock on the relation.  No new locks which
	 * would matter here can be acquired while that is held.
	 */
	if (!TransactionIdIsValid(PredXact->SxactGlobalXmin))
		return;

	if (!SerializationNeededForWrite(relation))
		return;

	/*
	 * We're doing a write which might cause rw-conflicts now or later.
	 * Memorize that fact.
	 */
	MyXactDidWrite = true;

	Assert(relation->rd_index == NULL); /* not an index relation */

	dbId = relation->rd_locator.dbOid;
	heapId = relation->rd_id;

	LWLockAcquire(SerializablePredicateListLock, LW_EXCLUSIVE);
	for (i = 0; i < NUM_PREDICATELOCK_PARTITIONS; i++)
		LWLockAcquire(PredicateLockHashPartitionLockByIndex(i), LW_SHARED);
	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	/* Scan through target list */
	hash_seq_init(&seqstat, PredicateLockTargetHash);

	while ((target = (PREDICATELOCKTARGET *) hash_seq_search(&seqstat)))
	{
		dlist_mutable_iter iter;

		/*
		 * Check whether this is a target which needs attention.
		 */
		if (GET_PREDICATELOCKTARGETTAG_RELATION(target->tag) != heapId)
			continue;			/* wrong relation id */
		if (GET_PREDICATELOCKTARGETTAG_DB(target->tag) != dbId)
			continue;			/* wrong database id */

		/*
		 * Loop through locks for this target and flag conflicts.
		 */
		dlist_foreach_modify(iter, &target->predicateLocks)
		{
			PREDICATELOCK *predlock =
				dlist_container(PREDICATELOCK, targetLink, iter.cur);

			if (predlock->tag.myXact != MySerializableXact
				&& !RWConflictExists(predlock->tag.myXact, MySerializableXact))
			{
				FlagRWConflict(predlock->tag.myXact, MySerializableXact);
			}
		}
	}

	/* Release locks in reverse order */
	LWLockRelease(SerializableXactHashLock);
	for (i = NUM_PREDICATELOCK_PARTITIONS - 1; i >= 0; i--)
		LWLockRelease(PredicateLockHashPartitionLockByIndex(i));
	LWLockRelease(SerializablePredicateListLock);
}


/*
 * Flag a rw-dependency between two serializable transactions.
 *
 * The caller is responsible for ensuring that we have a LW lock on
 * the transaction hash table.
 */
/*
 * FlagRWConflict
 *      (中文)登记一条 读者→写者 的 rw 冲突边(含危险结构检查)
 *
 * 【作用】所有冲突登记点的统一入口:先调用
 * OnConflict_CheckForSerializationFailure 判断新边是否补全了
 * 危险结构(是则中止合适的事务);然后真正登记——任一端是
 * OldCommittedSxact(被摘要的老事务)时只置 SUMMARY_CONFLICT_IN/
 * OUT 标志,否则 SetRWConflict 建立实体边。
 *
 * 【设计思想】把"检查 + 登记"绑在一起,保证不会出现"已构成
 * 危险结构却没中止"的窗口;摘要端用标志位替代实体边(老事务
 * 对象已回收,无法挂链表)。
 *
 * 【参数】
 *   reader —— 冲突起点(读者);
 *   writer —— 冲突终点(写者)。
 * 【返回值】无(可能抛 40001)。调用者须持有
 * SerializableXactHashLock。
 */
static void
FlagRWConflict(SERIALIZABLEXACT *reader, SERIALIZABLEXACT *writer)
{
	Assert(reader != writer);

	/* First, see if this conflict causes failure. */
	OnConflict_CheckForSerializationFailure(reader, writer);

	/* Actually do the conflict flagging. */
	if (reader == OldCommittedSxact)
		writer->flags |= SXACT_FLAG_SUMMARY_CONFLICT_IN;
	else if (writer == OldCommittedSxact)
		reader->flags |= SXACT_FLAG_SUMMARY_CONFLICT_OUT;
	else
		SetRWConflict(reader, writer);
}

/*----------------------------------------------------------------------------
 * We are about to add a RW-edge to the dependency graph - check that we don't
 * introduce a dangerous structure by doing so, and abort one of the
 * transactions if so.
 *
 * A serialization failure can only occur if there is a dangerous structure
 * in the dependency graph:
 *
 *		Tin ------> Tpivot ------> Tout
 *			  rw			 rw
 *
 * Furthermore, Tout must commit first.
 *
 * One more optimization is that if Tin is declared READ ONLY (or commits
 * without writing), we can only have a problem if Tout committed before Tin
 * acquired its snapshot.
 *----------------------------------------------------------------------------
 */
/*
 * OnConflict_CheckForSerializationFailure
 *      (中文)新 rw 边加入依赖图前的危险结构检查(SSI 的核心判定)
 *
 * 【作用】在登记"reader → writer"边之前检查:新边是否使图中
 * 出现危险结构 T_in →rw T_pivot →rw T_out(且 T_out 先提交)?
 * 按三种构图可能逐一排查(细节见函数内英文注释的三段):
 * 1. writer 已提交且带冲突出边(writer 是枢轴,新边是"入"边):
 *    R → W → T2,T2 已提交 → 必失败(此时只能中止 reader);
 * 2. writer 带对已提交/已 prepared 事务的冲突出边(writer 成枢轴):
 *    检查 reader 与 writer 的提交时机是否都晚于 T2(任一方早于
 *    T2 则无异常),只读 reader 看其快照是否晚于 T2;
 * 3. reader 成枢轴(新边是"出"边):writer 已 prepared,检查
 *    reader 的冲入边来源 T0 是否晚于 writer 提交(或 T0 只读且
 *    与 writer 重叠)→ 失败。
 *
 * 【判定失败后】选择牺牲者:
 * - writer 是自己:直接抛 40001(本事务即枢轴);
 * - writer 已 prepared:不能再中止它,只能中止自己(reader);
 * - 其余:把 writer 标 DOOMED,由它自己在提交/下次检查时中止
 *   (宁可中止枢轴,保证重试有进展,见 PreCommit 注释)。
 *
 * 【设计思想】危险结构 = 依赖环的"充分可疑子图"(README-SSI);
 * 两条优化(只对 T_out 先提交的结构中止、只读 T_in 需 T_out 早于
 * 其快照)大幅降低误报。函数必须在 SerializableXactHashLock
 * 下调用(提交序号/标志的可见性)。
 *
 * 【参数】
 *   reader —— 新边的读者端;
 *   writer —— 新边的写者端。
 * 【返回值】无(失败时抛 40001 或 DOOM writer)。
 */
static void
OnConflict_CheckForSerializationFailure(const SERIALIZABLEXACT *reader,
										SERIALIZABLEXACT *writer)
{
	bool		failure;

	Assert(LWLockHeldByMe(SerializableXactHashLock));

	failure = false;

	/*------------------------------------------------------------------------
	 * Check for already-committed writer with rw-conflict out flagged
	 * (conflict-flag on W means that T2 committed before W):
	 *
	 *		R ------> W ------> T2
	 *			rw		  rw
	 *
	 * That is a dangerous structure, so we must abort. (Since the writer
	 * has already committed, we must be the reader)
	 *------------------------------------------------------------------------
	 */
	if (SxactIsCommitted(writer)
		&& (SxactHasConflictOut(writer) || SxactHasSummaryConflictOut(writer)))
		failure = true;

	/*------------------------------------------------------------------------
	 * Check whether the writer has become a pivot with an out-conflict
	 * committed transaction (T2), and T2 committed first:
	 *
	 *		R ------> W ------> T2
	 *			rw		  rw
	 *
	 * Because T2 must've committed first, there is no anomaly if:
	 * - the reader committed before T2
	 * - the writer committed before T2
	 * - the reader is a READ ONLY transaction and the reader was concurrent
	 *	 with T2 (= reader acquired its snapshot before T2 committed)
	 *
	 * We also handle the case that T2 is prepared but not yet committed
	 * here. In that case T2 has already checked for conflicts, so if it
	 * commits first, making the above conflict real, it's too late for it
	 * to abort.
	 *------------------------------------------------------------------------
	 */
	if (!failure && SxactHasSummaryConflictOut(writer))
		failure = true;
	else if (!failure)
	{
		dlist_iter	iter;

		dlist_foreach(iter, &writer->outConflicts)
		{
			RWConflict	conflict =
				dlist_container(RWConflictData, outLink, iter.cur);
			SERIALIZABLEXACT *t2 = conflict->sxactIn;

			if (SxactIsPrepared(t2)
				&& (!SxactIsCommitted(reader)
					|| t2->prepareSeqNo <= reader->commitSeqNo)
				&& (!SxactIsCommitted(writer)
					|| t2->prepareSeqNo <= writer->commitSeqNo)
				&& (!SxactIsReadOnly(reader)
					|| t2->prepareSeqNo <= reader->SeqNo.lastCommitBeforeSnapshot))
			{
				failure = true;
				break;
			}
		}
	}

	/*------------------------------------------------------------------------
	 * Check whether the reader has become a pivot with a writer
	 * that's committed (or prepared):
	 *
	 *		T0 ------> R ------> W
	 *			 rw		   rw
	 *
	 * Because W must've committed first for an anomaly to occur, there is no
	 * anomaly if:
	 * - T0 committed before the writer
	 * - T0 is READ ONLY, and overlaps the writer
	 *------------------------------------------------------------------------
	 */
	if (!failure && SxactIsPrepared(writer) && !SxactIsReadOnly(reader))
	{
		if (SxactHasSummaryConflictIn(reader))
		{
			failure = true;
		}
		else
		{
			dlist_iter	iter;

			/*
			 * The unconstify is needed as we have no const version of
			 * dlist_foreach().
			 */
			dlist_foreach(iter, &unconstify(SERIALIZABLEXACT *, reader)->inConflicts)
			{
				const RWConflict conflict =
					dlist_container(RWConflictData, inLink, iter.cur);
				const SERIALIZABLEXACT *t0 = conflict->sxactOut;

				if (!SxactIsDoomed(t0)
					&& (!SxactIsCommitted(t0)
						|| t0->commitSeqNo >= writer->prepareSeqNo)
					&& (!SxactIsReadOnly(t0)
						|| t0->SeqNo.lastCommitBeforeSnapshot >= writer->prepareSeqNo))
				{
					failure = true;
					break;
				}
			}
		}
	}

	if (failure)
	{
		/*
		 * We have to kill a transaction to avoid a possible anomaly from
		 * occurring. If the writer is us, we can just ereport() to cause a
		 * transaction abort. Otherwise we flag the writer for termination,
		 * causing it to abort when it tries to commit. However, if the writer
		 * is a prepared transaction, already prepared, we can't abort it
		 * anymore, so we have to kill the reader instead.
		 */
		if (MySerializableXact == writer)
		{
			LWLockRelease(SerializableXactHashLock);
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("could not serialize access due to read/write dependencies among transactions"),
					 errdetail_internal("Reason code: Canceled on identification as a pivot, during write."),
					 errhint("The transaction might succeed if retried.")));
		}
		else if (SxactIsPrepared(writer))
		{
			LWLockRelease(SerializableXactHashLock);

			/* if we're not the writer, we have to be the reader */
			Assert(MySerializableXact == reader);
			ereport(ERROR,
					(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
					 errmsg("could not serialize access due to read/write dependencies among transactions"),
					 errdetail_internal("Reason code: Canceled on conflict out to pivot %u, during read.", writer->topXid),
					 errhint("The transaction might succeed if retried.")));
		}
		writer->flags |= SXACT_FLAG_DOOMED;
	}
}

/*
 * PreCommit_CheckForSerializationFailure
 *		Check for dangerous structures in a serializable transaction
 *		at commit.
 *
 * We're checking for a dangerous structure as each conflict is recorded.
 * The only way we could have a problem at commit is if this is the "out"
 * side of a pivot, and neither the "in" side nor the pivot has yet
 * committed.
 *
 * If a dangerous structure is found, the pivot (the near conflict) is
 * marked for death, because rolling back another transaction might mean
 * that we fail without ever making progress.  This transaction is
 * committing writes, so letting it commit ensures progress.  If we
 * canceled the far conflict, it might immediately fail again on retry.
 */
/*
 * PreCommit_CheckForSerializationFailure
 *      (中文)提交前的最后危险结构检查(提交门槛)
 *
 * 【作用】事务提交前的"最终判决":通常危险结构在加边时就已
 * 拦截,提交时刻唯一可能漏掉的情形是——本事务是危险结构的
 * "出边端"(T_out),而冲入端(T_in)与枢轴都还没提交(边登记时
 * 无法判定)。因此遍历本事务的冲入边,对每个未提交、未判死的
 * 冲入来源检查其冲入边:若发现"本事务"或另一个未提交、非
 * 只读、未判死的事务,即构成完整危险结构 → 中止枢轴
 * (冲入来源);枢轴已 prepared 则中止自己。通过后分配
 * prepareSeqNo 并置 PREPARED 标志——从这一刻起本事务不可再
 * 被中止。
 *
 * 【设计思想】PREPARED 是"提交不可撤回"的分界(见英文注释),
 * 之后的任何冲突检查看到 prepared 事务都只能自损或 DOOM 对方。
 * 中止枢轴而非远端事务,保证重试立即成功(远端中止会立刻
 * 在重试中再失败)。被 DOOMED 时直接报错(除非是部分释放的
 * 只读优化路径)。
 *
 * 【参数】无。【返回值】无(可能抛 40001)。
 */
void
PreCommit_CheckForSerializationFailure(void)
{
	dlist_iter	near_iter;

	if (MySerializableXact == InvalidSerializableXact)
		return;

	Assert(IsolationIsSerializable());

	LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);

	/*
	 * Check if someone else has already decided that we need to die.  Since
	 * we set our own DOOMED flag when partially releasing, ignore in that
	 * case.
	 */
	if (SxactIsDoomed(MySerializableXact) &&
		!SxactIsPartiallyReleased(MySerializableXact))
	{
		LWLockRelease(SerializableXactHashLock);
		ereport(ERROR,
				(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
				 errmsg("could not serialize access due to read/write dependencies among transactions"),
				 errdetail_internal("Reason code: Canceled on identification as a pivot, during commit attempt."),
				 errhint("The transaction might succeed if retried.")));
	}

	dlist_foreach(near_iter, &MySerializableXact->inConflicts)
	{
		RWConflict	nearConflict =
			dlist_container(RWConflictData, inLink, near_iter.cur);

		if (!SxactIsCommitted(nearConflict->sxactOut)
			&& !SxactIsDoomed(nearConflict->sxactOut))
		{
			dlist_iter	far_iter;

			dlist_foreach(far_iter, &nearConflict->sxactOut->inConflicts)
			{
				RWConflict	farConflict =
					dlist_container(RWConflictData, inLink, far_iter.cur);

				if (farConflict->sxactOut == MySerializableXact
					|| (!SxactIsCommitted(farConflict->sxactOut)
						&& !SxactIsReadOnly(farConflict->sxactOut)
						&& !SxactIsDoomed(farConflict->sxactOut)))
				{
					/*
					 * Normally, we kill the pivot transaction to make sure we
					 * make progress if the failing transaction is retried.
					 * However, we can't kill it if it's already prepared, so
					 * in that case we commit suicide instead.
					 */
					if (SxactIsPrepared(nearConflict->sxactOut))
					{
						LWLockRelease(SerializableXactHashLock);
						ereport(ERROR,
								(errcode(ERRCODE_T_R_SERIALIZATION_FAILURE),
								 errmsg("could not serialize access due to read/write dependencies among transactions"),
								 errdetail_internal("Reason code: Canceled on commit attempt with conflict in from prepared pivot."),
								 errhint("The transaction might succeed if retried.")));
					}
					nearConflict->sxactOut->flags |= SXACT_FLAG_DOOMED;
					break;
				}
			}
		}
	}

	MySerializableXact->prepareSeqNo = ++(PredXact->LastSxactCommitSeqNo);
	MySerializableXact->flags |= SXACT_FLAG_PREPARED;

	LWLockRelease(SerializableXactHashLock);
}

/*------------------------------------------------------------------------*/

/*
 * Two-phase commit support
 */

/*
 * AtPrepare_Locks
 *		Do the preparatory work for a PREPARE: make 2PC state file
 *		records for all predicate locks currently held.
 */
/*
 * AtPrepare_PredicateLocks
 *      (中文)PREPARE 时把谓词锁信息写入 2PC 状态文件
 *
 * 【作用】PREPARE TRANSACTION 时由 twophase 层调用:为当前事务
 * 生成一条事务记录(记录 type = XACT,xmin 与 flags)和每条
 * 谓词锁一条记录(记录目标 tag),全部经 RegisterTwoPhaseRecord
 * 写入 2PC 状态文件。非可串行化事务直接返回。
 *
 * 【设计思想】冲突出边链表不写进状态文件(见英文注释:prepare
 * 后新冲突仍可能加入,恢复时做保守假设即可)。锁列表取自共享
 * 事务的 predicateLocks 而非本地表(本地表可能失真)。prepare
 * 期间不会有并行 worker 运行,故无需 perXactPredicateListLock。
 *
 * 【参数】无。【返回值】无。
 */
void
AtPrepare_PredicateLocks(void)
{
	SERIALIZABLEXACT *sxact;
	TwoPhasePredicateRecord record;
	TwoPhasePredicateXactRecord *xactRecord;
	TwoPhasePredicateLockRecord *lockRecord;
	dlist_iter	iter;

	sxact = MySerializableXact;
	xactRecord = &(record.data.xactRecord);
	lockRecord = &(record.data.lockRecord);

	if (MySerializableXact == InvalidSerializableXact)
		return;

	/* Generate an xact record for our SERIALIZABLEXACT */
	record.type = TWOPHASEPREDICATERECORD_XACT;
	xactRecord->xmin = MySerializableXact->xmin;
	xactRecord->flags = MySerializableXact->flags;

	/*
	 * Note that we don't include the list of conflicts in our out in the
	 * statefile, because new conflicts can be added even after the
	 * transaction prepares. We'll just make a conservative assumption during
	 * recovery instead.
	 */

	RegisterTwoPhaseRecord(TWOPHASE_RM_PREDICATELOCK_ID, 0,
						   &record, sizeof(record));

	/*
	 * Generate a lock record for each lock.
	 *
	 * To do this, we need to walk the predicate lock list in our sxact rather
	 * than using the local predicate lock table because the latter is not
	 * guaranteed to be accurate.
	 */
	LWLockAcquire(SerializablePredicateListLock, LW_SHARED);

	/*
	 * No need to take sxact->perXactPredicateListLock in parallel mode
	 * because there cannot be any parallel workers running while we are
	 * preparing a transaction.
	 */
	Assert(!IsParallelWorker() && !ParallelContextActive());

	dlist_foreach(iter, &sxact->predicateLocks)
	{
		PREDICATELOCK *predlock =
			dlist_container(PREDICATELOCK, xactLink, iter.cur);

		record.type = TWOPHASEPREDICATERECORD_LOCK;
		lockRecord->target = predlock->tag.myTarget->tag;

		RegisterTwoPhaseRecord(TWOPHASE_RM_PREDICATELOCK_ID, 0,
							   &record, sizeof(record));
	}

	LWLockRelease(SerializablePredicateListLock);
}

/*
 * PostPrepare_Locks
 *		Clean up after successful PREPARE. Unlike the non-predicate
 *		lock manager, we do not need to transfer locks to a dummy
 *		PGPROC because our SERIALIZABLEXACT will stay around
 *		anyway. We only need to clean up our local state.
 */
/*
 * PostPrepare_PredicateLocks
 *      (中文)PREPARE 成功后的本地状态清理
 *
 * 【作用】PREPARE 成功后由 twophase 层调用:与普通锁管理器
 * (PostPrepare_Locks 把锁转给虚拟 PGPROC)不同,谓词锁的
 * SERIALIZABLEXACT 本身就留在共享内存中,无需转移;只需清除
 * 本后端的本地状态——置空 pid/pgprocno(事务已脱离进程,苏醒
 * 后经 SerializableXidHash 定位)、销毁本地锁表、重置
 * MySerializableXact 与 MyXactDidWrite。
 *
 * 【设计思想】prepared 事务仍带着 PREPARED 标志活在共享内存,
 * 后续 COMMIT/ROLLBACK PREPARED 走 PredicateLockTwoPhaseFinish
 * 复用同一对象。恢复(recovery)时由 predicatelock_twophase_recover
 * 重建。
 *
 * 【参数】fxid —— prepared 事务的完整事务号(本函数仅用于
 * 断言/标识,不使用其值)。【返回值】无。
 */
void
PostPrepare_PredicateLocks(FullTransactionId fxid)
{
	if (MySerializableXact == InvalidSerializableXact)
		return;

	Assert(SxactIsPrepared(MySerializableXact));

	MySerializableXact->pid = 0;
	MySerializableXact->pgprocno = INVALID_PROC_NUMBER;

	hash_destroy(LocalPredicateLockHash);
	LocalPredicateLockHash = NULL;

	MySerializableXact = InvalidSerializableXact;
	MyXactDidWrite = false;
}

/*
 * PredicateLockTwoPhaseFinish
 *		Release a prepared transaction's predicate locks once it
 *		commits or aborts.
 */
/*
 * PredicateLockTwoPhaseFinish
 *      (中文)prepared 事务提交/回滚时释放其谓词锁
 *
 * 【作用】COMMIT PREPARED / ROLLBACK PREPARED 时由 twophase 层
 * 调用:按 xid 找到 SERIALIZABLEXID → 事务对象,临时借用
 * MySerializableXact 槽位(该进程此刻本身无活动可串行化事务)
 * 并置 MyXactDidWrite = true(保守假设,使提交结算走可写路径),
 * 然后复用 ReleasePredicateLocks 完成完整的提交/回滚处理。
 *
 * 【设计思想】prepared 事务与普通事务共用同一套结束逻辑,包括
 * 危险结构结算、Finished 链表挂接与冲突清理;恢复的 prepared
 * 事务还可能带 SUMMARY 标志,同样在此结算。
 *
 * 【参数】
 *   fxid —— prepared 事务的完整事务号;
 *   isCommit —— true = COMMIT PREPARED;false = ROLLBACK PREPARED。
 * 【返回值】无(可能抛 40001,使 COMMIT PREPARED 失败)。
 */
void
PredicateLockTwoPhaseFinish(FullTransactionId fxid, bool isCommit)
{
	SERIALIZABLEXID *sxid;
	SERIALIZABLEXIDTAG sxidtag;

	sxidtag.xid = XidFromFullTransactionId(fxid);

	LWLockAcquire(SerializableXactHashLock, LW_SHARED);
	sxid = (SERIALIZABLEXID *)
		hash_search(SerializableXidHash, &sxidtag, HASH_FIND, NULL);
	LWLockRelease(SerializableXactHashLock);

	/* xid will not be found if it wasn't a serializable transaction */
	if (sxid == NULL)
		return;

	/* Release its locks */
	MySerializableXact = sxid->myXact;
	MyXactDidWrite = true;		/* conservatively assume that we wrote
								 * something */
	ReleasePredicateLocks(isCommit, false);
}

/*
 * Re-acquire a predicate lock belonging to a transaction that was prepared.
 */
/*
 * predicatelock_twophase_recover
 *      (中文)recovery 时重放 2PC 状态文件,重建 prepared 事务的谓词锁
 *
 * 【作用】崩溃恢复期间由 twophase rmgr 逐条重放本模块的状态
 * 文件记录:type = XACT 的记录重建 SERIALIZABLEXACT(从空闲池
 * 取槽,置 vxid = 无效进程号/xid、pid = 0、PREPARED 标志与恢复
 * 专用提交序号 RecoverySerCommitSeqNo,并保守地同时置
 * SUMMARY_CONFLICT_IN/OUT——不知道原冲突细节,只能按最坏
 * 情况假设,见英文注释;同时登记 xid 并维护 SxactGlobalXmin,
 * 允许其暂时倒退,因为恢复期没有事务提交);type = LOCK 的记录
 * 重建 PREDICATELOCK 锁条目。
 *
 * 【设计思想】恢复期不允许新事务提交,SLRU 为空,所以 xmin
 * 倒退无碍(见 SerialSetActiveSerXmin 的 RecoveryInProgress 分支)。
 * 重建顺序依赖:锁记录必须晚于其事务记录(XACT 记录先写)。
 *
 * 【参数】
 *   fxid —— prepared 事务完整事务号;
 *   info —— 记录类型信息(未用);
 *   recdata —— 记录内容(TwoPhasePredicateRecord);
 *   len —— 记录长度(断言为 sizeof(TwoPhasePredicateRecord))。
 * 【返回值】无。
 */
void
predicatelock_twophase_recover(FullTransactionId fxid, uint16 info,
							   void *recdata, uint32 len)
{
	TwoPhasePredicateRecord *record;
	TransactionId xid = XidFromFullTransactionId(fxid);

	Assert(len == sizeof(TwoPhasePredicateRecord));

	record = (TwoPhasePredicateRecord *) recdata;

	Assert((record->type == TWOPHASEPREDICATERECORD_XACT) ||
		   (record->type == TWOPHASEPREDICATERECORD_LOCK));

	if (record->type == TWOPHASEPREDICATERECORD_XACT)
	{
		/* Per-transaction record. Set up a SERIALIZABLEXACT. */
		TwoPhasePredicateXactRecord *xactRecord;
		SERIALIZABLEXACT *sxact;
		SERIALIZABLEXID *sxid;
		SERIALIZABLEXIDTAG sxidtag;
		bool		found;

		xactRecord = (TwoPhasePredicateXactRecord *) &record->data.xactRecord;

		LWLockAcquire(SerializableXactHashLock, LW_EXCLUSIVE);
		sxact = CreatePredXact();
		if (!sxact)
			ereport(ERROR,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of shared memory")));

		/* vxid for a prepared xact is INVALID_PROC_NUMBER/xid; no pid */
		sxact->vxid.procNumber = INVALID_PROC_NUMBER;
		sxact->vxid.localTransactionId = (LocalTransactionId) xid;
		sxact->pid = 0;
		sxact->pgprocno = INVALID_PROC_NUMBER;

		/* a prepared xact hasn't committed yet */
		sxact->prepareSeqNo = RecoverySerCommitSeqNo;
		sxact->commitSeqNo = InvalidSerCommitSeqNo;
		sxact->finishedBefore = InvalidTransactionId;

		sxact->SeqNo.lastCommitBeforeSnapshot = RecoverySerCommitSeqNo;

		/*
		 * Don't need to track this; no transactions running at the time the
		 * recovered xact started are still active, except possibly other
		 * prepared xacts and we don't care whether those are RO_SAFE or not.
		 */
		dlist_init(&(sxact->possibleUnsafeConflicts));

		dlist_init(&(sxact->predicateLocks));
		dlist_node_init(&sxact->finishedLink);

		sxact->topXid = xid;
		sxact->xmin = xactRecord->xmin;
		sxact->flags = xactRecord->flags;
		Assert(SxactIsPrepared(sxact));
		if (!SxactIsReadOnly(sxact))
		{
			++(PredXact->WritableSxactCount);
			Assert(PredXact->WritableSxactCount <=
				   (MaxBackends + max_prepared_xacts));
		}

		/*
		 * We don't know whether the transaction had any conflicts or not, so
		 * we'll conservatively assume that it had both a conflict in and a
		 * conflict out, and represent that with the summary conflict flags.
		 */
		dlist_init(&(sxact->outConflicts));
		dlist_init(&(sxact->inConflicts));
		sxact->flags |= SXACT_FLAG_SUMMARY_CONFLICT_IN;
		sxact->flags |= SXACT_FLAG_SUMMARY_CONFLICT_OUT;

		/* Register the transaction's xid */
		sxidtag.xid = xid;
		sxid = (SERIALIZABLEXID *) hash_search(SerializableXidHash,
											   &sxidtag,
											   HASH_ENTER, &found);
		Assert(sxid != NULL);
		Assert(!found);
		sxid->myXact = sxact;

		/*
		 * Update global xmin. Note that this is a special case compared to
		 * registering a normal transaction, because the global xmin might go
		 * backwards. That's OK, because until recovery is over we're not
		 * going to complete any transactions or create any non-prepared
		 * transactions, so there's no danger of throwing away.
		 */
		if ((!TransactionIdIsValid(PredXact->SxactGlobalXmin)) ||
			(TransactionIdFollows(PredXact->SxactGlobalXmin, sxact->xmin)))
		{
			PredXact->SxactGlobalXmin = sxact->xmin;
			PredXact->SxactGlobalXminCount = 1;
			SerialSetActiveSerXmin(sxact->xmin);
		}
		else if (TransactionIdEquals(sxact->xmin, PredXact->SxactGlobalXmin))
		{
			Assert(PredXact->SxactGlobalXminCount > 0);
			PredXact->SxactGlobalXminCount++;
		}

		LWLockRelease(SerializableXactHashLock);
	}
	else if (record->type == TWOPHASEPREDICATERECORD_LOCK)
	{
		/* Lock record. Recreate the PREDICATELOCK */
		TwoPhasePredicateLockRecord *lockRecord;
		SERIALIZABLEXID *sxid;
		SERIALIZABLEXACT *sxact;
		SERIALIZABLEXIDTAG sxidtag;
		uint32		targettaghash;

		lockRecord = (TwoPhasePredicateLockRecord *) &record->data.lockRecord;
		targettaghash = PredicateLockTargetTagHashCode(&lockRecord->target);

		LWLockAcquire(SerializableXactHashLock, LW_SHARED);
		sxidtag.xid = xid;
		sxid = (SERIALIZABLEXID *)
			hash_search(SerializableXidHash, &sxidtag, HASH_FIND, NULL);
		LWLockRelease(SerializableXactHashLock);

		Assert(sxid != NULL);
		sxact = sxid->myXact;
		Assert(sxact != InvalidSerializableXact);

		CreatePredicateLock(&lockRecord->target, targettaghash, sxact);
	}
}

/*
 * Prepare to share the current SERIALIZABLEXACT with parallel workers.
 * Return a handle object that can be used by AttachSerializableXact() in a
 * parallel worker.
 */
/*
 * ShareSerializableXact
 *      (中文)把当前事务对象句柄共享给并行 worker
 *
 * 【作用】并行查询启动时由 leader 调用:返回 MySerializableXact
 * 指针作为句柄,经共享内存传给 worker,供其
 * AttachSerializableXact 安装同一事务对象。非可串行化事务返回
 * NULL。
 *
 * 【设计思想】一个可串行化事务的所有 worker 必须共享同一
 * SERIALIZABLEXACT(同一 vxid、同一快照语义),谓词锁与冲突边
 * 都登记在它名下;perXactPredicateListLock 专为这种共享场景
 * 提供保护。
 *
 * 【参数】无。
 * 【返回值】SerializableXactHandle(即 SERIALIZABLEXACT 指针,
 * 可能为 NULL 表示无可共享事务)。
 */
SerializableXactHandle
ShareSerializableXact(void)
{
	return MySerializableXact;
}

/*
 * Allow parallel workers to import the leader's SERIALIZABLEXACT.
 */
/*
 * AttachSerializableXact
 *      (中文)并行 worker 安装 leader 的事务对象
 *
 * 【作用】并行 worker 启动时由 parallel.c 调用:把 leader 传来的
 * 句柄装进本进程的 MySerializableXact,并创建本地锁表。句柄为
 * NULL(leader 不在 SSI)则保持空。此后 worker 的一切谓词锁/
 * 冲突登记都作用于共享的同一事务对象。
 *
 * 【设计思想】与 SetSerializableTransactionSnapshot 的 worker
 * 快速返回呼应:快照导入时不建事务对象,由本函数统一安装;
 * worker 退出时也只做本地清理(ReleasePredicateLocks 的
 * IsParallelWorker 分支),共享对象由 leader 负责回收。
 *
 * 【参数】handle —— ShareSerializableXact 返回的句柄。
 * 【返回值】无。
 */
void
AttachSerializableXact(SerializableXactHandle handle)
{

	Assert(MySerializableXact == InvalidSerializableXact);

	MySerializableXact = (SERIALIZABLEXACT *) handle;
	if (MySerializableXact != InvalidSerializableXact)
		CreateLocalPredicateLockHash();
}
