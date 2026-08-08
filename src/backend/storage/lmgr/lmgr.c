/*-------------------------------------------------------------------------
 *
 * lmgr.c
 *	  POSTGRES lock manager code
 *
 * 【模块总览(中文)】
 * 本文件是 PostgreSQL 锁管理器"面向调用者的高级接口"层:它不直接操纵
 * 共享内存中的 LOCK/PROCLOCK 结构,而是把 lock.c 提供的原语
 * (LockAcquire/LockAcquireExtended/LockRelease/LockHeldByMe 等)按各种
 * 常见场景封装成语义清晰的函数,供关系管理(relcache)、缓冲区管理、
 * 事务管理、索引访问方法、逻辑复制等模块调用。
 *
 * 【本层承担的职责】
 * 1. LOCKTAG 构造:调用者只需给出关系 OID、页号、元组 TID、XID 等
 *    业务含义的参数,本层负责按规范用 SET_LOCKTAG_* 宏拼出唯一的
 *    锁标签(含"系统关系用 InvalidOid 作库 ID"等细节),并决定用哪个
 *    lock method(默认的 DEFAULT_LOCKMETHOD)。
 * 2. 锁的生命周期管理:区分"事务级锁"(登记到 CurrentResourceOwner,
 *    事务结束自动释放)与"会话级锁"(sessionLock = true,跨事务存活,
 *    显式解锁或后端退出时才释放);XactLockTableInsert/Delete 在事务
 *    获取/释放 XID 时被调用,保证"等待事务结束"机制有锁可等。
 * 3. 与共享失效消息(sinval)协作:拿到锁之后调用
 *    AcceptInvalidationMessages() 吸收其他会话在加锁期间发出的目录
 *    失效消息,并借助 LockAcquireExtended 返回的 LOCKACQUIRE_ALREADY_CLEAR
 *    (本事务已持同种锁,肯定没有新的失效消息)避免多余处理——
 *    "先加锁、再刷新 relcache,然后才放心使用关系"是这个模块的重要
 *    调用约定。
 * 4. 专用锁的封装:关系扩展锁(扩展文件时互斥)、页锁(索引方法用)、
 *    元组锁(堆行并发控制)、speculative insertion 锁(唯一性检查期间
 *    的临时插入)、数据库对象/共享对象锁(目录与表空间保护)、
 *    advisory 锁(用户态)、应用事务锁(逻辑复制 subscriber)。
 * 5. 等待他人结束:VXID/XID 层面的等待(WaitForLockers、
 *    XactLockTableWait 等),供 DROP 对象、序列化等场景等待所有持锁者
 *    结束。
 *
 * 注意:本文件的大多数函数是"同步阻塞"语义,另有配套的
 * Conditional* 版本返回"拿不到就立即失败"。锁的具体状态(等待队列、
 * 冲突矩阵、fast-path 等)详见 lock.c 与 storage/lmgr/README。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/storage/lmgr/lmgr.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/subtrans.h"
#include "access/xact.h"
#include "catalog/catalog.h"
#include "commands/progress.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "storage/lmgr.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "utils/inval.h"


/*
 * Per-backend counter for generating speculative insertion tokens.
 *
 * This may wrap around, but that's OK as it's only used for the short
 * duration between inserting a tuple and checking that there are no (unique)
 * constraint violations.  It's theoretically possible that a backend sees a
 * tuple that was speculatively inserted by another backend, but before it has
 * started waiting on the token, the other backend completes its insertion,
 * and then performs 2^32 unrelated insertions.  And after all that, the
 * first backend finally calls SpeculativeInsertionLockAcquire(), with the
 * intention of waiting for the first insertion to complete, but ends up
 * waiting for the latest unrelated insertion instead.  Even then, nothing
 * particularly bad happens: in the worst case they deadlock, causing one of
 * the transactions to abort.
 */
static uint32 speculativeInsertionToken = 0;
/* (中文)本后端用于生成"推测插入(speculative insertion)"令牌的计数器:
 * 每做一次推测插入就加 1,用作 SET_LOCKTAG_SPECULATIVE_INSERTION 的
 * 第二字段,以区分同一事务的多次插入。
 * 它可能回绕(2^32 次插入后回到 0,特殊处理:0 表示"无令牌",故跳过),
 * 但这是可接受的:令牌只在"插入元组 → 检查唯一性约束"的短暂窗口内
 * 使用,最坏情况下(见英文注释)可能误等另一个无关插入,结果也只是
 * 一次可能触发死锁回滚,没有正确性问题。 */

/*
 * Struct to hold context info for transaction lock waits.
 *
 * 'oper' is the operation that needs to wait for the other transaction; 'rel'
 * and 'ctid' specify the address of the tuple being waited for.
 */
typedef struct XactLockTableWaitInfo
{
	XLTW_Oper	oper;
	Relation	rel;
	const ItemPointerData *ctid;
} XactLockTableWaitInfo;

/* (中文)XactLockTableWait 的错误上下文信息结构:
 * - oper : 等待时正在执行的操作类型(XLTW_Update/Delete/Lock/... ),
 *          决定错误消息的措辞;
 * - rel / ctid : 等待涉及的那个元组所在的关系与位置。
 * 当等待事务结束的过程中出错(如锁超时/被取消)时,错误上下文回调
 * XactLockTableWaitErrorCb 用这些信息拼出"while updating tuple (...)
 * in relation ..."之类的提示。 */

static void XactLockTableWaitErrorCb(void *arg);

/*
 * RelationInitLockInfo
 *		Initializes the lock information in a relation descriptor.
 *
 *		relcache.c must call this during creation of any reldesc.
 */
/*
 * RelationInitLockInfo
 *      (中文)初始化关系描述符中的锁信息(relcache 创建 reldesc 时调用)
 *
 * 【作用】把关系的锁标识(LockRelId = {dbId, relId})填进
 * relation->rd_lockInfo,使后续的 LockRelation/UnlockRelation 等函数
 * 能直接从中取 OID,而不必每次都查 relcache。
 *
 * 【设计思想】dbId 的取值约定:系统共享关系(relisshared,如
 * pg_database、pg_tablespace)的锁用 InvalidOid 作库 ID,使锁在整个
 * 集群内全局唯一;普通关系用 MyDatabaseId。这保证了不同数据库里的
 * 同名表不会共享同一把锁,而共享目录在集群范围内互斥。
 *
 * 【参数】relation —— 正在创建的关系描述符。
 * 【返回值】无。
 */
void
RelationInitLockInfo(Relation relation)
{
	Assert(RelationIsValid(relation));
	Assert(OidIsValid(RelationGetRelid(relation)));

	relation->rd_lockInfo.lockRelId.relId = RelationGetRelid(relation);

	if (relation->rd_rel->relisshared)
		relation->rd_lockInfo.lockRelId.dbId = InvalidOid;
	else
		relation->rd_lockInfo.lockRelId.dbId = MyDatabaseId;
}

/*
 * SetLocktagRelationOid
 *		Set up a locktag for a relation, given only relation OID
 */
/* (中文)仅凭关系 OID 构造关系的 LOCKTAG:
 * 共享关系(系统目录)用 InvalidOid 作为数据库 ID,使锁在整个集群内
 * 唯一;普通关系用 MyDatabaseId。与 RelationInitLockInfo 的取值规则
 * 严格一致。 */
static inline void
SetLocktagRelationOid(LOCKTAG *tag, Oid relid)
{
	Oid			dbid;

	if (IsSharedRelation(relid))
		dbid = InvalidOid;
	else
		dbid = MyDatabaseId;

	SET_LOCKTAG_RELATION(*tag, dbid, relid);
}

/*
 *		LockRelationOid
 *
 * Lock a relation given only its OID.  This should generally be used
 * before attempting to open the relation's relcache entry.
 */
/*
 * LockRelationOid
 *      (中文)仅凭关系 OID 加锁(通常用于打开 relcache 条目之前)
 *
 * 【作用】对指定 OID 的关系加指定模式的锁(阻塞式)。典型场景:
 * relation_open 之前的 RangeVarGetRelid,先拿锁再建 relcache 条目,
 * 保证拿到的 relcache 是最新版本。
 *
 * 【设计思想】
 * - 加锁成功后立刻吸收失效消息(AcceptInvalidationMessages):因为我们
 *   排队等待时,别的会话可能已修改了目录并广播了失效通知;不吸收的话,
 *   马上要用的 relcache 条目可能是陈旧的。但若返回
 *   LOCKACQUIRE_ALREADY_CLEAR(本事务已持有同种锁,此前已吸收过),
 *   则可跳过。
 * - 随后用 MarkLockClear(locallock) 在本地锁条目上打"已清"标记,
 *   使本事务后续重复加同一把锁时能直接返回 ALREADY_CLEAR,省去
 *   无谓的失效消息处理(见 LockAcquireExtended 的说明)。
 *
 * 【参数】
 *   relid    —— 关系 OID;
 *   lockmode —— 锁模式(通常 AccessShareLock/AccessExclusiveLock 等)。
 * 【返回值】无(阻塞直到拿到锁;不支持则报错)。
 */
void
LockRelationOid(Oid relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SetLocktagRelationOid(&tag, relid);

	res = LockAcquireExtended(&tag, lockmode, false, false, true, &locallock,
							  false);

	/*
	 * Now that we have the lock, check for invalidation messages, so that we
	 * will update or flush any stale relcache entry before we try to use it.
	 * RangeVarGetRelid() specifically relies on us for this.  We can skip
	 * this in the not-uncommon case that we already had the same type of lock
	 * being requested, since then no one else could have modified the
	 * relcache entry in an undesirable way.  (In the case where our own xact
	 * modifies the rel, the relcache update happens via
	 * CommandCounterIncrement, not here.)
	 *
	 * However, in corner cases where code acts on tables (usually catalogs)
	 * recursively, we might get here while still processing invalidation
	 * messages in some outer execution of this function or a sibling.  The
	 * "cleared" status of the lock tells us whether we really are done
	 * absorbing relevant inval messages.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}
}

/*
 *		ConditionalLockRelationOid
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true iff the lock was acquired.
 *
 * NOTE: we do not currently need conditional versions of all the
 * LockXXX routines in this file, but they could easily be added if needed.
 */
/*
 * ConditionalLockRelationOid
 *      (中文)LockRelationOid 的非阻塞版本
 *
 * 【作用】尝试对指定 OID 的关系加锁,拿不到就立即返回 false(绝不等待)。
 * 成功返回 true 并同样执行失效消息吸收与 MarkLockClear。
 *
 * 【设计思想】"条件加锁"用于调用者不想阻塞的场景,例如"有锁就做、
 * 没锁就换路径"(见各类 Conditional* 调用点);注意语义上的风险:
 * 返回 false 不代表将来加锁一定失败,只代表"此刻不可用"。
 *
 * 【参数】relid —— 关系 OID;lockmode —— 锁模式。
 * 【返回值】true = 已获得锁;false = 锁暂时不可用。
 */
bool
ConditionalLockRelationOid(Oid relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SetLocktagRelationOid(&tag, relid);

	res = LockAcquireExtended(&tag, lockmode, false, true, true, &locallock,
							  false);

	if (res == LOCKACQUIRE_NOT_AVAIL)
		return false;

	/*
	 * Now that we have the lock, check for invalidation messages; see notes
	 * in LockRelationOid.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}

	return true;
}

/*
 *		LockRelationId
 *
 * Lock, given a LockRelId.  Same as LockRelationOid but take LockRelId as an
 * input.
 */
/*
 * LockRelationId
 *      (中文)按 LockRelId(dbId, relId) 对关系加锁
 *
 * 【作用】与 LockRelationOid 等价,但直接使用关系描述符里预存的
 * LockRelId(避免再次判断"是否共享关系"),通常配合已打开的 relcache
 * 条目使用。
 *
 * 【参数】relid —— {dbId, relId} 结构;lockmode —— 锁模式。
 * 【返回值】无。
 */
void
LockRelationId(LockRelId *relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SET_LOCKTAG_RELATION(tag, relid->dbId, relid->relId);

	res = LockAcquireExtended(&tag, lockmode, false, false, true, &locallock,
							  false);

	/*
	 * Now that we have the lock, check for invalidation messages; see notes
	 * in LockRelationOid.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}
}

/*
 *		UnlockRelationId
 *
 * Unlock, given a LockRelId.  This is preferred over UnlockRelationOid
 * for speed reasons.
 */
/* (中文)按 LockRelId 解锁一把锁(LockRelease 的薄封装)。速度上优先于
 * UnlockRelationOid,因为它无需重新判断共享关系。 */
void
UnlockRelationId(LockRelId *relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION(tag, relid->dbId, relid->relId);

	LockRelease(&tag, lockmode, false);
}

/*
 *		UnlockRelationOid
 *
 * Unlock, given only a relation Oid.  Use UnlockRelationId if you can.
 */
/* (中文)仅凭关系 OID 解锁。能拿到 LockRelId 时应优先用 UnlockRelationId
 * (少一次共享关系判断,速度更快)。 */
void
UnlockRelationOid(Oid relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SetLocktagRelationOid(&tag, relid);

	LockRelease(&tag, lockmode, false);
}

/*
 *		LockRelation
 *
 * This is a convenience routine for acquiring an additional lock on an
 * already-open relation.  Never try to do "relation_open(foo, NoLock)"
 * and then lock with this.
 */
/*
 * LockRelation
 *      (中文)对"已打开的关系"再加一把锁
 *
 * 【作用】适用于"以 NoLock 方式打开关系后,再补加锁"的场合(例如
 * relation_open 时故意不加锁,后续按需加)。与 LockRelationId 相比
 * 只是参数从 LockRelId 变成 Relation 指针。
 *
 * 【注意】不要用"relation_open(foo, NoLock) + 本函数"的组合去替代
 * 普通的带锁打开——那样会有加锁前其他事务已修改关系的竞态窗口。
 *
 * 【参数】relation —— 已打开的关系;lockmode —— 锁模式。
 * 【返回值】无。
 */
void
LockRelation(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SET_LOCKTAG_RELATION(tag,
						 relation->rd_lockInfo.lockRelId.dbId,
						 relation->rd_lockInfo.lockRelId.relId);

	res = LockAcquireExtended(&tag, lockmode, false, false, true, &locallock,
							  false);

	/*
	 * Now that we have the lock, check for invalidation messages; see notes
	 * in LockRelationOid.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}
}

/*
 *		ConditionalLockRelation
 *
 * This is a convenience routine for acquiring an additional lock on an
 * already-open relation.  Never try to do "relation_open(foo, NoLock)"
 * and then lock with this.
 */
/* (中文)LockRelation 的非阻塞版本:拿不到锁立即返回 false,不等待。 */
bool
ConditionalLockRelation(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SET_LOCKTAG_RELATION(tag,
						 relation->rd_lockInfo.lockRelId.dbId,
						 relation->rd_lockInfo.lockRelId.relId);

	res = LockAcquireExtended(&tag, lockmode, false, true, true, &locallock,
							  false);

	if (res == LOCKACQUIRE_NOT_AVAIL)
		return false;

	/*
	 * Now that we have the lock, check for invalidation messages; see notes
	 * in LockRelationOid.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}

	return true;
}

/*
 *		UnlockRelation
 *
 * This is a convenience routine for unlocking a relation without also
 * closing it.
 */
/* (中文)解锁一个已打开的关系但不关闭它(不触发布缓冲等清理)。 */
void
UnlockRelation(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION(tag,
						 relation->rd_lockInfo.lockRelId.dbId,
						 relation->rd_lockInfo.lockRelId.relId);

	LockRelease(&tag, lockmode, false);
}

/*
 *		CheckRelationLockedByMe
 *
 * Returns true if current transaction holds a lock on 'relation' of mode
 * 'lockmode'.  If 'orstronger' is true, a stronger lockmode is also OK.
 * ("Stronger" is defined as "numerically higher", which is a bit
 * semantically dubious but is OK for the purposes we use this for.)
 */
/*
 * CheckRelationLockedByMe
 *      (中文)检查当前事务是否已持有关系上的某种锁
 *
 * 【作用】查询本事务(含本事务的所有资源所有者)是否持有该关系上的
 * lockmode 锁;orstronger 为 true 时,"数值上更大"的更强锁也算
 * (例如检查 AccessShareLock,而当前持有 RowExclusiveLock)。
 *
 * 【设计思想】常用于"避免重复加锁"或"决策是否执行某段需持锁的操作",
 * 只查本地锁表(LockHeldByMe 查 LOCALLOCK),绝不等待、绝不加锁。
 *
 * 【参数】relation —— 关系;lockmode —— 要检查的模式;
 * orstronger —— 是否接受更强模式。
 * 【返回值】true = 当前持有该锁;false = 未持有。
 */
bool
CheckRelationLockedByMe(Relation relation, LOCKMODE lockmode, bool orstronger)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION(tag,
						 relation->rd_lockInfo.lockRelId.dbId,
						 relation->rd_lockInfo.lockRelId.relId);

	return LockHeldByMe(&tag, lockmode, orstronger);
}

/*
 *		CheckRelationOidLockedByMe
 *
 * Like the above, but takes an OID as argument.
 */
/* (中文)CheckRelationLockedByMe 的 OID 版本(参数检查与语义完全相同)。 */
bool
CheckRelationOidLockedByMe(Oid relid, LOCKMODE lockmode, bool orstronger)
{
	LOCKTAG		tag;

	SetLocktagRelationOid(&tag, relid);

	return LockHeldByMe(&tag, lockmode, orstronger);
}

/*
 *		LockHasWaitersRelation
 *
 * This is a function to check whether someone else is waiting for a
 * lock which we are currently holding.
 */
/*
 * LockHasWaitersRelation
 *      (中文)检查是否有其他进程正等着我们持有的锁
 *
 * 【作用】查询本后端是否已持有该关系的 lockmode 锁,以及该锁上是否
 * 存在处于等待状态的请求者。常见用途:SPI/PL 等场景判断"别人在等我",
 * 以决定是否放弃持锁(如某些 DDL 策略)。
 *
 * 【注意】检查"是否有等待者"本身不做一致性快照:等待队列的状态可能
 * 瞬时变化,因此返回值仅作提示,不能作为可靠的事实依据(因此文档
 * 建议尽量少用)。
 *
 * 【参数】relation —— 关系;lockmode —— 锁模式。
 * 【返回值】true = 我们持有该锁且有其他进程在等待。
 */
bool
LockHasWaitersRelation(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION(tag,
						 relation->rd_lockInfo.lockRelId.dbId,
						 relation->rd_lockInfo.lockRelId.relId);

	return LockHasWaiters(&tag, lockmode, false);
}

/*
 *		LockRelationIdForSession
 *
 * This routine grabs a session-level lock on the target relation.  The
 * session lock persists across transaction boundaries.  It will be removed
 * when UnlockRelationIdForSession() is called, or if an ereport(ERROR) occurs,
 * or if the backend exits.
 *
 * Note that one should also grab a transaction-level lock on the rel
 * in any transaction that actually uses the rel, to ensure that the
 * relcache entry is up to date.
 */
/*
 * LockRelationIdForSession
 *      (中文)为"会话级"锁定加锁:跨事务存活
 *
 * 【作用】以 sessionLock = true 调用 LockAcquire,获得一把随会话存活、
 * 不随事务结束释放的锁(释放条件是:UnlockRelationIdForSession、
 * ereport(ERROR) 或后端退出)。
 *
 * 【设计思想】会话级锁用于"会话期间要保持某种保护"的场景(如
 * PREPARE 事务期间的锁、pg_import_system_colls 等)。注意:任何真正
 * 使用该关系的事务里仍应再加一把事务级锁,以保证 relcache 条目
 * 的最新性——事务级锁的失效消息吸收机制(见 LockRelationOid)不会
 * 被会话级锁触发。
 *
 * 【参数】relid —— {dbId, relId};lockmode —— 锁模式。
 * 【返回值】无。
 */
void
LockRelationIdForSession(LockRelId *relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION(tag, relid->dbId, relid->relId);

	(void) LockAcquire(&tag, lockmode, true, false);
}

/*
 *		UnlockRelationIdForSession
 */
/* (中文)释放一把会话级关系锁(sessionLock = true 的 LockRelease)。 */
void
UnlockRelationIdForSession(LockRelId *relid, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION(tag, relid->dbId, relid->relId);

	LockRelease(&tag, lockmode, true);
}

/*
 *		LockRelationForExtension
 *
 * This lock tag is used to interlock addition of pages to relations.
 * We need such locking because bufmgr/smgr definition of P_NEW is not
 * race-condition-proof.
 *
 * We assume the caller is already holding some type of regular lock on
 * the relation, so no AcceptInvalidationMessages call is needed here.
 */
/*
 * LockRelationForExtension
 *      (中文)对"关系扩展锁"加锁:串行化向关系追加页面的操作
 *
 * 【作用】获取关系扩展互斥锁(独立的 LOCKTAG,见
 * SET_LOCKTAG_RELATION_EXTEND),用于互斥"给关系追加新页"。
 *
 * 【设计思想】bufmgr/smgr 的 P_NEW 语义不具备原子性:两个进程可能
 * 同时算出同一个新页号。通过独立的关系扩展锁把"扩展"串行化,
 * 页号分配就天然唯一。它独立于普通关系锁,所以并发读(如持
 * AccessShareLock 的 SELECT)不必参与,只有扩展者之间互斥。
 * 调用者必须已持有某种普通关系锁(否则关系可能已被 DROP,扩展也
 * 无意义),因此这里不需要 AcceptInvalidationMessages。
 *
 * 【参数】relation —— 关系;lockmode —— 锁模式(扩展用
 * RowExclusiveLock 或 ExclusiveLock,配合"扩展加锁的立即失败版本")。
 * 【返回值】无。
 */
void
LockRelationForExtension(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION_EXTEND(tag,
								relation->rd_lockInfo.lockRelId.dbId,
								relation->rd_lockInfo.lockRelId.relId);

	(void) LockAcquire(&tag, lockmode, false, false);
}

/*
 *		ConditionalLockRelationForExtension
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true iff the lock was acquired.
 */
/* (中文)LockRelationForExtension 的非阻塞版本:立即尝试,失败返回 false
 * (调用方如 RelationGetBufferForTuple 会改用"一次性把锁升级为排他"等
 * 策略,因此拿到 false 时通常要换更强模式重试)。 */
bool
ConditionalLockRelationForExtension(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION_EXTEND(tag,
								relation->rd_lockInfo.lockRelId.dbId,
								relation->rd_lockInfo.lockRelId.relId);

	return (LockAcquire(&tag, lockmode, false, true) != LOCKACQUIRE_NOT_AVAIL);
}

/*
 *		RelationExtensionLockWaiterCount
 *
 * Count the number of processes waiting for the given relation extension lock.
 */
/* (中文)统计正等待某关系扩展锁的进程数(供并发扩展的流量控制使用,
 * 见 RelationGetBufferForTuple 中对扩展等待者数量的考量)。 */
int
RelationExtensionLockWaiterCount(Relation relation)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION_EXTEND(tag,
								relation->rd_lockInfo.lockRelId.dbId,
								relation->rd_lockInfo.lockRelId.relId);

	return LockWaiterCount(&tag);
}

/*
 *		UnlockRelationForExtension
 */
/* (中文)释放关系扩展锁。 */
void
UnlockRelationForExtension(Relation relation, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_RELATION_EXTEND(tag,
								relation->rd_lockInfo.lockRelId.dbId,
								relation->rd_lockInfo.lockRelId.relId);

	LockRelease(&tag, lockmode, false);
}

/*
 *		LockDatabaseFrozenIds
 *
 * This allows one backend per database to execute vac_update_datfrozenxid().
 */
/*
 * LockDatabaseFrozenIds
 *      (中文)加"数据库冻结 ID"锁:每个数据库同时只允许一个后端执行
 *      冻结清理
 *
 * 【作用】获取 SET_LOCKTAG_DATABASE_FROZEN_IDS 定义的那把全库级锁,
 * 使 vac_update_datfrozenxid()(由 VACUUM 或 autovacuum 调用)在同一
 * 数据库内互斥执行。
 *
 * 【设计思想】冻结 XID 的推进涉及共享的 pg_database 行更新,若多个
 * 后端并发推进会造成无谓竞争;此锁保证同一时刻只有一个后端在推进。
 * 用"全库唯一"的锁标签,而不是 per-relation 锁,因为冻结状态本身
 * 是数据库级的。
 *
 * 【参数】lockmode —— 锁模式(调用方一般用 ExclusiveLock)。
 * 【返回值】无。
 */
void
LockDatabaseFrozenIds(LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_DATABASE_FROZEN_IDS(tag, MyDatabaseId);

	(void) LockAcquire(&tag, lockmode, false, false);
}

/*
 *		LockPage
 *
 * Obtain a page-level lock.  This is currently used by some index access
 * methods to lock individual index pages.
 */
/*
 * LockPage
 *      (中文)加"页级锁":以单个索引页为粒度互斥
 *
 * 【作用】对关系中的指定页(blkno)加锁。目前供某些索引访问方法
 * (如 GiST 的页面拆分/合并、哈希索引的页面锁)保护单个索引页。
 *
 * 【设计思想】页级锁粒度小、冲突少,适合索引页这种"细粒度但需要
 * 一致性"的共享资源;但每把锁都要占用共享内存里的 LOCK 槽位,所以
 * 只用于少数热点页,不能每页都用。
 *
 * 【参数】relation —— 所属关系;blkno —— 页号;
 * lockmode —— 锁模式(通常 ExclusiveLock 或 ShareUpdateExclusiveLock)。
 * 【返回值】无。
 */
void
LockPage(Relation relation, BlockNumber blkno, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_PAGE(tag,
					 relation->rd_lockInfo.lockRelId.dbId,
					 relation->rd_lockInfo.lockRelId.relId,
					 blkno);

	(void) LockAcquire(&tag, lockmode, false, false);
}

/*
 *		ConditionalLockPage
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true iff the lock was acquired.
 */
/* (中文)LockPage 的非阻塞版本:拿不到立即返回 false,不等待。 */
bool
ConditionalLockPage(Relation relation, BlockNumber blkno, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_PAGE(tag,
					 relation->rd_lockInfo.lockRelId.dbId,
					 relation->rd_lockInfo.lockRelId.relId,
					 blkno);

	return (LockAcquire(&tag, lockmode, false, true) != LOCKACQUIRE_NOT_AVAIL);
}

/*
 *		UnlockPage
 */
/* (中文)释放页级锁。 */
void
UnlockPage(Relation relation, BlockNumber blkno, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_PAGE(tag,
					 relation->rd_lockInfo.lockRelId.dbId,
					 relation->rd_lockInfo.lockRelId.relId,
					 blkno);

	LockRelease(&tag, lockmode, false);
}

/*
 *		LockTuple
 *
 * Obtain a tuple-level lock.  This is used in a less-than-intuitive fashion
 * because we can't afford to keep a separate lock in shared memory for every
 * tuple.  See heap_lock_tuple before using this!
 */
/*
 * LockTuple
 *      (中文)加"元组级锁":锁住单个堆元组
 *
 * 【作用】对指定 TID 的元组加锁(锁标签含页号 + 页内偏移)。目前用于
 * heap_lock_tuple() 的 FOR UPDATE/FOR SHARE 行锁。
 *
 * 【设计思想】共享内存无法为每个元组都维持一把锁,所以这里其实
 * 只是在元组头部(infomask)标记加锁,XID 锁存于事务表;本函数创建
 * 的"元组锁"与 heap_lock_tuple 的行锁机制配合,见 heap_lock_tuple
 * 的详细注释。可以这样理解:行锁"真实存在"于元组头,而 LOCKTAG_TUPLE
 * 锁只是帮助死亡行被回收前(如 update 旧版本)维持可见性的辅助。
 *
 * 【参数】relation —— 所属关系;tid —— 元组 TID;lockmode —— 锁模式。
 * 【返回值】无。
 */
void
LockTuple(Relation relation, const ItemPointerData *tid, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_TUPLE(tag,
					  relation->rd_lockInfo.lockRelId.dbId,
					  relation->rd_lockInfo.lockRelId.relId,
					  ItemPointerGetBlockNumber(tid),
					  ItemPointerGetOffsetNumber(tid));

	(void) LockAcquire(&tag, lockmode, false, false);
}

/*
 *		ConditionalLockTuple
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true iff the lock was acquired.
 */
/*
 * ConditionalLockTuple
 *      (中文)LockTuple 的非阻塞版本
 *
 * 【作用】立即尝试对元组加锁,失败返回 false 不等待。参数比 LockTuple
 * 多一个 logLockFailure:为 true 时,加锁失败会按 LockAcquireExtended
 * 的规则记录"锁等待超时/死锁"日志(用于 heap_lock_tuple 这类对失败
 * 原因敏感的调用点,false 则静默失败)。
 *
 * 【参数】relation/tid/lockmode 同 LockTuple;
 * logLockFailure —— 失败时是否记日志。
 * 【返回值】true = 获得锁;false = 拿不到(未等待)。
 */
bool
ConditionalLockTuple(Relation relation, const ItemPointerData *tid, LOCKMODE lockmode,
					 bool logLockFailure)
{
	LOCKTAG		tag;

	SET_LOCKTAG_TUPLE(tag,
					  relation->rd_lockInfo.lockRelId.dbId,
					  relation->rd_lockInfo.lockRelId.relId,
					  ItemPointerGetBlockNumber(tid),
					  ItemPointerGetOffsetNumber(tid));

	return (LockAcquireExtended(&tag, lockmode, false, true, true, NULL,
								logLockFailure) != LOCKACQUIRE_NOT_AVAIL);
}

/*
 *		UnlockTuple
 */
/* (中文)释放元组级锁。 */
void
UnlockTuple(Relation relation, const ItemPointerData *tid, LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_TUPLE(tag,
					  relation->rd_lockInfo.lockRelId.dbId,
					  relation->rd_lockInfo.lockRelId.relId,
					  ItemPointerGetBlockNumber(tid),
					  ItemPointerGetOffsetNumber(tid));

	LockRelease(&tag, lockmode, false);
}

/*
 *		XactLockTableInsert
 *
 * Insert a lock showing that the given transaction ID is running ---
 * this is done when an XID is acquired by a transaction or subtransaction.
 * The lock can then be used to wait for the transaction to finish.
 */
/*
 * XactLockTableInsert
 *      (中文)登记"事务 XID 正在运行"的锁
 *
 * 【作用】事务(或子事务)获得 XID 时,为它插入一把排他锁
 * (LOCKTAG_TRANSACTION + ExclusiveLock)。这把锁的"存在"即代表
 * "该事务还活着",其他进程可以拿同一把锁的 ShareLock 来等待它结束。
 *
 * 【设计思想】这是用锁表模拟"事务存活性"的惯用法:持锁者(本事务)
 * 直到事务提交/回滚释放全部锁时才隐式释放它,所以"锁是否可获取"
 * 就精确反映了"事务是否仍在运行",且天然对并发等待者公平。
 *
 * 【参数】xid —— 要登记的事务 ID。
 * 【返回值】无。
 */
void
XactLockTableInsert(TransactionId xid)
{
	LOCKTAG		tag;

	SET_LOCKTAG_TRANSACTION(tag, xid);

	(void) LockAcquire(&tag, ExclusiveLock, false, false);
}

/*
 *		XactLockTableDelete
 *
 * Delete the lock showing that the given transaction ID is running.
 * (This is never used for main transaction IDs; those locks are only
 * released implicitly at transaction end.  But we do use it for subtrans IDs.)
 */
/*
 * XactLockTableDelete
 *      (中文)删除"XID 在运行"的锁(仅子事务使用)
 *
 * 【作用】释放指定 XID 的排他锁。主事务的锁在事务结束(锁清理)时
 * 隐式释放,这里从不调用;只有子事务结束时显式调用,以立即解除
 * "该子事务还在运行"的假象,让等待者尽快得知结果。
 *
 * 【设计思想】子事务的 XID 锁无法留到事务结束(共享内存里子事务
 * 锁太多、也无必要),所以子事务一结束(无论成败)就释放锁,等待方
 * 靠 XactLockTableWait 的"仍在运行?"检查来区分该等谁(见其注释)。
 *
 * 【参数】xid —— 已结束的子事务 ID。
 * 【返回值】无。
 */
void
XactLockTableDelete(TransactionId xid)
{
	LOCKTAG		tag;

	SET_LOCKTAG_TRANSACTION(tag, xid);

	LockRelease(&tag, ExclusiveLock, false);
}

/*
 *		XactLockTableWait
 *
 * Wait for the specified transaction to commit or abort.  If an operation
 * is specified, an error context callback is set up.  If 'oper' is passed as
 * None, no error context callback is set up.
 *
 * Note that this does the right thing for subtransactions: if we wait on a
 * subtransaction, we will exit as soon as it aborts or its top parent commits.
 * It takes some extra work to ensure this, because to save on shared memory
 * the XID lock of a subtransaction is released when it ends, whether
 * successfully or unsuccessfully.  So we have to check if it's "still running"
 * and if so wait for its parent.
 */
/*
 * XactLockTableWait
 *      (中文)等待指定事务提交或回滚
 *
 * 【作用】阻塞直到 xid 代表的事务(或子事务)结束。结束 = 子事务
 * abort,或它的最顶层父事务 commit(见下)。
 *
 * 【算法】循环:
 * 1. 对 xid 加 ShareLock(等锁表里的排他锁消失)再立刻释放——若该
 *    事务仍持有排他锁,这一步会阻塞直到它结束;
 * 2. 用 TransactionIdIsInProgress 复核 xid 是否真的不再运行。为什么
 *    要复核?因为子事务的 XID 锁在其结束时立即释放(见
 *    XactLockTableDelete),而"子事务结束"并不等于"整个事务结束":
 *    若子事务成功提交,它不再"in progress",但它的顶层父事务还在
 *    运行,需要继续等待父事务;
 * 3. 于是沿父子链把 xid 升到其"还在运行"的最顶层父事务,继续循环。
 *
 * 【参数】
 *   xid  —— 要等待结束的事务 ID(不能是本事务的顶层 XID);
 *   rel / ctid —— 涉及的关系与元组(供错误上下文);
 *   oper —— 等待时的操作类型;XLTW_None 则不注册错误上下文回调。
 * 【返回值】无(以等待结束或抛出错误告终)。
 */
void
XactLockTableWait(TransactionId xid, Relation rel, const ItemPointerData *ctid,
				  XLTW_Oper oper)
{
	LOCKTAG		tag;
	XactLockTableWaitInfo info;
	ErrorContextCallback callback;
	bool		first = true;

	/*
	 * If an operation is specified, set up our verbose error context
	 * callback.
	 */
	if (oper != XLTW_None)
	{
		Assert(RelationIsValid(rel));
		Assert(ItemPointerIsValid(ctid));

		info.rel = rel;
		info.ctid = ctid;
		info.oper = oper;

		callback.callback = XactLockTableWaitErrorCb;
		callback.arg = &info;
		callback.previous = error_context_stack;
		error_context_stack = &callback;
	}

	for (;;)
	{
		Assert(TransactionIdIsValid(xid));
		Assert(!TransactionIdEquals(xid, GetTopTransactionIdIfAny()));

		SET_LOCKTAG_TRANSACTION(tag, xid);

		(void) LockAcquire(&tag, ShareLock, false, false);

		LockRelease(&tag, ShareLock, false);

		if (!TransactionIdIsInProgress(xid))
			break;

		/*
		 * If the Xid belonged to a subtransaction, then the lock would have
		 * gone away as soon as it was finished; for correct tuple visibility,
		 * the right action is to wait on its parent transaction to go away.
		 * But instead of going levels up one by one, we can just wait for the
		 * topmost transaction to finish with the same end result, which also
		 * incurs less locktable traffic.
		 *
		 * Some uses of this function don't involve tuple visibility -- such
		 * as when building snapshots for logical decoding.  It is possible to
		 * see a transaction in ProcArray before it registers itself in the
		 * locktable.  The topmost transaction in that case is the same xid,
		 * so we try again after a short sleep.  (Don't sleep the first time
		 * through, to avoid slowing down the normal case.)
		 */
		if (!first)
		{
			CHECK_FOR_INTERRUPTS();
			pg_usleep(1000L);
		}
		first = false;
		xid = SubTransGetTopmostTransaction(xid);
	}

	if (oper != XLTW_None)
		error_context_stack = callback.previous;
}

/*
 *		ConditionalXactLockTableWait
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true if the lock was acquired.
 */
/*
 * ConditionalXactLockTableWait
 *      (中文)XactLockTableWait 的非阻塞版本
 *
 * 【作用】若 xid 的排他锁立即可获取则视为"事务已结束",返回 true;
 * 否则(锁被占着)立即返回 false,不等待。用于调用者只想"试一下"的
 * 场合。
 *
 * 【设计思想】与阻塞版相同,依赖"子事务结束→升到最顶层父事务再查"
 * 的逻辑,只是把阻塞式 LockAcquire 换成条件式
 * (LockAcquireExtended + dontWait)。logLockFailure 控制拿不到锁时
 * 是否记日志。
 *
 * 【参数】xid —— 要检查的事务;logLockFailure —— 失败时是否记日志。
 * 【返回值】true = 该事务已不再运行;false = 它仍在运行(未等待)。
 */
bool
ConditionalXactLockTableWait(TransactionId xid, bool logLockFailure)
{
	LOCKTAG		tag;
	bool		first = true;

	for (;;)
	{
		Assert(TransactionIdIsValid(xid));
		Assert(!TransactionIdEquals(xid, GetTopTransactionIdIfAny()));

		SET_LOCKTAG_TRANSACTION(tag, xid);

		if (LockAcquireExtended(&tag, ShareLock, false, true, true, NULL,
								logLockFailure)
			== LOCKACQUIRE_NOT_AVAIL)
			return false;

		LockRelease(&tag, ShareLock, false);

		if (!TransactionIdIsInProgress(xid))
			break;

		/* See XactLockTableWait about this case */
		if (!first)
		{
			CHECK_FOR_INTERRUPTS();
			pg_usleep(1000L);
		}
		first = false;
		xid = SubTransGetTopmostTransaction(xid);
	}

	return true;
}

/*
 *		SpeculativeInsertionLockAcquire
 *
 * Insert a lock showing that the given transaction ID is inserting a tuple,
 * but hasn't yet decided whether it's going to keep it.  The lock can then be
 * used to wait for the decision to go ahead with the insertion, or aborting
 * it.
 *
 * The token is used to distinguish multiple insertions by the same
 * transaction.  It is returned to caller.
 */
/*
 * SpeculativeInsertionLockAcquire
 *      (中文)登记"本事务正在做推测插入"的锁
 *
 * 【作用】推测插入(speculative insertion,见 heap_insert 的
 * speculativeInsertion 分支):唯一性索引检查前,元组尚未最终确认,
 * 本函数为 (xid, token) 建立一把排他锁,表示"xid 在插元组、还没决定
 * 去留"。其他事务可对它加 ShareLock 等待决定结果(保留或回滚)。
 *
 * 【设计思想】token 用于区分同一事务的多次推测插入:若不加 token,
 * 同一事务先后两次插入会共用同一把锁,等待方可能被"第一次插入
 * 已解决、第二次还在进行"误判。token 由模块级计数器生成(见
 * speculativeInsertionToken 的注释),0 是保留值,回绕时跳到 1。
 *
 * 【参数】xid —— 正在做推测插入的事务。
 * 【返回值】本次插入使用的令牌(调用方要保存,供 Release/Wait 使用)。
 */
uint32
SpeculativeInsertionLockAcquire(TransactionId xid)
{
	LOCKTAG		tag;

	speculativeInsertionToken++;

	/*
	 * Check for wrap-around. Zero means no token is held, so don't use that.
	 */
	if (speculativeInsertionToken == 0)
		speculativeInsertionToken = 1;

	SET_LOCKTAG_SPECULATIVE_INSERTION(tag, xid, speculativeInsertionToken);

	(void) LockAcquire(&tag, ExclusiveLock, false, false);

	return speculativeInsertionToken;
}

/*
 *		SpeculativeInsertionLockRelease
 *
 * Delete the lock showing that the given transaction is speculatively
 * inserting a tuple.
 */
/*
 * SpeculativeInsertionLockRelease
 *      (中文)解除"推测插入"锁:插入的决定已做出
 *
 * 【作用】唯一性检查完成(决定保留或回滚元组)后,释放由
 * SpeculativeInsertionLockAcquire 建立的锁,让所有等待者(在
 * SpeculativeInsertionWait 上阻塞的进程)立即唤醒并重新判断元组状态。
 *
 * 【注意】令牌用的是模块级计数器当前值,因此只适用于"同一事务、
 * 顺序、单线程"地成对使用 Acquire/Release 的调用模式。
 *
 * 【参数】xid —— 做推测插入的事务。
 * 【返回值】无。
 */
void
SpeculativeInsertionLockRelease(TransactionId xid)
{
	LOCKTAG		tag;

	SET_LOCKTAG_SPECULATIVE_INSERTION(tag, xid, speculativeInsertionToken);

	LockRelease(&tag, ExclusiveLock, false);
}

/*
 *		SpeculativeInsertionWait
 *
 * Wait for the specified transaction to finish or abort the insertion of a
 * tuple.
 */
/*
 * SpeculativeInsertionWait
 *      (中文)等待某事务的推测插入尘埃落定
 *
 * 【作用】对 (xid, token) 那把排他锁加 ShareLock 再立即释放:若 xid
 * 仍在做该次推测插入,这步会阻塞直到它调用 SpeculativeInsertionLockRelease
 * (决定保留)或事务回滚(锁随事务结束隐式释放)。锁拿到即代表插入
 * 已成定局,可放心依据元组现状继续处理。
 *
 * 【参数】xid —— 正在插入的事务;token —— 其插入令牌(Acquire 的
 * 返回值,保证不为 0)。
 * 【返回值】无。
 */
void
SpeculativeInsertionWait(TransactionId xid, uint32 token)
{
	LOCKTAG		tag;

	SET_LOCKTAG_SPECULATIVE_INSERTION(tag, xid, token);

	Assert(TransactionIdIsValid(xid));
	Assert(token != 0);

	(void) LockAcquire(&tag, ShareLock, false, false);
	LockRelease(&tag, ShareLock, false);
}

/*
 * XactLockTableWaitErrorCb
 *		Error context callback for transaction lock waits.
 */
/*
 * XactLockTableWaitErrorCb
 *      (中文)事务锁等待的错误上下文回调
 *
 * 【作用】XactLockTableWait 中注册的 errcontext 回调:当等待期间抛出
 * 错误(锁超时、查询取消、死锁)时,在错误详情后追加一行说明当时
 * 在做什么,例如:
 *   while updating tuple (5,11) in relation "mytable"
 * 使报错信息对用户可理解。
 *
 * 【设计思想】根据 oper(XLTW_Update/Delete/Lock/InsertIndex 等)选择
 * 措辞;不打印 schema 名,因为那需要 syscache 查找,而错误处理期间
 * 不应再访问可能不一致的目录。只打印关系名、块号、偏移。
 *
 * 【参数】arg —— XactLockTableWaitInfo 指针。
 * 【返回值】无。
 */
static void
XactLockTableWaitErrorCb(void *arg)
{
	XactLockTableWaitInfo *info = (XactLockTableWaitInfo *) arg;

	/*
	 * We would like to print schema name too, but that would require a
	 * syscache lookup.
	 */
	if (info->oper != XLTW_None &&
		ItemPointerIsValid(info->ctid) && RelationIsValid(info->rel))
	{
		const char *cxt;

		switch (info->oper)
		{
			case XLTW_Update:
				cxt = gettext_noop("while updating tuple (%u,%u) in relation \"%s\"");
				break;
			case XLTW_Delete:
				cxt = gettext_noop("while deleting tuple (%u,%u) in relation \"%s\"");
				break;
			case XLTW_Lock:
				cxt = gettext_noop("while locking tuple (%u,%u) in relation \"%s\"");
				break;
			case XLTW_LockUpdated:
				cxt = gettext_noop("while locking updated version (%u,%u) of tuple in relation \"%s\"");
				break;
			case XLTW_InsertIndex:
				cxt = gettext_noop("while inserting index tuple (%u,%u) in relation \"%s\"");
				break;
			case XLTW_InsertIndexUnique:
				cxt = gettext_noop("while checking uniqueness of tuple (%u,%u) in relation \"%s\"");
				break;
			case XLTW_FetchUpdated:
				cxt = gettext_noop("while rechecking updated tuple (%u,%u) in relation \"%s\"");
				break;
			case XLTW_RecheckExclusionConstr:
				cxt = gettext_noop("while checking exclusion constraint on tuple (%u,%u) in relation \"%s\"");
				break;

			default:
				return;
		}

		errcontext(cxt,
				   ItemPointerGetBlockNumber(info->ctid),
				   ItemPointerGetOffsetNumber(info->ctid),
				   RelationGetRelationName(info->rel));
	}
}

/*
 * WaitForLockersMultiple
 *		Wait until no transaction holds locks that conflict with the given
 *		locktags at the given lockmode.
 *
 * To do this, obtain the current list of lockers, and wait on their VXIDs
 * until they are finished.
 *
 * Note we don't try to acquire the locks on the given locktags, only the
 * VXIDs and XIDs of their lock holders; if somebody grabs a conflicting lock
 * on the objects after we obtained our initial list of lockers, we will not
 * wait for them.
 */
/*
 * WaitForLockersMultiple
 *      (中文)等待"持有与给定锁冲突的锁"的全部事务结束
 *
 * 【作用】对每个 locktag,用 GetLockConflicts 找出当前持有冲突锁的
 * 事务列表(以 VXID 表示),然后逐个用 VirtualXactLock 等它们结束。
 * DROP 表/表空间、CLUSTER 等需要"驱逐所有冲突持有者"的场景使用。
 *
 * 【设计思想】
 * - 等待对象是"持有者的 VXID/XID"而不是锁本身:不真正加锁,只是
 *   等旧持有者走人,因此若在我们收集列表之后又有新事务抢到冲突锁,
 *   我们不会等它(文档承认这是可接受的竞态);
 * - GetLockConflicts 不会报告我们自己的 XID(自己等自己无意义),
 *   但会报告并等待 prepared 事务(两阶段提交的预备事务也是要等的);
 * - 可选 progress:通过 pgstat 向"进度查看"汇报等待总数/已完成数/
 *   当前等待的 PID(vacuum 等的 progress 视图)。
 *
 * 【参数】
 *   locktags —— 要排查的锁标签列表(每个都要等其冲突持有者);
 *   lockmode —— 判断冲突所用的锁模式;
 *   progress —— 是否向 pgstat 汇报进度。
 * 【返回值】无(阻塞至全部相关事务结束)。
 */
void
WaitForLockersMultiple(List *locktags, LOCKMODE lockmode, bool progress)
{
	List	   *holders = NIL;
	ListCell   *lc;
	int			total = 0;
	int			done = 0;

	/* Done if no locks to wait for */
	if (locktags == NIL)
		return;

	/* Collect the transactions we need to wait on */
	foreach(lc, locktags)
	{
		LOCKTAG    *locktag = lfirst(lc);
		int			count;

		holders = lappend(holders,
						  GetLockConflicts(locktag, lockmode,
										   progress ? &count : NULL));
		if (progress)
			total += count;
	}

	if (progress)
		pgstat_progress_update_param(PROGRESS_WAITFOR_TOTAL, total);

	/*
	 * Note: GetLockConflicts() never reports our own xid, hence we need not
	 * check for that.  Also, prepared xacts are reported and awaited.
	 */

	/* Finally wait for each such transaction to complete */
	foreach(lc, holders)
	{
		VirtualTransactionId *lockholders = lfirst(lc);

		while (VirtualTransactionIdIsValid(*lockholders))
		{
			/* If requested, publish who we're going to wait for. */
			if (progress)
			{
				PGPROC	   *holder = ProcNumberGetProc(lockholders->procNumber);

				if (holder)
					pgstat_progress_update_param(PROGRESS_WAITFOR_CURRENT_PID,
												 holder->pid);
			}
			VirtualXactLock(*lockholders, true);
			lockholders++;

			if (progress)
				pgstat_progress_update_param(PROGRESS_WAITFOR_DONE, ++done);
		}
	}
	if (progress)
	{
		const int	index[] = {
			PROGRESS_WAITFOR_TOTAL,
			PROGRESS_WAITFOR_DONE,
			PROGRESS_WAITFOR_CURRENT_PID
		};
		const int64 values[] = {
			0, 0, 0
		};

		pgstat_progress_update_multi_param(3, index, values);
	}

	list_free_deep(holders);
}

/*
 * WaitForLockers
 *
 * Same as WaitForLockersMultiple, for a single lock tag.
 */
/* (中文)WaitForLockersMultiple 的单锁标签便捷封装(参数含义相同)。 */
void
WaitForLockers(LOCKTAG heaplocktag, LOCKMODE lockmode, bool progress)
{
	List	   *l;

	l = list_make1(&heaplocktag);
	WaitForLockersMultiple(l, lockmode, progress);
	list_free(l);
}


/*
 *		LockDatabaseObject
 *
 * Obtain a lock on a general object of the current database.  Don't use
 * this for shared objects (such as tablespaces).  It's unwise to apply it
 * to relations, also, since a lock taken this way will NOT conflict with
 * locks taken via LockRelation and friends.
 */
/*
 * LockDatabaseObject
 *      (中文)对本数据库内"任意对象"加锁(目录对象锁)
 *
 * 【作用】用 (dbId, classid, objid, objsubid) 标识一个通用对象并加锁,
 * 用于保护例如"整个表(作为目录对象)"的 DROP、ALTER 等操作的互斥
 * (DROP 期间其他事务对该对象的访问要等着)。
 *
 * 【注意】不要用于共享对象(表空间等,请用 LockSharedObject);也不要
 * 用于关系对象——它用的是独立的 LOCKTAG_OBJECT,不会与
 * LockRelation 系的锁冲突,若混用,一个事务可能"以为锁住了关系",
 * 而另一个事务通过 LockRelation 照常访问。
 *
 * 【参数】classid —— 对象类型(OID of pg_class 等);objid —— 对象 OID;
 * objsubid —— 子对象号(0 表示对象本身);lockmode —— 锁模式。
 * 【返回值】无(加锁成功后吸收失效消息,保证 syscache 最新)。
 */
void
LockDatabaseObject(Oid classid, Oid objid, uint16 objsubid,
				   LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_OBJECT(tag,
					   MyDatabaseId,
					   classid,
					   objid,
					   objsubid);

	(void) LockAcquire(&tag, lockmode, false, false);

	/* Make sure syscaches are up-to-date with any changes we waited for */
	AcceptInvalidationMessages();
}

/*
 *		ConditionalLockDatabaseObject
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true iff the lock was acquired.
 */
/*
 * ConditionalLockDatabaseObject
 *      (中文)LockDatabaseObject 的非阻塞版本
 *
 * 【作用】立即尝试对目录对象加锁,拿不到返回 false 不等待;成功时
 * 同样执行失效消息吸收与 MarkLockClear(与 LockRelationOid 相同的
 * 约定,避免重复吸收)。
 *
 * 【参数】classid/objid/objsubid/lockmode —— 同 LockDatabaseObject。
 * 【返回值】true = 已获得锁;false = 暂不可用。
 */
bool
ConditionalLockDatabaseObject(Oid classid, Oid objid, uint16 objsubid,
							  LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SET_LOCKTAG_OBJECT(tag,
					   MyDatabaseId,
					   classid,
					   objid,
					   objsubid);

	res = LockAcquireExtended(&tag, lockmode, false, true, true, &locallock,
							  false);

	if (res == LOCKACQUIRE_NOT_AVAIL)
		return false;

	/*
	 * Now that we have the lock, check for invalidation messages; see notes
	 * in LockRelationOid.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}

	return true;
}

/*
 *		UnlockDatabaseObject
 */
/* (中文)释放数据库对象锁。 */
void
UnlockDatabaseObject(Oid classid, Oid objid, uint16 objsubid,
					 LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_OBJECT(tag,
					   MyDatabaseId,
					   classid,
					   objid,
					   objsubid);

	LockRelease(&tag, lockmode, false);
}

/*
 *		LockSharedObject
 *
 * Obtain a lock on a shared-across-databases object.
 */
/*
 * LockSharedObject
 *      (中文)对"跨数据库共享对象"加锁
 *
 * 【作用】与 LockDatabaseObject 相同,但用 InvalidOid 作为 dbId,使锁
 * 在整个集群范围有效——适合保护表空间、共享目录行等所有数据库
 * 共享的对象(例如 ALTER TABLESPACE 与在其中建表互斥)。
 *
 * 【参数】classid/objid/objsubid/lockmode —— 同 LockDatabaseObject
 * (dbId 固定 InvalidOid)。
 * 【返回值】无(成功后吸收失效消息)。
 */
void
LockSharedObject(Oid classid, Oid objid, uint16 objsubid,
				 LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_OBJECT(tag,
					   InvalidOid,
					   classid,
					   objid,
					   objsubid);

	(void) LockAcquire(&tag, lockmode, false, false);

	/* Make sure syscaches are up-to-date with any changes we waited for */
	AcceptInvalidationMessages();
}

/*
 *		ConditionalLockSharedObject
 *
 * As above, but only lock if we can get the lock without blocking.
 * Returns true iff the lock was acquired.
 */
/* (中文)LockSharedObject 的非阻塞版本(语义与 Conditional* 系列一致)。 */
bool
ConditionalLockSharedObject(Oid classid, Oid objid, uint16 objsubid,
							LOCKMODE lockmode)
{
	LOCKTAG		tag;
	LOCALLOCK  *locallock;
	LockAcquireResult res;

	SET_LOCKTAG_OBJECT(tag,
					   InvalidOid,
					   classid,
					   objid,
					   objsubid);

	res = LockAcquireExtended(&tag, lockmode, false, true, true, &locallock,
							  false);

	if (res == LOCKACQUIRE_NOT_AVAIL)
		return false;

	/*
	 * Now that we have the lock, check for invalidation messages; see notes
	 * in LockRelationOid.
	 */
	if (res != LOCKACQUIRE_ALREADY_CLEAR)
	{
		AcceptInvalidationMessages();
		MarkLockClear(locallock);
	}

	return true;
}

/*
 *		UnlockSharedObject
 */
/* (中文)释放共享对象锁。 */
void
UnlockSharedObject(Oid classid, Oid objid, uint16 objsubid,
				   LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_OBJECT(tag,
					   InvalidOid,
					   classid,
					   objid,
					   objsubid);

	LockRelease(&tag, lockmode, false);
}

/*
 *		LockSharedObjectForSession
 *
 * Obtain a session-level lock on a shared-across-databases object.
 * See LockRelationIdForSession for notes about session-level locks.
 */
/*
 * LockSharedObjectForSession
 *      (中文)对共享对象加"会话级"锁
 *
 * 【作用】同 LockSharedObject,但 sessionLock = true:锁跨事务存活,
 * 直到显式解锁、出错或后端退出才释放。用途如 PREPARE 事务保持对
 * 表空间的保护。
 *
 * 【参数】classid/objid/objsubid —— 对象标识;lockmode —— 锁模式。
 * 【返回值】无。
 */
void
LockSharedObjectForSession(Oid classid, Oid objid, uint16 objsubid,
						   LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_OBJECT(tag,
					   InvalidOid,
					   classid,
					   objid,
					   objsubid);

	(void) LockAcquire(&tag, lockmode, true, false);
}

/*
 *		UnlockSharedObjectForSession
 */
/* (中文)释放共享对象的会话级锁。 */
void
UnlockSharedObjectForSession(Oid classid, Oid objid, uint16 objsubid,
							 LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_OBJECT(tag,
					   InvalidOid,
					   classid,
					   objid,
					   objsubid);

	LockRelease(&tag, lockmode, true);
}

/*
 *		LockApplyTransactionForSession
 *
 * Obtain a session-level lock on a transaction being applied on a logical
 * replication subscriber. See LockRelationIdForSession for notes about
 * session-level locks.
 */
/*
 * LockApplyTransactionForSession
 *      (中文)对逻辑复制"正在应用的事务"加会话级锁
 *
 * 【作用】逻辑复制订阅端应用一个远端事务时,为 (dbId, suboid, xid,
 * objid) 建立会话级锁。这把锁使同一订阅应用同一事务的操作互斥,
 * 并防止订阅被 DROP 时正在应用的事务被误清理(参见逻辑复制
 * apply 工作器的加锁流程)。
 *
 * 【参数】suboid —— 订阅 OID;xid —— 正在应用的远端事务 XID;
 * objid —— 用途子标识;lockmode —— 锁模式。
 * 【返回值】无。
 */
void
LockApplyTransactionForSession(Oid suboid, TransactionId xid, uint16 objid,
							   LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_APPLY_TRANSACTION(tag,
								  MyDatabaseId,
								  suboid,
								  xid,
								  objid);

	(void) LockAcquire(&tag, lockmode, true, false);
}

/*
 *		UnlockApplyTransactionForSession
 */
/* (中文)释放"应用事务"的会话级锁。 */
void
UnlockApplyTransactionForSession(Oid suboid, TransactionId xid, uint16 objid,
								 LOCKMODE lockmode)
{
	LOCKTAG		tag;

	SET_LOCKTAG_APPLY_TRANSACTION(tag,
								  MyDatabaseId,
								  suboid,
								  xid,
								  objid);

	LockRelease(&tag, lockmode, true);
}

/*
 * Append a description of a lockable object to buf.
 *
 * Ideally we would print names for the numeric values, but that requires
 * getting locks on system tables, which might cause problems since this is
 * typically used to report deadlock situations.
 */
/*
 * DescribeLockTag
 *      (中文)把锁标签描述成可读文本
 *
 * 【作用】按 locktag_type 分派,把锁标签的各个字段(库 ID、关系 OID、
 * 页号、元组位置、事务号等)格式化追加到 buf。典型调用场景:死锁
 * 报告、锁等待日志(pg_stat_activity 的 wait_event、log_lock_waits)、
 * DEBUG 输出。
 *
 * 【设计思想】只用数值打印,不查系统目录把 OID 翻译成名字——打印
 * 死锁报告时正处于异常状态,再去拿系统表锁会引入新的风险(自身
 * 可能再次死锁)。
 *
 * 【参数】buf —— 目标 StringInfo;tag —— 要描述的锁标签。
 * 【返回值】无。
 */
void
DescribeLockTag(StringInfo buf, const LOCKTAG *tag)
{
	switch ((LockTagType) tag->locktag_type)
	{
		case LOCKTAG_RELATION:
			appendStringInfo(buf,
							 _("relation %u of database %u"),
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		case LOCKTAG_RELATION_EXTEND:
			appendStringInfo(buf,
							 _("extension of relation %u of database %u"),
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		case LOCKTAG_DATABASE_FROZEN_IDS:
			appendStringInfo(buf,
							 _("pg_database.datfrozenxid of database %u"),
							 tag->locktag_field1);
			break;
		case LOCKTAG_PAGE:
			appendStringInfo(buf,
							 _("page %u of relation %u of database %u"),
							 tag->locktag_field3,
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		case LOCKTAG_TUPLE:
			appendStringInfo(buf,
							 _("tuple (%u,%u) of relation %u of database %u"),
							 tag->locktag_field3,
							 tag->locktag_field4,
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		case LOCKTAG_TRANSACTION:
			appendStringInfo(buf,
							 _("transaction %u"),
							 tag->locktag_field1);
			break;
		case LOCKTAG_VIRTUALTRANSACTION:
			appendStringInfo(buf,
							 _("virtual transaction %d/%u"),
							 tag->locktag_field1,
							 tag->locktag_field2);
			break;
		case LOCKTAG_SPECULATIVE_TOKEN:
			appendStringInfo(buf,
							 _("speculative token %u of transaction %u"),
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		case LOCKTAG_OBJECT:
			appendStringInfo(buf,
							 _("object %u of class %u of database %u"),
							 tag->locktag_field3,
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		case LOCKTAG_USERLOCK:
			/* reserved for old contrib code, now on pgfoundry */
			appendStringInfo(buf,
							 _("user lock [%u,%u,%u]"),
							 tag->locktag_field1,
							 tag->locktag_field2,
							 tag->locktag_field3);
			break;
		case LOCKTAG_ADVISORY:
			appendStringInfo(buf,
							 _("advisory lock [%u,%u,%u,%u]"),
							 tag->locktag_field1,
							 tag->locktag_field2,
							 tag->locktag_field3,
							 tag->locktag_field4);
			break;
		case LOCKTAG_APPLY_TRANSACTION:
			appendStringInfo(buf,
							 _("remote transaction %u of subscription %u of database %u"),
							 tag->locktag_field3,
							 tag->locktag_field2,
							 tag->locktag_field1);
			break;
		default:
			appendStringInfo(buf,
							 _("unrecognized locktag type %d"),
							 (int) tag->locktag_type);
			break;
	}
}

/*
 * GetLockNameFromTagType
 *
 *	Given locktag type, return the corresponding lock name.
 */
/*
 * GetLockNameFromTagType
 *      (中文)按锁标签类型返回其名称
 *
 * 【作用】由 locktag_type 查 LockTagTypeNames[] 表得到类型名
 * (如 "relation"、"page"、"object"),供 pg_locks 视图等把类型号
 * 翻译成字符串。越界时返回 "???" 兜底。
 *
 * 【参数】locktag_type —— 锁标签类型号。
 * 【返回值】对应的类型名字符串。
 */
const char *
GetLockNameFromTagType(uint16 locktag_type)
{
	if (locktag_type > LOCKTAG_LAST_TYPE)
		return "???";
	return LockTagTypeNames[locktag_type];
}
