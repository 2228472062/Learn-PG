/*-------------------------------------------------------------------------
 *
 * twophase_rmgr.c
 *	  Two-phase-commit resource managers tables
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/access/transam/twophase_rmgr.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * 中文注释：
 * 本文件是两阶段提交（2PC）的“资源管理器回调分发表”。
 *
 * PREPARE TRANSACTION 会把一个事务涉及的所有资源（锁、MultiXact、谓词锁、统计信息等）
 * 序列化到 pg_twophase 文件中。之后该事务可能被 COMMIT PREPARED 或 ROLLBACK PREPARED，
 * 也可能在崩溃恢复时由 WAL 中的 XLOG_XACT_PREPARE 记录重新构造出来。不同种类的资源
 * 需要不同的恢复/提交/中止动作，因此 PostgreSQL 为每一类资源分配一个 TwoPhaseRmgrId，
 * 并在下面四张表中按 ID 放置回调函数指针：
 *
 *   - twophase_recover_callbacks：崩溃恢复、重放 PREPARE 记录时调用；
 *   - twophase_postcommit_callbacks：COMMIT PREPARED 成功后调用；
 *   - twophase_postabort_callbacks：ROLLBACK PREPARED 后调用；
 *   - twophase_standby_recover_callbacks：在备库上重放 PREPARE 记录时调用。
 *
 * 这种“ID + 函数指针表”的设计把 2PC 核心逻辑与具体资源类型解耦：twophase.c 只负责
 * 读写状态文件并遍历记录，完全不需要知道每种资源内部如何恢复；新增资源类型时只需在
 * 这里登记回调，并保证 ID 与 twophase_rmgr.h 中的枚举一致。
 */
#include "postgres.h"

#include "access/multixact.h"
#include "access/twophase_rmgr.h"
#include "pgstat.h"
#include "storage/lock.h"
#include "storage/predicate.h"


/*
 * 中文注释：
 * 恢复阶段的回调表，按 TwoPhaseRmgrId 索引。
 * 当系统在崩溃恢复（或备库回放）中遇到 XLOG_XACT_PREPARE 记录时，会重建该预备事务的
 * 状态。表中第 0 项是 END ID 哨兵，不承载实际资源；其余项分别负责恢复锁、MultiXact
 * 和谓词锁。某个资源在恢复时若无需特殊处理，就填 NULL，调用方会跳过。
 */
const TwoPhaseCallback twophase_recover_callbacks[TWOPHASE_RM_MAX_ID + 1] =
{
	NULL,						/* END ID */
	lock_twophase_recover,		/* Lock */
	NULL,						/* pgstat */
	multixact_twophase_recover, /* MultiXact */
	predicatelock_twophase_recover	/* PredicateLock */
};

/*
 * 中文注释：
 * 提交阶段的回调表。COMMIT PREPARED 在删除 pg_twophase 状态文件之前/之后，需要通知
 * 各资源管理器“这个事务已经提交”。例如锁管理器释放属于该事务的锁，统计系统把事务
 * 期间累积的统计信息合并到共享统计中，MultiXact 系统完成相关成员关系的提交。
 * 注意谓词锁在这里为 NULL：SSI 谓词锁只需在恢复/中止时特殊处理，提交时随事务自然失效。
 */
const TwoPhaseCallback twophase_postcommit_callbacks[TWOPHASE_RM_MAX_ID + 1] =
{
	NULL,						/* END ID */
	lock_twophase_postcommit,	/* Lock */
	pgstat_twophase_postcommit, /* pgstat */
	multixact_twophase_postcommit,	/* MultiXact */
	NULL						/* PredicateLock */
};

/*
 * 中文注释：
 * 中止阶段的回调表。ROLLBACK PREPARED 或恢复过程中放弃一个预备事务时，各资源管理器
 * 需要撤销该事务留下的效果：释放锁、回滚 MultiXact 成员关系、清理统计信息等。
 * 谓词锁没有中止回调，因为它会随事务状态变为“已中止”而自动失效。
 */
const TwoPhaseCallback twophase_postabort_callbacks[TWOPHASE_RM_MAX_ID + 1] =
{
	NULL,						/* END ID */
	lock_twophase_postabort,	/* Lock */
	pgstat_twophase_postabort,	/* pgstat */
	multixact_twophase_postabort,	/* MultiXact */
	NULL						/* PredicateLock */
};

/*
 * 中文注释：
 * 备库恢复回调表。主库上的预备事务会通过 WAL 传到备库，备库回放 XLOG_XACT_PREPARE
 * 时不能让这些锁真正阻塞查询，而要转换成“备库锁”（standby lock）语义，等最终提交或
 * 中止记录到达后再释放。这里只有锁管理器需要特殊处理；其他资源在备库上没有额外动作。
 */
const TwoPhaseCallback twophase_standby_recover_callbacks[TWOPHASE_RM_MAX_ID + 1] =
{
	NULL,						/* END ID */
	lock_twophase_standby_recover,	/* Lock */
	NULL,						/* pgstat */
	NULL,						/* MultiXact */
	NULL						/* PredicateLock */
};
