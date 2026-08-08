/*-------------------------------------------------------------------------
 *
 * sharedfileset.c
 *	  Shared temporary file management.
 *
 * 【模块总览(中文)】
 * 本文件实现 SharedFileSet(共享文件集合):在 FileSet(见 fileset.c)
 * 之上增加"多后端共享"语义,是并行查询(parallel query)中共享临时
 * 文件的基础设施。
 *
 * 要解决的问题:并行工作进程彼此隔离,各自的临时文件互不可见;而
 * 并行算子(如并行 Hash Join 的共享哈希文件、并行排序)需要所有参与
 * 进程读写同一组临时文件。SharedFileSet 让一组进程通过同一个 DSM
 * (dynamic shared memory)段持有同一个 SharedFileSet 结构,从而共享
 * 同一命名空间(目录名来自 FileSet 的 creator_pid+number,见
 * fileset.c)。
 *
 * 生命周期:SharedFileSet 整体存放在 DSM 段中,段随最后一个使用者
 * detach 而销毁。为此引入引用计数(refcnt,自旋锁保护):
 * - 创建者(Init)refcnt 置 1,并注册 on_dsm_detach 回调;
 * - 每个加入者(Attach)把 refcnt 加 1 并注册同样的回调;
 * - 谁先 detach,谁就把 refcnt 减 1;减到 0 的最后一个进程负责
 *   递归删除全部文件目录(FileSetDeleteAll)。
 * 这样"文件存活到最后一个使用者退出"的语义由 DSM 机制自然保证,
 * 中途任何进程崩溃/回滚,也会因 detach 回调而被清理,不会泄漏。
 *
 * 注意:目录的物理所有权始终在"引用计数归零的瞬间"被移交——目录名
 * 对所有参与者可见、可打开,但删除动作只有一次,由最后离开者执行。
 * 目录清理路径与 fd.c 的进程退出清理机制(PG_TEMP_FILE_PREFIX 前缀
 * 识别)互为后备。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/file/sharedfileset.c
 *
 * SharedFileSets provide a temporary namespace (think directory) so that
 * files can be discovered by name, and a shared ownership semantics so that
 * shared files survive until the last user detaches.
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <limits.h>

#include "storage/dsm.h"
#include "storage/sharedfileset.h"

/* SharedFileSetOnDetach 回调的函数原型(见函数定义处的详细注释) */
static void SharedFileSetOnDetach(dsm_segment *segment, Datum datum);

/*
 * Initialize a space for temporary files that can be opened by other backends.
 * Other backends must attach to it before accessing it.  Associate this
 * SharedFileSet with 'seg'.  Any contained files will be deleted when the
 * last backend detaches.
 *
 * Under the covers the set is one or more directories which will eventually
 * be deleted.
 */
/*
 * SharedFileSetInit (中文)初始化共享文件集合,并把它绑定到给定的 DSM 段
 *
 * 【作用】由并行查询的发起进程(leader)创建:完成 FileSet 的底层
 * 初始化(命名空间 + 表空间选择),把引用计数置为 1(创建者自己算
 * 一个引用),并在 DSM 段上注册 detach 清理回调。
 *
 * 【设计思想】
 * - SharedFileSet 结构本身由调用方(通常是 leader)提前分配在 DSM
 *   段中,其他进程 attach 该段后即可访问同一份结构;
 * - 引用计数从 1 起步,保证"即使没有其他进程 attach,段销毁时也会
 *   触发一次完整的清理";
 * - 回调注册到 DSM 段上而非数据库会话上:不管进程是正常退出还是
 *   崩溃,段 detach 机制都会执行回调,确保文件不会无限期残留。
 *
 * 【参数】
 *   fileset —— 指向 DSM 段内 SharedFileSet 结构的指针(存储由调用方
 *              负责分配);
 *   seg     —— 承载该结构的 DSM 段;为 NULL 时跳过回调注册(单进程
 *              使用场景,不依赖 DSM)。
 * 【返回值】无。
 */
void
SharedFileSetInit(SharedFileSet *fileset, dsm_segment *seg)
{
	/* Initialize the shared fileset specific members. */
	SpinLockInit(&fileset->mutex);
	fileset->refcnt = 1;

	/* Initialize the fileset. */
	FileSetInit(&fileset->fs);

	/* Register our cleanup callback. */
	if (seg)
		on_dsm_detach(seg, SharedFileSetOnDetach, PointerGetDatum(fileset));
}

/*
 * Attach to a set of directories that was created with SharedFileSetInit.
 */
/*
 * SharedFileSetAttach (中文)让一个后端加入(attach)既有的共享文件集合
 *
 * 【作用】并行工作进程在 attach 到承载 SharedFileSet 的 DSM 段后调用:
 * 原子地把引用计数加 1,表示"我也在使用这个集合",并注册自己的
 * detach 清理回调。此后该进程就可以用 FileSet 的 API 打开/创建集合
 * 中的文件。
 *
 * 【设计思想】引用计数在自旋锁保护下先检查再递增(refcnt == 0 表示
 * 集合已被最后的使用者销毁并开始清理,此时加入会失败并报错),保证
 * "销毁与加入"两个并发操作不会交错出悬挂引用。计数为 0 时拒绝 attach
 * 而不是等待,因为段即将消失,继续使用集合必然出错,尽早失败更安全。
 *
 * 【参数】
 *   fileset —— DSM 段内已初始化好的 SharedFileSet;
 *   seg     —— 承载它的 DSM 段(用于注册回调)。
 * 【返回值】无(集合已销毁时抛 ERROR)。
 */
void
SharedFileSetAttach(SharedFileSet *fileset, dsm_segment *seg)
{
	bool		success;

	SpinLockAcquire(&fileset->mutex);
	if (fileset->refcnt == 0)
		success = false;
	else
	{
		++fileset->refcnt;
		success = true;
	}
	SpinLockRelease(&fileset->mutex);

	if (!success)
		ereport(ERROR,
				(errcode(ERRCODE_OBJECT_NOT_IN_PREREQUISITE_STATE),
				 errmsg("could not attach to a SharedFileSet that is already destroyed")));

	/* Register our cleanup callback. */
	on_dsm_detach(seg, SharedFileSetOnDetach, PointerGetDatum(fileset));
}

/*
 * Delete all files in the set.
 */
/*
 * SharedFileSetDeleteAll (中文)主动删除共享文件集合的全部文件
 *
 * 【作用】直接委托给 FileSetDeleteAll,按目录递归删除集合在全部
 * 表空间下的文件。与"最后 detach 者自动清理"相比,这是主动的
 * 提前清理手段(例如并行算子结束后立即回收磁盘空间,不必等段
 * 销毁)。删除后集合仍可继续使用(只是文件没了)。
 *
 * 【参数】fileset —— 共享文件集合。
 * 【返回值】无。
 */
void
SharedFileSetDeleteAll(SharedFileSet *fileset)
{
	FileSetDeleteAll(&fileset->fs);
}

/*
 * Callback function that will be invoked when this backend detaches from a
 * DSM segment holding a SharedFileSet that it has created or attached to.  If
 * we are the last to detach, then try to remove the directories and
 * everything in them.  We can't raise an error on failures, because this runs
 * in error cleanup paths.
 */
/*
 * SharedFileSetOnDetach (中文)DSM 段 detach 时的清理回调(引用计数减一)
 *
 * 【作用】每个创建者/加入者都在 SharedFileSetInit/SharedFileSetAttach
 * 时通过 on_dsm_detach 注册本函数。当本进程与承载该集合的 DSM 段
 * 分离(正常退出、事务结束、崩溃清理等任何路径)时被调用:把引用
 * 计数减 1;若减到 0,说明自己是最后一个使用者,负责递归删除集合
 * 的全部目录与文件。
 *
 * 【设计思想】
 * - 引用计数与删除动作分开执行:先持锁减计数并决定"是否由我删除",
 *   释放锁后再做昂贵的 I/O 删除。整个函数仍处于 attach 状态
 *   (回调期间段未被真正释放),因此访问 fileset 结构是安全的;
 * - 本函数运行在错误清理路径上,绝不能抛错——删除失败只打日志,
 *   残留文件交由 fd.c 的进程退出临时目录清理兜底;
 * - 保证"删一次":即使多个进程几乎同时 detach,也只有计数减到 0
 *   的那一个执行 FileSetDeleteAll。
 *
 * 【参数】
 *   segment —— 被 detach 的 DSM 段(本实现未使用);
 *   datum   —— on_dsm_detach 传入的 SharedFileSet 指针。
 * 【返回值】无。
 */
static void
SharedFileSetOnDetach(dsm_segment *segment, Datum datum)
{
	bool		unlink_all = false;
	SharedFileSet *fileset = (SharedFileSet *) DatumGetPointer(datum);

	SpinLockAcquire(&fileset->mutex);
	Assert(fileset->refcnt > 0);
	if (--fileset->refcnt == 0)
		unlink_all = true;
	SpinLockRelease(&fileset->mutex);

	/*
	 * If we are the last to detach, we delete the directory in all
	 * tablespaces.  Note that we are still actually attached for the rest of
	 * this function so we can safely access its data.
	 */
	if (unlink_all)
		FileSetDeleteAll(&fileset->fs);
}
