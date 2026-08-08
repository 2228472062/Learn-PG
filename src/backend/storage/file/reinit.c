/*-------------------------------------------------------------------------
 *
 * reinit.c
 *	  Reinitialization of unlogged relations
 *
 * 【模块总览(中文)】
 * 本文件在数据库启动(崩溃恢复)时"重置非日志表(unlogged relations)"
 * 的内容,由 postmaster/startup.c 在恢复完成后调用
 * ResetUnloggedRelations()。
 *
 * 为什么需要重置:UNLOGGED 表的修改不写 WAL,崩溃后这些表的数据
 * 状态不可靠,因此 PostgreSQL 让每个 UNLOGGED 表在创建时附带一个
 * "init fork"(init 分支,文件名为 <OID>_init,存的是表结构空模板,
 * 见 access/heap/reloptions.c 与 smgr)。崩溃恢复时只需:
 * - CLEANUP(UNLOGGED_RELATION_CLEANUP):把每个存在 init fork 的表
 *   的所有 fork(主、vm、fsm 等)全部删除,只保留 init fork 本身;
 * - INIT(UNLOGGED_RELATION_INIT):把 init fork 复制回主 fork
 *   (对每个段号),恢复出"空表"形态;同时 fsync 新文件与目录,
 *   因为恢复期间没有检查点代劳。
 *
 * 实现要点:
 * - 遍历路径:$PGDATA/base(默认表空间) + pg_tblspc 下每个
 *   表空间的每个数字命名的 per-database 目录(跳过非数字目录,
 *   恰好也排除了 "." "..");
 * - CLEANUP 采用"两趟扫描 + 哈希表"避免 O(n^2):第一趟收集所有
 *   init fork 的 relfilenumber,第二趟删除匹配的非 init fork 文件;
 * - 文件名解析用 parse_filename_for_nontemp_relation():严格校验
 *   "<OID>[_fork][.段号]" 格式、拒绝前导零,保证同一 relnumber
 *   不可能由两种不同写法产生,避免误删;
 * - 全程使用独立内存上下文,结束时整体删除,杜绝内存泄漏;
 * - 用 begin_startup_progress_phase / ereport_startup_progress 上报
 *   启动进度(与 pg_ctl 的进度显示联动)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/file/reinit.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <unistd.h>

#include "common/relpath.h"
#include "postmaster/startup.h"
#include "storage/copydir.h"
#include "storage/fd.h"
#include "storage/reinit.h"
#include "utils/hsearch.h"
#include "utils/memutils.h"

/* ResetUnloggedRelations 的两个静态辅助函数原型(见各函数定义处注释) */
static void ResetUnloggedRelationsInTablespaceDir(const char *tsdirname,
												  int op);
static void ResetUnloggedRelationsInDbspaceDir(const char *dbspacedirname,
											   int op);

/* 哈希表条目:CLEANUP 第一趟扫描时记录"有 init fork 的表"的
 * RelFileNumber(即 relnumber,哈希键)。只存键不存别的数据,
 * 纯粹当作 OID 集合使用 */
typedef struct
{
	RelFileNumber relnumber;	/* hash key */
} unlogged_relation_entry;

/*
 * Reset unlogged relations from before the last restart.
 *
 * If op includes UNLOGGED_RELATION_CLEANUP, we remove all forks of any
 * relation with an "init" fork, except for the "init" fork itself.
 *
 * If op includes UNLOGGED_RELATION_INIT, we copy the "init" fork to the main
 * fork.
 */
/*
 * ResetUnloggedRelations (中文)重置上次崩溃残留的非日志表数据
 *
 * 【作用】启动(崩溃恢复)时由 startup 进程调用:遍历默认表空间
 * ($PGDATA/base)与所有非默认表空间(pg_tblspc 下的每个目录),
 * 对每个 per-database 目录执行 op 指定的操作:
 * - UNLOGGED_RELATION_CLEANUP:删除所有带 init fork 的表除 init
 *   fork 外的全部 fork 文件;
 * - UNLOGGED_RELATION_INIT  :把 init fork 复制成主 fork,重建空表。
 * 两操作可按位或同时指定,恢复流程通常两者都做。
 *
 * 【设计思想】
 * - 专门为临时工作创建内存上下文:文件名字符串、哈希表等中间对象
 *   全部在其中分配,函数返回前整体删除,防止启动阶段内存泄漏;
 * - 先处理 "base" 目录,再遍历 pg_tblspc 下各表空间目录:对
 *   表空间目录的遍历中,符号链接/乱入文件会被 ReadDir 带出但由
 *   下一层按"数字命名"过滤;
 * - 用 begin_startup_progress_phase 进入进度上报阶段,配合下层
 *   ereport_startup_progress 输出"正在重置(init/cleanup)..."信息。
 *
 * 【参数】op —— 操作位掩码(UNLOGGED_RELATION_CLEANUP 和/或
 * UNLOGGED_RELATION_INIT,定义见 reinit.h)。
 * 【返回值】无(致命错误直接报 ERROR,启动失败)。
 */
void
ResetUnloggedRelations(int op)
{
	char		temp_path[MAXPGPATH + sizeof(PG_TBLSPC_DIR) + sizeof(TABLESPACE_VERSION_DIRECTORY)];
	DIR		   *spc_dir;
	struct dirent *spc_de;
	MemoryContext tmpctx,
				oldctx;

	/* Log it. */
	elog(DEBUG1, "resetting unlogged relations: cleanup %d init %d",
		 (op & UNLOGGED_RELATION_CLEANUP) != 0,
		 (op & UNLOGGED_RELATION_INIT) != 0);

	/*
	 * Just to be sure we don't leak any memory, let's create a temporary
	 * memory context for this operation.
	 */
	tmpctx = AllocSetContextCreate(CurrentMemoryContext,
								   "ResetUnloggedRelations",
								   ALLOCSET_DEFAULT_SIZES);
	oldctx = MemoryContextSwitchTo(tmpctx);

	/* Prepare to report progress resetting unlogged relations. */
	begin_startup_progress_phase();

	/*
	 * First process unlogged files in pg_default ($PGDATA/base)
	 */
	ResetUnloggedRelationsInTablespaceDir("base", op);

	/*
	 * Cycle through directories for all non-default tablespaces.
	 */
	spc_dir = AllocateDir(PG_TBLSPC_DIR);

	while ((spc_de = ReadDir(spc_dir, PG_TBLSPC_DIR)) != NULL)
	{
		if (strcmp(spc_de->d_name, ".") == 0 ||
			strcmp(spc_de->d_name, "..") == 0)
			continue;

		snprintf(temp_path, sizeof(temp_path), "%s/%s/%s",
				 PG_TBLSPC_DIR, spc_de->d_name, TABLESPACE_VERSION_DIRECTORY);
		ResetUnloggedRelationsInTablespaceDir(temp_path, op);
	}

	FreeDir(spc_dir);

	/*
	 * Restore memory context.
	 */
	MemoryContextSwitchTo(oldctx);
	MemoryContextDelete(tmpctx);
}

/*
 * Process one tablespace directory for ResetUnloggedRelations
 */
/*
 * ResetUnloggedRelationsInTablespaceDir (中文)处理一个表空间目录
 *
 * 【作用】遍历给定表空间目录(它直接包含若干数字命名的 per-database
 * 子目录),对每个数据库目录递归调用下一层处理函数。
 *
 * 【容错设计】目录打不开且 errno 为 ENOENT 时只记 LOG 并返回,而不是
 * 让启动失败:可能发生在上一次 DROP TABLESPACE 在"删除目录"与
 * "删除 pg_tblspc 里的符号链接"两步之间崩溃的场景;其余错误(权限、
 * 磁盘等)由 ReadDir 抛出,启动失败。数据库子目录以"全部字符都是
 * 数字"识别——这同时天然跳过了 "." 与 ".."。
 *
 * 【进度上报】op 含 INIT 时报告 "resetting unlogged relations (init)",
 * 否则若含 CLEANUP 报告 "(cleanup)",信息里带当前处理路径,便于
 * 长时间重置时观察进度。
 *
 * 【参数】
 *   tsdirname —— 表空间目录的完整路径;
 *   op        —— 操作位掩码,透传给下层。
 * 【返回值】无。
 */
static void
ResetUnloggedRelationsInTablespaceDir(const char *tsdirname, int op)
{
	DIR		   *ts_dir;
	struct dirent *de;
	char		dbspace_path[MAXPGPATH * 2];

	ts_dir = AllocateDir(tsdirname);

	/*
	 * If we get ENOENT on a tablespace directory, log it and return.  This
	 * can happen if a previous DROP TABLESPACE crashed between removing the
	 * tablespace directory and removing the symlink in pg_tblspc.  We don't
	 * really want to prevent database startup in that scenario, so let it
	 * pass instead.  Any other type of error will be reported by ReadDir
	 * (causing a startup failure).
	 */
	if (ts_dir == NULL && errno == ENOENT)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not open directory \"%s\": %m",
						tsdirname)));
		return;
	}

	while ((de = ReadDir(ts_dir, tsdirname)) != NULL)
	{
		/*
		 * We're only interested in the per-database directories, which have
		 * numeric names.  Note that this code will also (properly) ignore "."
		 * and "..".
		 */
		if (strspn(de->d_name, "0123456789") != strlen(de->d_name))
			continue;

		snprintf(dbspace_path, sizeof(dbspace_path), "%s/%s",
				 tsdirname, de->d_name);

		if (op & UNLOGGED_RELATION_INIT)
			ereport_startup_progress("resetting unlogged relations (init), elapsed time: %ld.%02d s, current path: %s",
									 dbspace_path);
		else if (op & UNLOGGED_RELATION_CLEANUP)
			ereport_startup_progress("resetting unlogged relations (cleanup), elapsed time: %ld.%02d s, current path: %s",
									 dbspace_path);

		ResetUnloggedRelationsInDbspaceDir(dbspace_path, op);
	}

	FreeDir(ts_dir);
}

/*
 * Process one per-dbspace directory for ResetUnloggedRelations
 */
/*
 * ResetUnloggedRelationsInDbspaceDir (中文)处理一个 per-database 目录
 *
 * 【作用】对单个数据库目录执行 CLEANUP/INIT 两种操作(可同时出现):
 * - CLEANUP 是"两趟扫描":第一趟把所有 init fork 文件的
 *   RelFileNumber 收进哈希表(只要 init fork 存在,该表就必须重置);
 *   若一个都没有,直接返回(无需清理)。第二趟删除目录中所有
 *   "与哈希表键匹配且不是 init fork"的关系文件;
 * - INIT 在 CLEANUP 之后执行:逐个把 init fork 复制为对应段号的主
 *   fork 文件(copy_file),然后单独再扫一遍目录,对每个新建的主
 *   fork 文件做 fsync(单独一趟是为了让内核把前面 copy_file 触发
 *   的全部数据冲刷一次性完成,尤其是元数据部分),最后 fsync
 *   数据库目录本身(保证文件创建/删除的目录项已落盘)。
 *
 * 【设计思想】
 * - CLEANUP 用哈希表(而非数组/链表)收集 OID:同一个表空间里可能
 *   有大量 unlogged 表,线性查找会退化为 O(n^2);
 * - 复制用 copydir.c 的 copy_file(其中已含 pg_flush_data),文件
 *   的持久化由后续独立一趟的 fsync 兜底——恢复期间没有检查点会
 *   替我们做这件事;
 * - 只做 CLEANUP 时不 fsync 目录:若恢复在 INIT 之前崩溃,下次启动
 *   会重做整个清理步骤,所以此刻的目录项是否持久化无关紧要。
 *
 * 【参数】
 *   dbspacedirname —— 数据库目录的完整路径;
 *   op             —— 操作位掩码(必须至少含一种操作)。
 * 【返回值】无(失败报 ERROR)。
 */
static void
ResetUnloggedRelationsInDbspaceDir(const char *dbspacedirname, int op)
{
	DIR		   *dbspace_dir;
	struct dirent *de;
	char		rm_path[MAXPGPATH * 2];

	/* Caller must specify at least one operation. */
	Assert((op & (UNLOGGED_RELATION_CLEANUP | UNLOGGED_RELATION_INIT)) != 0);

	/*
	 * Cleanup is a two-pass operation.  First, we go through and identify all
	 * the files with init forks.  Then, we go through again and nuke
	 * everything with the same OID except the init fork.
	 */
	if ((op & UNLOGGED_RELATION_CLEANUP) != 0)
	{
		HTAB	   *hash;
		HASHCTL		ctl;

		/*
		 * It's possible that someone could create a ton of unlogged relations
		 * in the same database & tablespace, so we'd better use a hash table
		 * rather than an array or linked list to keep track of which files
		 * need to be reset.  Otherwise, this cleanup operation would be
		 * O(n^2).
		 */
		ctl.keysize = sizeof(Oid);
		ctl.entrysize = sizeof(unlogged_relation_entry);
		ctl.hcxt = CurrentMemoryContext;
		hash = hash_create("unlogged relation OIDs", 32, &ctl,
						   HASH_ELEM | HASH_BLOBS | HASH_CONTEXT);

		/* Scan the directory. */
		dbspace_dir = AllocateDir(dbspacedirname);
		while ((de = ReadDir(dbspace_dir, dbspacedirname)) != NULL)
		{
			ForkNumber	forkNum;
			unsigned	segno;
			unlogged_relation_entry ent;

			/* Skip anything that doesn't look like a relation data file. */
			if (!parse_filename_for_nontemp_relation(de->d_name,
													 &ent.relnumber,
													 &forkNum, &segno))
				continue;

			/* Also skip it unless this is the init fork. */
			if (forkNum != INIT_FORKNUM)
				continue;

			/*
			 * Put the RelFileNumber into the hash table, if it isn't already.
			 */
			(void) hash_search(hash, &ent, HASH_ENTER, NULL);
		}

		/* Done with the first pass. */
		FreeDir(dbspace_dir);

		/*
		 * If we didn't find any init forks, there's no point in continuing;
		 * we can bail out now.
		 */
		if (hash_get_num_entries(hash) == 0)
		{
			hash_destroy(hash);
			return;
		}

		/*
		 * Now, make a second pass and remove anything that matches.
		 */
		dbspace_dir = AllocateDir(dbspacedirname);
		while ((de = ReadDir(dbspace_dir, dbspacedirname)) != NULL)
		{
			ForkNumber	forkNum;
			unsigned	segno;
			unlogged_relation_entry ent;

			/* Skip anything that doesn't look like a relation data file. */
			if (!parse_filename_for_nontemp_relation(de->d_name,
													 &ent.relnumber,
													 &forkNum, &segno))
				continue;

			/* We never remove the init fork. */
			if (forkNum == INIT_FORKNUM)
				continue;

			/*
			 * See whether the OID portion of the name shows up in the hash
			 * table.  If so, nuke it!
			 */
			if (hash_search(hash, &ent, HASH_FIND, NULL))
			{
				snprintf(rm_path, sizeof(rm_path), "%s/%s",
						 dbspacedirname, de->d_name);
				if (unlink(rm_path) < 0)
					ereport(ERROR,
							(errcode_for_file_access(),
							 errmsg("could not remove file \"%s\": %m",
									rm_path)));
				else
					elog(DEBUG2, "unlinked file \"%s\"", rm_path);
			}
		}

		/* Cleanup is complete. */
		FreeDir(dbspace_dir);
		hash_destroy(hash);
	}

	/*
	 * Initialization happens after cleanup is complete: we copy each init
	 * fork file to the corresponding main fork file.  Note that if we are
	 * asked to do both cleanup and init, we may never get here: if the
	 * cleanup code determines that there are no init forks in this dbspace,
	 * it will return before we get to this point.
	 */
	if ((op & UNLOGGED_RELATION_INIT) != 0)
	{
		/* Scan the directory. */
		dbspace_dir = AllocateDir(dbspacedirname);
		while ((de = ReadDir(dbspace_dir, dbspacedirname)) != NULL)
		{
			ForkNumber	forkNum;
			RelFileNumber relNumber;
			unsigned	segno;
			char		srcpath[MAXPGPATH * 2];
			char		dstpath[MAXPGPATH];

			/* Skip anything that doesn't look like a relation data file. */
			if (!parse_filename_for_nontemp_relation(de->d_name, &relNumber,
													 &forkNum, &segno))
				continue;

			/* Also skip it unless this is the init fork. */
			if (forkNum != INIT_FORKNUM)
				continue;

			/* Construct source pathname. */
			snprintf(srcpath, sizeof(srcpath), "%s/%s",
					 dbspacedirname, de->d_name);

			/* Construct destination pathname. */
			if (segno == 0)
				snprintf(dstpath, sizeof(dstpath), "%s/%u",
						 dbspacedirname, relNumber);
			else
				snprintf(dstpath, sizeof(dstpath), "%s/%u.%u",
						 dbspacedirname, relNumber, segno);

			/* OK, we're ready to perform the actual copy. */
			elog(DEBUG2, "copying %s to %s", srcpath, dstpath);
			copy_file(srcpath, dstpath);
		}

		FreeDir(dbspace_dir);

		/*
		 * copy_file() above has already called pg_flush_data() on the files
		 * it created. Now we need to fsync those files, because a checkpoint
		 * won't do it for us while we're in recovery. We do this in a
		 * separate pass to allow the kernel to perform all the flushes
		 * (especially the metadata ones) at once.
		 */
		dbspace_dir = AllocateDir(dbspacedirname);
		while ((de = ReadDir(dbspace_dir, dbspacedirname)) != NULL)
		{
			RelFileNumber relNumber;
			ForkNumber	forkNum;
			unsigned	segno;
			char		mainpath[MAXPGPATH];

			/* Skip anything that doesn't look like a relation data file. */
			if (!parse_filename_for_nontemp_relation(de->d_name, &relNumber,
													 &forkNum, &segno))
				continue;

			/* Also skip it unless this is the init fork. */
			if (forkNum != INIT_FORKNUM)
				continue;

			/* Construct main fork pathname. */
			if (segno == 0)
				snprintf(mainpath, sizeof(mainpath), "%s/%u",
						 dbspacedirname, relNumber);
			else
				snprintf(mainpath, sizeof(mainpath), "%s/%u.%u",
						 dbspacedirname, relNumber, segno);

			fsync_fname(mainpath, false);
		}

		FreeDir(dbspace_dir);

		/*
		 * Lastly, fsync the database directory itself, ensuring the
		 * filesystem remembers the file creations and deletions we've done.
		 * We don't bother with this during a call that does only
		 * UNLOGGED_RELATION_CLEANUP, because if recovery crashes before we
		 * get to doing UNLOGGED_RELATION_INIT, we'll redo the cleanup step
		 * too at the next startup attempt.
		 */
		fsync_fname(dbspacedirname, true);
	}
}

/*
 * Basic parsing of putative relation filenames.
 *
 * This function returns true if the file appears to be in the correct format
 * for a non-temporary relation and false otherwise.
 *
 * If it returns true, it sets *relnumber, *fork, and *segno to the values
 * extracted from the filename. If it returns false, these values are set to
 * InvalidRelFileNumber, InvalidForkNumber, and 0, respectively.
 */
/*
 * parse_filename_for_nontemp_relation (中文)解析关系数据文件名
 *
 * 【作用】判断一个文件名是否符合"非临时关系文件"的命名规范
 * "<RelFileNumber>[_<fork>][.<segno>]",符合则把解析出的
 * relnumber/fork/段号写入输出参数。它是 reinit.c 一切文件筛选的
 * 前提:先确认"这确实是个关系文件",再判断要不要动它。
 *
 * 【设计思想】格式校验非常严格,核心目的是杜绝歧义:
 * - 关系文件名的首字符必须是 1~9(前导零一律拒绝)。这样对任意
 *   一个 relnumber 值,最多只有一种写法能解析出它(否则像
 *   "0017.3" 这样的怪名可能与 relfilenode 17 的第 3 段混淆,
 *   误删风险不可接受);
 * - 数值段用 strtoul 解析并检查 errno/溢出,值域限制在
 *   PG_UINT32_MAX(RelFileNumber 的宽度)内;
 * - fork 名必须命中已知后缀(forkname_chars,如 _init/_vm/_fsm);
 * - 整个字符串必须被消费完,结尾不允许有任何多余字符。
 *
 * 【参数】
 *   name      —— 待解析的文件名(不含目录);
 *   relnumber —— 输出:关系的 RelFileNumber;
 *   fork      —— 输出:ForkNumber(文件名无 fork 后缀时为 MAIN_FORKNUM);
 *   segno     —— 输出:段号(无段后缀时为 0)。
 * 【返回值】true 表示文件名是规范的关系文件且输出参数有效;
 * false 表示不是,此时三个输出参数分别为
 * InvalidRelFileNumber / InvalidForkNumber / 0。
 */
bool
parse_filename_for_nontemp_relation(const char *name, RelFileNumber *relnumber,
									ForkNumber *fork, unsigned *segno)
{
	unsigned long n,
				s;
	ForkNumber	f;
	char	   *endp;

	*relnumber = InvalidRelFileNumber;
	*fork = InvalidForkNumber;
	*segno = 0;

	/*
	 * Relation filenames should begin with a digit that is not a zero. By
	 * rejecting cases involving leading zeroes, the caller can assume that
	 * there's only one possible string of characters that could have produced
	 * any given value for *relnumber.
	 *
	 * (To be clear, we don't expect files with names like 0017.3 to exist at
	 * all -- but if 0017.3 does exist, it's a non-relation file, not part of
	 * the main fork for relfilenode 17.)
	 */
	if (name[0] < '1' || name[0] > '9')
		return false;

	/*
	 * Parse the leading digit string. If the value is out of range, we
	 * conclude that this isn't a relation file at all.
	 */
	errno = 0;
	n = strtoul(name, &endp, 10);
	if (errno || name == endp || n <= 0 || n > PG_UINT32_MAX)
		return false;
	name = endp;

	/* Check for a fork name. */
	if (*name != '_')
		f = MAIN_FORKNUM;
	else
	{
		int			forkchar;

		forkchar = forkname_chars(name + 1, &f);
		if (forkchar <= 0)
			return false;
		name += forkchar + 1;
	}

	/* Check for a segment number. */
	if (*name != '.')
		s = 0;
	else
	{
		/* Reject leading zeroes, just like we do for RelFileNumber. */
		if (name[1] < '1' || name[1] > '9')
			return false;

		errno = 0;
		s = strtoul(name + 1, &endp, 10);
		if (errno || name + 1 == endp || s <= 0 || s > PG_UINT32_MAX)
			return false;
		name = endp;
	}

	/* Now we should be at the end. */
	if (*name != '\0')
		return false;

	/* Set out parameters and return. */
	*relnumber = (RelFileNumber) n;
	*fork = f;
	*segno = (unsigned) s;
	return true;
}
