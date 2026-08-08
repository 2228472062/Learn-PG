/*-------------------------------------------------------------------------
 *
 * fileset.c
 *	  Management of named temporary files.
 *
 * 【模块总览(中文)】
 * 本文件实现 FileSet(临时文件集合):为一组临时文件提供"命名空间"
 * (可以想象成一个逻辑目录),使得文件可以按名字查找、反复打开/关闭,
 * 且能跨事务存活。
 *
 * 为什么需要它:普通的临时文件(OpenTemporaryFile)随着事务结束就自动
 * 清理了,且没有名字、无法被其他进程找到;而排序/哈希/并行执行等场景
 * 需要"有名字、可复用、可跨事务、甚至可被其他后端共享"的临时文件。
 * FileSet 就是为满足这些需求而生的中层抽象:底层文件仍由 fd.c 的
 * PathNameCreateTemporaryFile/PathNameOpenTemporaryFile 管理(受 VFD
 * 限额与"退出时自动清理"的保护),但文件放在一组按固定命名规则生成的
 * 目录里:
 *   <表空间临时目录>/pgsql_tmp<creator_pid>.<number>.fileset/<文件名>
 * 其中 creator_pid 是创建者进程的 PID,number 是本进程内递增的序号,
 * 二者组合保证不同创建者、不同集合之间绝不冲突。
 *
 * 生命周期管理:目录由创建者负责显式删除(FileSetDelete /
 * FileSetDeleteAll),调用方负责在不再需要时清理;进程异常退出时,
 * fd.c 的临时目录清理机制(以 PG_TEMP_FILE_PREFIX 识别)会把整个
 * 目录连同文件一起收掉,因此不会泄漏。
 *
 * 表空间分布:文件可以分散存放在 temp_tablespaces 配置的多个表空间中
 * (每个文件按名字哈希选择一个表空间),以摊薄 I/O 压力;默认表空间
 * (InvalidOid)在初始化时被解析成具体 OID,保证所有使用者观点一致。
 *
 * 上层使用者:单个后端的 FileSet(本文件)、多后端共享的 SharedFileSet
 * (sharedfileset.c)、以及基于 FileSet 段文件实现超大临时文件的 BufFile
 * (buffile.c)都构建在这套 API 之上。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/file/fileset.c
 *
 * FileSets provide a temporary namespace (think directory) so that files can
 * be discovered by name.
 *
 * FileSets can be used by backends when the temporary files need to be
 * opened/closed multiple times and the underlying files need to survive across
 * transactions.
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include <limits.h>

#include "commands/tablespace.h"
#include "common/file_utils.h"
#include "common/hashfn.h"
#include "miscadmin.h"
#include "storage/fileset.h"

static void FileSetPath(char *path, FileSet *fileset, Oid tablespace);
static void FilePath(char *path, FileSet *fileset, const char *name);
static Oid	ChooseTablespace(const FileSet *fileset, const char *name);

/*
 * Initialize a space for temporary files. This API can be used by shared
 * fileset as well as if the temporary files are used only by single backend
 * but the files need to be opened and closed multiple times and also the
 * underlying files need to survive across transactions.
 *
 * The callers are expected to explicitly remove such files by using
 * FileSetDelete/FileSetDeleteAll.
 *
 * Files will be distributed over the tablespaces configured in
 * temp_tablespaces.
 *
 * Under the covers the set is one or more directories which will eventually
 * be deleted.
 */
/*
 * FileSetInit (中文)初始化一个临时文件集合:分配名称空间并确定用哪些表空间
 *
 * 【作用】为 FileSet 分配唯一标识(creator_pid + number)并固化"文件应该
 * 放在哪些表空间",之后所有文件路径都基于这两个要素派生。既用于单后端
 * 场景,也作为 SharedFileSet 的底层初始化(见 sharedfileset.c)。
 *
 * 【设计思想】
 * - 每个 FileSet 在磁盘上对应一组目录(每个表空间一个),目录名含
 *   creator_pid 与 number,因此任何两个 FileSet 的目录互不相同,
 *   不存在命名冲突;
 * - 表空间列表在初始化时立即固化:先调用 PrepareTempTablespaces()
 *   把 temp_tablespaces GUC 解析出来(可能触发目录创建/权限检查),
 *   再用 GetTempTablespaces() 取 OID 列表;
 * - GUC 为空时退回当前数据库的默认表空间;列表中的 InvalidOid 条目
 *   (表示"使用数据库默认表空间")也在此时替换成具体 OID——这是为了让
 *   所有使用者(比如并行查询里的所有进程,它们各自的 GUC 解析结果可能
 *   不同)对"文件实际放在哪"达成一致。
 *
 * 【参数】fileset —— 待初始化的 FileSet 结构(存储由调用方提供,通常
 * 位于长期存活的内存上下文,如 DSM 段或专用上下文)。
 * 【返回值】无。
 */
void
FileSetInit(FileSet *fileset)
{
	/* 进程内静态计数器:为每个 FileSet 生成进程内唯一的序号(回绕到
	 * INT_MAX 时折返,与 creator_pid 组合后仍足以避免冲突) */
	static uint32 counter = 0;

	fileset->creator_pid = MyProcPid;
	fileset->number = counter;
	counter = (counter + 1) % INT_MAX;

	/* Capture the tablespace OIDs so that all backends agree on them. */
	PrepareTempTablespaces();
	fileset->ntablespaces =
		GetTempTablespaces(&fileset->tablespaces[0],
						   lengthof(fileset->tablespaces));
	if (fileset->ntablespaces == 0)
	{
		/* If the GUC is empty, use current database's default tablespace */
		fileset->tablespaces[0] = MyDatabaseTableSpace;
		fileset->ntablespaces = 1;
	}
	else
	{
		int			i;

		/*
		 * An entry of InvalidOid means use the default tablespace for the
		 * current database.  Replace that now, to be sure that all users of
		 * the FileSet agree on what to do.
		 */
		for (i = 0; i < fileset->ntablespaces; i++)
		{
			if (fileset->tablespaces[i] == InvalidOid)
				fileset->tablespaces[i] = MyDatabaseTableSpace;
		}
	}
}

/*
 * Create a new file in the given set.
 */
/*
 * FileSetCreate (中文)在文件集合中创建一个新的临时文件
 *
 * 【作用】按"文件名 -> 表空间 -> 目录 -> 文件"的规则构造完整路径,并
 * 在 fd.c 的临时文件管理下创建文件(以 O_CREAT 打开,成功返回 VFD
 * 句柄)。若首次使用某个表空间导致目录尚不存在,则按需创建目录后重试。
 *
 * 【设计思想】"失败时按需建目录"与"先直接创建、失败再建目录重试"
 * 的策略,使初始化顺序不再重要:无论调用方是否先调用了
 * PathNameCreateTemporaryDir,首次创建文件总能成功,且避免了每个文件
 * 创建前都白白做一次 stat。
 *
 * 【参数】
 *   fileset —— 目标文件集合;
 *   name    —— 文件名(仅文件名本身,不含路径)。
 * 【返回值】新文件的 VFD 句柄(File,>0 表示成功;失败报 ERROR)。
 */
File
FileSetCreate(FileSet *fileset, const char *name)
{
	char		path[MAXPGPATH];
	File		file;

	FilePath(path, fileset, name);
	file = PathNameCreateTemporaryFile(path, false);

	/* If we failed, see if we need to create the directory on demand. */
	if (file <= 0)
	{
		char		tempdirpath[MAXPGPATH];
		char		filesetpath[MAXPGPATH];
		Oid			tablespace = ChooseTablespace(fileset, name);

		TempTablespacePath(tempdirpath, tablespace);
		FileSetPath(filesetpath, fileset, tablespace);
		PathNameCreateTemporaryDir(tempdirpath, filesetpath);
		file = PathNameCreateTemporaryFile(path, true);
	}

	return file;
}

/*
 * Open a file that was created with FileSetCreate()
 */
/*
 * FileSetOpen (中文)按名字打开文件集合中已有的临时文件
 *
 * 【作用】根据文件名计算出完整路径,用指定的 mode(通常是 O_RDONLY)
 * 打开之。文件可能由本进程先前创建,也可能由共享 FileSet 场景下
 * (SharedFileSet)的其他后端创建——路径规则相同,所以都能找到。
 *
 * 【参数】
 *   fileset —— 目标文件集合;
 *   name    —— 文件名;
 *   mode    —— open(2) 的标志位。
 * 【返回值】打开的 VFD 句柄;文件不存在时返回 <= 0(不报错,由调用方
 * 决定如何处理,例如 BufFileOpenFileSet 用它探测"还有没有下一个段")。
 */
File
FileSetOpen(FileSet *fileset, const char *name, int mode)
{
	char		path[MAXPGPATH];
	File		file;

	FilePath(path, fileset, name);
	file = PathNameOpenTemporaryFile(path, mode);

	return file;
}

/*
 * Delete a file that was created with FileSetCreate().
 *
 * Return true if the file existed, false if didn't.
 */
/*
 * FileSetDelete (中文)删除文件集合中指定的临时文件
 *
 * 【作用】删除一个由 FileSetCreate 创建的文件。返回文件是否存在,
 * 便于调用方决定是否报错:error_on_failure 为 true 时,若文件实际
 * 不存在(比如崩溃重启后残留目录已被清理),PathNameDeleteTemporaryFile
 * 会按约定报错,调用方可根据返回值自行处理。
 *
 * 【参数】
 *   fileset           —— 目标文件集合;
 *   name              —— 文件名;
 *   error_on_failure  —— true 时文件缺失会作为错误处理(见 fd.c)。
 * 【返回值】true 表示文件确实存在且已删除;false 表示本来就不存在。
 */
bool
FileSetDelete(FileSet *fileset, const char *name,
			  bool error_on_failure)
{
	char		path[MAXPGPATH];

	FilePath(path, fileset, name);

	return PathNameDeleteTemporaryFile(path, error_on_failure);
}

/*
 * Delete all files in the set.
 */
/*
 * FileSetDeleteAll (中文)删除文件集合的全部目录(连带其中的所有文件)
 *
 * 【作用】把这个 FileSet 在"每个表空间"下创建的目录整目录删除(递归,
 * 见 fd.c 的 PathNameDeleteTemporaryDir)。常用于错误清理路径
 * (error cleanup),因此不主动报错,但遇到 I/O 错误会打 LOG 日志。
 *
 * 【设计思想】按目录粒度清理而非逐个删文件:目录名携带集合的唯一
 * 标识,删目录即可安全地覆盖该集合的所有文件;同时只删除本集合创建
 * 的目录,不会误伤同表空间下的其他临时文件。
 *
 * 【参数】fileset —— 目标文件集合。
 * 【返回值】无。
 */
void
FileSetDeleteAll(FileSet *fileset)
{
	char		dirpath[MAXPGPATH];
	int			i;

	/*
	 * Delete the directory we created in each tablespace.  Doesn't fail
	 * because we use this in error cleanup paths, but can generate LOG
	 * message on IO error.
	 */
	for (i = 0; i < fileset->ntablespaces; ++i)
	{
		FileSetPath(dirpath, fileset, fileset->tablespaces[i]);
		PathNameDeleteTemporaryDir(dirpath);
	}
}

/*
 * Build the path for the directory holding the files backing a FileSet in a
 * given tablespace.
 */
/*
 * FileSetPath (中文)构造文件集合在某个表空间下的目录完整路径
 *
 * 【作用】目录名规则:<表空间临时目录>/pgsql_tmp<creator_pid>.<number>
 * .fileset。PG_TEMP_FILE_PREFIX(pgsql_tmp)前缀是 fd.c 进程退出清理
 * 机制的识别标志,保证异常退出后残留文件能被自动回收。
 *
 * 【参数】
 *   path      —— 输出缓冲区(至少 MAXPGPATH 字节);
 *   fileset   —— 文件集合;
 *   tablespace —— 表空间 OID。
 * 【返回值】无(结果写入 path)。
 */
static void
FileSetPath(char *path, FileSet *fileset, Oid tablespace)
{
	char		tempdirpath[MAXPGPATH];

	TempTablespacePath(tempdirpath, tablespace);
	snprintf(path, MAXPGPATH, "%s/%s%lu.%u.fileset",
			 tempdirpath, PG_TEMP_FILE_PREFIX,
			 (unsigned long) fileset->creator_pid, fileset->number);
}

/*
 * Sorting has to determine which tablespace a given temporary file belongs in.
 */
/*
 * ChooseTablespace (中文)为指定文件名挑选存放它的表空间
 *
 * 【作用】按文件名的哈希值对表空间数量取模,得到一个"看似随机但
 * 确定"的表空间:同一个名字永远落在同一个表空间,从而同一个 BufFile
 * 的所有段文件会被均匀散布到多个表空间(见 buffile.c 对超大临时文件
 * 分段的需求),同时又摊薄各表空间的 I/O 压力。
 *
 * 【设计思想】用文件名的哈希而非轮询/顺序分配:这样不同进程对同一
 * 文件名的计算结论一致(文件可被其他后端重新打开),且并发创建互不
 * 干扰、无需共享分配状态。
 *
 * 【参数】
 *   fileset —— 文件集合;
 *   name    —— 文件名。
 * 【返回值】选中的表空间 OID。
 */
static Oid
ChooseTablespace(const FileSet *fileset, const char *name)
{
	uint32		hash = hash_bytes((const unsigned char *) name, strlen(name));

	return fileset->tablespaces[hash % fileset->ntablespaces];
}

/*
 * Compute the full path of a file in a FileSet.
 */
/*
 * FilePath (中文)构造文件集合中某个文件的完整路径
 *
 * 【作用】先按文件名选表空间、构造集合目录路径,再拼上文件名,
 * 得到文件在磁盘上的最终完整路径。文件集合的所有路径计算
 * (FileSetCreate/FileSetOpen/FileSetDelete)最终都汇聚到本函数,
 * 保证路径规则唯一、一致。
 *
 * 【参数】
 *   path    —— 输出缓冲区(至少 MAXPGPATH 字节);
 *   fileset —— 文件集合;
 *   name    —— 文件名。
 * 【返回值】无(结果写入 path)。
 */
static void
FilePath(char *path, FileSet *fileset, const char *name)
{
	char		dirpath[MAXPGPATH];

	FileSetPath(dirpath, fileset, ChooseTablespace(fileset, name));
	snprintf(path, MAXPGPATH, "%s/%s", dirpath, name);
}
