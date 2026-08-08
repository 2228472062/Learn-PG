/*-------------------------------------------------------------------------
 *
 * copydir.c
 *	  copies a directory
 *
 * 【模块总览(中文)】
 * 本文件提供目录复制功能:递归地把一个目录的内容(含子目录与普通
 * 文件)复制到另一个目录。核心用途是 CREATE DATABASE:新数据库的
 * 数据目录通过复制模板数据库(template0 等)得到。
 *
 * 三个要点:
 * 1) 复制策略由 GUC file_copy_method 控制(见 copydir.h 的
 *    FileCopyMethod 枚举):
 *    - FILE_COPY_METHOD_COPY :普通复制,按固定大小缓冲区循环
 *      read/write(copy_file);
 *    - FILE_COPY_METHOD_CLONE:尽力使用文件系统级"克隆/写时复制"
 *      机制(clone_file:macOS 的 copyfile(COPYFILE_CLONE_FORCE)
 *      或 Linux 的 copy_file_range),真正复制时毫秒级完成、且不
 *      占用额外磁盘空间;内核不支持时由调用方回退到普通复制。
 * 2) 可靠性:复制完成后必须 fsync。设计上"数据先落盘、目录项后
 *    落盘":先逐个 fsync 复制出的文件,最后 fsync 目标目录本身
 *    (仅 fsync 文件不保证目录项已同步,ext4 等文件系统曾因此有
 *    较长的窗口)。若 enableFsync 关闭则整体跳过。
 * 3) 健壮性:复制过程中定期 CHECK_FOR_INTERRUPTS 响应取消请求;
 *    只处理目录与普通文件,符号链接等其它类型被忽略;文件复制期间
 *    每隔 FLUSH_DISTANCE 调用 pg_flush_data 主动冲刷内核缓存,避免
 *    脏页堆积、让内核提前开始落盘。
 *
 * 注意:本模块不使用缓冲池/共享内存,全部走 fd.c 的临时文件
 * (TransientFile)机制,由 VFD 统一管理。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *	While "xcopy /e /i /q" works fine for copying directories, on Windows XP
 *	it requires a Window handle which prevents it from working when invoked
 *	as a service.
 *
 * IDENTIFICATION
 *	  src/backend/storage/file/copydir.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#ifdef HAVE_COPYFILE_H
#include <copyfile.h>
#endif
#include <fcntl.h>
#include <unistd.h>

#include "common/file_utils.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "storage/copydir.h"
#include "storage/fd.h"
#include "utils/wait_event.h"

/* GUC:文件复制方式(FILE_COPY_METHOD_COPY=普通复制 /
 * FILE_COPY_METHOD_CLONE=克隆,见 config.sgml 的 file_copy_method 文档)。
 * 集中在这里,供 copydir() 在复制每个文件时读取 */
int			file_copy_method = FILE_COPY_METHOD_COPY;

/* clone_file 的函数原型(见函数定义处的详细注释) */
static void clone_file(const char *fromfile, const char *tofile);

/*
 * copydir: copy a directory
 *
 * If recurse is false, subdirectories are ignored.  Anything that's not
 * a directory or a regular file is ignored.
 *
 * This function uses the file_copy_method GUC.  New uses of this function must
 * be documented in doc/src/sgml/config.sgml.
 */
/*
 * copydir (中文)递归复制目录(供 CREATE DATABASE 使用)
 *
 * 【作用】把 fromdir 下的内容复制到 todir:先创建目标目录,再遍历源
 * 目录;对子目录按 recurse 决定是否递归(递归时同样以本函数处理),
 * 对普通文件按 file_copy_method 选择"普通复制 copy_file"或"克隆
 * clone_file";目录与普通文件之外的条目(符号链接等)一律忽略。
 * 最后做 fsync 收尾:逐文件 fsync + fsync 目标目录本身。
 *
 * 【设计思想】
 * - 复制顺序"先建目标目录、后复制内容、最后 fsync 目录",与
 *   fsync 语义配合:文件 fsync 只保证文件数据落盘,目录项(名字、
 *   大小、时间戳)由目录的 fsync 保证,因此目录必须最后刷;
 * - 递归子目录由内层 copydir 自己 fsync,外层不再重复刷子目录;
 * - 复制每个文件前 CHECK_FOR_INTERRUPTS,长目录复制可被取消;
 * - 目标目录用 MakePGDirectory 创建,已存在则报错(复制目标应是
 *   全新目录,防止覆盖已有数据)。
 *
 * 【参数】
 *   fromdir —— 源目录;
 *   todir   —— 目标目录(必须尚不存在);
 *   recurse —— true 时递归复制子目录,false 时跳过子目录。
 * 【返回值】无(失败报 ERROR)。
 */
void
copydir(const char *fromdir, const char *todir, bool recurse)
{
	DIR		   *xldir;
	struct dirent *xlde;
	char		fromfile[MAXPGPATH * 2];
	char		tofile[MAXPGPATH * 2];

	if (MakePGDirectory(todir) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not create directory \"%s\": %m", todir)));

	xldir = AllocateDir(fromdir);

	while ((xlde = ReadDir(xldir, fromdir)) != NULL)
	{
		PGFileType	xlde_type;

		/* If we got a cancel signal during the copy of the directory, quit */
		CHECK_FOR_INTERRUPTS();

		if (strcmp(xlde->d_name, ".") == 0 ||
			strcmp(xlde->d_name, "..") == 0)
			continue;

		snprintf(fromfile, sizeof(fromfile), "%s/%s", fromdir, xlde->d_name);
		snprintf(tofile, sizeof(tofile), "%s/%s", todir, xlde->d_name);

		xlde_type = get_dirent_type(fromfile, xlde, false, ERROR);

		if (xlde_type == PGFILETYPE_DIR)
		{
			/* recurse to handle subdirectories */
			if (recurse)
				copydir(fromfile, tofile, true);
		}
		else if (xlde_type == PGFILETYPE_REG)
		{
			if (file_copy_method == FILE_COPY_METHOD_CLONE)
				clone_file(fromfile, tofile);
			else
				copy_file(fromfile, tofile);
		}
	}
	FreeDir(xldir);

	/*
	 * Be paranoid here and fsync all files to ensure the copy is really done.
	 * But if fsync is disabled, we're done.
	 */
	if (!enableFsync)
		return;

	xldir = AllocateDir(todir);

	while ((xlde = ReadDir(xldir, todir)) != NULL)
	{
		if (strcmp(xlde->d_name, ".") == 0 ||
			strcmp(xlde->d_name, "..") == 0)
			continue;

		snprintf(tofile, sizeof(tofile), "%s/%s", todir, xlde->d_name);

		/*
		 * We don't need to sync subdirectories here since the recursive
		 * copydir will do it before it returns
		 */
		if (get_dirent_type(tofile, xlde, false, ERROR) == PGFILETYPE_REG)
			fsync_fname(tofile, false);
	}
	FreeDir(xldir);

	/*
	 * It's important to fsync the destination directory itself as individual
	 * file fsyncs don't guarantee that the directory entry for the file is
	 * synced. Recent versions of ext4 have made the window much wider but
	 * it's been true for ext3 and other filesystems in the past.
	 */
	fsync_fname(todir, true);
}

/*
 * copy one file
 */
/*
 * copy_file (中文)普通方式复制单个文件(循环 read/write)
 *
 * 【作用】把 fromfile 的内容原样复制到 tofile(新创建,带 O_EXCL
 * 防止覆盖):以 COPY_BUF_SIZE(8 个块)为单位的缓冲区循环读写,
 * 直到读到 EOF。期间每隔 FLUSH_DISTANCE 用 pg_flush_data 主动
 * 冲刷已写区段(见下),并定期检查取消信号。I/O 时间计入
 * WAIT_EVENT_COPY_FILE_READ/COPY_FILE_WRITE 等待事件。
 *
 * 【设计思想】
 * - 用 palloc 而非栈/静态缓冲,保证缓冲区满足 maxaligned 对齐
 *   (某些平台要求直接 I/O 对齐);
 * - 复制期间周期性 pg_flush_data 而不等最后一次性 fsync:避免
 *   内核脏页缓存被大文件塞满("spamming the cache"),并让内核
 *   提前开始把数据写向磁盘,把最后 fsync 的代价摊开;冲刷距离
 *   FLUSH_DISTANCE 在 macOS(APFS)上取 32MB 而非 1MB,因为小粒度
 *   mmap/msync 请求在 macOS 上代价很高;
 * - write 后 errno 保持为 0 时若长度不足,按"磁盘满"处理
 *   (errno = ENOSPC),给出更合理的报错;
 * - 目标文件 O_CREAT|O_EXCL:调用方保证目标不存在,防止误覆盖。
 *
 * 【参数】
 *   fromfile —— 源文件路径;
 *   tofile   —— 目标文件路径。
 * 【返回值】无(任何 I/O 失败都报 ERROR)。
 */
void
copy_file(const char *fromfile, const char *tofile)
{
	char	   *buffer;
	int			srcfd;
	int			dstfd;
	ssize_t		nbytes;
	off_t		offset;
	off_t		flush_offset;

	/* Size of copy buffer (read and write requests) */
	/* 单次读写请求的缓冲区大小:8 个 BLCKSZ(默认 64KB)。
	 * 足够大以摊薄系统调用开销,又足够小以保持内存占用可控 */
#define COPY_BUF_SIZE (8 * BLCKSZ)

	/*
	 * Size of data flush requests.  It seems beneficial on most platforms to
	 * do this every 1MB or so.  But macOS, at least with early releases of
	 * APFS, is really unfriendly to small mmap/msync requests, so there do it
	 * only every 32MB.
	 */
	/* 主动冲刷内核缓存的距离:每复制这么多字节就 pg_flush_data 一次 */
#if defined(__darwin__)
#define FLUSH_DISTANCE (32 * 1024 * 1024)
#else
#define FLUSH_DISTANCE (1024 * 1024)
#endif

	/* Use palloc to ensure we get a maxaligned buffer */
	buffer = palloc(COPY_BUF_SIZE);

	/*
	 * Open the files
	 */
	srcfd = OpenTransientFile(fromfile, O_RDONLY | PG_BINARY);
	if (srcfd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not open file \"%s\": %m", fromfile)));

	dstfd = OpenTransientFile(tofile, O_RDWR | O_CREAT | O_EXCL | PG_BINARY);
	if (dstfd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not create file \"%s\": %m", tofile)));

	/*
	 * Do the data copying.
	 */
	flush_offset = 0;
	for (offset = 0;; offset += nbytes)
	{
		/* If we got a cancel signal during the copy of the file, quit */
		CHECK_FOR_INTERRUPTS();

		/*
		 * We fsync the files later, but during the copy, flush them every so
		 * often to avoid spamming the cache and hopefully get the kernel to
		 * start writing them out before the fsync comes.
		 */
		if (offset - flush_offset >= FLUSH_DISTANCE)
		{
			pg_flush_data(dstfd, flush_offset, offset - flush_offset);
			flush_offset = offset;
		}

		pgstat_report_wait_start(WAIT_EVENT_COPY_FILE_READ);
		nbytes = read(srcfd, buffer, COPY_BUF_SIZE);
		pgstat_report_wait_end();
		if (nbytes < 0)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not read file \"%s\": %m", fromfile)));
		if (nbytes == 0)
			break;
		errno = 0;
		pgstat_report_wait_start(WAIT_EVENT_COPY_FILE_WRITE);
		if (write(dstfd, buffer, nbytes) != nbytes)
		{
			/* if write didn't set errno, assume problem is no disk space */
			if (errno == 0)
				errno = ENOSPC;
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not write to file \"%s\": %m", tofile)));
		}
		pgstat_report_wait_end();
	}

	if (offset > flush_offset)
		pg_flush_data(dstfd, flush_offset, offset - flush_offset);

	if (CloseTransientFile(dstfd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", tofile)));

	if (CloseTransientFile(srcfd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", fromfile)));

	pfree(buffer);
}

/*
 * clone one file
 */
/*
 * clone_file (中文)用文件系统"克隆"机制复制单个文件(写时复制)
 *
 * 【作用】按 file_copy_method = FILE_COPY_METHOD_CLONE 时调用,尽量
 * 使用内核提供的快速克隆接口,避免真正逐字节读写:
 * - macOS:copyfile(..., COPYFILE_CLONE_FORCE) 创建克隆文件
 *   (与 APFS clonefile 等价);
 * - Linux:打开源/目标文件后用 copy_file_range(内核支持时走
 *   reflink/写时复制,否则退化为普通拷贝)循环复制,每次最多 1MB
 *   以便途中检查取消信号。
 * 若平台不支持任何克隆机制,本函数绝不应被调用(pg_unreachable)。
 *
 * 【设计思想】克隆的收益:物理复制 O(数据量),克隆 O(1)、且共享
 * 底层数据块(写时才分配新块)。CREATE DATABASE 复制模板库时,
 * 克隆能显著加速并大幅节省磁盘占用。
 *
 * 【参数】
 *   fromfile —— 源文件路径;
 *   tofile   —— 目标文件路径。
 * 【返回值】无(失败报 ERROR)。
 */
static void
clone_file(const char *fromfile, const char *tofile)
{
#if defined(HAVE_COPYFILE) && defined(COPYFILE_CLONE_FORCE)
	if (copyfile(fromfile, tofile, NULL, COPYFILE_CLONE_FORCE) < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not clone file \"%s\" to \"%s\": %m",
						fromfile, tofile)));
#elif defined(HAVE_COPY_FILE_RANGE)
	int			srcfd;
	int			dstfd;
	ssize_t		nbytes;

	srcfd = OpenTransientFile(fromfile, O_RDONLY | PG_BINARY);
	if (srcfd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not open file \"%s\": %m", fromfile)));

	dstfd = OpenTransientFile(tofile, O_WRONLY | O_CREAT | O_EXCL | PG_BINARY);
	if (dstfd < 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not create file \"%s\": %m", tofile)));

	do
	{
		/*
		 * Don't copy too much at once, so we can check for interrupts from
		 * time to time if it falls back to a slow copy.
		 */
		CHECK_FOR_INTERRUPTS();
		pgstat_report_wait_start(WAIT_EVENT_COPY_FILE_COPY);
		nbytes = copy_file_range(srcfd, NULL, dstfd, NULL, 1024 * 1024, 0);
		if (nbytes < 0 && errno != EINTR)
			ereport(ERROR,
					(errcode_for_file_access(),
					 errmsg("could not clone file \"%s\" to \"%s\": %m",
							fromfile, tofile)));
		pgstat_report_wait_end();
	}
	while (nbytes != 0);

	if (CloseTransientFile(dstfd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", tofile)));

	if (CloseTransientFile(srcfd) != 0)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not close file \"%s\": %m", fromfile)));
#else
	/* If there is no CLONE support this function should not be called. */
	pg_unreachable();
#endif
}
