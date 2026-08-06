/*-------------------------------------------------------------------------
 *
 * main.c
 *	  Stub main() routine for the postgres executable.
 *
 * This does some essential startup tasks for any incarnation of postgres
 * (postmaster, standalone backend, standalone bootstrap process, or a
 * separately exec'd child of a postmaster) and then dispatches to the
 * proper FooMain() routine for the incarnation.
 *
 * 【中文总述】
 * 本文件是 postgres 可执行程序的统一入口（main 函数所在处）。
 * 无论 postgres 进程以哪种身份被启动，都会先执行这里的 main()：
 *   - postmaster（主服务进程，负责监听连接、管理子进程）
 *   - 单用户模式后端（--single）
 *   - 引导模式/检查模式（--boot / --check，用于 initdb 时创建系统表）
 *   - EXEC_BACKEND 平台下被单独 exec 出来的子进程（--forkchild）
 * main() 只负责做"所有身份都必需"的公共初始化：
 *   1. 平台相关的启动 hack（Windows 专用）
 *   2. 保存 argv 以便 ps 显示进程标题
 *   3. 初始化内存管理（MemoryContext）与错误报告（elog/ereport）基础设施
 *   4. 设置堆栈深度检测基准点、初始化 locale
 *   5. 处理 --help / --version 等标准选项，检查是否以 root 运行
 *   6. 根据第一个参数（--boot / --single / --check 等）分发给对应的
 *      FooMain() 函数；若无特殊参数，则以 postmaster 身份启动。
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/main/main.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <unistd.h>

#if defined(WIN32)
#include <crtdbg.h>
#endif

#if defined(__NetBSD__)
#include <sys/param.h>
#endif

#include "bootstrap/bootstrap.h"
#include "common/username.h"
#include "miscadmin.h"
#include "postmaster/postmaster.h"
#include "tcop/tcopprot.h"
#include "utils/help_config.h"
#include "utils/memutils.h"
#include "utils/pg_locale.h"
#include "utils/ps_status.h"


const char *progname;			/* 全局进程名，供错误信息/ps 显示等使用 */
static bool reached_main = false;	/* 标记 main() 是否已进入（供 sanitizer 回调判断） */

/*
 * 特殊"必须放在第一位"的选项名，用于把启动分发给各个子程序。
 * 注意下标与 DispatchOption 枚举一一对应（见 postmaster.h）。
 * DISPATCH_POSTMASTER 没有对应的选项名（默认身份）。
 */
static const char *const DispatchOptionNames[] =
{
	[DISPATCH_CHECK] = "check",
	[DISPATCH_BOOT] = "boot",
	[DISPATCH_FORKCHILD] = "forkchild",
	[DISPATCH_DESCRIBE_CONFIG] = "describe-config",
	[DISPATCH_SINGLE] = "single",
	/* DISPATCH_POSTMASTER has no name */
};

/* 编译期断言：数组长度必须等于枚举元素个数，防止两者不同步 */
StaticAssertDecl(lengthof(DispatchOptionNames) == DISPATCH_POSTMASTER,
				 "array length mismatch");

static void startup_hacks(const char *progname);
static void init_locale(const char *categoryname, int category, const char *locale);
static void help(const char *progname);
static void check_root(const char *progname);


/*
 * Any Postgres server process begins execution here.
 * 【中文】所有 PostgreSQL 服务进程（postmaster/后端/引导进程）都从这里开始执行。
 */
int
main(int argc, char *argv[])
{
	bool		do_check_root = true;	/* 默认需要检查是否以 root 运行 */
	DispatchOption dispatch_option = DISPATCH_POSTMASTER;	/* 默认以 postmaster 身份启动 */

	reached_main = true;

	/*
	 * If supported on the current platform, set up a handler to be called if
	 * the backend/postmaster crashes with a fatal signal or exception.
	 * 【中文】在 Windows 平台上安装崩溃转储（crash dump）处理回调，
	 * 以便进程因致命信号/异常崩溃时生成 dump 文件便于排查。
	 */
#if defined(WIN32)
	pgwin32_install_crashdump_handler();
#endif

	/* 从 argv[0] 中提取不带路径的程序名（如 "postgres"），存到全局变量 */
	progname = get_progname(argv[0]);

	/*
	 * Platform-specific startup hacks
	 * 【中文】平台相关的启动设置（Windows 专用：Winsock 初始化、
	 * 标准输出不缓冲、错误输出方式等）。
	 */
	startup_hacks(progname);

	/*
	 * Remember the physical location of the initially given argv[] array for
	 * possible use by ps display.  On some platforms, the argv[] storage must
	 * be overwritten in order to set the process title for ps. In such cases
	 * save_ps_display_args makes and returns a new copy of the argv[] array.
	 *
	 * save_ps_display_args may also move the environment strings to make
	 * extra room. Therefore this should be done as early as possible during
	 * startup, to avoid entanglements with code that might save a getenv()
	 * result pointer.
	 *
	 * 【中文】为 ps 进程显示做准备：某些平台上要改写 argv 才能设置
	 * 进程标题，此时该函数会拷贝一份新的 argv 返回（原数组被改）。
	 * 另外它还可能挪动环境变量字符串，所以必须尽早调用，
	 * 避免与保存了 getenv() 返回指针的代码冲突。
	 */
	argv = save_ps_display_args(argc, argv);

	/*
	 * Fire up essential subsystems: error and memory management
	 *
	 * Code after this point is allowed to use elog/ereport, though
	 * localization of messages may not work right away, and messages won't go
	 * anywhere but stderr until GUC settings get loaded.
	 *
	 * 【中文】启动两大基础子系统：错误处理与内存管理。
	 * 在此之后代码才允许使用 elog/ereport 报告错误；
	 * 不过在 GUC 配置加载之前，消息只能输出到 stderr，且还没有本地化。
	 */
	MyProcPid = getpid();		/* 记录本进程 PID（供错误信息等使用） */
	MemoryContextInit();		/* 初始化内存上下文体系（TopMemoryContext 等） */

	/*
	 * Set reference point for stack-depth checking.  (There's no point in
	 * enabling this before error reporting works.)
	 * 【中文】记录当前栈顶位置作为"栈深度检查"的基准点，
	 * 之后递归过深（如无限递归的 SQL）时能检测到栈溢出。
	 * （错误报告可用之前设置它没有意义，所以要放在上面两步之后。）
	 */
	(void) set_stack_base();

	/*
	 * Set up locale information
	 * 【中文】设置程序名对应的 locale 消息目录（gettext 本地化所需），
	 * 并确定服务目录位置。
	 */
	set_pglocale_pgservice(argv[0], PG_TEXTDOMAIN("postgres"));

	/*
	 * Collation is handled by pg_locale.c, and the behavior is dependent on
	 * the provider. strcoll(), etc., should not be called directly.
	 * 【中文】字符串排序规则（排序/比较行为）由 pg_locale.c 统一管理，
	 * 不要直接调用 strcoll() 等 libc 函数。这里先把 LC_COLLATE 置为 "C"。
	 */
	init_locale("LC_COLLATE", LC_COLLATE, "C");

	/*
	 * In the postmaster, absorb the environment value for LC_CTYPE.
	 * Individual backends will change it later to pg_database.datctype, but
	 * the postmaster cannot do that.  If we leave it set to "C" then message
	 * localization might not work well in the postmaster.
	 *
	 * 【中文】postmaster 需要吸收环境变量中的 LC_CTYPE（字符分类，
	 * 影响大小写转换等）。单个后端进程之后会改成所连数据库的
	 * pg_database.datctype，但 postmaster 做不到，所以在这里先取环境值。
	 * 若一直保持 "C"，postmaster 内的消息本地化可能不正常。
	 */
	init_locale("LC_CTYPE", LC_CTYPE, "");

	/*
	 * LC_MESSAGES will get set later during GUC option processing, but we set
	 * it here to allow startup error messages to be localized.
	 * 【中文】LC_MESSAGES（消息语言）之后在 GUC 处理时会再设置，
	 * 这里先设置是为了让启动阶段的错误信息也能本地化。
	 */
#ifdef LC_MESSAGES
	init_locale("LC_MESSAGES", LC_MESSAGES, "");
#endif

	/* We keep these set to "C" always.  See pg_locale.c for explanation. */
	/* 【中文】这三类始终固定为 "C"（不做本地化），原因见 pg_locale.c。 */
	init_locale("LC_MONETARY", LC_MONETARY, "C");
	init_locale("LC_NUMERIC", LC_NUMERIC, "C");
	init_locale("LC_TIME", LC_TIME, "C");

	/*
	 * Now that we have absorbed as much as we wish to from the locale
	 * environment, remove any LC_ALL setting, so that the environment
	 * variables installed by pg_perm_setlocale have force.
	 * 【中文】上面已经吸收了需要的 locale 环境，现在删除 LC_ALL，
	 * 否则 LC_ALL 会覆盖 pg_perm_setlocale 设置的所有类别，
	 * 导致上面的显式设置失效。
	 */
	unsetenv("LC_ALL");

	/*
	 * Catch standard options before doing much else, in particular before we
	 * insist on not being root.
	 *
	 * 【中文】尽早处理标准选项，特别是要在"拒绝 root 运行"检查之前：
	 * --help / -? 打印帮助，--version / -V 打印版本号，然后直接退出。
	 */
	if (argc > 1)
	{
		if (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-?") == 0)
		{
			help(progname);
			exit(0);
		}
		if (strcmp(argv[1], "--version") == 0 || strcmp(argv[1], "-V") == 0)
		{
			fputs(PG_BACKEND_VERSIONSTR, stdout);
			exit(0);
		}

		/*
		 * In addition to the above, we allow "--describe-config" and "-C var"
		 * to be called by root.  This is reasonably safe since these are
		 * read-only activities.  The -C case is important because pg_ctl may
		 * try to invoke it while still holding administrator privileges on
		 * Windows.  Note that while -C can normally be in any argv position,
		 * if you want to bypass the root check you must put it first.  This
		 * reduces the risk that we might misinterpret some other mode's -C
		 * switch as being the postmaster/postgres one.
		 *
		 * 【中文】此外还允许 root 调用 --describe-config（列出所有配置参数）
		 * 和 -C var（打印某个参数的值）。这两个都是只读操作，相对安全；
		 * 其中 -C 很重要，因为 Windows 上 pg_ctl 可能还持有管理员权限时
		 * 就来调用它。注意：想绕过 root 检查，这两个选项必须放在第一个参数。
		 */
		if (strcmp(argv[1], "--describe-config") == 0)
			do_check_root = false;
		else if (argc > 2 && strcmp(argv[1], "-C") == 0)
			do_check_root = false;
	}

	/*
	 * Make sure we are not running as root, unless it's safe for the selected
	 * option.
	 * 【中文】默认情况下拒绝以 root（Windows 上是管理员）运行 postgres，
	 * 防止权限过高带来安全隐患；上面标记为安全的选项除外。
	 */
	if (do_check_root)
		check_root(progname);

	/*
	 * Dispatch to one of various subprograms depending on first argument.
	 * 【中文】根据第一个参数分发给不同的子程序（详见各分支）。
	 * 只有以 "--" 开头（如 "--boot"）才被解析为分发选项；
	 * 普通 postgres 启动命令没有这类参数，走最后的 DISPATCH_POSTMASTER。
	 */
	if (argc > 1 && argv[1][0] == '-' && argv[1][1] == '-')
		dispatch_option = parse_dispatch_option(&argv[1][2]);

	switch (dispatch_option)
	{
		case DISPATCH_CHECK:
			/* --check：检查模式，initdb 早期用来验证系统表能否被读回 */
			BootstrapModeMain(argc, argv, true);
			break;
		case DISPATCH_BOOT:
			/* --boot：引导模式，initdb 用它创建系统表并写入基础数据 */
			BootstrapModeMain(argc, argv, false);
			break;
		case DISPATCH_FORKCHILD:
			/* --forkchild：仅 EXEC_BACKEND 平台（如 Windows）使用，
			 * 由 postmaster exec 出来的子进程从这里进入
			 * SubPostmasterMain()（例如做 WAL 归档、校验等工作）。
			 * 普通 fork 平台理论上不会出现，所以 Assert 防御。 */
#ifdef EXEC_BACKEND
			SubPostmasterMain(argc, argv);
#else
			Assert(false);		/* should never happen */
#endif
			break;
		case DISPATCH_DESCRIBE_CONFIG:
			/* --describe-config：打印所有 GUC 参数，供 pg_config 等工具使用 */
			GucInfoMain();
			break;
		case DISPATCH_SINGLE:
			/* --single：单用户模式（如 initdb 后期、紧急修复时使用），
			 * 用户名取自操作系统用户 */
			PostgresSingleUserMain(argc, argv,
								   strdup(get_user_name_or_exit(progname)));
			break;
		case DISPATCH_POSTMASTER:
			/* 默认身份：postmaster 主进程，整个数据库服务从这里开始。
			 * 它会负责监听端口、fork 后端进程、管理共享内存等。 */
			PostmasterMain(argc, argv);
			break;
	}

	/* 上面的 FooMain 函数都不应返回；如果返回说明出错了，强制 abort */
	abort();
}

/*
 * Returns the matching DispatchOption value for the given option name.  If no
 * match is found, DISPATCH_POSTMASTER is returned.
 * 【中文】根据选项名字符串找到对应的 DispatchOption 枚举值；
 * 找不到就返回 DISPATCH_POSTMASTER（视为默认的 postmaster 启动）。
 */
DispatchOption
parse_dispatch_option(const char *name)
{
	for (size_t i = 0; i < lengthof(DispatchOptionNames); i++)
	{
		/*
		 * Unlike the other dispatch options, "forkchild" takes an argument,
		 * so we just look for the prefix for that one.  For non-EXEC_BACKEND
		 * builds, we never want to return DISPATCH_FORKCHILD, so skip over it
		 * in that case.
		 *
		 * 【中文】"forkchild" 与其他选项不同，它后面还带参数
		 * （如 "--forkchild=...类型"），所以这里只比较前缀；
		 * 非 EXEC_BACKEND 平台永远不可能用到它，直接跳过。
		 */
		if (i == DISPATCH_FORKCHILD)
		{
#ifdef EXEC_BACKEND
			if (strncmp(DispatchOptionNames[DISPATCH_FORKCHILD], name,
						strlen(DispatchOptionNames[DISPATCH_FORKCHILD])) == 0)
				return DISPATCH_FORKCHILD;
#endif
			continue;
		}

		/* 其余选项要求完全匹配 */
		if (strcmp(DispatchOptionNames[i], name) == 0)
			return (DispatchOption) i;
	}

	/* 没有匹配项，说明是 postmaster */
	return DISPATCH_POSTMASTER;
}

/*
 * Place platform-specific startup hacks here.  This is the right
 * place to put code that must be executed early in the launch of any new
 * server process.  Note that this code will NOT be executed when a backend
 * or sub-bootstrap process is forked, unless we are in a fork/exec
 * environment (ie EXEC_BACKEND is defined).
 *
 * XXX The need for code here is proof that the platform in question
 * is too brain-dead to provide a standard C execution environment
 * without help.  Avoid adding more here, if you can.
 *
 * 【中文】放置平台相关的启动 hack（这里是 Windows 专用设置）。
 * 注意：普通 fork 平台下，后端进程是通过 fork 继承父进程环境的，
 * 不会重新执行这里的代码；只有 EXEC_BACKEND（fork/exec）平台才会。
 * XXX 需要在这里写代码，说明该平台连标准 C 执行环境都得帮一把，能不加就不加。
 */
static void
startup_hacks(const char *progname)
{
	/*
	 * Windows-specific execution environment hacking.
	 * 【中文】Windows 平台执行环境设置：
	 *  - 标准输出/错误改为不缓冲
	 *  - 初始化 Winsock（网络库）
	 *  - abort() 行为设置、错误模式设置（避免弹窗、改为输出到 stderr）
	 */
#ifdef WIN32
	{
		WSADATA		wsaData;
		int			err;

		/* Make output streams unbuffered by default */
		setvbuf(stdout, NULL, _IONBF, 0);
		setvbuf(stderr, NULL, _IONBF, 0);

		/* Prepare Winsock */
		/* 【中文】初始化 Winsock 库，失败则报错退出 */
		err = WSAStartup(MAKEWORD(2, 2), &wsaData);
		if (err != 0)
		{
			write_stderr("%s: WSAStartup failed: %d\n",
						 progname, err);
			exit(1);
		}

		/*
		 * By default abort() only generates a crash-dump in *non* debug
		 * builds. As our Assert() / ExceptionalCondition() uses abort(),
		 * leaving the default in place would make debugging harder.
		 *
		 * MINGW's own C runtime doesn't have _set_abort_behavior(). When
		 * targeting Microsoft's UCRT with mingw, it never links to the debug
		 * version of the library and thus doesn't need the call to
		 * _set_abort_behavior() either.
		 *
		 * 【中文】默认情况下 abort() 只在非 debug 构建里生成崩溃转储，
		 * 而 PG 的 Assert/ExceptionalCondition 正是用 abort()，
		 * 保持默认会导致调试困难，因此这里显式开启崩溃报告行为。
		 */
#if !defined(__MINGW32__) && !defined(__MINGW64__)
		_set_abort_behavior(_CALL_REPORTFAULT | _WRITE_ABORT_MSG,
							_CALL_REPORTFAULT | _WRITE_ABORT_MSG);
#endif							/* !defined(__MINGW32__) &&
								 * !defined(__MINGW64__) */

		/*
		 * SEM_FAILCRITICALERRORS causes more errors to be reported to
		 * callers.
		 *
		 * We used to also specify SEM_NOGPFAULTERRORBOX, but that prevents
		 * windows crash reporting from working. Which includes registered
		 * just-in-time debuggers, making it unnecessarily hard to debug
		 * problems on windows. Now we try to disable sources of popups
		 * separately below (note that SEM_NOGPFAULTERRORBOX did not actually
		 * prevent all sources of such popups).
		 *
		 * 【中文】设置错误模式：让系统把关键错误回报给调用者而不是弹窗。
		 * 早期还加过 SEM_NOGPFAULTERRORBOX，但那会禁用 Windows 崩溃报告
		 * 和实时调试器，反而增加调试难度，所以现在单独处理各类弹窗来源。
		 */
		SetErrorMode(SEM_FAILCRITICALERRORS);

		/*
		 * Show errors on stderr instead of popup box (note this doesn't
		 * affect errors originating in the C runtime, see below).
		 * 【中文】错误输出到 stderr 而不是弹窗
		 * （注意这不影响 C 运行时自身的错误，下面单独处理）。
		 */
		_set_error_mode(_OUT_TO_STDERR);

		/*
		 * In DEBUG builds, errors, including assertions, C runtime errors are
		 * reported via _CrtDbgReport. By default such errors are displayed
		 * with a popup (even with NOGPFAULTERRORBOX), preventing forward
		 * progress. Instead report such errors stderr (and the debugger).
		 * This is C runtime specific and thus the above incantations aren't
		 * sufficient to suppress these popups.
		 *
		 * 【中文】Debug 构建下 C 运行时的错误/断言默认通过 _CrtDbgReport
		 * 以弹窗显示（即使设置了 NOGPFAULTERRORBOX 也一样），
		 * 这里把所有报告方式改为输出到 stderr（同时通知调试器），
		 * 避免弹窗阻塞程序运行。
		 */
		_CrtSetReportMode(_CRT_ERROR, _CRTDBG_MODE_FILE | _CRTDBG_MODE_DEBUG);
		_CrtSetReportFile(_CRT_ERROR, _CRTDBG_FILE_STDERR);
		_CrtSetReportMode(_CRT_ASSERT, _CRTDBG_MODE_FILE | _CRTDBG_MODE_DEBUG);
		_CrtSetReportFile(_CRT_ASSERT, _CRTDBG_FILE_STDERR);
		_CrtSetReportMode(_CRT_WARN, _CRTDBG_MODE_FILE | _CRTDBG_MODE_DEBUG);
		_CrtSetReportFile(_CRT_WARN, _CRTDBG_FILE_STDERR);
	}
#endif							/* WIN32 */
}


/*
 * Make the initial permanent setting for a locale category.  If that fails,
 * perhaps due to LC_foo=invalid in the environment, use locale C.  If even
 * that fails, perhaps due to out-of-memory, the entire startup fails with it.
 * When this returns, we are guaranteed to have a setting for the given
 * category's environment variable.
 *
 * 【中文】为某个 locale 类别做初始化设置。
 * 逻辑：先用指定的 locale 尝试设置（可能是环境变量里给的无效值），
 * 失败则回退到 "C"；连 "C" 都失败（如内存不足）就直接 FATAL 退出。
 * 该函数返回后，对应类别的环境变量一定有有效设置。
 */
static void
init_locale(const char *categoryname, int category, const char *locale)
{
	if (pg_perm_setlocale(category, locale) == NULL &&
		pg_perm_setlocale(category, "C") == NULL)
		elog(FATAL, "could not adopt \"%s\" locale nor C locale for %s",
			 locale, categoryname);
}



/*
 * Help display should match the options accepted by PostmasterMain()
 * and PostgresMain().
 *
 * XXX On Windows, non-ASCII localizations of these messages only display
 * correctly if the console output code page covers the necessary characters.
 * Messages emitted in write_console() do not exhibit this problem.
 *
 * 【中文】打印 --help 的帮助信息（选项列表）。
 * 内容应与 PostmasterMain()/PostgresMain() 实际接受的选项保持一致。
 * XXX Windows 上非 ASCII 文本是否能正常显示取决于控制台代码页。
 */
static void
help(const char *progname)
{
	printf(_("%s is the PostgreSQL server.\n\n"), progname);
	printf(_("Usage:\n  %s [OPTION]...\n\n"), progname);
	printf(_("Options:\n"));
	printf(_("  -B NBUFFERS        number of shared buffers\n"));
	printf(_("  -c NAME=VALUE      set run-time parameter\n"));
	printf(_("  -C NAME            print value of run-time parameter, then exit\n"));
	printf(_("  -d 1-5             debugging level\n"));
	printf(_("  -D DATADIR         database directory\n"));
	printf(_("  -e                 use European date input format (DMY)\n"));
	printf(_("  -F                 turn fsync off\n"));
	printf(_("  -h HOSTNAME        host name or IP address to listen on\n"));
	printf(_("  -i                 enable TCP/IP connections (deprecated)\n"));
	printf(_("  -k DIRECTORY       Unix-domain socket location\n"));
#ifdef USE_SSL
	printf(_("  -l                 enable SSL connections\n"));
#endif
	printf(_("  -N MAX-CONNECT     maximum number of allowed connections\n"));
	printf(_("  -p PORT            port number to listen on\n"));
	printf(_("  -s                 show statistics after each query\n"));
	printf(_("  -S WORK-MEM        set amount of memory for sorts (in kB)\n"));
	printf(_("  -V, --version      output version information, then exit\n"));
	printf(_("  --NAME=VALUE       set run-time parameter\n"));
	printf(_("  --describe-config  describe configuration parameters, then exit\n"));
	printf(_("  -?, --help         show this help, then exit\n"));

	printf(_("\nDeveloper options:\n"));
	printf(_("  -f s|i|o|b|t|n|m|h forbid use of some plan types\n"));
	printf(_("  -O                 allow system table structure changes\n"));
	printf(_("  -P                 disable system indexes\n"));
	printf(_("  -t pa|pl|ex        show timings after each query\n"));
	printf(_("  -T                 send SIGABRT to all backend processes if one dies\n"));
	printf(_("  -W NUM             wait NUM seconds to allow attach from a debugger\n"));

	printf(_("\nOptions for single-user mode:\n"));
	printf(_("  --single           selects single-user mode (must be first argument)\n"));
	printf(_("  DBNAME             database name (defaults to user name)\n"));
	printf(_("  -d 0-5             override debugging level\n"));
	printf(_("  -E                 echo statement before execution\n"));
	printf(_("  -j                 do not use newline as interactive query delimiter\n"));
	printf(_("  -r FILENAME        send stdout and stderr to given file\n"));

	printf(_("\nOptions for bootstrapping mode:\n"));
	printf(_("  --boot             selects bootstrapping mode (must be first argument)\n"));
	printf(_("  --check            selects check mode (must be first argument)\n"));
	printf(_("  DBNAME             database name (mandatory argument in bootstrapping mode)\n"));
	printf(_("  -r FILENAME        send stdout and stderr to given file\n"));

	printf(_("\nPlease read the documentation for the complete list of run-time\n"
			 "configuration settings and how to set them on the command line or in\n"
			 "the configuration file.\n\n"
			 "Report bugs to <%s>.\n"), PACKAGE_BUGREPORT);
	printf(_("%s home page: <%s>\n"), PACKAGE_NAME, PACKAGE_URL);
}



/*
 * 检查当前是否以 root（Windows 上是管理员）身份运行，是则报错退出。
 * 原因：以高权限运行数据库服务，一旦被攻破将威胁整个系统，
 * 官方要求用非特权用户启动。分为两步检查：
 *  1. 有效 UID 不能是 root；
 *  2. 真实 UID 与有效 UID 必须一致——防止 setuid 程序被 root shell
 *     调用后，内部某个危险子程序又能把权限切回 root。
 *     （虽然没人真把 postgres 当 setuid 程序用，但检查一下成本低收益高。）
 */
static void
check_root(const char *progname)
{
#ifndef WIN32
	if (geteuid() == 0)
	{
		write_stderr("\"root\" execution of the PostgreSQL server is not permitted.\n"
					 "The server must be started under an unprivileged user ID to prevent\n"
					 "possible system security compromise.  See the documentation for\n"
					 "more information on how to properly start the server.\n");
		exit(1);
	}

	/*
	 * Also make sure that real and effective uids are the same. Executing as
	 * a setuid program from a root shell is a security hole, since on many
	 * platforms a nefarious subroutine could setuid back to root if real uid
	 * is root.  (Since nobody actually uses postgres as a setuid program,
	 * trying to actively fix this situation seems more trouble than it's
	 * worth; we'll just expend the effort to check for it.)
	 */
	if (getuid() != geteuid())
	{
		write_stderr("%s: real and effective user IDs must match\n",
					 progname);
		exit(1);
	}
#else							/* WIN32 */
	if (pgwin32_is_admin())
	{
		write_stderr("Execution of PostgreSQL by a user with administrative permissions is not\n"
					 "permitted.\n"
					 "The server must be started under an unprivileged user ID to prevent\n"
					 "possible system security compromises.  See the documentation for\n"
					 "more information on how to properly start the server.\n");
		exit(1);
	}
#endif							/* WIN32 */
}

/*
 * At least on linux, set_ps_display() breaks /proc/$pid/environ. The
 * sanitizer library uses /proc/$pid/environ to implement getenv() as it wants
 * to work independent of libc. Depending on which sanitizers are enabled,
 * the sanitizer library may not get initialized until after we've called
 * set_ps_display(), preventing the sanitizer from seeing environment-supplied
 * options.
 *
 * We can work around that by defining __ubsan_default_options, a weak symbol
 * libsanitizer uses to get defaults from the application, and return
 * getenv("UBSAN_OPTIONS"). But only if main already was reached, so that we
 * don't end up relying on a not-yet-working getenv().
 *
 * On the other hand, with different sanitizers enabled, libsanitizer can
 * call this so early that it's not fully initialized itself, resulting in
 * recursion and a core dump within libsanitizer.  To prevent that, ensure
 * that this function is built without any sanitizer callbacks in it.
 *
 * As this function won't get called when not running a sanitizer, it doesn't
 * seem necessary to only compile it conditionally.
 *
 * 【中文】仅供 UBSan（未定义行为消毒器）使用的弱符号回调：
 *  - set_ps_display() 会破坏 Linux 上 /proc/$pid/environ，而 sanitizer 库
 *    依赖它实现 getenv()，若不处理，sanitizer 初始化后就看不到
 *    环境变量里传来的 UBSAN_OPTIONS 了。
 *  - 本函数返回 getenv("UBSAN_OPTIONS") 作为 sanitizer 的默认选项；
 *    但只有 main() 已进入（libc 保证可用）时才返回真实值。
 *  - 某些 sanitizer 可能在自身完全初始化前就调用本函数，导致递归崩溃，
 *    所以本函数编译时被禁止插入 sanitizer 回调（disable_sanitizer_instrumentation）。
 */
const char *__ubsan_default_options(void);

#if __has_attribute(disable_sanitizer_instrumentation)
__attribute__((disable_sanitizer_instrumentation))
#endif
const char *
__ubsan_default_options(void)
{
	/* don't call libc before it's guaranteed to be initialized */
	/* 【中文】main() 还没进入前不调用 libc（getenv 不可靠），返回空串 */
	if (!reached_main)
		return "";

	/* main() 已进入，安全返回环境变量中的 UBSAN_OPTIONS */
	return getenv("UBSAN_OPTIONS");
}
