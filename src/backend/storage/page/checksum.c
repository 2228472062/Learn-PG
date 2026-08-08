/*-------------------------------------------------------------------------
 *
 * checksum.c
 *	  Checksum implementation for data pages.
 *
 * 【模块总览(中文)】
 * 本文件是数据页校验和(checksum)的"外层装配层"。PostgreSQL 为每个
 * 磁盘页计算 CRC32C 校验和,写入页头 pd_checksum 字段,读页时核验,
 * 用于检测磁盘介质损坏等静默数据损坏(data corruption)。真正的算法
 * 实现位于 storage/checksum_impl.h,逐块累加的循环体位于
 * storage/checksum_block_internal.h;本文件只负责:
 * 1) 提供通用的标量(fallback)实现;
 * 2) 在支持 AVX2 的平台上提供向量化实现,运行时用 x86_feature_available
 *    探测 CPU 能力后自动选择;
 * 3) 通过函数指针 pg_checksum_block 对外暴露"当前最优实现"。
 *
 * 这种"算法实现在头文件、由本文件选择并导出"的布局,是为了让外部程序
 * (如 pg_controldata、pg_checksums、pg_rewind 等)可以只 #include 导出
 * 头文件就复用同一套校验和代码;PG_CHECKSUM_INTERNAL 宏则让核心能启用
 * 硬件相关优化而不影响外部程序(与旧的 pg_crc.h CRC 处理方式类似)。
 *
 * 对外接口:写盘前计算校验和用 bufpage.c 的 PageSetChecksum,读盘后
 * 核验用 PageIsVerified;是否启用校验和由 GUC 参数 data_checksums 决定
 * (对应 DataChecksumsNeedWrite / DataChecksumsNeedVerify)。
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/storage/page/checksum.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "port/pg_cpu.h"
#include "storage/checksum.h"
/*
 * The actual code is in storage/checksum_impl.h.  This is done so that
 * external programs can incorporate the checksum code by #include'ing
 * that file from the exported Postgres headers.  (Compare our legacy
 * CRC code in pg_crc.h.)
 * The PG_CHECKSUM_INTERNAL symbol allows core to use hardware-specific
 * coding without affecting external programs.
 */
#define PG_CHECKSUM_INTERNAL
#include "storage/checksum_impl.h"	/* IWYU pragma: keep */


/*
 * pg_checksum_block_fallback
 *      (中文)页校验和的通用标量实现
 *
 * 【作用】对整页数据按 32 字节为单位累加计算 CRC32C 校验和。函数体由
 * #include "storage/checksum_block_internal.h" 展开:该文件包含一段与
 * 硬件无关的循环(每次调用 pg_checksum_block 处理 32 字节,页尾不足
 * 32 字节的残留部分一并处理),计算完成后返回 16 位校验和。校验和的
 * 初始种子、字节序处理与结果掩码等细节全部在 checksum_impl.h 中定义。
 *
 * 【设计思想】把"以 32 字节为单位的循环体"放在头文件里,在此处与
 * AVX2 版本各 #include 一次,两个实现共享同一份逐块逻辑,避免维护
 * 漂移;编译器为 fallback 版本生成普通标量指令,保证在不支持 AVX2 的
 * CPU 上也能运行。
 *
 * 【参数】page —— 待计算的页(PGChecksummablePage:按 32 字节对齐的
 * 页内存视图,见 checksum_impl.h)。
 * 【返回值】16 位页校验和。
 */
static uint32
pg_checksum_block_fallback(const PGChecksummablePage *page)
{
#include "storage/checksum_block_internal.h"
}

/*
 * pg_checksum_block_avx2
 *      (中文)基于 AVX2 向量指令的页校验和实现
 *
 * 【作用】与 pg_checksum_block_fallback 功能完全等价,但利用 AVX2 的
 * 256 位向量单元一次并行累加多个 32 字节块,显著加快大数据量下的校验
 * 和计算(恢复、备份、大表扫描等场景)。循环体同样来自
 * storage/checksum_block_internal.h,与 fallback 一致,只是本函数通过
 * pg_attribute_target("avx2") 获得生成 AVX2 指令的许可。
 *
 * 【设计思想】
 * - 仅在编译期确认平台可能支持 AVX2 时(USE_AVX2_WITH_RUNTIME_CHECK)
 *   才编译本函数;是否真正启用由运行时探测决定(见 pg_checksum_choose),
 *   因此同一份二进制在旧 CPU 上自动退回标量实现,保持向后兼容;
 * - pg_attribute_target("avx2") 把 AVX2 指令的使用范围限定在本函数内,
 *   无需让整个编译单元都开启 -mavx2(那会拖累其他代码);
 * - 注意页缓冲池需要满足 AVX2 对齐要求(校验和实现约定 32 字节对齐,
 *   见 checksum_impl.h)。
 *
 * 【参数】page —— 待计算的页。
 * 【返回值】16 位页校验和。
 *
 * AVX2-optimized block checksum algorithm.
 */
#ifdef USE_AVX2_WITH_RUNTIME_CHECK
pg_attribute_target("avx2")
static uint32
pg_checksum_block_avx2(const PGChecksummablePage *page)
{
#include "storage/checksum_block_internal.h"
}
#endif							/* USE_AVX2_WITH_RUNTIME_CHECK */

/*
 * pg_checksum_choose
 *      (中文)运行时选择当前最优的校验和实现并执行
 *
 * 【作用】函数指针 pg_checksum_block 的"首次解析"入口:先默认指向
 * fallback 实现;若平台支持 AVX2 且运行时探测到 CPU 具备该能力,则改
 * 指向 AVX2 实现,然后调用所选实现完成计算并返回结果。
 *
 * 【设计思想】这是"函数指针 + 一次性静态初始化"的惯用模式:
 * - pg_checksum_block 是静态变量,初始值指向本函数(见文件末尾);因此
 *   第一次调用时实际执行的是本函数,完成选择后函数指针被改写为具体
 *   实现,后续所有调用直接命中,不再有选择开销;
 * - 函数指针是本进程私有的静态变量,只在本进程内被改写,不存在跨进程
 *   并发问题,无需加锁。
 *
 * 【参数】page —— 待计算的页。
 * 【返回值】所选实现计算出的 16 位页校验和。
 *
 * Choose the best available checksum implementation.
 */
static uint32
pg_checksum_choose(const PGChecksummablePage *page)
{
	pg_checksum_block = pg_checksum_block_fallback;

#ifdef USE_AVX2_WITH_RUNTIME_CHECK
	if (x86_feature_available(PG_AVX2))
		pg_checksum_block = pg_checksum_block_avx2;
#endif

	return pg_checksum_block(page);
}

/* 页校验和计算函数指针:初始指向 pg_checksum_choose(首次调用时被改写为
 * fallback 或 AVX2 实现,见其注释),此后所有页校验和计算都经此指针
 * 分发。 */
static uint32 (*pg_checksum_block) (const PGChecksummablePage *page) = pg_checksum_choose;
