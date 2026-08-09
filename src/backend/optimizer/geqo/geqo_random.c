/*------------------------------------------------------------------------
 *
 * geqo_random.c
 *	   random number generator
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/backend/optimizer/geqo/geqo_random.c
 *
 * 【模块总览(中文)】
 * 本文件为遗传算法(GEQO)提供统一的随机数接口。GEQO 的几乎所有操作——
 * 初始化种群、选择父代、各类交叉/变异算子、随机重启等——都需要"可复现
 * 且线程安全"的随机性。为此,本模块把所有随机状态收敛到一处:存放在
 * PlannerInfo 的扩展状态(GeqoPrivateData)中,通过 GetGeqoPrivateData
 * 取得,而不是使用全局静态变量。
 *
 * 设计要点:
 * - 随机源是 pg_prng(PostgreSQL 内置的可移植伪随机数发生器,由
 *   common/pg_prng.h 提供)。它是纯函数的 PRNG,状态封装在
 *   pg_prng_state 结构体里,因此每个查询会话(每个 PlannerInfo)各持有一份
 *   独立状态,并发执行多个查询不会互相干扰;
 * - geqo_set_seed 用 pg_prng_fseed 播种;默认种子 Geqo_seed 来自 GUC,置为
 *   0 时由 pg_prng 自动随机化种子,否则用固定种子保证结果可复现(便于调试
 *   与回归测试);
 * - geqo_rand 返回 [0,1) 区间的 double(PRNG 底层保证永远 < 1.0),是所有
 *   连续型随机选择的来源;geqo_randint 返回 [lower, upper] 闭区间整数,
 *   是各类离散随机选择(选起点、选交叉点等)的来源。
 *
 * 各算子文件(geqo_cx/erx/ox1/ox2/pmx/px/mutation/selection/eval)都只通过
 * 本模块访问随机性,从而保证 GEQO 的随机行为集中、可控、可测试。
 *
 * IDENTIFICATION
 *	  src/backend/optimizer/geqo/geqo_random.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "optimizer/geqo_random.h"

/*
 * geqo_set_seed - (中文)用指定种子为 GEQO 随机数发生器播种
 *
 * 【作用】把 PlannerInfo 扩展状态中保存的 pg_prng 随机状态重置为 seed 派生
 * 的种子值。由 geqo_main.c 的 geqo() 在演化开始前调用一次,用于让整次
 * GEQO 运行使用一致的随机流。
 *
 * 【设计思想】种子是双精度浮点,但 PRNG 状态是内部结构;pg_prng_fseed
 * 负责把浮点种子散列成 PRNG 内部状态。使用固定种子时,同一查询输入总是
 * 得到同一序列的随机数,保证 GEQO 结果可复现(调试与回归测试依赖这点);
 * seed 为 0 时 PRNG 会自动选用熵源产生不可预测的种子。GeqoPrivateData 是
 * 每个 PlannerInfo 一份的私有扩展状态,因此不同查询的随机状态彼此隔离。
 *
 * 【参数】
 *   root —— PlannerInfo,通过 GetGeqoPrivateData 定位随机状态;
 *   seed —— 双精度种子,0 表示使用系统随机种子。
 * 【返回值】无。
 */
void
geqo_set_seed(PlannerInfo *root, double seed)
{
	GeqoPrivateData *private = GetGeqoPrivateData(root);

	pg_prng_fseed(&private->random_state, seed);
}

/*
 * geqo_rand - (中文)返回 [0,1) 区间内的均匀随机数
 *
 * 【作用】从 PlannerInfo 的 PRNG 状态取一个 [0,1) 的 double,供 GEQO 中
 * 所有"连续型随机决策"使用(如选择算子的概率分布采样)。所有算子应通过
 * 本函数而非直接调用 pg_prng,以便集中管理随机流。
 *
 * 【设计思想】pg_prng_double 保证返回值满足 0.0 <= x < 1.0,不会等于 1.0;
 * 这是本模块与调用方之间的契约(geqo_selection.c 的 linear_rand 依赖它来
 * 保证下标严格落在 [0, pool_size) 内)。随机状态只存储于 root 的私有扩展
 * 数据中,不依赖全局变量,天然支持并发执行多个 GEQO。
 *
 * 【参数】root —— PlannerInfo,提供随机状态。
 * 【返回值】[0,1) 区间内的 double。
 */
double
geqo_rand(PlannerInfo *root)
{
	GeqoPrivateData *private = GetGeqoPrivateData(root);

	return pg_prng_double(&private->random_state);
}

/*
 * geqo_randint - (中文)返回 [lower, upper] 闭区间内的均匀随机整数
 *
 * 【作用】在给定闭区间内取一个均匀随机整数,是 GEQO 各类离散随机选择的
 * 统一入口:如选择随机起始位置(CX/ERX)、随机交叉点(OX1/PMX)、随机
 * 城市/父代下标等。注意参数顺序是 (upper, lower),与直觉相反,调用方务必
 * 按此顺序传参。
 *
 * 【设计思想】直接委托给 pg_prng_uint64_range,由 PRNG 实现无偏的闭区间
 * 均匀采样(能正确处理 upper 与 lower 的任意顺序,但本模块约定调用时总是
 * upper >= lower)。代码里有一段注释说明:当前所有调用点的 lower 均非负,
 * 因此可以安全使用无符号版本的 uint64 区间采样,避免符号数边界问题;
 * 若未来出现负数 lower 的调用点,则需要改用其它接口。返回前把 uint64
 * 强转为 int,基于"当前上下界都不超出 int 范围"的假设。
 *
 * 【参数】
 *   root  —— PlannerInfo,提供随机状态;
 *   upper —— 区间上界;
 *   lower —— 区间下界。
 * 【返回值】[lower, upper] 内的随机整数。
 */
int
geqo_randint(PlannerInfo *root, int upper, int lower)
{
	GeqoPrivateData *private = GetGeqoPrivateData(root);

	/*
	 * In current usage, "lower" is never negative so we can just use
	 * pg_prng_uint64_range directly.
	 */
	return (int) pg_prng_uint64_range(&private->random_state, lower, upper);
}
