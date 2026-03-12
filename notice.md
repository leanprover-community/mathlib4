useful Kolmogorov inequality results

1. `MeasureTheory.maximal_ineq`：Doob 的 maximal inequality，适用于**非负 submartingale**。文档写得很明确。
2. `ProbabilityTheory.IndepFun.variance_sum`：有限个两两独立实随机变量的方差可加。
3. `ProbabilityTheory.meas_ge_le_variance_div_sq`：Chebyshev 不等式。

2026-03-12:

4. 在 `Kolmogorov.lean` 里先落了一个纯代数步骤，不碰概率空间：
   `Kolmogorov.sum_range_shift_eq_sub` 和 `Kolmogorov.sum_range_shift_succ_eq_sub`。
   它们把尾和 `∑_{i < n} f (m + i)` / `∑_{i < n} f (m + 1 + i)` 改写成两个初始部分和的差。
5. 这一步用归纳最稳。试过直接拿 `Finset.sum_Ico_eq_sub` + `simp`，化简方向不太顺，先不硬凑。
6. 代码里注意本地记号是 `∑ i ∈ s, ...`，不是 `∑ i in s, ...`。
