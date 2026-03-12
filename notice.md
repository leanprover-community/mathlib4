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

2026-03-12 当前进展（阶段性总结）:

7. 已经把“尾部部分和”这条链路的基础接口铺到概率层了，主要分成六层：
   (a) 纯代数：`partialSum`、`partialSum_tail_eq_sub`，把 shifted partial sums 改写成原序列两个部分和的差。
   (b) 最大部分和：`partialSumMax`、`abs_partialSum_le_partialSumMax`、`abs_sub_partialSum_le_partialSumMax_tail`。
   (c) 事件层：`partialSumMax_event_eq_biUnion`、`partialSumMax_tail_event_eq_biUnion_sub`，把 maximal event 改写成有限并。
   (d) union bound：`measure_partialSumMax_event_le_sum`、`measure_partialSumMax_tail_event_le_sum_sub`。
   (e) `ε/2` 缩放：`partialSumMax_nonneg`、`event_two_mul_partialSumMax_ge_eq`、`measure_event_two_mul_partialSumMax_tail_le_sum_sub`、`measure_event_two_mul_partialSumMax_tail_le_sum_sub'`。
   (f) 概率与方差：`partialSum_memLp`、`measure_partialSum_ge_le_variance_div_sq`、`measure_partialSum_tail_ge_le_variance_div_sq`、`variance_partialSum_eq_sum_variance`、`variance_partialSum_tail_eq_sum_variance`。

8. 已经有一个相当关键的尾部估计：
   `measure_partialSum_tail_ge_le_sum_variance_div_sq`。
   它把 shifted partial sum 的 Chebyshev 上界直接改写成“尾部方差和 / ε^2”形式。

9. 在“尾部部分和均值为 0”的附加假设下，又得到：
   `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_mean_zero`。
   这已经非常接近原证明里真正想用的
   `μ { ε ≤ |∑ tail terms| } ≤ ...`
   形式。

10. 当前还没做的核心部分主要有两块：
   (a) 把单个 shifted partial sum 的方差和版 Chebyshev 上界，系统地汇总成一个 finite maximal inequality 风格的结论。
   (b) 从 finite tail estimate 走到 `limsup - liminf = 0` a.s.，也就是 two-series theorem 的收尾部分。

11. 一个重要判断：现在仓库里虽然还没有真正的 Kolmogorov inequality lemma，但已经有足够多的接口，能把“最大值事件”“`ε/2` 缩放”“tail difference”“方差和”这些步骤几乎逐块拼起来。剩下工作比前面更像“组装”而不是“找定理名”。

2026-03-12 接下来最自然的计划:

12. 下一小步优先做一个 finite tail maximal bound，目标形状接近：
   `μ {ω | ε ≤ 2 * partialSumMax (fun j => X (m+1+j)) n ω} ≤ ENNReal.ofReal (4 * ((∑ variance)/ε^2))`
   或等价改写。
   这一步应该只是在现有 lemma 之间做一次组合，不需要碰最终 almost sure 收敛。

13. 如果上一步顺利，再继续做一个“零均值如何传给 tail partial sums”的小 lemma。
   目前零均值版本是手工假设 `μ[partialSum ...] = 0`。
   后面最好把它从更原子的假设
   `∀ k < n, μ[X (m+1+k)] = 0`
   推出来。

14. 再下一步才是处理极限对象：
   把 `limsup S_N - liminf S_N` 用 tail maximal sums 控制；
   然后利用 tail variance sums 随 `m → ∞` 消失，得到 oscillation 为 `0`。

15. 目前建议继续保持“小步可编译”的节奏：
   一次只加一个桥接 lemma；
   每次优先让新 lemma 的 statement 尽量贴近原证明文本；
   避免过早把整个 two-series theorem 的顶层 statement 硬写出来。
