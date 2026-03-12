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

2026-03-12 本次推进:

16. 这次优先补了“零均值如何传给 tail partial sums”这一层，没有直接碰 maximal inequality。
    新增了三个 lemma：
    (a) `integral_partialSum_eq_sum_integral`：把 `μ[partialSum X n]` 展开成有限和 `∑ μ[X k]`；
    (b) `integral_partialSum_tail_eq_zero_of_forall_integral_zero`：若尾部每一项均值为 `0`，则尾部 partial sum 的均值为 `0`；
    (c) `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero`：把现有 Chebyshev + variance bound 包装成直接接受“逐项零均值”假设的版本。

17. 搜索记录：
    (a) `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` 里的 `integral_finset_sum` 可以直接处理 `μ[∑ i ∈ s, f i]`；
    (b) `MemLp.integrable` 足够把 `MemLp _ 2 μ` 降到可积性；
    (c) 试过直接 `rw [partialSum, integral_finset_sum]`，rewrite 方向不稳，最后改成 `simpa [partialSum] using integral_finset_sum ...` 更可靠。

18. 完成情况：
    (a) `lake env lean Kolmogorov.lean` 已通过；
    (b) 当前零均值接口不再需要手工提供 `μ[partialSum ...] = 0`，后面拼 maximal bound 时可以直接从逐项均值为零出发。

19. 下一小步建议：
    用 `measure_event_two_mul_partialSumMax_tail_le_sum_sub'` 和新得到的
    `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero`
    组装出一个 finite tail maximal bound。
    即使暂时还是 union-bound 形状，也能把“最大值事件”统一改写成“若干 tail variance sums”的和，为后面再收紧常数做准备。

2026-03-12 继续推进:

20. 这次没有直接做完整 maximal bound，而是先补了一个更细的“截断接口”：
    `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero_of_mem_range`。
    它的作用是：
    若我们已知对 `range (n + 1)` 上所有 tail terms 都有 `MemLp`、两两独立、均值为 `0`，
    那么对任意 `k ≤ n`，都能直接得到第 `k` 个 tail partial sum 的 variance bound。

21. 这一步的技术点主要是“把大范围假设限制到小范围”：
    (a) `MemLp` 和均值为零都用 `Finset.mem_range.mp` + `Nat.lt_trans` 从 `j < k` 推到 `j < n + 1`；
    (b) pairwise independence 用 `Set.Pairwise.mono` 把
        `↑(Finset.range (n + 1))` 上的结论限制到 `↑(Finset.range k)`。

22. 完成情况：
    (a) 新 lemma 已加入 `Kolmogorov.lean`；
    (b) `lake env lean Kolmogorov.lean` 再次通过；
    (c) 现在已经能对 union bound 展开后每一个 summand 自动套上同一模板，不必再为每个 `k` 单独重建假设。

23. 下一小步更明确了：
    直接从 `measure_event_two_mul_partialSumMax_tail_le_sum_sub'` 出发，
    对右侧 `∑ k ∈ range (n + 1), μ {... partialSum ... k ...}` 的每一项应用新 lemma，
    得到一个 finite maximal event 的总和上界。
    这一步很可能就是把当前准备好的接口真正“组装”起来。

2026-03-12 再推进一步:

24. 这次把上两步准备好的接口真正组装起来了，新增：
    `measure_event_two_mul_partialSumMax_tail_le_sum_variance_div_sq_of_forall_mean_zero`。
    它给出一个 finite maximal event 的总和上界：
    `μ { ε ≤ 2 * partialSumMax tail n }`
    被一个
    `∑ k ∈ range (n + 1), ENNReal.ofReal ((∑_{j<k} variance_j) / (ε/2)^2)`
    控制。

25. 证明结构非常直接：
    (a) 先用 `measure_event_two_mul_partialSumMax_tail_le_sum_sub'`
        把 maximal event 变成对各个 `k` 的 partial sum 事件求和；
    (b) 再对每一项调用
        `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero_of_mem_range`；
    (c) `ε / 2 > 0` 用一次 `linarith` 即可。

26. 完成情况：
    (a) 这已经是第一个真正意义上的 finite tail maximal bound，只是右侧还是“前缀方差和的有限和”；
    (b) `lake env lean Kolmogorov.lean` 通过；
    (c) 目前还没有把右侧再压缩成单个尾部方差和，常数也还没整理成 `4 / ε^2` 的经典外形。

27. 下一小步建议：
    尝试继续压缩右侧的有限和。
    可能有两条路：
    (a) 先做一个纯代数/序上的 lemma，比较
        `∑ k ≤ n, (∑ j < k, a_j)` 和 `C * ∑ j < n, a_j`；
    (b) 或者改方向，直接开始接 Doob/maximal inequality，避免 union bound 带来的多余求和。
    从当前文件状态看，若继续保持“小步稳编译”，更适合先把右侧有限和的整理接口做出来。

2026-03-12 再压一层:

28. 这次在上一条 finite maximal bound 的基础上，新增了
    `measure_event_two_mul_partialSumMax_tail_le_mul_variance_div_sq_of_forall_mean_zero`。
    它把右侧的“前缀方差和的有限和”压成
    `(n + 1) * ENNReal.ofReal ((尾部总方差和) / (ε / 2)^2)`。

29. 证明思路是纯序比较，没有新概率内容：
    (a) 对每个 `k ≤ n`，用
        `∑_{j < k} variance_j ≤ ∑_{j < n+1} variance_j`；
    (b) 这里用的是
        `Finset.sum_le_sum_of_subset_of_nonneg`，
        非负性来自 `variance_nonneg`；
    (c) 然后把有限个相同常数求和，`simp` 自动化成 `(n + 1) * c`。

30. 这一步的意义：
    虽然还保留了多余的 `(n + 1)` 因子，离真正的 Kolmogorov inequality 还差一截，
    但右侧现在已经从“双重和”化成“单个 tail variance sum”，后面无论继续做纯代数整理，
    还是改走 Doob/maximal inequality 路线，接口都会更干净。

31. 完成情况：
    (a) 新 lemma 已加入 `Kolmogorov.lean`；
    (b) `lake env lean Kolmogorov.lean` 通过；
    (c) 这说明当前 union-bound 路线至少已经稳定地产出了一个可用但较弱的 finite maximal estimate。

32. 下一小步建议：
    更合理的是开始尝试避开 union bound 的 `(n + 1)` 损失。
    即优先研究能否把 `partialSum` 序列包装成 martingale / submartingale，
    然后直接套 `MeasureTheory.maximal_ineq` 或相关结果。
    如果先不换路线，也可以补一个纯代数 lemma，把
    `ENNReal.ofReal ((A) / (ε / 2)^2)` 改写成
    `ENNReal.ofReal (4 * A / ε^2)` 的经典常数外形。

2026-03-12 常数整理:

33. 这次先走了上面 32(b) 这条更稳的小步，没有碰 martingale。
    新增了两个 lemma：
    (a) `div_sq_half_eq_four_mul_div_sq`：
        纯代数地把 `a / (ε / 2)^2` 改写成 `4 * a / ε^2`；
    (b) `measure_event_two_mul_partialSumMax_tail_le_mul_four_mul_variance_div_sq_of_forall_mean_zero`：
        把前一版 finite tail maximal bound 的常数整理成更贴近原证明文本的
        `4 / ε^2` 外形。

34. 搜索/实现记录：
    (a) 这一步不需要新搜 mathlib 定理，直接在本地做一个实数域恒等式最省事；
    (b) `field_simp` + `ring` 足够处理 `ε ≠ 0` 情形；
    (c) `ε = 0` 单独分支后 `simp` 即可，所以这个重写 lemma 不需要额外假设。

35. 完成情况：
    (a) `Kolmogorov.lean` 新增经典常数版接口；
    (b) `lake env lean Kolmogorov.lean` 已通过；
    (c) 现在现有的较弱 finite maximal estimate 在 statement 上已经更接近 wiki 里的 `4 ε^{-2}` 形式，
        后续如果改走 Doob/maximal inequality，只需要继续去掉多余的 `(n + 1)` 因子。

36. 下一小步建议：
    优先开始研究 `partialSum` 是否已经能接到现成的 martingale / submartingale maximal inequality。
    如果能直接套 `MeasureTheory.maximal_ineq`，就有机会绕开 union bound，
    从当前“弱但形状接近”的版本过渡到真正的 Kolmogorov inequality。

2026-03-12 自然过滤桥接:

37. 这次开始实际探 Doob / martingale 方向，但仍然只补一个桥接层，没有去写完整 martingale 证明。
    新增了两个 lemma：
    (a) `partialSum_stronglyMeasurable_natural`：
        若 `n ≤ i + 1`，则 `partialSum X n` 对 `Filtration.natural X` 在时刻 `i` 强可测；
    (b) `stronglyAdapted_partialSum_succ_natural`：
        于是过程 `n ↦ partialSum X (n + 1)` 对 `X` 的自然过滤是 `StronglyAdapted`。

38. 搜索记录：
    (a) `Mathlib/Probability/Process/Adapted.lean` 里有
        `Filtration.stronglyAdapted_natural`，可直接给 `X` 在自己自然过滤下的强适应性；
    (b) `Mathlib/Probability/BorelCantelli.lean` 里有
        `iIndepFun.condExp_natural_ae_eq_of_lt`，
        这说明后面要做“未来项对过去过滤的条件期望等于常数”时，不必从头证明；
    (c) 一个重要判断：更合适的对象不是 `partialSum X n`，而是 shifted process
        `n ↦ partialSum X (n + 1)`，这样时刻 `i` 的过滤正好包含第 `i` 项增量。

39. 实现细节：
    (a) `partialSum_stronglyMeasurable_natural` 用 `partialSum_succ` 归纳；
    (b) 递归项里 `partialSum X n` 保持在同一时刻 `i` 上可测，
        单项 `X n` 则由 `Filtration.stronglyAdapted_natural hX n`
        再用 filtration monotonicity 推到时刻 `i`；
    (c) 为了使用这些接口，这次在 `Kolmogorov.lean` 补加了
        `import Mathlib.Probability.Process.Adapted`。

40. 完成情况：
    (a) `lake env lean Kolmogorov.lean` 已通过；
    (b) 现在已经把 partial sums 和 natural filtration 接到了同一套语言里，
        后面可以继续尝试证明 shifted partial sums 是 martingale，
        再考虑 `square` / `pos` / `maximal_ineq` 这条线。

41. 下一小步建议：
    直接尝试证明一个“shifted partial sums 在自然过滤下是 martingale”的 lemma。
    预期关键步会是把
    `μ[X j | Filtration.natural X i]`
    在 `i < j` 时改写成常数 `μ[X j]`，然后在零均值假设下化成 `0`。
