useful Kolmogorov inequality results

1. `MeasureTheory.maximal_ineq`：Doob 的 maximal inequality，适用于非负 submartingale。
2. `ProbabilityTheory.IndepFun.variance_sum`：有限个两两独立实随机变量的方差可加。
3. `ProbabilityTheory.meas_ge_le_variance_div_sq`：Chebyshev 不等式。
4. `ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt`：未来项对自然过滤的条件期望等于常数期望。
5. `MeasureTheory.martingale_of_condExp_sub_eq_zero_nat`：用一步增量条件期望为零构造 martingale。
6. `MeasureTheory.submartingale_of_condExp_sub_nonneg_nat`：用一步条件期望增量非负构造 submartingale。
7. `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp`：conditional Jensen 风格桥接的核心接口。

2026-03-12 当前有效进展

A. 已经完成的接口分层

8. 纯代数 / tail 重写：
   `partialSum`,
   `sum_range_shift_eq_sub`,
   `sum_range_shift_succ_eq_sub`,
   `partialSum_tail_eq_sub`,
   `partialSum_succ_sub_partialSum`.

9. 最大部分和与事件层：
   `partialSumMax`,
   `abs_partialSum_le_partialSumMax`,
   `partialSumMax_succ_eq_sup_abs_partialSum_succ`,
   `sq_le_sup_partialSum_succ_sq_iff_le_partialSumMax_succ`,
   `event_sup_partialSum_succ_sq_ge_eq_event_partialSumMax_ge`,
   `abs_sub_partialSum_le_partialSumMax_tail`,
   `partialSumMax_event_eq_biUnion`,
   `partialSumMax_tail_event_eq_biUnion_sub`,
   `measure_partialSumMax_event_le_sum`,
   `measure_partialSumMax_tail_event_le_sum_sub`,
   `measure_event_two_mul_partialSumMax_tail_le_sum_sub`,
   `measure_event_two_mul_partialSumMax_tail_le_sum_sub'`.

10. 单个 partial sum 的概率/方差控制：
   `partialSum_memLp`,
   `measure_partialSum_ge_le_variance_div_sq`,
   `integral_partialSum_eq_zero_of_forall_integral_zero`,
   `integral_partialSum_sq_eq_variance_of_forall_mean_zero`,
   `measure_partialSum_tail_ge_le_variance_div_sq`,
   `variance_partialSum_eq_sum_variance`,
   `variance_partialSum_tail_eq_sum_variance`,
   `measure_partialSum_tail_ge_le_sum_variance_div_sq`.

11. 零均值接口：
    `integral_partialSum_eq_sum_integral`,
    `integral_partialSum_tail_eq_zero_of_forall_integral_zero`,
    `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_mean_zero`,
    `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero`,
    `measure_partialSum_tail_abs_ge_le_sum_variance_div_sq_of_forall_mean_zero_of_mem_range`.

12. union-bound 路线下的弱 finite maximal bound：
    `measure_event_two_mul_partialSumMax_tail_le_sum_variance_div_sq_of_forall_mean_zero`,
    `measure_event_two_mul_partialSumMax_tail_le_mul_variance_div_sq_of_forall_mean_zero`,
    `div_sq_half_eq_four_mul_div_sq`,
    `measure_event_two_mul_partialSumMax_tail_le_mul_four_mul_variance_div_sq_of_forall_mean_zero`.
    注意：这些结果仍然带有多余的 `(n + 1)` 损失，只能算弱版。

13. 自然过滤与 martingale 路线：
    `partialSum_stronglyMeasurable_natural`,
    `stronglyAdapted_partialSum_succ_natural`,
    `condExp_natural_eq_zero_of_mean_zero`,
    `condExp_partialSum_succ_sub_eq_zero_of_mean_zero`,
    `martingale_partialSum_succ_natural_of_mean_zero`.

14. 平方过程与 submartingale 路线：
    `partialSum_succ_sq_nonneg`,
    `stronglyAdapted_partialSum_succ_sq_natural`,
    `integrable_partialSum_succ_sq`,
    `partialSum_succ_sq_le_condExp_partialSum_succ_sq_of_mean_zero`,
    `submartingale_partialSum_succ_sq_natural_of_mean_zero`,
    `smul_measure_partialSum_succ_sq_sup_ge_le_integral_partialSum_succ_sq_of_mean_zero`,
    `smul_measure_partialSumMax_ge_le_integral_partialSum_succ_sq_of_mean_zero`,
    `smul_measure_partialSumMax_ge_le_variance_partialSum_of_mean_zero`,
    `smul_measure_partialSumMax_ge_le_sum_variance_of_mean_zero`,
    `measure_partialSumMax_ge_le_sum_variance_div_sq_of_mean_zero`,
    `measure_partialSumMax_tail_ge_le_sum_variance_div_sq_of_mean_zero`,
    `measure_partialSumMax_tail_ge_le_sum_variance_div_sq_of_mean_zero'`,
    `measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero`.

B. 目前最重要的判断

15. 现在已经不需要继续扩写 union-bound 路线。
    Doob/maximal inequality 路线已经有了真正可用的输入对象：
    `fun n ω => partialSum X (n + 1) ω ^ 2`
    是自然过滤下的非负 submartingale。

16. 因此当前最自然的下一步是：
    直接把
    `submartingale_partialSum_succ_sq_natural_of_mean_zero`
    和
    `partialSum_succ_sq_nonneg`
    喂给 `MeasureTheory.maximal_ineq`，
    先得到一个以 `sup' (partialSum^2)` 表述的 finite maximal inequality。
    这一层现在已经完成；当前得到的是带 `NNReal` 阈值、右端为
    `∫ partialSum X (n + 1)^2 dμ`
    的 Doob 型不等式。

17. 做完 16 之后，还需要把 `maximal_ineq` 的 `sup'` 事件翻译回当前文件的
    `partialSumMax` / tail 记号，
    才能真正替代目前那个带 `(n + 1)` 损失的弱版 maximal bound。
    这是下一步唯一自然目标。
    其中第一层纯代数重写现在也已到位：
    `partialSumMax X (n + 1)` 已可改写成
    `sup' (fun k => |partialSum X (k + 1)|)`，
    即去掉了 `partialSumMax` 里的初始零项。
    这一层现在进一步完成到了事件/测度层：
    `((ε : ℝ)^2 ≤ sup' partialSum^2)` 已可精确改写为
    `(ε ≤ partialSumMax)`，
    因而 Doob 不等式左端已经转成了真正可用的
    `(ε^2) • μ {ε ≤ partialSumMax ...}`。
    右端也已完成第一层改写：
    在零均值假设下，
    `∫ partialSum X (n + 1)^2 dμ = variance (partialSum X (n + 1))`，
    且现在也已成功接上有限方差可加，
    得到
    `(ε^2) • μ {ε ≤ partialSumMax X (n + 1)} ≤ ofReal (∑ variance (X k))`。
    这最后一层纯代数整理现在也已完成 finite 版本：
    `μ {ε ≤ partialSumMax X (n + 1)} ≤ ofReal ((∑ variance (X k)) / ε^2)`。
    当前真正剩余的瓶颈已经切换到 tail 版本：
    把这条强版 finite Kolmogorov inequality 施加到 shifted sequence
    `fun j => X (m + 1 + j)`，
    再配合 `ε / 2` 改写成证明 two-series theorem 所需的
    `4 / ε^2` 形状。

C. 离最终 two-series theorem 还差什么

18. strong tail maximal inequality 已经具备 theorem-ready 输入：
    `measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero`
    直接给出
    `μ {ε ≤ 2 * partialSumMax (fun j => X (m + 1 + j)) n} ≤ ofReal (4 * tailVarSum / ε^2)`。
    因而概率论部分当前不再是瓶颈。

19. 下一步 1：先做纯确定性的 oscillation 控制小 lemma。
    目标形状应尽量只涉及有限 tail partial sums，
    例如先证明对任意固定 `m` 与样本点 `ω`，
    所有
    `S_(m + k) ω - S_m ω`
    都被
    `partialSumMax (fun j => X (m + 1 + j)) n ω`
    控制；
    再把它提升为
    `limsup (fun N => S_N ω - S_m ω) - liminf (fun N => S_N ω - S_m ω)
      ≤ 2 * sInf {a | ...}` / 或更直接的 tail `sup` 控制版本。
    这里应优先复用
    `partialSum_tail_eq_sub`
    和
    `abs_sub_partialSum_le_partialSumMax_tail`，
    不要重新走一遍索引代数。

20. 下一步 2：把 19 的 deterministic bound 接到事件层。
    需要得到“oscillation 大于等于 `ε` 的事件”
    被
    `{ω | ε ≤ 2 * partialSumMax tail}`
    覆盖，
    这样才能直接套用 18。
    这一步应该先做集合包含，再转成测度不等式。

21. 下一步 3：补实分析尾和衰减。
    从
    `HasSum (fun n => variance (X n) μ) s`
    或相应的级数收敛假设，
    推出对每个 `ε > 0`，
    存在 `M`，使得当 `m ≥ M` 时，
    所有有限 tail sums
    `∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ`
    都足够小。
    这一层一旦完成，18 的右端就能随 `m → ∞` 压到 `0`。

22. 下一步 4：完成 mean-zero 的 a.s. 收敛。
    用 20 和 21 证明 tail oscillation 的概率任意小，
    再令 `m → ∞` 得到 oscillation 为 `0` a.s.；
    随后把“oscillation 为 0”转成部分和序列 a.s. 收敛。

23. 下一步 5：最后才做一般均值版本。
    定义中心化变量
    `Y n ω = X n ω - ∫ ω, X n ω ∂μ`，
    对 `Y` 应用 22，
    再用 `∑ μ_n` 收敛把原部分和恢复回来。

24. 当前最小可执行目标：
    先在 `Kolmogorov.lean` 中加入一个纯 deterministic oscillation bridge lemma，
    只处理固定 `m`、固定 tail partial sums 与 `partialSumMax` 的关系，
    暂时不要同时碰 a.e.、`limsup/liminf` 与级数尾和衰减三层内容。

D. 实现时的具体注意点

24. 处理 natural filtration 时，shifted process
    `n ↦ partialSum X (n + 1)`
    比 `partialSum X n` 更顺手，因为时刻 `i` 的增量正好是 `X (i + 1)`。

25. `MeasureTheory.maximal_ineq` 的准确输出形状是
    `ε • μ {ω | ε ≤ sup' ...} ≤ ENNReal.ofReal (∫_event f n dμ)`，
    因而第一步最好先用 `setIntegral_le_integral` 把右端放宽到全空间积分，
    再做事件改写和除以阈值的整理。

26. `Finset.sup'_le_iff` / `Finset.le_sup'` 足够处理
    `partialSumMax` 与 shifted `sup'` 的确定性改写；
    这一步不需要额外找 `sup'_image` 风格 API。

27. 处理平方阈值时，`sq_le_sq₀` 比 `sq_le_sq` 更合适：
    因为阈值来自 `NNReal`，其非负性可直接使用，
    从而能在
    `ε^2 ≤ |x|^2` 和 `ε ≤ |x|`
    之间稳定往返。

28. 右端从 `∫ S_n^2` 到 `variance S_n` 的改写不需要额外概率论 machinery：
    直接用 `variance_eq_integral`，
    再用零均值把 `μ[S_n]` 消掉即可。

29. `iIndepFun.indepFun (hij : i ≠ j)` 足够直接构造
    `variance_partialSum_eq_sum_variance`
    所需的有限 `Set.Pairwise` 独立性；
    这里不需要额外的 finite-family bridge lemma。

30. 在 `ENNReal.le_div_iff_mul_le` 里，
    用 `ε : NNReal` 组织“除以 `ε^2`”最稳，
    然后再通过
    `ENNReal.ofReal_div_of_pos` 和
    `ENNReal.ofReal_pow`
    回到实数里的 `/ ε^2` 形状。

31. 把 non-tail 引理搬到 shifted sequence 时，
    `iIndepFun.precomp` 已经够用；
    目前这条路线里的索引偏移已经通过对 `n = 0 / n + 1` 分情况吸收掉了。

32. strong tail maximal inequality 现在已经不再依赖 union-bound；
    旧的 weak tail lemmas 可以作为对照保留，但主线应优先使用
    `measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero`。

33. `condExp_of_stronglyMeasurable` 给的是函数等式；
    若要和 `condExp_sub` 等 a.e. 等式拼接，需要显式加 `.eventuallyEq`。

34. `condVar_ae_eq_condExp_sq_sub_sq_condExp` 比直接找 “square is submartingale” theorem
    更好用；当前平方过程 submartingale 的证明就是通过它手工搭起来的。

35. 目前 `notice.md` 已清理过一次。
    以后优先维护：
    当前有效接口、
    当前真实瓶颈、
    下一步唯一最自然的目标。
    不要继续累积已经完成后的旧“下一步建议”。

2026-03-12 本轮新增进展

36. 这次按“小步推进”只补了 deterministic bridge，不碰 a.e.、`limsup/liminf` 和尾和收敛。
    新增：
    `abs_sub_partialSum_le_two_mul_partialSumMax_tail`，
    `tail_pair_event_subset_two_mul_partialSumMax_event`。
    它们把原先“每个 tail partial sum 与基点 `S_(m+1)` 的距离受控”
    升级成
    “任意两个有限 tail partial sums 的差都受 `2 * partialSumMax` 控制”
    以及对应事件包含。

37. 本轮搜索/实现结论：
    证明这个 pairwise bound 不需要新找概率论 API；
    直接用
    `abs_sub_partialSum_le_partialSumMax_tail`
    两次，
    再配合实数三角不等式 `abs_add_le` 与 `ring_nf`
    做代数重写即可。
    因而这一步是稳定的 deterministic 层封装。

38. 当前真实瓶颈进一步收缩为：
    把 36 的 pairwise finite oscillation 控制提升到真正要用的
    tail oscillation / `limsup - liminf` 控制。
    下一步最自然目标是：
    先在固定样本点 `ω` 下，把有限窗口
    `sup_{j,k≤n} |S_{m+j+1} ω - S_{m+k+1} ω|`
    压到
    `2 * partialSumMax tail n ω`；
    之后再考虑把这个 finite 版本送入 `limsup/liminf`。
