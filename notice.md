Kolmogorov two-series theorem formalization notes

2026-03-12 current state

1. Useful Mathlib interfaces

- `MeasureTheory.maximal_ineq`: Doob maximal inequality for nonnegative submartingales.
- `ProbabilityTheory.IndepFun.variance_sum`: finite variance additivity under pairwise independence.
- `ProbabilityTheory.meas_ge_le_variance_div_sq`: Chebyshev inequality.
- `ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt`: future coordinate has constant conditional expectation on the natural filtration.
- `MeasureTheory.martingale_of_condExp_sub_eq_zero_nat`: build a martingale from one-step conditional expectation zero.
- `MeasureTheory.submartingale_of_condExp_sub_nonneg_nat`: build a submartingale from one-step conditional expectation increment nonnegative.
- `ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp`: main bridge for the square-process submartingale proof.

2. Current effective interfaces in `Kolmogorov.lean`

- Partial sums and tail reindexing:
  `partialSum`,
  `partialSum_tail_eq_sub`,
  `partialSum_succ_sub_partialSum`.
- Strong finite Kolmogorov inequality for tails:
  `measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero`.
- Finite oscillation objects:
  `finiteTailOscillationMax`,
  `finiteTailSup`,
  `finiteTailInf`.
- Finite oscillation vs maximal tail partial sum:
  `finiteTailOscillationMax_le_two_mul_partialSumMax_tail`,
  `measure_finiteTailOscillationMax_event_le_four_mul_variance_div_sq_of_mean_zero`,
  `measure_finiteTailSup_sub_finiteTailInf_event_le_four_mul_variance_div_sq_of_mean_zero`.
- Deterministic tail bridge:
  `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`.
  This is the current key deterministic lemma.

3. What is already solved

- The probability-theoretic finite/tail maximal inequality is no longer the bottleneck.
- The deterministic bridge from tail partial sums to a tail oscillation envelope is essentially in place.
- In particular, for fixed `m` and `ω`, the tail oscillation
  `limsup partialSum tail - liminf partialSum tail`
  is now controlled by
  `liminf (finiteTailOscillationMax X m n ω)`.

4. Real bottleneck now

- Convert the deterministic bridge into an event inclusion and then a measure inequality.
- After that, prove tail variance sums go to `0` from the summability/convergence assumption on
  `variance (X n)`.
- Then finish the mean-zero almost sure convergence.
- Only after that, do the general nonzero-mean version by centering.

5. Next natural steps

- Step 1:
  Prove an event-level lemma of the form
  `{ω | ε ≤ liminf (fun n => finiteTailOscillationMax X m n ω)}`
  is controlled by finite oscillation events, or directly by the existing strong tail maximal bound.
- Step 2:
  Deduce a measure bound for
  `{ω | ε ≤ limsup tail partial sums - liminf tail partial sums}`.
- Step 3:
  From convergence/summability of `∑ variance (X n)`, prove every finite tail variance sum
  `∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ`
  becomes small as `m → ∞`.
- Step 4:
  Finish the mean-zero theorem: tail oscillation is `0` a.s., hence partial sums converge a.s.
- Step 5:
  Center the variables
  `Y n ω = X n ω - μ[X n]`,
  apply the mean-zero result to `Y`,
  then restore the original series using convergence of `∑ μ[X n]`.

6. Implementation notes

- Main line should use the strong tail maximal inequality
  `measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero`,
  not the older union-bound route.
- The shifted process `n ↦ partialSum X (n + 1)` is the convenient martingale index convention.
- For deterministic tail arguments, reuse
  `finiteTailOscillationMax`,
  `finiteTailSup`,
  `finiteTailInf`
  instead of rebuilding finite-window objects.
- For limsup/liminf inequalities on `ℝ`, prefer the existing wrappers in this file:
  `limsup_le_of_eventually_le_nat'`,
  `le_liminf_of_eventually_le_nat'`,
  `limsup_sub_liminf_le_of_eventually_bounded_nat'`.
- When combining `condExp_of_stronglyMeasurable` with `condExp_sub`-style lemmas, remember to use
  `.eventuallyEq` explicitly.

7. Latest completed step

- Added
  `ciSup_finiteTailSup_sub_ciInf_finiteTailInf_le_liminf_finiteTailOscillationMax`
  and
  `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`.
- This means the deterministic oscillation bridge has reached the form actually needed for the final theorem.

2026-03-12 Step1 progress update

8. What was completed this round

- Finished the `notice` Step 1 in the minimal useful form.
- Added `finiteTailOscillationMax_nonneg`.
  This packages the trivial lower bound needed to use `Filter.eventually_lt_of_lt_liminf`.
- Added
  `event_le_liminf_finiteTailOscillationMax_subset_iUnion`.
  Concretely, for `η < ε`,
  `{ω | ε ≤ liminf (fun n => finiteTailOscillationMax X m n ω)}`
  is contained in
  `⋃ n, {ω | η ≤ finiteTailOscillationMax X m n ω}`.

9. Useful search result for this step

- `Mathlib/Order/LiminfLimsup.lean`:
  `Filter.eventually_lt_of_lt_liminf`.
  This is the right interface to turn a pointwise inequality
  `η < liminf u`
  into an eventual statement `η < u n`.
- `Mathlib/Order/Filter/IsBounded.lean`:
  `Filter.isBoundedUnder_of`.
  This is the clean way to manufacture the bounded-below hypothesis for the liminf lemma from
  `finiteTailOscillationMax_nonneg`.

10. Why this formulation was chosen

- It keeps the step small and directly reusable for the measure step.
- The target set is controlled by a countable union of finite oscillation events, so the next move can use
  `measure_iUnion_le`.
- I intentionally used a slack threshold `η < ε` instead of trying to force the exact threshold `ε`.
  The strict liminf API naturally gives eventual strict inequalities, so this avoids unnecessary friction.
  For the next step, taking `η = ε / 2` when `ε > 0` should be the clean path.

11. Immediate next step

- Use the deterministic bridge
  `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`
  together with
  `event_le_liminf_finiteTailOscillationMax_subset_iUnion`
  to get an event inclusion for
  `{ω | ε ≤ limsup tail partial sums - liminf tail partial sums}`.
- Then convert that inclusion into a measure bound, probably first with
  `measure_iUnion_le`, and only afterwards optimize it if a sharper monotone-union argument is available.
