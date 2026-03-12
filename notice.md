Kolmogorov two-series theorem formalization notes

2026-03-12 concise state

1. Current status

- Finite Kolmogorov tail inequality is already formalized.
- Deterministic tail oscillation bridge is already formalized.
- Step 1 is done: the liminf tail-oscillation event is reduced to a countable union of finite oscillation events.

2. Most useful lemmas already in `Kolmogorov.lean`

- `measure_event_two_mul_partialSumMax_tail_le_four_mul_variance_div_sq_of_mean_zero`
- `measure_finiteTailOscillationMax_event_le_four_mul_variance_div_sq_of_mean_zero`
- `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`
- `finiteTailOscillationMax_nonneg`
- `event_le_liminf_finiteTailOscillationMax_subset_iUnion`

3. What remains

- Step 2:
  Turn
  `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`
  plus
  `event_le_liminf_finiteTailOscillationMax_subset_iUnion`
  into a measure bound for
  `{ω | ε ≤ limsup tail partial sums - liminf tail partial sums}`.
- Step 3:
  Show tail variance sums
  `∑ j ∈ Finset.range n, variance (X (m + 1 + j)) μ`
  go to `0` as `m → ∞`, assuming convergence/summability of `∑ variance (X n)`.
- Step 4:
  Finish the mean-zero theorem: tail oscillation is `0` almost surely, hence partial sums converge a.s.
- Step 5:
  Handle the general case by centering:
  `Y n ω = X n ω - μ[X n]`,
  apply the mean-zero theorem to `Y`,
  then add back the convergent series of means.

4. Search notes worth remembering

- `Filter.eventually_lt_of_lt_liminf`
- `Filter.isBoundedUnder_of`
- For measure estimates, likely next tool is `measure_iUnion_le`.

5. Implementation reminders

- Work in `Kolmogorov.lean` only.
- Prefer the strong tail maximal inequality route, not the older union-bound route.
- Reuse
  `finiteTailOscillationMax`,
  `finiteTailSup`,
  `finiteTailInf`
  rather than rebuilding finite window objects.
