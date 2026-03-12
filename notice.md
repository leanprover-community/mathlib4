Kolmogorov two-series theorem formalization notes

2026-03-12 minimal state

1. Done

- Finite Kolmogorov tail inequality.
- Deterministic tail oscillation bridge.
- Step 1: liminf tail-oscillation event reduced to a countable union.
- Step 2: tail oscillation event has a measure bound in terms of an `iSup` of finite tail variance bounds.
- Step 3: the tail variance bound is now controlled by tail `tsum`, and tends to `0` as `m → ∞`.
- Step 4: for each fixed `ε > 0`, the bad tail-oscillation event `⋂ m, tailOscillationEvent X m ε`
  has measure `0`; using the scales `1 / (n + 1)`, the partial sums are a.e. Cauchy, hence a.e.
  convergent in `ℝ`.

2. Key lemmas in `Kolmogorov.lean`

- `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`
- `event_le_liminf_finiteTailOscillationMax_subset_iUnion`
- `measure_tail_oscillation_event_le_iSup_four_mul_variance_div_sq_of_mean_zero`
- `tailVarianceBound`
- `iSup_four_mul_variance_div_sq_le_ofReal_tsum_variance_tail`
- `tendsto_iSup_four_mul_variance_div_sq_of_summable`
- `tailOscillationEvent`
- `measure_tailOscillationEvent_le_tailVarianceBound_of_mean_zero`
- `measure_iInter_tailOscillationEvent_eq_zero_of_summable`
- `ae_cauchySeq_partialSum_of_summable_variance_of_mean_zero`
- `ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero`

3. Remaining steps

- Step 5:
  Center the variables and deduce the general nonzero-mean case.

4. Next useful interfaces

- `tendsto_measure_iInter_atTop`
- `measure_eq_zero_iff_ae_notMem`
- `ae_all_iff`
- `Metric.cauchySeq_iff`
- `cauchySeq_tendsto_of_complete`
