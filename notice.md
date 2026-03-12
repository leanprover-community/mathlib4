Kolmogorov two-series theorem formalization notes

2026-03-12 minimal state

1. Done

- Finite Kolmogorov tail inequality.
- Deterministic tail oscillation bridge.
- Step 1: liminf tail-oscillation event reduced to a countable union.
- Step 2: tail oscillation event has a measure bound in terms of an `iSup` of finite tail variance bounds.
- Step 3: the tail variance bound is now controlled by tail `tsum`, and tends to `0` as `m → ∞`.

2. Key lemmas in `Kolmogorov.lean`

- `limsup_sub_liminf_partialSum_tail_le_liminf_finiteTailOscillationMax`
- `event_le_liminf_finiteTailOscillationMax_subset_iUnion`
- `measure_tail_oscillation_event_le_iSup_four_mul_variance_div_sq_of_mean_zero`
- `tailVarianceBound`
- `iSup_four_mul_variance_div_sq_le_ofReal_tsum_variance_tail`
- `tendsto_iSup_four_mul_variance_div_sq_of_summable`

3. Remaining steps

- Step 4:
  Finish the mean-zero theorem: tail oscillation is `0` a.s., hence partial sums converge a.s.
- Step 5:
  Center the variables and deduce the general nonzero-mean case.

4. Next useful interfaces

- `Monotone.measure_iUnion`
- `_root_.tendsto_sum_nat_add`
- `Summable.sum_le_tsum`
