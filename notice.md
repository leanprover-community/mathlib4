Kolmogorov two-series theorem formalization notes

2026-03-12 status

Done:
- Step 1: reduce the tail oscillation event to a countable union of finite oscillation events.
- Step 2: bound the tail oscillation event by `tailVarianceBound`.
- Step 3: show `tailVarianceBound → 0` from summable variances.
- Step 4: in the mean-zero case, partial sums are a.e. Cauchy, hence a.e. convergent in `ℝ`.

Current endpoint in `Kolmogorov.lean`:
- `ae_exists_tendsto_partialSum_of_summable_variance_of_mean_zero`

Remaining:
- Step 5: center the variables and deduce the full nonzero-mean Kolmogorov two-series theorem.
