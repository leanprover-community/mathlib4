Kolmogorov two-series theorem formalization notes

2026-03-12 status

Done:
- Step 1: reduce the tail oscillation event to a countable union of finite oscillation events.
- Step 2: bound the tail oscillation event by `tailVarianceBound`.
- Step 3: show `tailVarianceBound → 0` from summable variances.
- Step 4: in the mean-zero case, partial sums are a.e. Cauchy, hence a.e. convergent in `ℝ`.
- Step 5: center the variables and deduce the general theorem on a probability space.

Current endpoint in `Kolmogorov.lean`:
- `kolmogorov_two_series`

Remaining:
- No remaining step in `notice.md`.

Useful Step 5 lemmas added:
- `centered`
- `integral_centered_eq_zero`
- `variance_centered_eq`
- `partialSum_eq_partialSum_centered_add_sum_integral`
- `ae_exists_tendsto_partialSum_of_summable_mean_of_summable_variance`
