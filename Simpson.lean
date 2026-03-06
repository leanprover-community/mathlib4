/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Field

/-!
# Simpson's Midpoint Rule

This file contains a definition of integration via Simpson's midpoint rule, along with
an error bound in terms of a bound on the third derivative of the antiderivative.

## Main results
- `simpson_midpoint_error_le`: the convergence theorem for Simpson's midpoint rule.
- `simpson_midpoint_composite_error_le`: the composite midpoint rule error bound.

## References
We follow the standard proof for the error bound of the midpoint rule.
-/

@[expose] public section

open MeasureTheory intervalIntegral Interval Finset HasDerivWithinAt Set

/-- Integration of `f` from `a` to `b` using Simpson's midpoint rule with `N` subintervals.
This uses the midpoint of each subinterval: `∫_a^b f(x) dx ≈ h * ∑_{i=0}^{n-1} f(x_{i+1/2})`
where `h = (b - a) / n` and `x_{i+1/2} = a + (i + 1/2) * h`. -/
noncomputable def simpson_midpoint_integral (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  ((b - a) / N) * ∑ k ∈ range N, f (a + (k + 1 / 2 : ℝ) * (b - a) / N)

/-- The absolute error of Simpson's midpoint integration. -/
noncomputable def simpson_midpoint_error (f : ℝ → ℝ) (N : ℕ) (a b : ℝ) : ℝ :=
  (simpson_midpoint_integral f N a b) - (∫ x in a..b, f x)

/-- Just like exact integration, the Simpson midpoint approximation retains the same magnitude but
changes sign when the endpoints are swapped. -/
theorem simpson_midpoint_integral_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    simpson_midpoint_integral f N a b = -(simpson_midpoint_integral f N b a) := by
  unfold simpson_midpoint_integral

  have h_coeff : (b - a) / N = -((a - b) / N) := by ring

  -- 证明求和部分相等：用变量替换 j = N - 1 - k
  have h_sum : ∑ k ∈ range N, f (a + (k + (1 / 2 : ℝ)) * (b - a) / N)
             = ∑ k ∈ range N, f (b + (k + (1 / 2 : ℝ)) * (a - b) / N) := by
    -- 使用 Finset.sum_range_reflect
    have h1 : ∑ k ∈ range N, f (b + (k + (1 / 2 : ℝ)) * (a - b) / N)
            = ∑ k ∈ range N, f (b + ((N - 1 - k : ℕ) + (1 / 2 : ℝ)) * (a - b) / N) := by
      rw [← Finset.sum_range_reflect (fun k => f (b + (k + (1 / 2 : ℝ)) * (a - b) / N)) N]
    rw [h1]

    -- 现在证明对应项相等
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have hN : (N : ℝ) ≠ 0 := by
      intro h
      have : N = 0 := by
        exact_mod_cast h
      linarith [N_nonzero]

    -- 证明：a + (k + 1/2)*(b-a)/N = b + ((N-1-k) + 1/2)*(a-b)/N
    have h3 : k ≤ N - 1 := by omega
    have h4 : (N - 1 - k : ℕ) = N - 1 - k := by omega

    -- 关键引理：((N - 1 - k : ℕ) : ℝ) = (N : ℝ) - 1 - k
    have h5 : ((N - 1 - k : ℕ) : ℝ) = (N : ℝ) - 1 - k := by
      rw [h4]
      have h6 : (k : ℕ) ≤ N - 1 := h3
      have h7 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by linarith : 1 ≤ N)]
        simp
      have h8 : ((N - 1 - k : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) - k := by
        rw [Nat.cast_sub h6]
      rw [h8, h7]

    have h_eq : a + (k + (1 / 2 : ℝ)) * (b - a) / N
              = b + ((N - 1 - k : ℕ) + (1 / 2 : ℝ)) * (a - b) / N := by
      calc
        a + (k + (1 / 2 : ℝ)) * (b - a) / N
          = a + (k + (1 / 2 : ℝ)) * (b - a) / N := rfl
        _ = b + ((N : ℝ) - 1 - k + (1 / 2 : ℝ)) * (a - b) / N := by
          field_simp [hN]
          ring_nf
        _ = b + (((N - 1 - k : ℕ) : ℝ) + (1 / 2 : ℝ)) * (a - b) / N := by
          rw [h5]
        _ = b + ((N - 1 - k : ℕ) + (1 / 2 : ℝ)) * (a - b) / N := by
          norm_cast
    rw [h_eq]

  rw [h_coeff, h_sum]
  ring

/-- The absolute error of Simpson's midpoint rule does not change when the endpoints are swapped. -/
theorem simpson_midpoint_error_symm (f : ℝ → ℝ) {N : ℕ} (N_nonzero : 0 < N) (a b : ℝ) :
    simpson_midpoint_error f N a b = -simpson_midpoint_error f N b a := by
  unfold simpson_midpoint_error
  have h_integral : simpson_midpoint_integral f N a b = -(simpson_midpoint_integral f N b a) :=
    simpson_midpoint_integral_symm f N_nonzero a b
  have h_exact : (∫ x in a..b, f x) = -(∫ x in b..a, f x) := by
    rw [intervalIntegral.integral_symm]
  rw [h_integral, h_exact]
  ring

/-- Just like exact integration, the Simpson midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem simpson_midpoint_integral_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) :
    simpson_midpoint_integral f N a a = 0 := by
  unfold simpson_midpoint_integral
  simp

/-- The error of Simpson's midpoint integration from `a` to `a` is zero. -/
@[simp]
theorem simpson_midpoint_error_eq (f : ℝ → ℝ) (N : ℕ) (a : ℝ) :
    simpson_midpoint_error f N a a = 0 := by
  unfold simpson_midpoint_error
  simp

/-- An exact formula for integration with a single midpoint evaluation. -/
@[simp]
theorem simpson_midpoint_integral_one (f : ℝ → ℝ) (a b : ℝ) :
    simpson_midpoint_integral f 1 a b = (b - a) * f ((a + b) / 2) := by
  unfold simpson_midpoint_integral
  simp only [Nat.cast_one, range_one, sum_singleton]
  ring_nf

/-- A basic Simpson midpoint equivalent to `IntervalIntegral.sum_integral_adjacent_intervals`. More
general theorems can be derived from repeated applications of this one. -/
theorem sum_simpson_midpoint_integral_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) :
    ∑ i ∈ range N, simpson_midpoint_integral f 1 (a + i * h) (a + (i + 1) * h)
      = simpson_midpoint_integral f N a (a + N * h) := by
  have h1 : ∀ i ∈ range N, simpson_midpoint_integral f 1 (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h)
              = h * f (a + ((i : ℝ) + 1 / 2) * h) := by
    intro i hi
    rw [simpson_midpoint_integral_one]
    ring_nf
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.mul_sum]
  have h3 : (a + N * h - a) / N = h := by
    field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
    ring_nf
  rw [simpson_midpoint_integral]
  congr 1
  · rw [h3]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  field_simp [Nat.cast_ne_zero.mpr N_nonzero.ne']
  ring

/-- A simplified version of the previous theorem, for use in proofs by induction and the like. -/
theorem simpson_midpoint_integral_ext {f : ℝ → ℝ} {N : ℕ} {a h : ℝ} (N_nonzero : 0 < N) :
    simpson_midpoint_integral f N a (a + N * h) + simpson_midpoint_integral f 1 (a + N * h) (a + (N + 1) * h)
      = simpson_midpoint_integral f (N + 1) a (a + (N + 1) * h) := by
  sorry

/-- Since we have `sum_[]_adjacent_intervals` theorems for both exact and Simpson midpoint integration,
it's natural to combine them into a similar formula for the error. This theorem is in particular
used in the proof of the general error bound. -/
theorem sum_simpson_midpoint_error_adjacent_intervals {f : ℝ → ℝ} {N : ℕ} {a h : ℝ}
    (N_nonzero : 0 < N) (h_f_int : IntervalIntegrable f volume a (a + N * h)) :
    ∑ i ∈ range N, simpson_midpoint_error f 1 (a + i * h) (a + (i + 1) * h)
      = simpson_midpoint_error f N a (a + N * h) := by
  sorry

/-- The most basic case: error bound for the midpoint rule on a single interval with ordered endpoints.
Given `F` with `F' = f`, we bound `|(b-a) * F'((a+b)/2) - (F(b) - F(a))|`.

This is the key lemma: for `F` satisfying
`(hf : ContDiffOn ℝ 2 F (Icc 0 h))`
`(hf' : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc 0 h)) (Ioo 0 h))`
and `(fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc 0 h) x| ≤ M)`,
we have `|F h - F 0 - (derivWithin F (Icc 0 h) (h/2)) * h| ≤ (h^3 / 24) * M`. -/
private lemma simpson_midpoint_error_le_of_lt' {F : ℝ → ℝ} {M : ℝ} {a b : ℝ} (a_lt_b : a < b)
    (hF : ContDiffOn ℝ 2 F (Icc a b))
    (hF_diff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b))
    (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ (b - a) ^ 3 * M / 24 := by
  sorry

/-- The standard error bound for Simpson's midpoint integration on a single interval `[[a, b]]`.

For a function `F` with `F' = f`, if `F` is twice continuously differentiable on `[[a, b]]`,
the second derivative is differentiable on `(a, b)`, and the third derivative is bounded by `M`,
then the midpoint rule error is bounded by `|b - a|^3 * M / 24`. -/
theorem simpson_midpoint_error_le {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContDiffOn ℝ 2 F (Icc a b))
    (hF_diff : DifferentiableOn ℝ (iteratedDerivWithin 2 F (Icc a b)) (Ioo a b))
    {M : ℝ} (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ |b - a| ^ 3 * M / 24 := by
  sorry

/-- The error bound for Simpson's midpoint integration in the case where `F` is `C^3`.

If `F` is three times continuously differentiable on `[[a, b]]` and the third derivative
is bounded by `M`, then the midpoint rule error is bounded by `|b - a|^3 * M / 24`. -/
theorem simpson_midpoint_error_le_of_c3 {F : ℝ → ℝ} {a b : ℝ}
    (hF_c3 : ContDiffOn ℝ 3 F (Icc a b)) {M : ℝ}
    (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
    |F b - F a - (derivWithin F (Icc a b) ((a + b) / 2)) * (b - a)| ≤ |b - a| ^ 3 * M / 24 := by
  sorry

/-- The composite Simpson's midpoint rule error bound.

For `F` with `F' = f`, the error in approximating `∫_a^b f(x) dx` by the midpoint sum
`h * ∑_{i=0}^{n-1} f(x_{i+1/2})` is bounded by `(h^2 / 24) * M * |b - a|`
where `h = (b-a)/n` and `M` bounds `|F'''|`.

Equivalently, since `|b - a| = n * h`, the bound can be written as `(h^2 / 24) * M * (b - a)`. -/
theorem simpson_midpoint_composite_error_le {F : ℝ → ℝ} {a b : ℝ} {N : ℕ} (N_nonzero : 0 < N)
    (hF_c3 : ContDiffOn ℝ 3 F (Icc a b)) {M : ℝ}
    (fpp_bound : ∀ x, |iteratedDerivWithin 3 F (Icc a b) x| ≤ M) :
    let h := (b - a) / N
    |simpson_midpoint_error F N a b| ≤ (h ^ 2 / 24) * M * |b - a| := by
  sorry

end
