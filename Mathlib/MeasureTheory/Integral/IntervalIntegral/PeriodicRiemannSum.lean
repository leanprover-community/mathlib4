/-
Copyright (c) 2026 Runtian Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Runtian Zhou, Xichen Tang
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Riemann sums of periodic functions of bounded variation

For a `1`-periodic function `f : ℝ → ℝ` of bounded variation on `[0, 1]`, the equally spaced
Riemann sum `N⁻¹ ∑_{j < N} f (j / N + β)` approximates `∫₀¹ f` with error at most
`Var_{[0,1]} f / (2 N)`, uniformly in the shift `β`.

For comparison, Koksma's inequality bounds the same error by `Var f` times the star discrepancy of
the sample points, which for the points `j / N + β` lies between `1 / (2 N)` and `1 / N` depending
on `β`. Periodicity removes the dependence on `β`.

The constant `1 / 2` is optimal for every `N`: the indicator function of `ℤ` has variation `2` on
`[0, 1]` and integral `0`, while for `β = 0` its Riemann sum is `1 / N`.

## Main results

* `Function.Periodic.abs_sum_sub_integral_le_eVariationOn`: the Riemann sum error bound above.

## Implementation notes

The proof is elementary. The grid `t j = j / N + β` tiles one period `[β, β + 1]`. By periodicity
the endpoint averages `(f (t j) + f (t (j + 1))) / 2` have the same sum as the samples `f (t j)`,
so the error is `∑ j, ∫ u in t j..t (j + 1), (average - f u)`. On each tile the integrand is at
most half the variation of `f` there, by the three-point partition `t j ≤ u ≤ t (j + 1)`, and the
tile variations add up to the variation over the period.

## Tags

Riemann sum, bounded variation, periodic function, Koksma inequality
-/

@[expose] public section

open Finset Set MeasureTheory

/-- Three-point bound: `|f a - f u| + |f u - f b|` is at most the variation of `f` on `[a, b]`. -/
private theorem abs_sub_add_abs_sub_le_eVariationOn_toReal {f : ℝ → ℝ} {a u b : ℝ}
    (hau : a ≤ u) (hub : u ≤ b) (hfin : eVariationOn f (Icc a b) ≠ ⊤) :
    |f a - f u| + |f u - f b| ≤ (eVariationOn f (Icc a b)).toReal := by
  have h1 := eVariationOn.edist_le f (s := Icc a u) ⟨le_rfl, hau⟩ ⟨hau, le_rfl⟩
  have h2 := eVariationOn.edist_le f (s := Icc u b) ⟨le_rfl, hub⟩ ⟨hub, le_rfl⟩
  have hsplit : eVariationOn f (Icc a u) + eVariationOn f (Icc u b) = eVariationOn f (Icc a b) := by
    simpa using eVariationOn.Icc_add_Icc f (s := univ) hau hub (mem_univ _)
  rw [edist_dist, Real.dist_eq] at h1 h2
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin, ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
    ← hsplit]
  exact add_le_add h1 h2

namespace Function.Periodic

variable {f : ℝ → ℝ}

/-- If `f` is `1`-periodic and of bounded variation on `[0, 1]`, then for every `N ≠ 0` and every
shift `β`, the equally spaced Riemann sum `N⁻¹ ∑_{j < N} f (j / N + β)` differs from `∫₀¹ f` by
at most `Var_{[0,1]} f / (2 N)`. This is a sharp form of Koksma's inequality for these points.

The constant is optimal: equality holds for the indicator function of `ℤ` with `β = 0`. -/
theorem abs_sum_sub_integral_le_eVariationOn (hf : Periodic f 1)
    (hbv : BoundedVariationOn f (Icc 0 1)) {N : ℕ} (hN : N ≠ 0) (β : ℝ) :
    |(N : ℝ)⁻¹ * ∑ j ∈ range N, f ((j : ℝ) / N + β) - ∫ x in (0 : ℝ)..1, f x|
      ≤ (eVariationOn f (Icc 0 1)).toReal / (2 * N) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero hN)
  -- the grid `t j = j / N + β` tiles the period `[β, β + 1]` into `N` tiles of length `N⁻¹`
  let t : ℕ → ℝ := fun j ↦ (j : ℝ) / N + β
  have htmono : Monotone t := fun i j hij ↦ by
    simp only [t]
    gcongr
  have hstep (j : ℕ) : t (j + 1) - t j = (N : ℝ)⁻¹ := by
    simp only [t]
    push_cast
    field_simp
    ring
  have ht0 : t 0 = β := by simp [t]
  have htN : t N = β + 1 := by
    simp only [t]
    field_simp
    ring
  have hsub (j : ℕ) (hj : j < N) : Icc (t j) (t (j + 1)) ⊆ Icc β (β + 1) :=
    Icc_subset_Icc (ht0.symm.trans_le (htmono (Nat.zero_le j))) ((htmono hj).trans_eq htN)
  -- `f` has bounded variation on the period window, hence on every tile
  have hwindow : eVariationOn f (Icc β (β + 1)) = eVariationOn f (Icc 0 1) :=
    hf.eVariationOn_Icc_add_one β
  have hbvβ : BoundedVariationOn f (Icc β (β + 1)) := by
    change eVariationOn f (Icc β (β + 1)) ≠ ⊤
    rw [hwindow]
    exact hbv
  have hfin (j : ℕ) (hj : j < N) : eVariationOn f (Icc (t j) (t (j + 1))) ≠ ⊤ :=
    ne_top_of_le_ne_top hbvβ (eVariationOn.mono f (hsub j hj))
  have hint (j : ℕ) (hj : j < N) : IntervalIntegrable f volume (t j) (t (j + 1)) := by
    refine hbvβ.intervalIntegrable ?_
    rw [uIcc_of_le (htmono (Nat.le_succ j))]
    exact hsub j hj
  -- the tiles reassemble one period
  have hIsum : ∑ j ∈ range N, ∫ u in (t j)..(t (j + 1)), f u = ∫ x in (0 : ℝ)..1, f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint, ht0, htN]
    simpa using hf.intervalIntegral_add_eq β 0
  -- the error is the sum over tiles of `∫ (c j - f u)`, where `c j` is the endpoint average:
  -- by periodicity the averages have the same sum as the left-endpoint samples
  let c : ℕ → ℝ := fun j ↦ (f (t j) + f (t (j + 1))) / 2
  have hdiff : (N : ℝ)⁻¹ * ∑ j ∈ range N, f (t j) - ∫ x in (0 : ℝ)..1, f x
      = ∑ j ∈ range N, ∫ u in (t j)..(t (j + 1)), (c j - f u) := by
    have havg : ∑ j ∈ range N, c j = ∑ j ∈ range N, f (t j) := by
      have htel : ∑ j ∈ range N, (f (t j) - f (t (j + 1))) = f (t 0) - f (t N) :=
        sum_range_sub' (fun j ↦ f (t j)) N
      rw [ht0, htN, hf β, sub_self, sum_sub_distrib, sub_eq_zero] at htel
      simp only [c, ← sum_div, sum_add_distrib, ← htel]
      ring
    rw [← havg, mul_sum, ← hIsum, ← sum_sub_distrib]
    refine sum_congr rfl fun j hj ↦ ?_
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j (mem_range.1 hj)),
      intervalIntegral.integral_const, smul_eq_mul, hstep j]
  -- on each tile `|c j - f u| ≤ Var f / 2`, by the three-point partition `t j ≤ u ≤ t (j + 1)`
  have hterm (j : ℕ) (hj : j ∈ range N) :
      |∫ u in (t j)..(t (j + 1)), (c j - f u)|
        ≤ (eVariationOn f (Icc (t j) (t (j + 1)))).toReal / 2 * (N : ℝ)⁻¹ := by
    have hle := htmono (Nat.le_succ j)
    have hC : ∀ u ∈ uIoc (t j) (t (j + 1)),
        ‖c j - f u‖ ≤ (eVariationOn f (Icc (t j) (t (j + 1)))).toReal / 2 := by
      intro u hu
      rw [uIoc_of_le hle] at hu
      have h3 := abs_sub_add_abs_sub_le_eVariationOn_toReal hu.1.le hu.2 (hfin j (mem_range.1 hj))
      have h4 : |c j - f u| ≤ (|f (t j) - f u| + |f u - f (t (j + 1))|) / 2 := by
        rw [show c j - f u = ((f (t j) - f u) + (f (t (j + 1)) - f u)) / 2 by simp only [c]; ring,
          abs_div, abs_two, abs_sub_comm (f u)]
        linarith [abs_add_le (f (t j) - f u) (f (t (j + 1)) - f u)]
      rw [Real.norm_eq_abs]
      linarith
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hC
    rwa [Real.norm_eq_abs, hstep j, abs_of_pos (inv_pos.2 hNR)] at hb
  -- sum the tile bounds; the tile variations add up to the variation over one period
  rw [hdiff]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans_eq ?_)
  rw [← sum_mul, ← sum_div, ← ENNReal.toReal_sum fun j hj ↦ hfin j (mem_range.1 hj),
    eVariationOn.sum' f htmono, ht0, htN, hwindow]
  ring

end Function.Periodic
