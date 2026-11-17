/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.NumberTheory.LSeries.HardyZ
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Critical-Line Symmetry, IVT Zero Detection, and 3-4-1 Positivity for `riemannZeta`

This file collects elementary unconditional tools for locating zeros of `riemannZeta` on the
critical line `Re(s) = 1 / 2` and isolating the classical 3-4-1 non-vanishing kernel:

* `criticalLine`: embedding `t ↦ 1 / 2 + I * t` of the critical line in `ℂ`.
* `three_add_four_cos_add_cos_two_mul_nonneg`: de la Vallée Poussin's `3 + 4 cos θ + cos(2θ) ≥ 0`.
* `norm_riemannZeta_product_ge_one`: specialization of `norm_LFunction_product_ge_one` to `ζ`.
* `exists_criticalLine_zero_of_sign_change` and `exists_criticalLine_zero_of_hardyZ_sign_change`:
  Intermediate Value Theorem certification of critical-line zeros from sign changes.
* `infinite_criticalLine_zeros_of_sign_changes` and `infinite_hardyZ_zeros_of_sign_changes`:
  infinitude of critical-line and Hardy `Z`-zeros from unbounded sign changes.

## References

* G. H. Hardy, *Sur les zéros de la fonction ζ(s) de Riemann*, C. R. Acad. Sci. Paris 158 (1914).
* Ch.-J. de la Vallée Poussin, *Recherches analytiques sur la théorie des nombres premiers* (1899).
-/

@[expose] public section

open Complex Set DirichletCharacter

/-- Embedding of the critical line `Re(s) = 1 / 2` parametrized by `t : ℝ`. -/
noncomputable def criticalLine (t : ℝ) : ℂ := 1 / 2 + I * (t : ℂ)

/-- The real part of any point on the critical line is identically `1 / 2`. -/
theorem criticalLine_re (t : ℝ) : (criticalLine t).re = 1 / 2 := by
  simp [criticalLine]

/-- Reflection involution across the critical line: `1 - criticalLine t = criticalLine (-t)`. -/
theorem one_sub_criticalLine (t : ℝ) : 1 - criticalLine t = criticalLine (-t) := by
  simp only [criticalLine, ofReal_neg]
  ring

/-- The completed Riemann zeta function is even along the critical line. -/
theorem completedRiemannZeta_criticalLine_neg (t : ℝ) :
    completedRiemannZeta (criticalLine (-t)) = completedRiemannZeta (criticalLine t) := by
  rw [← one_sub_criticalLine, completedRiemannZeta_one_sub]

/-- Intermediate Value Theorem zero detector for continuous real functions with a sign change. -/
private lemma exists_zero_of_sign_change {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hsign : f a * f b ≤ 0) :
    ∃ t₀ ∈ Icc a b, f t₀ = 0 := by
  rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact intermediate_value_Icc' hab hcont ⟨h2, h1⟩
  · exact intermediate_value_Icc hab hcont ⟨h1, h2⟩

/-- Unconditional Intermediate Value Theorem certification of critical-line zeros:
if a continuous real detector `Z : ℝ → ℝ` changes sign on `[a, b]`, then `riemannZeta` has a zero
on the critical line `Re(s) = 1 / 2` in `[a, b]`. -/
theorem exists_criticalLine_zero_of_sign_change {Z : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn Z (Icc a b))
    (hzero : ∀ t ∈ Icc a b, Z t = 0 → riemannZeta (criticalLine t) = 0)
    (hsign : Z a * Z b ≤ 0) :
    ∃ t₀ ∈ Icc a b, (criticalLine t₀).re = 1 / 2 ∧ riemannZeta (criticalLine t₀) = 0 := by
  rcases exists_zero_of_sign_change hab hcont hsign with ⟨t₀, ht₀, heq⟩
  exact ⟨t₀, ht₀, criticalLine_re t₀, hzero t₀ ht₀ heq⟩

/-- Specialization of sign-change critical-line zero detection to Hardy's `hardyZ` function. -/
theorem exists_criticalLine_zero_of_hardyZ_sign_change {a b : ℝ} (hab : a ≤ b)
    (hsign : hardyZ a * hardyZ b ≤ 0) :
    ∃ t₀ ∈ Icc a b, (criticalLine t₀).re = 1 / 2 ∧ riemannZeta (criticalLine t₀) = 0 := by
  have hzero : ∀ t ∈ Icc a b, hardyZ t = 0 → riemannZeta (criticalLine t) = 0 := by
    intro t _ ht
    have heq : criticalLine t = 1 / 2 + (t : ℂ) * I := by
      simp only [criticalLine]
      ring
    rw [heq]
    exact (hardyZ_eq_zero_iff t).mp ht
  exact exists_criticalLine_zero_of_sign_change hab continuous_hardyZ.continuousOn hzero hsign

/-- If Hardy's `Z`-function has sign changes arbitrarily far out on `ℝ`, then `riemannZeta` has
infinitely many zeros on the critical line `Re(s) = 1 / 2`. -/
theorem infinite_criticalLine_zeros_of_sign_changes
    (h_sign : ∀ T : ℝ, ∃ a b : ℝ, T < a ∧ a ≤ b ∧ hardyZ a * hardyZ b ≤ 0) :
    {t : ℝ | riemannZeta (criticalLine t) = 0}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun T => ?_
  rcases h_sign T with ⟨a, b, hTa, hab, hsign⟩
  rcases exists_criticalLine_zero_of_hardyZ_sign_change hab hsign with ⟨t₀, ht₀, _, ht₀_zero⟩
  exact ⟨t₀, ht₀_zero, lt_of_lt_of_le hTa ht₀.1⟩

/-- The zero set of Hardy's `Z`-function on `ℝ` is infinite whenever it has unbounded sign
changes. -/
theorem infinite_hardyZ_zeros_of_sign_changes
    (h_sign : ∀ T : ℝ, ∃ a b : ℝ, T < a ∧ a ≤ b ∧ hardyZ a * hardyZ b ≤ 0) :
    {t : ℝ | hardyZ t = 0}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun T => ?_
  rcases h_sign T with ⟨a, b, hTa, hab, hsign⟩
  rcases exists_zero_of_sign_change hab continuous_hardyZ.continuousOn hsign with ⟨t₀, ht₀, hzt⟩
  exact ⟨t₀, hzt, lt_of_lt_of_le hTa ht₀.1⟩

/-- De la Vallée Poussin's (1899) trigonometric identity `3 + 4 cos θ + cos(2θ) = 2(1 + cos θ)²`.
-/
theorem three_add_four_cos_add_cos_two_mul_eq (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- Pointwise non-negativity of the 3-4-1 trigonometric kernel: `0 ≤ 3 + 4 cos θ + cos(2θ)`. -/
theorem three_add_four_cos_add_cos_two_mul_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [three_add_four_cos_add_cos_two_mul_eq]
  positivity

/-- Pointwise product inequality for the Riemann zeta function:
`1 ≤ ‖ζ(1 + x) ^ 3 * ζ(1 + x + I * y) ^ 4 * ζ(1 + x + 2 * I * y)‖` for `0 < x` and `y : ℝ`.
Deduced by specializing `norm_LFunction_product_ge_one` at `N = 1` and `χ = 1`. -/
theorem norm_riemannZeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖ := by
  have h := norm_LFunction_product_ge_one (N := 1) (1 : DirichletCharacter ℂ 1) hx y
  simp only [LFunctionTrivChar, LFunction_modOne_eq, one_pow] at h
  exact h
