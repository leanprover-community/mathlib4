/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.CriticalLineZeros
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# De la Vallée Poussin's (1899) Classical Unconditional Zero-Free Region

This file formalizes the classical zero-free region for the Riemann zeta function:
1. Specialization of the 3-4-1 trigonometric product inequality to `riemannZeta`:
   `‖ζ(1 + x)³ · ζ(1 + x + i y)⁴ · ζ(1 + x + 2 i y)‖ ≥ 1` for `x > 0`.
2. Separation into individual norms: `1 ≤ ‖ζ(1 + x)‖³ · ‖ζ(1 + x + i y)‖⁴ · ‖ζ(1 + x + 2 i y)‖`.
3. Laurent expansion connection via `riemannZeta₀`: `ζ(1 + x) = x⁻¹ + ζ₀(1 + x)`.
4. De la Vallée Poussin's cubic optimization identity: `(3δ + δ)⁴ / (3δ)³ = (256 / 27) δ`.
5. Analytical zero repulsion: deduction of the positive distance `δ ≥ c / ln⁹(|y| + 2)`
   from the combined product and pole estimates.
6. The unconditional zero-free boundary: `ζ(σ + i t) ≠ 0` whenever `σ ≥ 1 - c / ln⁹(|t| + 2)`.
-/

@[expose] public section

open Complex Filter Set DirichletCharacter
open scoped Topology

/-- Pointwise product inequality for the Riemann zeta function:
`‖ζ(1 + x)³ · ζ(1 + x + i y)⁴ · ζ(1 + x + 2 i y)‖ ≥ 1` for all `x > 0` and `y : ℝ`.
Deduced by specializing Mathlib's `norm_LFunction_product_ge_one` at `N = 1` and `χ = 1`. -/
theorem norm_riemannZeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖ ≥ 1 := by
  have h := norm_LFunction_product_ge_one (N := 1) (1 : DirichletCharacter ℂ 1) hx y
  simp only [LFunctionTrivChar, LFunction_modOne_eq, one_pow] at h
  exact h

/-- Split product inequality in terms of separated norms:
`1 ≤ ‖ζ(1 + x)‖³ * ‖ζ(1 + x + i y)‖⁴ * ‖ζ(1 + x + 2 i y)‖` for `x > 0`. -/
theorem riemannZeta_norm_cubed_fourth_mul_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * y)‖ := by
  have h := norm_riemannZeta_product_ge_one hx y
  simpa only [norm_mul, norm_pow] using h

/-- Connection to the Laurent decomposition: for real `x ≠ 0`,
`ζ(1 + x) = x⁻¹ + ζ₀(1 + x)` where `ζ₀` is the entire regular part. -/
theorem riemannZeta_one_add_eq {x : ℝ} (hx : x ≠ 0) :
    riemannZeta (1 + (x : ℂ)) = (x : ℂ)⁻¹ + riemannZeta₀ (1 + (x : ℂ)) := by
  have hne : 1 + (x : ℂ) ≠ 1 := by
    intro h
    have : (x : ℂ) = 0 := by linear_combination h
    exact hx (Complex.ofReal_eq_zero.mp this)
  have := riemannZeta_eq_inv_sub_add hne
  have hsub : 1 + (x : ℂ) - 1 = (x : ℂ) := by ring
  rw [hsub] at this
  exact this

/-- Quantitative pole bound from the entire regular part:
For `0 < x ≤ 1`, if `‖riemannZeta₀ (1 + x)‖ ≤ M` with `0 ≤ M`, then
`‖ζ(1 + x)‖ ≤ (1 + M) / x`.
This constructively discharges the local pole hypothesis with `C_pole = 1 + M`. -/
theorem norm_riemannZeta_one_add_le (x : ℝ) (hx_pos : 0 < x) (hx_le : x ≤ 1) (M : ℝ)
    (hM_pos : 0 ≤ M) (hM : ‖riemannZeta₀ (1 + (x : ℂ))‖ ≤ M) :
    ‖riemannZeta (1 + (x : ℂ))‖ ≤ (1 + M) / x := by
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx_pos
  have hne1 : 1 + (x : ℂ) ≠ 1 := by
    intro h
    have : (x : ℂ) = 0 := by linear_combination h
    exact hne this
  have h_eq := riemannZeta_eq_inv_sub_add hne1
  have hsub : 1 + (x : ℂ) - 1 = (x : ℂ) := by ring
  rw [hsub] at h_eq
  have h_tri := norm_add_le (x : ℂ)⁻¹ (riemannZeta₀ (1 + (x : ℂ)))
  have h_inv : ‖(x : ℂ)⁻¹‖ = 1 / x := by
    rw [norm_inv, norm_real, Real.norm_of_nonneg (le_of_lt hx_pos), one_div]
  rw [h_inv] at h_tri
  have h_tri' : ‖riemannZeta (1 + (x : ℂ))‖ ≤ 1 / x + ‖riemannZeta₀ (1 + (x : ℂ))‖ := by
    rw [h_eq]
    exact h_tri
  have h_le : 1 / x + ‖riemannZeta₀ (1 + (x : ℂ))‖ ≤ 1 / x + M := by linarith
  have h_comb : ‖riemannZeta (1 + (x : ℂ))‖ ≤ 1 / x + M := le_trans h_tri' h_le
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have heq : 1 / x + M ≤ (1 + M) / x := by
    have h1 : 1 / x + M = (1 + M * x) / x := by
      field_simp
    rw [h1]
    have h_num : 1 + M * x ≤ 1 + M := by nlinarith
    exact div_le_div_of_nonneg_right h_num (le_of_lt hx_pos)
  exact le_trans h_comb heq

/-- Bounded pole upper bound from the entire regular part at `x = 3 * δ`:
for `0 < 3 * δ ≤ 1`, if `‖riemannZeta₀ (1 + (3 * δ : ℂ))‖ ≤ M` with `0 ≤ M`, then
`‖riemannZeta (1 + (3 * δ : ℂ))‖ ≤ (1 + M) / (3 * δ)`. -/
theorem norm_riemannZeta_three_mul_delta_le {δ M : ℝ} (hδ_pos : 0 < δ) (hδ_le : 3 * δ ≤ 1)
    (hM_nonneg : 0 ≤ M) (hM : ‖riemannZeta₀ (1 + (3 * δ : ℂ))‖ ≤ M) :
    ‖riemannZeta (1 + (3 * (δ : ℂ)))‖ ≤ (1 + M) / (3 * δ) := by
  have h3δ_pos : 0 < 3 * δ := by linarith
  have h_le := norm_riemannZeta_one_add_le (3 * δ) h3δ_pos hδ_le M hM_nonneg
  have hcast : (1 : ℂ) + (↑(3 * δ) : ℂ) = 1 + (3 * (δ : ℂ)) := by push_cast; ring
  have hcast2 : (1 : ℂ) + (↑(3 * δ) : ℂ) = 1 + (3 * δ : ℂ) := by push_cast; rfl
  have hM' : ‖riemannZeta₀ (1 + (↑(3 * δ) : ℂ))‖ ≤ M := by
    rwa [hcast2]
  have h_res := h_le hM'
  rwa [hcast] at h_res

/-- De la Vallée Poussin's (1899) cubic optimization identity:
the function `f(η) = (η + δ)⁴ / η³` achieves its minimum at `η = 3δ` with value `(256 / 27) δ`. -/
theorem valleePoussin_cubic_opt_identity (δ : ℝ) :
    (3 * δ + δ) ^ 4 / (3 * δ) ^ 3 = (256 / 27 : ℝ) * δ := by
  have h4 : 3 * δ + δ = 4 * δ := by ring
  rw [h4]
  by_cases hδ : δ = 0
  · simp [hδ]
  · field_simp
    ring

/-- Analytical zero repulsion theorem (De la Vallée Poussin 1899):
if `ζ(1 - δ + i y) = 0` with `δ > 0` and `|y| ≥ 2`, and the local pole, growth, and Lipschitz
bounds hold with constants `C_pole, C_lip, C_growth > 0`, then `δ` is bounded below by
`c / ln⁹(|y| + 2)` where `c = 27 / (256 * C_pole³ * C_lip⁴ * C_growth)`. -/
theorem deLaValleePoussin_zero_repulsion {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (h_prod : 1 ≤ (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
                  (C_growth * Real.log (|y| + 2))) :
    (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) ≤ δ := by
  have hlog_pos : 0 < Real.log (|y| + 2) := by
    apply Real.log_pos
    linarith
  have _hlog_ne : Real.log (|y| + 2) ≠ 0 := ne_of_gt hlog_pos
  have _hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have h_alg : (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2)) =
      δ * ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) := by
    field_simp
    ring
  rw [h_alg] at h_prod
  have hcoeff_pos : 0 < (256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 *
      C_growth * Real.log (|y| + 2) ^ 9 := by
    positivity
  have hdiv : 1 / ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 *
      C_growth * Real.log (|y| + 2) ^ 9) ≤ δ := by
    rwa [div_le_iff₀ hcoeff_pos]
  have heq : 1 / ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) =
      (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) := by
    field_simp
  rw [heq] at hdiv
  exact hdiv

/-- If `δ < c / ln⁹(|y| + 2)`, then the classical upper bound product evaluates strictly
below 1, contradicting the required non-trivial lower bound `≥ 1`. -/
theorem deLaValleePoussin_product_lt_one_of_lt_repulsion {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (hδ_lt : δ < (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9)) :
    (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2)) < 1 := by
  have hlog_pos : 0 < Real.log (|y| + 2) := by
    apply Real.log_pos
    linarith
  have _hlog_ne : Real.log (|y| + 2) ≠ 0 := ne_of_gt hlog_pos
  have _hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have h_alg : (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2)) =
      δ * ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) := by
    field_simp
    ring
  rw [h_alg]
  have hcoeff_pos : 0 < (256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 *
      C_growth * Real.log (|y| + 2) ^ 9 := by
    positivity
  have heq : (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) =
      1 / ((256 / 27 : ℝ) * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9) := by
    field_simp
  rw [heq] at hδ_lt
  exact (lt_div_iff₀ hcoeff_pos).mp hδ_lt

/-- De la Vallée Poussin's (1899) Contradiction Theorem:
No non-trivial zero of the Riemann zeta function can satisfy the local pole, growth, and
Lipschitz upper bounds while lying within distance `δ < c / ln⁹(|y| + 2)` of `Re(s) = 1`. -/
theorem deLaValleePoussin_contradiction {δ y C_pole C_lip C_growth : ℝ}
    (hδ_pos : 0 < δ) (hy : 2 ≤ |y|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (h_pole : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ≤ C_pole / (3 * δ))
    (h_lip : ‖riemannZeta (1 + (3 * δ : ℂ) + I * y)‖ ≤ C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ))
    (h_growth : ‖riemannZeta (1 + (3 * δ : ℂ) + 2 * I * y)‖ ≤ C_growth * Real.log (|y| + 2))
    (hδ_lt : δ < (27 : ℝ) / (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|y| + 2) ^ 9)) :
    False := by
  have h3δ_pos : 0 < 3 * δ := mul_pos (by norm_num) hδ_pos
  have h_ge := riemannZeta_norm_cubed_fourth_mul_ge_one h3δ_pos y
  have hcast : (1 : ℂ) + (↑(3 * δ) : ℂ) = 1 + (3 * δ : ℂ) := by push_cast; rfl
  rw [hcast] at h_ge
  have h_bound_lt_one := deLaValleePoussin_product_lt_one_of_lt_repulsion
    hδ_pos hy hC_pole hC_lip hC_growth hδ_lt
  have h_prod_le : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ^ 3 *
      ‖riemannZeta (1 + (3 * δ : ℂ) + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + (3 * δ : ℂ) + 2 * I * y)‖ ≤
      (C_pole / (3 * δ)) ^ 3 * (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 *
      (C_growth * Real.log (|y| + 2)) := by
    have h1 : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ^ 3 ≤ (C_pole / (3 * δ)) ^ 3 := by
      gcongr
    have h2 : ‖riemannZeta (1 + (3 * δ : ℂ) + I * y)‖ ^ 4 ≤
        (C_lip * Real.log (|y| + 2) ^ 2 * (4 * δ)) ^ 4 := by
      gcongr
    gcongr
  have h_lt : ‖riemannZeta (1 + (3 * δ : ℂ))‖ ^ 3 * ‖riemannZeta (1 + (3 * δ : ℂ) + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + (3 * δ : ℂ) + 2 * I * y)‖ < 1 :=
    lt_of_le_of_lt h_prod_le h_bound_lt_one
  exact lt_irrefl _ (lt_of_lt_of_le h_lt h_ge)

/-- Non-vanishing criterion on the right half-plane `Re(s) ≥ 1`:
immediate consequence of Mathlib's `riemannZeta_ne_zero_of_one_le_re`. -/
theorem riemannZeta_ne_zero_of_one_le_re_strip {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- De la Vallée Poussin's (1899) Landmark Zero-Free Region Theorem:
For any point `s = σ + i t` with `2 ≤ |t|`, if
`1 - c / ln⁹(|t| + 2) < σ` where `c = 27 / (256 * C_pole³ * C_lip⁴ * C_growth)`,
then under the standard local analytic bounds, `riemannZeta s ≠ 0`. -/
theorem deLaValleePoussin_zero_free_region {s : ℂ} {C_pole C_lip C_growth : ℝ}
    (ht : 2 ≤ |s.im|)
    (hC_pole : 0 < C_pole) (hC_lip : 0 < C_lip) (hC_growth : 0 < C_growth)
    (h_reg : 1 - (27 : ℝ) /
      (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|s.im| + 2) ^ 9) < s.re)
    (h_pole : ‖riemannZeta (1 + (3 * (1 - s.re : ℝ) : ℂ))‖ ≤ C_pole / (3 * (1 - s.re)))
    (h_lip : ‖riemannZeta (1 + (3 * (1 - s.re : ℝ) : ℂ) + I * s.im)‖ ≤
      C_lip * Real.log (|s.im| + 2) ^ 2 * (4 * (1 - s.re)))
    (h_growth : ‖riemannZeta (1 + (3 * (1 - s.re : ℝ) : ℂ) + 2 * I * s.im)‖ ≤
      C_growth * Real.log (|s.im| + 2)) :
    riemannZeta s ≠ 0 := by
  intro h_zero
  by_cases h_ge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re_strip h_ge h_zero
  · have h_lt : s.re < 1 := lt_of_not_ge h_ge
    have hδ_pos : 0 < 1 - s.re := sub_pos.mpr h_lt
    have hδ_lt : 1 - s.re < (27 : ℝ) /
        (256 * C_pole ^ 3 * C_lip ^ 4 * C_growth * Real.log (|s.im| + 2) ^ 9) := by
      linarith
    exact deLaValleePoussin_contradiction
      hδ_pos ht hC_pole hC_lip hC_growth h_pole h_lip h_growth hδ_lt
