/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function.

-/

@[expose] public noncomputable section

namespace Complex

open scoped Nat Real
open Topology Filter

/-- The ascending Pochhammer symbol is given by the ratio of `Γ` functions. -/
theorem Gamma_nat_add_div_Gamma_eq {n : ℕ} (z : ℂ) (hz : ∀ k : ℕ, -z ≠ k) :
    Gamma (n + z) / Gamma z = (ascPochhammer ℂ n).eval z := by
  induction n generalizing z with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_add, ascPochhammer_zero, Polynomial.eval_one,
      div_self_eq_one₀]
    intro h
    rw [Gamma_eq_zero_iff] at h
    grind
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one, ascPochhammer_succ_right, Polynomial.eval_mul, ← ih z hz,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
    rw [div_mul_eq_mul_div]
    congr
    calc
      _ = Gamma ((z + n) + 1) := by group
      _ =  (z + n) * Gamma (z + n) := by apply Gamma_add_one; grind
      _ = _ := by group

variable {p q : ℕ}

variable {a : Fin p → ℂ} {b : Fin q → ℂ}

/-- The coefficients of the regularized hypergeometric series. -/
def regularizedHGFunCoeff (a : Fin p → ℂ) (b : Fin q → ℂ) (n : ℕ) : ℂ :=
  (∏ i : Fin p, (ascPochhammer ℂ n).eval (a i)) / (n ! * ∏ j : Fin q, Gamma (b j + n))

theorem regularizedHGFunCoeff_eq_zero_iff {a : Fin p → ℂ} {b : Fin q → ℂ} {n : ℕ} :
    regularizedHGFunCoeff a b n = 0 ↔
    (∃ j, ∃ k < n, k = -a j) ∨ ∃ (j : Fin q) (m : ℕ), b j + n = -m := by
  unfold regularizedHGFunCoeff
  simp [Finset.prod_eq_zero_iff, Gamma_eq_zero_iff, n.factorial_ne_zero]




theorem regularizedHGFunCoeff_eq_zero_right (a : Fin p → ℂ) (b : Fin q → ℂ) (n : ℕ)
    (hb : ∃ (j : Fin q) (m : ℕ), b j = -n - m) : regularizedHGFunCoeff a b n = 0 := by
  grind [regularizedHGFunCoeff_eq_zero_iff]

theorem regularizedHGFunCoeff_eq_zero_left (a : Fin p → ℂ) (b : Fin q → ℂ) (n : ℕ)
    (ha : ∃ (j : Fin p), ∃ k < n, k = -a j) : regularizedHGFunCoeff a b n = 0 := by
  grind [regularizedHGFunCoeff_eq_zero_iff]

/-- If `a j = -k` for some `k : ℕ`, then the coefficients of the regularized hypergeometric series
vanish for all `n > k`. -/
theorem regularizedHGFunCoeff_eq_zero_left' (a : Fin p → ℂ) (b : Fin q → ℂ) (k n : ℕ)
    (ha : ∃ (j : Fin p), a j = -k) (hkn : k < n) : regularizedHGFunCoeff a b n = 0 := by
  apply regularizedHGFunCoeff_eq_zero_left
  obtain ⟨j, hj⟩ := ha
  use j, k, hkn
  simp [hj]

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one {a : Fin p → ℂ} {b : Fin q → ℂ} {n : ℕ}
    (hb : ∀ j, b j ≠ -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      ((∏ i : Fin p, (a i + n)) / ((∏ i : Fin q, (b i + n)) * (n + 1))) := calc
  _ = (∏ i : Fin p, ((ascPochhammer ℂ n).eval (a i)) * (a i + n)) /
      (n ! * (n + 1) * ∏ j : Fin q, Gamma (b j + n) * (b j + n)) := by
    unfold regularizedHGFunCoeff
    congr
    · ext j
      simp [ascPochhammer_succ_right]
    · rw [Nat.factorial_succ]
      norm_cast
      group
    · ext j
      simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
      rw [Gamma_add_one _ (by grind only [hb j])]
      group
  _ = _ := by
    unfold regularizedHGFunCoeff
    simp_rw [div_mul_div_comm, Finset.prod_mul_distrib]
    ring

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one_div_self {a : Fin p → ℂ} {b : Fin q → ℂ} {n : ℕ}
    (h : regularizedHGFunCoeff a b n ≠ 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      (∏ i : Fin p, (a i + n)) / ((∏ i : Fin q, (b i + n)) * (n + 1)) := by
  by_cases! hb : ∀ j, b j ≠ -n
  · rw [regularizedHGFunCoeff_add_one hb]
    field_simp
  · obtain ⟨j, hj⟩ := hb
    have h₁ : (∏ i, (b i + n)) = 0 := by
      grind [Finset.prod_eq_zero_iff]
    rw [regularizedHGFunCoeff_eq_zero_right a b n (by use j, 0; grind)]
    simp [h₁]

private theorem prod_eq_pow_mul_prod (a : Fin p → ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∏ i, (a i + n) = n ^ p * ∏ i, (a i / n + 1) := calc
  _ = ∏ i, n * (a i / n + 1) := by
    congr; ext; field_simp
  _ = _ := by
    simp [Finset.prod_mul_distrib]

theorem foobar (a : Fin p → ℂ) (b : Fin q → ℂ) {n : ℕ} (hn : n ≠ 0) :
    (∏ i : Fin p, (a i + n)) / ((∏ i : Fin q, (b i + n)) * (n + 1)) =
    n ^ (p - (q : ℤ) - 1) * (∏ i, (a i / n + 1)) / ((∏ i, (b i / n + 1)) * (1 + (n : ℂ)⁻¹)) := by
  rw [prod_eq_pow_mul_prod a hn, prod_eq_pow_mul_prod b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ q * n ^ (p - q - (1 : ℤ)) * ∏ x, (a x + n) / n := by
      congr 1
      rw [← pow_succ']
      simp_rw [← zpow_natCast]
      rw [← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by
      ring

/-- The regularized hypergeometric series. -/
def regularizedHGFunSeries (a : Fin p → ℂ) (b : Fin q → ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (regularizedHGFunCoeff a b)

@[simp]
theorem regularizedHGFunSeries_coeff (a : Fin p → ℂ) (b : Fin q → ℂ) :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

/-- The regularized hypergeometric function. -/
def regularizedHGFun (a : Fin p → ℂ) (b : Fin q → ℂ) (z : ℂ) : ℂ :=
  (regularizedHGFunSeries a b).sum z

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFun (a b c z : ℂ) : ℂ :=
  regularizedHGFun (fun (k : Fin 2) ↦ if k = 0 then a else b) (fun _ : Fin 1 ↦ c) z

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
theorem radius_regularizedHGFunSeries_eq_top_of_finite {a : Fin p → ℂ} {b : Fin q → ℂ}
    (ha : ∃ (j : Fin p) (k : ℕ), a j = -k) : (regularizedHGFunSeries a b).radius = ⊤ := by
  obtain ⟨j, k, h⟩ := ha
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use k + 1
  intro j' hj'
  unfold regularizedHGFunSeries
  simp only [FormalMultilinearSeries.ofScalars_eq_zero]
  apply regularizedHGFunCoeff_eq_zero_left' a b k j' ⟨_, h⟩
  grind

/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero {a : Fin p → ℂ} {b : Fin q → ℂ}
    (h : ∀ (j : Fin p) (k : ℕ), a j ≠ -↑k) :
    ∀ᶠ (n : ℕ) in atTop, regularizedHGFunCoeff a b n ≠ 0 := by
  rw [Filter.eventually_atTop]
  use ⌈iSup (-re ∘ b)⌉₊ + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, k, h'⟩)
  · grind
  · have h_nonempty : Nonempty (Fin q) := ⟨j⟩
    simp only [Order.add_one_le_iff] at hn
    have := lt_of_le_of_lt (Nat.ceil_mono <| Finite.le_ciSup (f := -re ∘ b) j) hn
    have foo : b j = -k - n := by grind
    simp only [Pi.neg_apply, Function.comp_apply, foo, sub_re, neg_re, natCast_re, neg_sub,
      sub_neg_eq_add] at this
    norm_cast at this
    rw [Nat.ceil_natCast (n + k)] at this
    simp at this

variable (a) in
private theorem blubb : Tendsto (fun n : ℕ ↦ (∏ i, (a i / n + 1))) atTop (𝓝 1) := by
  suffices ∀ i ∈ Finset.univ, Tendsto (fun n : ℕ ↦ (a i / n + 1)) atTop (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_finsetProd Finset.univ this
  intro i
  simpa using (tendsto_const_div_atTop_nhds_zero_nat (a i)).add_const 1

variable (a b) in
private theorem blubb' :
    Tendsto (fun n : ℕ ↦ (∏ i, (a i / n + 1)) / ((∏ i, (b i / n + 1)) * (1 + (n : ℂ)⁻¹))) atTop
      (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (blubb a).div ((blubb b).mul <| h.const_add 1) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

theorem radius_regularizedHGFunSeries_eq_top (a : Fin p → ℂ) (b : Fin q → ℂ) (h : p < q + 1) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : ∃ (j : Fin p) (k : ℕ), a j = -k
  · apply radius_regularizedHGFunSeries_eq_top_of_finite ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero ha
  · simp only [Nat.succ_eq_add_one]
    have h₁ : Tendsto (fun (n : ℕ) ↦ (n : ℂ) ^ (p - (q : ℤ) - 1)) atTop (𝓝 0) := by
      rw [NormedAddCommGroup.tendsto_atTop']
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_lt h
      simp only [Nat.add_right_cancel_iff] at hj
      rw [hj]
      simp only [Nat.cast_add, sub_add_cancel_left, sub_zero, norm_zpow, RCLike.norm_natCast]
      intro ε hε
      use 1 + ⌈ε ^ (-(j : ℝ) - 1)⁻¹⌉₊
      intro n hn
      have hn₁ : 0 < n := lt_of_le_of_lt (by simp) hn
      have hn₂ : ε ^ (-(j : ℝ) - 1)⁻¹ < n := calc
        _ < 1 + ε ^ (-(j : ℝ) - 1)⁻¹ := by grind
        _ ≤ 1 + (⌈ε ^ (-(j : ℝ) - 1)⁻¹⌉₊ : ℝ) := by
          gcongr
          apply Nat.le_ceil
        _ < n := by
          norm_cast
          push_cast
          apply hn
      rw [← Real.rpow_intCast]
      push_cast
      rwa [← Real.rpow_inv_lt_iff_of_neg hε (by norm_cast) (by grind)]
    have := (h₁.mul (blubb' a b)).norm
    simp only [mul_one, norm_zero] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero ha (b := b)
    rw [eventually_atTop] at h_ne
    obtain ⟨k, hk⟩ := h_ne
    rw [Filter.EventuallyEq, eventually_atTop]
    use 1 + k
    intro n hn
    rw [← Complex.norm_div, regularizedHGFunCoeff_add_one_div_self (hk n <| by grind),
      foobar a b (by grind), mul_div]

theorem radius_regularizedHGFunSeries_eq_one (a : Fin p → ℂ) (b : Fin q → ℂ) (h : p = q + 1)
    (h' : ∀ (j : Fin p) (k : ℕ), a j ≠ -↑k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have : Tendsto (fun n ↦ ‖regularizedHGFunCoeff a b n.succ‖ / ‖regularizedHGFunCoeff a b n‖) atTop
      (𝓝 1) := by
    have := (blubb' a b).norm
    simp only [norm_one] at this
    apply this.congr'
    have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero h' (b := b)
    rw [eventually_atTop] at h_ne
    obtain ⟨k, hk⟩ := h_ne
    rw [Filter.EventuallyEq, eventually_atTop]
    use 1 + k
    intro n hn
    rw [Nat.succ_eq_add_one, ← Complex.norm_div,
      regularizedHGFunCoeff_add_one_div_self (hk n <| by grind), foobar a b (by grind)]
    simp [h]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ _ (by simp) this
  simpa

end Complex
