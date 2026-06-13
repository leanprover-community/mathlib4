/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.NumberTheory.AbelSummation

/-!
# Euler-Maclaurin summation formula

This file proves a first-order Euler-Maclaurin summation formula. The proof specializes Abel
summation to the constant coefficient sequence and rewrites the floor correction by integration by
parts.

## Main declarations

* `periodizedBernoulli1`: the first periodized Bernoulli function, `x ↦ Int.fract x - 1 / 2`.
* `sum_eq_integral_add_integral_deriv_mul_periodizedBernoulli1`: a first-order Euler-Maclaurin
  summation formula for functions `ℝ → 𝕜`, with `[RCLike 𝕜]`.
-/

@[expose] public section

noncomputable section

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The first periodized Bernoulli function, written on `ℝ` using the fractional part. -/
def periodizedBernoulli1 (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- The first periodized Bernoulli function is strongly measurable. -/
@[fun_prop]
lemma aestronglyMeasurable_periodizedBernoulli1 :
    AEStronglyMeasurable periodizedBernoulli1 := by
  unfold periodizedBernoulli1
  fun_prop

/-- The first periodized Bernoulli function has absolute value at most `1 / 2`. -/
lemma abs_periodizedBernoulli1_le_half (x : ℝ) :
    |periodizedBernoulli1 x| ≤ 1 / 2 := by
  unfold periodizedBernoulli1
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [Int.fract_nonneg x]
  · linarith [Int.fract_lt_one x]

/-- Integration by parts for multiplying a derivative by an affine function. -/
lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b)
    (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t =
      (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have h_deriv_left : ∀ t ∈ [[a, b]], HasDerivAt (fun t : ℝ ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    simpa only [RCLike.ofRealCLM_apply, map_one] using
      (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul h_deriv_left hf_diff (by simp) h_int]
  simp

/-- Multiplying a continuous derivative by `periodizedBernoulli1` is interval integrable. -/
lemma intervalIntegrable_deriv_mul_periodizedBernoulli1 (hab : a ≤ b)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * periodizedBernoulli1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  simpa only [RCLike.norm_ofReal] using abs_periodizedBernoulli1_le_half x

private lemma natFloor_cast_eq_intFloor_cast {t : ℝ} (ht : 0 ≤ t) :
    ((⌊t⌋₊ : ℕ) : 𝕜) = (⌊t⌋ : ℤ) := by
  have hfloor_nonneg : 0 ≤ ⌊t⌋ := Int.floor_nonneg.2 ht
  have hfloor_nat : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := by
    rw [← Int.floor_toNat t, Int.toNat_of_nonneg hfloor_nonneg]
  exact_mod_cast hfloor_nat

private lemma natFloor_add_one_eq_add_half_sub_periodizedBernoulli1 {t : ℝ} (ht : 0 ≤ t) :
    ((⌊t⌋₊ : ℕ) : 𝕜) + 1 =
      (t + (1 / 2 : 𝕜)) - (periodizedBernoulli1 t : 𝕜) := by
  rw [natFloor_cast_eq_intFloor_cast (𝕜 := 𝕜) ht, periodizedBernoulli1, Int.fract]
  push_cast
  ring

private lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) =
      (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) -
        ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
  calc
    _ = ∫ t in a..b, deriv f t * (t + 1 / 2) -
          deriv f t * periodizedBernoulli1 t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hab] at ht
        have ht_nonneg : 0 ≤ t := ha.trans ht.1
        change deriv f t * (((⌊t⌋₊ : ℕ) : 𝕜) + 1) =
          deriv f t * (t + (1 / 2 : 𝕜)) -
            deriv f t * (periodizedBernoulli1 t : 𝕜)
        rw [natFloor_add_one_eq_add_half_sub_periodizedBernoulli1 (𝕜 := 𝕜) ht_nonneg]
        ring
    _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) -
        ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
      exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop))
        (intervalIntegrable_deriv_mul_periodizedBernoulli1 hab h_cont)
    _ = _ := by
      conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
      rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

/-- The first-order Euler-Maclaurin summation formula. -/
theorem sum_eq_integral_add_integral_deriv_mul_periodizedBernoulli1 (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * periodizedBernoulli1 a - f b * periodizedBernoulli1 b + (∫ t in a..b, f t) +
        ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
  have h_sum := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff
    (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at h_sum
  rw [h_sum, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold periodizedBernoulli1
  rw [Int.fract, Int.fract]
  push_cast
  rw [natFloor_cast_eq_intFloor_cast (𝕜 := 𝕜) ha,
    natFloor_cast_eq_intFloor_cast (𝕜 := 𝕜) (ha.trans hab)]
  ring_nf

end
