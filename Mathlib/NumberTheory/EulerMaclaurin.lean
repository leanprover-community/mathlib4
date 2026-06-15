/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.ZetaValues

/-!
# First-order Euler-Maclaurin summation formula

This file proves the first-order Euler-Maclaurin formula, relating a sum of a function over the
integers in an interval to its integral, a boundary correction, and an error integral against the
periodized first Bernoulli function (the sawtooth function).

## Main definitions

* `periodizedBernoulli1`: the periodized first Bernoulli function
  `x ↦ bernoulliFun 1 (Int.fract x)`, the one-periodic sawtooth taking values in `[-1/2, 1/2)`.
  This is the `n = 1` case of the periodized Bernoulli family; the general
  `periodizedBernoulli n := bernoulliFun n ∘ Int.fract` and the corresponding n-order
  Euler-Maclaurin formula are queued as a follow-up PR.

## Main statements

* `sum_eq_integral_add_integral_deriv_mul_periodizedBernoulli1`: for `f : ℝ → 𝕜` with `[RCLike 𝕜]`,
  `0 ≤ a ≤ b`, `f` differentiable on `Set.Icc a b` and `deriv f` continuous on `[[a, b]]`,
  `∑ k ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f k` equals
  `f a * periodizedBernoulli1 a - f b * periodizedBernoulli1 b + (∫ t in a..b, f t)
    + ∫ t in a..b, deriv f t * periodizedBernoulli1 t`.

The proof specializes Abel summation (`sum_mul_eq_sub_sub_integral_mul`) to the constant
coefficient `1`, then rewrites the floor correction by integration by parts.

This complements the existing `bernoulliFun` (the polynomial `x ↦ x - 1 / 2` at `n = 1`) and the
`UnitAddCircle`-valued `periodizedBernoulli`; here we provide the `ℝ → ℝ` periodization used in
summation estimates, expressed directly in terms of `bernoulliFun`.

## Floor convention

This file standardizes on `Int.floor` (`⌊·⌋`) rather than `Nat.floor` (`⌊·⌋₊`) throughout the main
theorem statement. On the range `[a, b]` with `0 ≤ a`, the two floors agree (witnessed by
`natFloor_cast_eq_intFloor_cast` below), so the underlying Nat-indexed Abel summation method is
preserved while the public statement matches the convention needed for any general
`periodizedBernoulli n : ℝ → ℝ` extension.
-/

@[expose] public section

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The periodized first Bernoulli function, the one-periodic sawtooth
`x ↦ bernoulliFun 1 (Int.fract x)`. Equivalent to `Int.fract x - 1 / 2`.

This is the `n = 1` case of the periodized Bernoulli functions
`periodizedBernoulli n := bernoulliFun n ∘ Int.fract`; the general family and the n-order
Euler-Maclaurin formula are queued as a follow-up PR. -/
noncomputable def periodizedBernoulli1 (x : ℝ) : ℝ := bernoulliFun 1 (Int.fract x)

/-- Unfold lemma for `periodizedBernoulli1` to the explicit sawtooth form. -/
lemma periodizedBernoulli1_eq (x : ℝ) : periodizedBernoulli1 x = Int.fract x - 1 / 2 := by
  unfold periodizedBernoulli1
  rw [bernoulliFun_one]

@[fun_prop]
lemma aestronglyMeasurable_periodizedBernoulli1 :
    AEStronglyMeasurable periodizedBernoulli1 := by
  simp_rw [funext periodizedBernoulli1_eq]
  fun_prop

/-- The periodized first Bernoulli function is bounded in absolute value by `1 / 2`. -/
lemma abs_periodizedBernoulli1_le_half (x : ℝ) : |periodizedBernoulli1 x| ≤ 1 / 2 := by
  rw [periodizedBernoulli1_eq]
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Int.fract_nonneg x]
  · grind [Int.fract_lt_one x]

/-- Integration by parts against the affine function `t ↦ t + c`. -/
lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b)
    (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have h_deriv_left : ∀ t ∈ [[a, b]], HasDerivAt (fun t : ℝ ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    simpa only [RCLike.ofRealCLM_apply, map_one] using
      (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul h_deriv_left hf_diff (by simp) h_int]
  simp

/-- The integrand `deriv f · periodizedBernoulli1` is interval integrable. -/
lemma intervalIntegrable_deriv_mul_periodizedBernoulli1 (hab : a ≤ b)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * periodizedBernoulli1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x _
  norm_cast
  exact abs_periodizedBernoulli1_le_half x

/-- Bridge: on nonneg reals, casting `Nat.floor x` to `ℤ` equals `Int.floor x`. -/
lemma natFloor_cast_eq_intFloor_cast (x : ℝ) (hx : (0 : ℝ) ≤ x) :
    ((⌊x⌋₊ : ℤ) : ℝ) = ⌊x⌋ := by
  rw [Int.natCast_floor_eq_floor hx]

/-- The error integral against the floor function, rewritten via integration by parts.
Stated with `Int.floor` for consistency with the public theorem; the Nat.floor version
is recovered by the bridge `natFloor_cast_eq_intFloor_cast` on `0 ≤ a ≤ b`. -/
private lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋ + 1) =
      (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t)
        - ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) - deriv f t * periodizedBernoulli1 t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have hft : ((⌊t⌋ : 𝕜)) = ((t : ℝ) : 𝕜) - ((Int.fract t : ℝ) : 𝕜) := by
      have : ((⌊t⌋ : ℝ)) = t - Int.fract t := Int.self_sub_fract t |>.symm
      rw [← RCLike.ofReal_intCast, this]
      push_cast
      ring
    rw [periodizedBernoulli1_eq, hft]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2))
        - ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop))
      (intervalIntegrable_deriv_mul_periodizedBernoulli1 hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext t; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

/-- Reindex the nonnegative integer interval between its `Int.floor` and `Nat.floor` endpoints. -/
private lemma sum_Ioc_intFloor_eq_sum_Ioc_natFloor (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ k ∈ Ioc ⌊a⌋ ⌊b⌋, f k) = ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k := by
  have hIoc : (Ioc ⌊a⌋ ⌊b⌋ : Finset ℤ) =
      (Ioc ⌊a⌋₊ ⌊b⌋₊).map (Nat.castEmbedding (R := ℤ)) := by
    have hfa : ((⌊a⌋₊ : ℤ)) = ⌊a⌋ := Int.natCast_floor_eq_floor ha
    have hfb : ((⌊b⌋₊ : ℤ)) = ⌊b⌋ := Int.natCast_floor_eq_floor (ha.trans hab)
    rw [← hfa, ← hfb]
    ext z
    simp only [mem_Ioc, mem_map, Nat.castEmbedding_apply]
    constructor
    · intro hz
      have hz0 : 0 ≤ z := le_trans (Int.natCast_nonneg ⌊a⌋₊) hz.1.le
      refine ⟨z.toNat, ?_, ?_⟩
      · have hzt : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
        constructor
        · rw [← hzt] at hz
          exact_mod_cast hz.1
        · rw [← hzt] at hz
          exact_mod_cast hz.2
      · exact Int.toNat_of_nonneg hz0
    · rintro ⟨n, hn, rfl⟩
      constructor
      · exact_mod_cast hn.1
      · exact_mod_cast hn.2
  rw [hIoc, sum_map]
  rfl

/-- **First-order Euler-Maclaurin summation formula**. For `f : ℝ → 𝕜` with `[RCLike 𝕜]`,
`0 ≤ a ≤ b`, `f` differentiable on `Set.Icc a b` and `deriv f` continuous on `[[a, b]]`, the sum of
`f` over the integers in `Finset.Ioc ⌊a⌋ ⌊b⌋` equals its integral plus a boundary correction and
an error integral against the periodized first Bernoulli function. -/
theorem sum_eq_integral_add_integral_deriv_mul_periodizedBernoulli1 (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋ ⌊b⌋, f k =
      f a * periodizedBernoulli1 a - f b * periodizedBernoulli1 b + (∫ t in a..b, f t)
        + ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
  rw [sum_Ioc_intFloor_eq_sum_Ioc_natFloor ha hab]
  have h_sum := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff
    (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at h_sum
  rw [h_sum, ← intervalIntegral.integral_of_le hab]
  have h_nat_int_integral :
      (∫ t in a..b, deriv f t * (⌊t⌋₊ + 1)) =
        ∫ t in a..b, deriv f t * (⌊t⌋ + 1) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at ht
    have ht0 : 0 ≤ t := ha.trans ht.1
    have hfloor : (((⌊t⌋₊ : ℕ) : 𝕜)) = ((⌊t⌋ : ℤ) : 𝕜) := by
      have hfloor_int : ((⌊t⌋₊ : ℤ)) = ⌊t⌋ := Int.natCast_floor_eq_floor ht0
      exact_mod_cast hfloor_int
    rw [hfloor]
  rw [h_nat_int_integral]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  rw [periodizedBernoulli1_eq, periodizedBernoulli1_eq]
  rw [Int.fract, Int.fract]
  push_cast
  have hfloor_a : (((⌊a⌋₊ : ℕ) : 𝕜)) = ((⌊a⌋ : ℤ) : 𝕜) := by
    have hfloor_int : ((⌊a⌋₊ : ℤ)) = ⌊a⌋ := Int.natCast_floor_eq_floor ha
    exact_mod_cast hfloor_int
  have hfloor_b : (((⌊b⌋₊ : ℕ) : 𝕜)) = ((⌊b⌋ : ℤ) : 𝕜) := by
    have hfloor_int : ((⌊b⌋₊ : ℤ)) = ⌊b⌋ := Int.natCast_floor_eq_floor (ha.trans hab)
    exact_mod_cast hfloor_int
  rw [hfloor_a, hfloor_b]
  ring_nf

/-- Nat-endpoint version of the first-order Euler-Maclaurin summation formula. -/
theorem sum_natFloor_eq_integral_add_integral_deriv_mul_periodizedBernoulli1
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f (k : ℝ) =
      f a * periodizedBernoulli1 a - f b * periodizedBernoulli1 b + (∫ t in a..b, f t)
        + ∫ t in a..b, deriv f t * periodizedBernoulli1 t := by
  calc
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f (k : ℝ) = ∑ k ∈ Ioc ⌊a⌋ ⌊b⌋, f (k : ℝ) := by
      exact (sum_Ioc_intFloor_eq_sum_Ioc_natFloor (f := f) ha hab).symm
    _ = f a * periodizedBernoulli1 a - f b * periodizedBernoulli1 b + (∫ t in a..b, f t)
          + ∫ t in a..b, deriv f t * periodizedBernoulli1 t :=
      sum_eq_integral_add_integral_deriv_mul_periodizedBernoulli1 ha hab hf_diff h_cont
