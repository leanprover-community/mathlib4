/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chebyshev polynomials over the reals: roots and extrema

## Main statements

* T_n(x) ∈ [-1, 1] iff x ∈ [-1, 1]: `abs_eval_T_real_le_one_iff`
* Values of x such that |T_n(x)| = 1: `abs_eval_T_real_eq_one_iff`
* Zeroes of T and U: `roots_T_real`, `roots_U_real`
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Real

theorem eval_T_real_mem_Icc (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]

theorem abs_eval_T_real_le_one (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(T ℝ n).eval x| ≤ 1 := by grind [eval_T_real_mem_Icc]

theorem one_le_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ (T ℝ n).eval x := by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]

theorem one_lt_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < x) :
    1 < (T ℝ n).eval x := by
  have : arcosh x ≠ 0 := by
    by_contra! h
    grind [cosh_arcosh, cosh_zero]
  rw [←cosh_arcosh (le_of_lt hx), T_real_cosh, one_lt_cosh, mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩

theorem one_le_negOnePow_mul_eval_T_real (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
    1 ≤ (-1) ^ n * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

theorem one_lt_negOnePow_mul_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x < -1) :
    1 < (-1) ^ n * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert one_lt_eval_T_real hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

theorem one_le_abs_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ |(T ℝ n).eval x| := by
  cases le_abs.mp hx with
  | inl hx => exact one_le_eval_T_real n hx |> .inl |> le_abs.mpr
  | inr hx =>
    have := one_le_negOnePow_mul_eval_T_real n (le_neg_of_le_neg hx)
    have : 1 ≤ |(-1) ^ n * (T ℝ n).eval x| := by grind
    convert this using 1
    simp [abs_mul, abs_zpow]

theorem one_lt_abs_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < |x|) :
    1 < |(T ℝ n).eval x| := by
  cases lt_abs.mp hx with
  | inl hx => exact one_lt_eval_T_real hn hx |> .inl |> lt_abs.mpr
  | inr hx =>
    have := one_lt_negOnePow_mul_eval_T_real hn (lt_neg_of_lt_neg hx)
    have : 1 < |(-1) ^ n * (T ℝ n).eval x| := by grind
    convert this using 1
    simp [abs_mul, abs_zpow]

theorem abs_eval_T_real_le_one_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    |x| ≤ 1 ↔ |(T ℝ n).eval x| ≤ 1 := by
  constructor
  · intro hx; exact abs_eval_T_real_le_one n hx
  · intro hx; contrapose! hx; exact one_lt_abs_eval_T_real hn hx

theorem abs_eval_T_real_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |(T ℝ n).eval x| = 1 ↔ ∃ k ≤ n, x = cos (k * π / n) := by
  constructor
  · intro hTx
    have hx := (abs_eval_T_real_le_one_iff (Nat.cast_ne_zero.mpr hn) x).mpr (le_of_eq hTx)
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx), T_real_cos,
      Int.cast_natCast] at hTx
    have : ∃ (k : ℤ), k * π = n * arccos x := by
      cases (abs_eq zero_le_one).mp hTx
      case inl h =>
        obtain ⟨k, hk⟩ := (cos_eq_one_iff _).mp h
        use 2 * k
        grind
      case inr h =>
        obtain ⟨k, hk⟩ := cos_eq_neg_one_iff.mp h
        use 2 * k + 1
        grind
    obtain ⟨k, hk⟩ := this
    replace hk : arccos x = (k * π) / n := by aesop
    have k_nonneg : 0 ≤ k := by
      suffices 0 ≤ (k : ℝ) by norm_cast at this
      have : 0 ≤ k * π / n := by grind [arccos_nonneg]
      linear_combination (norm := field_simp) (n / π) * this
      grind
    have k_le_n : k ≤ n := by
      suffices (k : ℝ) ≤ n by norm_cast at this
      have : k * π / n ≤ π := by grind [arccos_le_pi]
      linear_combination (norm := field_simp) (n / π) * this
      grind
    use k.toNat
    refine ⟨Int.toNat_le.mpr k_le_n, ?_⟩
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx), hk]
    congr
    exact (Int.toNat_of_nonneg k_nonneg).symm
  · rintro ⟨k, hk, hx⟩
    have : ((n : ℤ) : ℝ) * (k * π / n) = (k : ℤ) * π := by norm_cast; field_simp
    rw [hx, T_real_cos, this, cos_int_mul_pi, abs_neg_one_zpow]

theorem roots_T_real (n : ℕ) :
    (T ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))).val := by
  by_cases n = 0
  case pos hn => simp [hn]
  case neg =>
  · refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
    · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
      rw [← hx, T_real_cos, cos_eq_zero_iff]
      use k
      field_simp
      norm_cast
    · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, Int.natAbs_natCast]
      apply injOn_cos.comp (by aesop)
      intro k hk
      apply Set.mem_Icc.mpr
      constructor
      · positivity
      · field_simp
        norm_cast
        grind

theorem rootMultiplicity_T_real {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (cos ((2 * k + 1) * π / (2 * n))) = 1 := by
  rw [← count_roots, roots_T_real, Multiset.count_eq_one_of_mem (by simp)]
  grind

theorem roots_U_real (n : ℕ) :
    (U ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((k + 1) * π / (n + 1)))).val := by
  by_cases n = 0
  case pos hn => simp [hn]
  case neg =>
  · refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
    · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
      suffices (U ℝ n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
        apply (mul_eq_zero_iff_right (ne_of_gt ?_)).mp this
        apply sin_pos_of_pos_of_lt_pi (by positivity)
        field_simp
        norm_cast
        grind
      rw [← hx, U_real_cos, sin_eq_zero_iff]
      use k + 1
      field_simp
      norm_cast
      ring
    · rw [Finset.card_image_of_injOn, Finset.card_range, degree_U_natCast]
      apply injOn_cos.comp
      · intro x hx y hy hxy
        field_simp at hxy
        aesop
      · intro k hk
        apply Set.mem_Icc.mpr
        constructor
        · positivity
        · field_simp
          norm_cast
          grind

theorem rootMultiplicity_U_real {n k : ℕ} (hk : k < n) :
    (U ℝ n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1 := by
  rw [← count_roots, roots_U_real, Multiset.count_eq_one_of_mem (by simp)]
  grind

end Polynomial.Chebyshev
