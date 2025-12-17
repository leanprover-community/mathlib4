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

* T_n(x) ∈ [-1, 1] iff x ∈ [-1, 1]: `T_real_abs_le_one_iff_abs_le_one`
* Zeroes of T and U: `T_real_roots_eq`, `U_real_roots_eq`
* Extrema of T: `T_real_eval_at_extremum`, `T_real_extrema_eq`

## TODO

* Prove orthogonality with respect to appropriate inner product.
-/

@[expose] public section

namespace Polynomial.Chebyshev

open Real

theorem T_real_eval_bounded_of_bounded (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [← cos_arccos (x := x) (by grind) (by grind)]
  grind [T_real_cos, cos_mem_Icc]

theorem T_real_abs_eval_le_one_of_abs_le_one (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(T ℝ n).eval x| ≤ 1 := by
  grind [T_real_eval_bounded_of_bounded]

theorem T_real_one_le_eval_of_one_le (n : ℤ) {x : ℝ} (hx : 1 ≤ x) : 1 ≤ (T ℝ n).eval x := by
  rw [← cosh_arcosh hx]
  grind [T_real_cosh, one_le_cosh]

theorem T_real_one_lt_eval_of_one_lt {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < x) :
    1 < (T ℝ n).eval x := by
  have : arcosh x ≠ 0 := by
    by_contra! h
    grind [cosh_arcosh, cosh_zero]
  rw [←cosh_arcosh (le_of_lt hx), T_real_cosh, one_lt_cosh, mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩

theorem T_real_one_le_negOnePow_mul_eval_of_le_neg_one (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
    1 ≤ (-1) ^ n * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert T_real_one_le_eval_of_one_le n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

theorem T_real_one_lt_negOnePow_mul_eval_of_lt_neg_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x < -1) :
    1 < (-1) ^ n * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert T_real_one_lt_eval_of_one_lt hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

theorem T_real_one_le_abs_eval_of_one_le_abs (n : ℤ) {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ |(T ℝ n).eval x| := by
  cases le_abs.mp hx with
  | inl hx => exact T_real_one_le_eval_of_one_le n hx |> .inl |> le_abs.mpr
  | inr hx =>
    have := T_real_one_le_negOnePow_mul_eval_of_le_neg_one n (le_neg_of_le_neg hx)
    have : 1 ≤ |(-1) ^ n * (T ℝ n).eval x| := by grind
    convert this using 1
    simp [abs_mul, abs_zpow]

theorem T_real_one_lt_abs_eval_of_one_lt_abs {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < |x|) :
    1 < |(T ℝ n).eval x| := by
  cases lt_abs.mp hx with
  | inl hx => exact T_real_one_lt_eval_of_one_lt hn hx |> .inl |> lt_abs.mpr
  | inr hx =>
    have := T_real_one_lt_negOnePow_mul_eval_of_lt_neg_one hn (lt_neg_of_lt_neg hx)
    have : 1 < |(-1) ^ n * (T ℝ n).eval x| := by grind
    convert this using 1
    simp [abs_mul, abs_zpow]

theorem T_real_abs_eval_le_one_iff_abs_le_one {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    |x| ≤ 1 ↔ |(T ℝ n).eval x| ≤ 1 := by
  constructor
  · intro hx; exact T_real_abs_eval_le_one_of_abs_le_one n hx
  · intro hx; contrapose! hx; exact T_real_one_lt_abs_eval_of_one_lt_abs hn hx

theorem T_real_eval_eq_cos_of_abs_le_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : |(T ℝ n).eval x| ≤ 1) :
    (T ℝ n).eval x = cos (n * arccos x) := by
  have := (T_real_abs_eval_le_one_iff_abs_le_one hn x).mpr hx
  rw [← T_real_cos, cos_arccos (by grind) (by grind)]


/-- `T_real_roots n` is the set of roots of `T ℝ n`. -/
noncomputable def T_real_roots (n : ℕ) : Finset ℝ :=
  (Finset.range n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))

@[simp]
theorem card_T_real_roots (n : ℕ) : (T_real_roots n).card = n := by
  by_cases n = 0
  case pos hn => simp [T_real_roots, hn]
  case neg hn =>
    rw [T_real_roots, Finset.card_image_of_injOn, Finset.card_range]
    apply injOn_cos.comp (by aesop)
    intro k hk
    apply Set.mem_Icc.mpr
    constructor
    · positivity
    · field_simp
      norm_cast
      grind

theorem T_real_roots_eq {n : ℕ} (hn : n ≠ 0) : (T ℝ n).roots = (T_real_roots n).val := by
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) (by simp)
  obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
  rw [← hx, T_real_cos, cos_eq_zero_iff]
  use k
  field_simp
  norm_cast


/-- `T_real_extrema n` is the set of extremal points of `T ℝ n` in [-1, 1]. -/
noncomputable def T_real_extrema (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).image (fun (k : ℕ) => cos (k * π / n))

@[simp]
theorem card_T_real_extrema (n : ℕ) : (T_real_extrema n).card = n + 1 := by
  by_cases n = 0
  case pos hn => simp [T_real_extrema, hn]
  case neg hn =>
  rw [T_real_extrema, Finset.card_image_of_injOn, Finset.card_range]
  apply injOn_cos.comp (by aesop)
  intro k hk
  apply Set.mem_Icc.mpr
  constructor
  · positivity
  · field_simp
    norm_cast
    grind

theorem T_real_eval_at_extremum {n : ℤ} (hn : n ≠ 0) (k : ℤ) :
    (T ℝ n).eval (cos (k * π / n)) = (-1) ^ k := by
  rw [T_real_cos, ← cos_int_mul_pi]
  congr 1
  field_simp

theorem T_real_extrema_eq {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |(T ℝ n).eval x| = 1 ↔ x ∈ T_real_extrema n := by
  have hnℤ : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnℝ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp_rw [T_real_extrema, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · intro hTx
    have hx := (T_real_abs_eval_le_one_iff_abs_le_one hnℤ x).mpr (by grind)
    rw [T_real_eval_eq_cos_of_abs_le_one hnℤ (le_of_eq hTx), Int.cast_natCast] at hTx
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
    refine ⟨by grind, ?_⟩
    rw [← cos_arccos (x := x) (by grind) (by grind), hk]
    congr
    norm_cast
    exact Int.toNat_of_nonneg k_nonneg
  · rintro ⟨k, hk, hx⟩
    have := T_real_eval_at_extremum hnℤ k
    aesop


/-- `U_real_roots n` is the set of roots of `U ℝ n`. -/
noncomputable def U_real_roots (n : ℕ) : Finset ℝ :=
  (Finset.range n).image (fun (k : ℕ) => cos ((k + 1) * π / (n + 1)))

@[simp]
theorem card_U_real_roots (n : ℕ) : (U_real_roots n).card = n := by
  rw [U_real_roots, Finset.card_image_of_injOn, Finset.card_range]
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

theorem U_real_roots_eq {n : ℕ} : (U ℝ n).roots = (U_real_roots n).val := by
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) (by simp)
  obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
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

end Polynomial.Chebyshev
