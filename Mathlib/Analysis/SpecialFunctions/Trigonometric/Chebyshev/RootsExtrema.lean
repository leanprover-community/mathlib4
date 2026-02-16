/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Niven

/-!
# Chebyshev polynomials over the reals: roots and extrema

## Main statements

* T_n(x) ∈ [-1, 1] iff x ∈ [-1, 1]: `abs_eval_T_real_le_one_iff`
* Zeroes of T and U: `roots_T_real`, `roots_U_real`
* Local extrema of T: `isLocalExtr_T_real_iff`, `isExtrOn_T_real_iff`
* Irrationality of zeroes of T other than zero: `irrational_of_isRoot_T_real`
-/

public section

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
  have : arcosh x ≠ 0 := by grind [cosh_arcosh, cosh_zero]
  rw [← cosh_arcosh (le_of_lt hx), T_real_cosh, one_lt_cosh, mul_ne_zero_iff]
  exact ⟨by norm_cast, by assumption⟩

theorem one_le_negOnePow_mul_eval_T_real (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
    1 ≤ n.negOnePow * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert one_le_eval_T_real n (le_neg_of_le_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

theorem one_lt_negOnePow_mul_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x < -1) :
    1 < n.negOnePow * (T ℝ n).eval x := by
  rw [← neg_neg x, T_eval_neg]
  convert one_lt_eval_T_real hn (lt_neg_of_lt_neg hx)
  rw [Int.cast_negOnePow, ← mul_assoc, ← mul_zpow]
  simp

theorem one_le_abs_eval_T_real (n : ℤ) {x : ℝ} (hx : 1 ≤ |x|) :
    1 ≤ |(T ℝ n).eval x| := by
  wlog! h : 0 ≤ x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n (-x) (by grind) (by grind)
  · exact one_le_eval_T_real n (abs_of_nonneg h ▸ hx) |>.trans <| le_abs_self _

theorem one_lt_abs_eval_T_real {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 1 < |x|) :
    1 < |(T ℝ n).eval x| := by
  wlog! h : 0 ≤ x
  · simpa [T_eval_neg, abs_mul, abs_unit_intCast] using @this n hn (-x) (by grind) (by grind)
  · exact one_lt_eval_T_real hn (abs_of_nonneg h ▸ hx) |>.trans_le <| le_abs_self _

theorem abs_eval_T_real_le_one_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    |x| ≤ 1 ↔ |(T ℝ n).eval x| ≤ 1 :=
  ⟨abs_eval_T_real_le_one n, by simpa using mt <| one_lt_abs_eval_T_real hn⟩

theorem abs_eval_T_real_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |(T ℝ n).eval x| = 1 ↔ ∃ k ≤ n, x = cos (k * π / n) := by
  constructor
  · intro hTx
    have hx := (abs_eval_T_real_le_one_iff (Nat.cast_ne_zero.mpr hn) x).mpr (le_of_eq hTx)
    rw [← cos_arccos (neg_le_of_abs_le hx) (le_of_max_le_left hx), T_real_cos,
      Int.cast_natCast, abs_cos_eq_one_iff] at hTx
    obtain ⟨k, hk⟩ := hTx
    have hk' : k = n * (arccos x / π) := by simpa [field]
    lift k to ℕ using (by rw [← Int.cast_nonneg_iff (R := ℝ), hk']; positivity [arccos_nonneg x])
    simp only [Int.cast_natCast] at hk hk'
    have hkn : (k : ℝ) ≤ n := by
      rw [← mul_one (n : ℝ), hk']
      gcongr
      exact div_le_one_of_le₀ (arccos_le_pi x) (by positivity)
    refine ⟨k, by simpa using hkn, ?_⟩
    convert congr(cos ($hk.symm / n))
    rw [mul_div_cancel_left₀ _ (by simpa), cos_arccos (by grind) (by grind)]
  · rintro ⟨k, hk, rfl⟩
    rw [T_real_cos, abs_cos_eq_one_iff]
    exact ⟨k, by simp [field]⟩

theorem eval_T_real_cos_int_mul_pi_div {k : ℕ} {n : ℕ} (hn : n ≠ 0) :
    (T ℝ n).eval (cos (k * π / n)) = (k : ℤ).negOnePow := by
  rw [T_real_cos, Int.cast_negOnePow]
  convert Real.cos_int_mul_pi k using 2
  simp [field]

theorem eval_T_real_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    (T ℝ n).eval x = 1 ↔ ∃ k ≤ n, Even k ∧ x = cos (k * π / n) := by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans abs_one)
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂, eval_T_real_cos_int_mul_pi_div hn, Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_one_iff_even (by grind)).mp hx
  · rintro ⟨k, hk₁, hk₂, hx⟩
    rw [hx, eval_T_real_cos_int_mul_pi_div hn, Int.negOnePow_even k ((Int.even_coe_nat k).mpr hk₂)]
    norm_cast

theorem eval_T_real_eq_neg_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    (T ℝ n).eval x = -1 ↔ ∃ k ≤ n, Odd k ∧ x = cos (k * π / n) := by
  constructor
  · intro hx
    obtain ⟨k, hk₁, hk₂⟩ := (abs_eval_T_real_eq_one_iff hn x).mp
      ((abs_eq_abs.mpr (.inl hx)).trans ((abs_neg 1).trans abs_one))
    use k
    refine ⟨hk₁, ?_, hk₂⟩
    rw [hk₂, eval_T_real_cos_int_mul_pi_div hn, Int.cast_negOnePow_natCast] at hx
    exact (neg_one_pow_eq_neg_one_iff_odd (by grind)).mp hx
  · rintro ⟨k, hk₁, hk₂, hx⟩
    rw [hx, eval_T_real_cos_int_mul_pi_div hn, Int.negOnePow_odd k ((Int.odd_coe_nat k).mpr hk₂)]
    norm_cast

theorem roots_T_real_nodup (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((2 * k + 1) * π / (2 * n))) (.range n)).Nodup := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  refine injOn_cos.comp (by aesop) fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
  field_simp
  norm_cast
  grind

theorem roots_T_real (n : ℕ) :
    (T ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))).val := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    rw [← hx, T_real_cos, cos_eq_zero_iff]
    use k
    field_simp
    norm_cast
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_T, Int.natAbs_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_T_real_nodup n)

theorem rootMultiplicity_T_real {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (cos ((2 * k + 1) * π / (2 * n))) = 1 := by
  rw [← count_roots, roots_T_real, Multiset.count_eq_one_of_mem (by simp)]
  grind

theorem roots_U_real_nodup (n : ℕ) :
    (Multiset.map (fun k : ℕ ↦ cos ((k + 1) * π / (n + 1))) (.range n)).Nodup := by
  refine (Finset.range n).nodup_map_iff_injOn.mpr ?_
  apply injOn_cos.comp
  · intro x hx y hy hxy
    field_simp at hxy
    aesop
  · refine fun k hk => Set.mem_Icc.mpr ⟨by positivity, ?_⟩
    field_simp
    norm_cast
    grind

theorem roots_U_real (n : ℕ) :
    (U ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((k + 1) * π / (n + 1)))).val := by
  wlog! hn : n ≠ 0
  · simp [hn]
  refine roots_eq_of_degree_eq_card (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp hx
    suffices (U ℝ n).eval x * sin ((k + 1) * π / (n + 1)) = 0 by
      refine (mul_eq_zero_iff_right (ne_of_gt (sin_pos_of_pos_of_lt_pi (by positivity) ?_))).mp this
      field_simp
      norm_cast
      grind
    rw [← hx, U_real_cos, sin_eq_zero_iff]
    use k + 1
    field_simp
    norm_cast
    ring
  · rw [Finset.card_image_of_injOn, Finset.card_range, degree_U_natCast]
    exact (Finset.range n).nodup_map_iff_injOn.mp (roots_U_real_nodup n)

theorem rootMultiplicity_U_real {n k : ℕ} (hk : k < n) :
    (U ℝ n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1 := by
  rw [← count_roots, roots_U_real, Multiset.count_eq_one_of_mem (by simp)]
  grind

theorem isLocalMax_T_real {n k : ℕ} (hn : n ≠ 0) (hk₀ : 0 < k) (hk₁ : k < n) (hk₂ : Even k) :
    IsLocalMax (T ℝ n).eval (cos (k * π / n)) := by
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eval_T_real_eq_one_iff hn _).mpr ⟨k, le_of_lt hk₁, hk₂, rfl⟩]
    exact (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
  · rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_of_lt zero_lt) (le_refl π) lt_pi
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt lt_pi) zero_lt

theorem isLocalMin_T_real {n k : ℕ} (hn : n ≠ 0) (hk₁ : k < n) (hk₂ : Odd k) :
    IsLocalMin (T ℝ n).eval (cos (k * π / n)) := by
  have k_pos : 0 < k := hk₂.pos
  have zero_lt : 0 < k * π / n := by positivity
  have lt_pi : k * π / n < π := calc
    k * π / n < n * π / n := by gcongr
    _ = π := mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)
  refine eventually_nhds_iff.mpr ⟨Set.Ioo (-1) 1, ?_, isOpen_Ioo, ?_, ?_⟩
  · intro x hx
    dsimp
    rw [(eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, le_of_lt hk₁, hk₂, rfl⟩]
    refine (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1
  · rw [← cos_pi]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_of_lt zero_lt) (le_refl π) lt_pi
  · rw [← cos_zero]
    exact cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt lt_pi) zero_lt

theorem isLocalExtr_T_real {n k : ℕ} (hn : n ≠ 0) (hk₀ : 0 < k) (hk₁ : k < n) :
    IsLocalExtr (T ℝ n).eval (cos (k * π / n)) := by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isLocalMax_T_real hn hk₀ hk₁ hk₂)
  case inr hk₂ => exact .inl (isLocalMin_T_real hn hk₁ hk₂)

theorem isLocalExtr_T_real_iff {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    IsLocalExtr (T ℝ n).eval x ↔ ∃ k ∈ Finset.Ioo 0 n, x = cos (k * π / n) := by
  constructor
  · intro hx
    replace hx := hx.deriv_eq_zero
    rw [Polynomial.deriv, T_derivative_eq_U, eval_mul, Int.cast_natCast, eval_natCast,
      mul_eq_zero_iff_left (by aesop)] at hx
    replace hx : x ∈ (U ℝ (n - 1)).roots :=
      (mem_roots (degree_ne_bot.mp (ne_of_eq_of_ne (by grind [degree_U_natCast])
        (WithBot.natCast_ne_bot (n - 1))))).mpr hx
    rw [show (n - 1 : ℤ) = (n - 1 : ℕ) by grind, roots_U_real] at hx
    obtain ⟨k, hk₁, hx⟩ := Finset.mem_image.mp hx
    refine ⟨k + 1, Finset.mem_Ioo.mpr ⟨k.zero_lt_succ, by grind⟩, ?_⟩
    rw [← hx]
    congr <;> norm_cast
    exact Nat.sub_add_cancel (Nat.one_le_of_lt hn)
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isLocalExtr_T_real (Nat.ne_zero_of_lt hn)
      (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2

theorem isMaxOn_T_real {n k : ℕ} (hn : n ≠ 0) (hk₁ : k ≤ n) (hk₂ : Even k) :
    IsMaxOn (T ℝ n).eval (Set.Icc (-1) 1) (cos (k * π / n)) :=
  isMaxOn_iff.mpr (fun x hx => le_of_le_of_eq (abs_le.mp (abs_eval_T_real_le_one n (by grind))).2
    ((eval_T_real_eq_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩).symm)

theorem isMinOn_T_real {n k : ℕ} (hn : n ≠ 0) (hk₁ : k ≤ n) (hk₂ : Odd k) :
    IsMinOn (T ℝ n).eval (Set.Icc (-1) 1) (cos (k * π / n)) :=
  isMinOn_iff.mpr (fun x hx => le_of_eq_of_le
    ((eval_T_real_eq_neg_one_iff hn _).mpr ⟨k, hk₁, hk₂, rfl⟩)
    (abs_le.mp (abs_eval_T_real_le_one n (by grind))).1)

theorem isExtrOn_T_real {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ n) :
    IsExtrOn (T ℝ n).eval (Set.Icc (-1) 1) (cos (k * π / n)) := by
  cases k.even_or_odd
  case inl hk₂ => exact .inr (isMaxOn_T_real hn hk hk₂)
  case inr hk₂ => exact .inl (isMinOn_T_real hn hk hk₂)

theorem isExtrOn_T_real_iff {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    IsExtrOn (T ℝ n).eval (Set.Icc (-1) 1) x ↔
    ∃ k ≤ n, x = cos (k * π / n) := by
  constructor
  · intro h
    apply (abs_eval_T_real_eq_one_iff hn x).mp
    apply eq_of_le_of_ge (abs_eval_T_real_le_one n (by grind))
    refine h.elim (fun h => ?_) (fun h => ?_)
    · refine le_abs.mpr (.inr (le_neg_of_le_neg ?_))
      have := isMinOn_iff.mp h (cos (1 * π / n)) (by grind [abs_cos_le_one])
      rw [(eval_T_real_eq_neg_one_iff hn (cos (1 * π / n))).mpr ⟨1, Nat.one_le_iff_ne_zero.mpr hn,
        by simp⟩] at this
      assumption
    · refine le_abs.mpr (.inl ?_)
      have := isMaxOn_iff.mp h (cos (0 * π / n)) (by simp)
      rw [(eval_T_real_eq_one_iff hn _).mpr ⟨0, by simp, by simp⟩] at this
      assumption
  · rintro ⟨k, hk, hx⟩
    rw [hx]
    exact isExtrOn_T_real hn hk

theorem irrational_of_isRoot_T_real {n : ℕ} {x : ℝ} (hroot : (T ℝ n).IsRoot x) (hnz : x ≠ 0) :
    Irrational x := by
  rw [← mem_roots (T_ne_zero ℝ n), roots_T_real] at hroot
  obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hroot
  have hn : n ≠ 0 := by grind
  suffices Irrational (cos ((Rat.divInt (2 * k + 1) (2 * n)) * π)) by
    rw [← hk₂]; convert this using 2; push_cast; field_simp
  apply irrational_cos_rat_mul_pi
  contrapose! hnz
  have : (Rat.divInt (2 * k + 1) (2 * n)).den = 2 * (n / n.gcd (2 * k + 1)) := calc
    _ = 2 * n / (2 * n).gcd (2 * k + 1) := by rw [Rat.den_divInt]; norm_cast; simp [hn]
    _ = _ := by rw [Nat.Coprime.gcd_mul_left_cancel n (by simp),
      Nat.mul_div_assoc _ (Nat.gcd_dvd_left ..)]
  have hn : 2 * k + 1 = n := Nat.eq_of_dvd_of_lt_two_mul (by simp) (Nat.gcd_eq_left_iff_dvd.mp <|
    Nat.eq_of_dvd_of_div_eq_one (Nat.gcd_dvd_left ..) (by grind [Rat.den_pos])) (by grind)
  rw_mod_cast [← hk₂, hn]; convert cos_pi_div_two using 2; push_cast; field_simp

end Polynomial.Chebyshev
