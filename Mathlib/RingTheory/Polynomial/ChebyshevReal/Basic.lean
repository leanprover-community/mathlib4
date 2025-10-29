/-
Copyright (c) 2020 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chebyshev polynomials over the reals

## Main statements

* T_n(x) ∈ [-1, 1] iff x ∈ [-1, 1]
* Zeroes of T and U
* Extrema of T

## TODO

* Prove orthogonality with respect to appropriate inner product.
* Prove more minimax properties of Chebyshev polynomials.
-/

namespace Polynomial

theorem roots_of_zeroes_of_card
  {R : Type _} [CommRing R] [IsDomain R] {p : Polynomial R} {S : Finset R}
  (hS : ∀ x ∈ S, p.eval x = 0) (hcard : S.card = p.degree) :
  p.roots = S.val := by
  have hp : p ≠ 0 := by contrapose! hcard; simp [hcard]
  symm; apply Multiset.eq_of_le_of_card_le
  · apply Finset.val_le_iff_val_subset.mpr
    intro x hx
    apply (p.mem_roots hp).mpr
    apply hS
    exact hx
  · change p.roots.card ≤ S.card
    have := p.card_roots hp
    rw [←hcard, Nat.cast_le] at this
    exact this

end Polynomial

namespace Polynomial.Chebyshev

open Polynomial
open Real

theorem T_degree_real (n : ℤ) : (T ℝ n).degree = n.natAbs := by
  exact T_degree ℝ (by simp) n

theorem T_natDegree_real (n : ℤ) : (T ℝ n).natDegree = n.natAbs := by
  exact T_natDegree ℝ (by simp) n

theorem T_leadingCoeff_real (n : ℤ) : (T ℝ n).leadingCoeff = 2^(n.natAbs - 1) := by
  exact T_leadingCoeff ℝ (by simp) n

theorem T_bounded_of_bounded (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
  (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc] at hx
  rw [←cos_arccos hx.1 hx.2, T_real_cos]
  apply cos_mem_Icc

theorem T_bounded_of_bounded' (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
  |(T ℝ n).eval x| ≤ 1 := by
  apply abs_le.mpr
  rw [←Set.mem_Icc]
  apply T_bounded_of_bounded n
  rw [Set.mem_Icc]
  exact abs_le.mp hx

/-- Inverse of `arccos`. -/
noncomputable def arccosh (x : ℝ) : ℝ := log (x + sqrt (x^2 - 1))

@[simp]
theorem cosh_arccosh {x : ℝ} (hx : 1 ≤ x) : cosh (arccosh x) = x := by
  unfold arccosh
  have : 0 < x + sqrt (x^2 - 1) := by positivity
  rw [cosh_eq, exp_neg, exp_log this]
  field_simp; ring_nf
  rw [sq_sqrt]
  · ring
  · linarith [show 1 ≤ x^2 from one_le_pow₀ hx]

theorem T_ge_of_ge_one (n : ℤ) {x : ℝ} (hx : x ≥ 1) :
  (T ℝ n).eval x ≥ 1 := by
  rw [←cosh_arccosh hx, T_real_cosh]
  apply one_le_cosh

theorem T_gt_of_gt_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x > 1) :
  (T ℝ n).eval x > 1 := by
  rw [←cosh_arccosh (le_of_lt hx), T_real_cosh]
  apply one_lt_cosh.mpr
  apply mul_ne_zero_iff.mpr
  constructor
  · norm_cast
  by_contra! h
  have : x = 1 := by rw [←cosh_arccosh (le_of_lt hx), h, cosh_zero]
  subst this
  exact (lt_self_iff_false 1).mp hx

theorem T_ge_of_le_neg_one (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
  n.negOnePow * (T ℝ n).eval x ≥ 1 := by
  rw [←neg_neg x, T_eval_neg, ←mul_assoc]
  norm_cast
  rw [←Int.negOnePow_add, ←two_mul, Int.negOnePow_two_mul]
  norm_cast; rw [one_mul]
  apply T_ge_of_ge_one n
  linarith

theorem T_gt_of_lt_neg_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x < -1) :
  n.negOnePow * (T ℝ n).eval x > 1 := by
  rw [←neg_neg x, T_eval_neg, ←mul_assoc]
  norm_cast
  rw [←Int.negOnePow_add, ←two_mul, Int.negOnePow_two_mul]
  norm_cast; rw [one_mul]
  apply T_gt_of_gt_one hn
  linarith

theorem T_abs_ge_of_abs_ge (n : ℤ) {x : ℝ} (hx : |x| ≥ 1) :
  |(T ℝ n).eval x| ≥ 1 := by
  apply le_abs.mpr
  cases le_abs.mp hx with
  | inl hx =>
    left
    exact T_ge_of_ge_one n hx
  | inr hx =>
    have : x ≤ -1 := by linarith
    have := T_ge_of_le_neg_one n this
    cases n.even_or_odd with
    | inl hn =>
      left
      rw [Int.negOnePow_even n hn] at this
      push_cast at this
      rw [one_mul] at this
      exact this
    | inr hn =>
      right
      rw [Int.negOnePow_odd n hn] at this
      push_cast at this
      rw [neg_one_mul] at this
      exact this

theorem T_abs_gt_of_abs_gt {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : |x| > 1) :
  |(T ℝ n).eval x| > 1 := by
  apply lt_abs.mpr
  cases lt_abs.mp hx with
  | inl hx =>
    left
    exact T_gt_of_gt_one hn hx
  | inr hx =>
    have : x < -1 := by linarith
    have := T_gt_of_lt_neg_one hn this
    cases n.even_or_odd with
    | inl hn =>
      left
      rw [Int.negOnePow_even n hn] at this
      push_cast at this
      rw [one_mul] at this
      exact this
    | inr hn =>
      right
      rw [Int.negOnePow_odd n hn] at this
      push_cast at this
      rw [neg_one_mul] at this
      exact this

theorem T_bounded_iff_bounded {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  |x| ≤ 1 ↔ |(T ℝ n).eval x| ≤ 1 := by
  constructor
  · intro hx; exact T_bounded_of_bounded' n hx
  · intro hx; contrapose! hx; exact T_abs_gt_of_abs_gt hn hx

theorem T_eq_cos_of_bounded {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : |y| ≤ 1) (x : ℝ) :
  (T ℝ n).eval x = y ↔ ∃ θ, cos θ = x ∧ cos (n * θ) = y := by
  constructor
  · intro h
    have hx : |x| ≤ 1 := by
      by_contra! hx
      have := T_abs_gt_of_abs_gt hn hx
      rw [h] at this
      linarith
    use arccos x
    constructor
    · exact cos_arccos (neg_le_of_abs_le hx) (le_of_abs_le hx)
    · rw [←h, ←T_real_cos (arccos x), cos_arccos (neg_le_of_abs_le hx) (le_of_abs_le hx)]
  · rintro ⟨θ, hx, hy⟩
    rw [← hx, T_real_cos, hy]

theorem T_eq_zero_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  (T ℝ n).eval x = 0 ↔ ∃ (k : ℤ), x = cos ((2 * k + 1) * π / (2 * n)) := by
  rw [T_eq_cos_of_bounded hn (show |0| ≤ 1 by norm_num)]
  constructor
  · rintro ⟨θ, hx, h0⟩
    obtain ⟨k, hθ⟩ := cos_eq_zero_iff.mp h0
    use k
    rw [←hx]
    congr 1
    linear_combination (norm := (field_simp; ring)) hθ / n
  · rintro ⟨k, hx⟩
    use (2*k+1)*π/(2*n)
    constructor; · rw [hx]
    apply cos_eq_zero_iff.mpr
    use k
    field_simp

/-- `T_roots n` is the set of roots of `T n`. -/
noncomputable def T_roots (n : ℕ) : Finset ℝ :=
  (Finset.Ico 0 n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))

@[simp]
theorem T_roots_card (n : ℕ) : (T_roots n).card = n := by
  unfold T_roots
  rw [Finset.card_image_of_injOn]
  · simp
  intro k₁ hk₁ k₂ hk₂
  dsimp
  by_cases n = 0
  case pos hn => simp [hn] at hk₁
  case neg hn =>
  have hnℝ : (n : ℝ) ≠ 0 := by contrapose! hn; exact Nat.cast_eq_zero.mp hn
  have {k : ℕ} (hk : k ∈ Finset.Ico 0 n) :
    (2 * k + 1) * π / (2 * n) ∈ Set.Icc 0 π := by
    apply Set.mem_Icc.mpr
    constructor
    · positivity
    calc
      (2 * k + 1) * π / (2 * n) ≤ (2 * (n - 1) + 1) * π / (2 * n) := by
        gcongr
        have := @Nat.cast_sub ℝ _ 1 n (by omega)
        push_cast at this
        rw [←this]
        apply Nat.cast_le.mpr
        have := Finset.mem_Ico.mp hk
        omega
      _ ≤ (2 * n) * π / (2 * n) := by gcongr; linarith
      _ ≤ π := by
        rw [mul_div_assoc, mul_div_cancel₀]
        contrapose! hnℝ
        linarith
  intro h
  have : (2 * k₁ + 1) * π / (2 * n) = (2 * k₂ + 1) * π / (2 * n) := by
    apply injOn_cos
    · exact this hk₁
    · exact this hk₂
    exact h
  field_simp at this
  norm_cast at this
  linarith

theorem T_roots_eq {n : ℕ} (hn : n ≠ 0) : (T ℝ n).roots = (T_roots n).val := by
  have hS : ∀ x ∈ T_roots n, (T ℝ n).eval x = 0 := by
    intro x hx
    unfold T_roots at hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, hx⟩ := hx
    apply (T_eq_zero_iff ?_ x).mpr
    · use k
      rw [←hx]
      push_cast; rfl
    contrapose! hn
    exact Int.ofNat_eq_zero.mp hn
  have hcard : (T_roots n).card = (T ℝ n).degree := by
    rw [T_roots_card n, T_degree] <;> simp
  apply roots_of_zeroes_of_card hS hcard

theorem T_eq_one_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  (T ℝ n).eval x = 1 ↔ ∃ (k : ℤ), x = cos (2 * k * π / n) := by
  rw [T_eq_cos_of_bounded hn (show |1| ≤ 1 by norm_num)]
  constructor
  · rintro ⟨θ, hx, h1⟩
    obtain ⟨k, hθ⟩ := (cos_eq_one_iff _).mp h1
    use k
    rw [←hx]
    congr 1
    linear_combination (norm := (field_simp; ring)) hθ.symm / n
  · rintro ⟨k, hx⟩
    use 2*k*π/n
    constructor; · rw [hx]
    apply (cos_eq_one_iff _).mpr
    use k
    field_simp

theorem T_eq_neg_one_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  (T ℝ n).eval x = -1 ↔ ∃ (k : ℤ), x = cos ((2 * k + 1) * π / n) := by
  rw [T_eq_cos_of_bounded hn (show |-1| ≤ 1 by norm_num)]
  constructor
  · rintro ⟨θ, hx, h1⟩
    obtain ⟨k, hθ⟩ := cos_eq_neg_one_iff.mp h1
    use k
    rw [←hx]
    congr 1
    linear_combination (norm := (field_simp; ring)) hθ.symm / n
  · rintro ⟨k, hx⟩
    use (2*k+1)*π/n
    constructor; · rw [hx]
    apply cos_eq_neg_one_iff.mpr
    use k
    field_simp; ring

theorem T_node_eval {n : ℤ} (hn : n ≠ 0) (k : ℤ) :
  (T ℝ n).eval (cos (k * π / n)) = (-1)^k := by
  rw [T_real_cos]
  trans cos (k * π)
  · congr 1; field_simp
  calc cos (k * π) = cos (0 + k * π) := by rw [zero_add]
    _ = (-1)^k * cos 0 := cos_add_int_mul_pi _ _
    _ = (-1)^k := by rw [cos_zero, mul_one]

theorem T_abs_eq_one_iff {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  |(T ℝ n).eval x| = 1 ↔ ∃ (k : ℤ), x = cos (k * π / n) := by
  constructor
  · intro h
    cases (abs_eq (by norm_num)).mp h with
    | inl h =>
      obtain ⟨k, hx⟩ := (T_eq_one_iff hn x).mp h
      use 2 * k
      rw [hx]; congr; push_cast; rfl
    | inr h =>
      obtain ⟨k, hx⟩ := (T_eq_neg_one_iff hn x).mp h
      use 2 * k + 1
      rw [hx]; congr; push_cast; rfl
  · rintro ⟨k, hx⟩
    rw [hx, T_real_cos]
    trans |cos (k * π)|
    · congr 2; field_simp
    exact abs_cos_int_mul_pi _

/-- `T_extrema n` is the set of extremal points of `T n` in [-1, 1]. -/
noncomputable def T_extrema (n : ℤ) : Finset ℝ :=
  (Finset.Icc 0 n.natAbs).image (fun (k : ℕ) => cos (k * π / n.natAbs))

@[simp]
theorem T_extrema_card (n : ℤ) : (T_extrema n).card = n.natAbs + 1 := by
  unfold T_extrema
  rw [Finset.card_image_of_injOn]
  · simp
  intro k₁ hk₁ k₂ hk₂
  dsimp
  push_cast at hk₁ hk₂
  by_cases n = 0
  case pos =>
    have := Set.mem_Icc.mp hk₁
    have := Set.mem_Icc.mp hk₂
    intro _
    omega
  case neg =>
    have {k : ℕ} (hk : k ∈ Set.Icc 0 n.natAbs) :
      k * π / n.natAbs ∈ Set.Icc 0 π := by
      apply Set.mem_Icc.mpr
      constructor
      · positivity
      calc
        k * π / n.natAbs ≤ n.natAbs * π / n.natAbs := by
          gcongr
          exact (Set.mem_Icc.mp hk).2
        _ ≤ π := by
          rw [mul_div_assoc, mul_div_cancel₀]
          positivity
    intro h
    have : k₁ * π / n.natAbs = k₂ * π / n.natAbs := by
      apply injOn_cos
      · exact this hk₁
      · exact this hk₂
      exact h
    field_simp at this
    norm_cast at this

theorem T_extrema_eq_nat {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
  |(T ℝ n).eval x| = 1 ↔ x ∈ T_extrema n := by
  have hn' : (n : ℤ) ≠ 0 := by omega
  constructor
  · intro h
    obtain ⟨k, hx⟩ := (T_abs_eq_one_iff hn' x).mp h
    unfold T_extrema
    apply Finset.mem_image.mpr
    let l := k % (2 * n)
    let r := k / (2 * n)
    have l_nonneg : 0 ≤ l := by exact k.emod_nonneg (by omega)
    have l_lt : l < 2 * n := by exact k.emod_lt_of_pos (by omega)
    have k_eq : k = l + r * (2 * n) := by have := k.mul_ediv_add_emod (2 * n); linarith
    let l' := l.toNat
    have hl' : l' = l := by omega
    by_cases l ≤ n
    case pos hl =>
      use l'
      constructor
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [hx]
      apply cos_eq_cos_iff.mpr
      use r
      left
      field_simp
      rw [k_eq, ← hl', Int.natAbs_cast]
      push_cast
      ring
    case neg =>
      use 2 * n - l'
      constructor
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      rw [hx]
      apply cos_eq_cos_iff.mpr
      use r + 1
      right
      field_simp
      rw [k_eq, ← hl', Nat.cast_sub (by omega)]
      rw [Int.natAbs_cast]
      push_cast
      ring
  · intro h
    unfold T_extrema at h
    obtain ⟨k, hk, hx⟩ := Finset.mem_image.mp h
    apply (T_abs_eq_one_iff hn' x).mpr
    use k
    rw [← hx]
    simp

theorem T_extrema_eq {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  |(T ℝ n).eval x| = 1 ↔ x ∈ T_extrema n := by
  obtain ⟨m, hmn⟩ := n.eq_nat_or_neg
  have hm : m ≠ 0 := by omega
  cases hmn with
  | inl hmn => subst hmn; exact T_extrema_eq_nat hm x
  | inr hmn =>
    subst hmn
    rw [T_neg]
    convert T_extrema_eq_nat hm x using 1
    unfold T_extrema
    simp

theorem U_degree_nat_real (n : ℕ) : (U ℝ n).degree = n := by
  exact U_degree_nat ℝ (by simp) n

theorem U_natDegree_nat_real (n : ℕ) : (U ℝ n).natDegree = n := by
  exact U_natDegree_nat ℝ (by simp) n

theorem U_degree_ne_neg_one_real (n : ℤ) (hn : n ≠ -1) :
  (U ℝ n).degree = ↑((n + 1).natAbs - 1) := by
  exact U_degree_ne_neg_one ℝ (by simp) n hn

theorem U_natDegree_real (n : ℤ) :
  (U ℝ n).natDegree = (n + 1).natAbs - 1 := by
  exact U_natDegree ℝ (by simp) n

theorem U_leadingCoeff_nat_real (n : ℕ) : (U ℝ n).leadingCoeff = 2^n := by
  exact U_leadingCoeff_nat ℝ (by simp) n

theorem U_eq_zero_if (n : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
  (U ℝ n).eval (cos (k * π / (n + 1))) = 0 := by
  have hn1 : (n + 1 : ℝ) ≠ 0 := by norm_cast
  have hpi := Real.pi_ne_zero
  have := U_real_cos (k * π / (n + 1)) n
  push_cast at this
  rw [mul_div_cancel₀ _ hn1, (@sin_eq_zero_iff (k*π)).mpr ⟨k, rfl⟩] at this
  refine (mul_eq_zero_iff_right ?_).mp this
  apply sin_ne_zero_iff.mpr
  intro l
  field_simp
  suffices l * (n + 1) ≠ k by
    contrapose! this
    suffices l * (n + 1) = (k : ℝ) by norm_cast; norm_cast at this
    linear_combination (norm := (field_simp; ring)) this * (n + 1) / π
  by_contra! h
  by_cases l ≤ 0
  case pos hl =>
    have : l * (n + 1) ≤ 0 := by apply Int.mul_nonpos_of_nonpos_of_nonneg hl; omega
    linarith
  case neg hl =>
    have : 1 ≤ l := by linarith
    have : l * (n + 1) ≥ n + 1 := by
      calc l * (n + 1) ≥ 1 * (n + 1) := by gcongr
        _ = (n + 1) := by rw [one_mul]
    linarith

/-- `U_roots n` is the set of roots of `U n`. -/
noncomputable def U_roots (n : ℕ) : Finset ℝ :=
  (Finset.Icc 1 n).image (fun (k : ℕ) => cos (k * π / (n + 1)))

@[simp]
theorem U_roots_card (n : ℕ) : (U_roots n).card = n := by
  unfold U_roots
  rw [Finset.card_image_of_injOn]
  · simp
  intro k₁ hk₁ k₂ hk₂
  dsimp
  have {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    k * π / (n + 1) ∈ Set.Icc 0 π := by
    apply Set.mem_Icc.mpr
    constructor
    · positivity
    calc
      k * π / (n + 1) ≤ n * π / (n + 1) := by
        gcongr
        apply Nat.cast_le.mpr
        exact (Finset.mem_Icc.mp hk).2
      _ ≤ (n + 1) * π / (n + 1) := by gcongr; linarith
      _ ≤ π := by
        rw [mul_div_assoc, mul_div_cancel₀]
        positivity
  intro h
  have : k₁ * π / (n + 1) = k₂ * π / (n + 1) := by
    apply injOn_cos
    · exact this hk₁
    · exact this hk₂
    exact h
  field_simp at this
  norm_cast at this

theorem U_roots_eq (n : ℕ) : (U ℝ n).roots = (U_roots n).val := by
  have hS : ∀ x ∈ U_roots n, (U ℝ n).eval x = 0 := by
    intro x hx
    unfold U_roots at hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, hx⟩ := hx
    replace hk := Finset.mem_Icc.mp hk
    rw [←hx]
    apply U_eq_zero_if n hk.1 hk.2
  have hcard : (U_roots n).card = (U ℝ n).degree := by
    rw [U_roots_card n, U_degree_nat]; simp
  apply roots_of_zeroes_of_card hS hcard

theorem U_eq_zero_iff (n : ℕ) (x : ℝ) :
  (U ℝ n).eval x = 0 ↔ ∃ (k : ℕ), 1 ≤ k ∧ k ≤ n ∧ x = cos (k * π / (n + 1)) := by
  change (U ℝ n).IsRoot x ↔ ∃ (k : ℕ), 1 ≤ k ∧ k ≤ n ∧ x = cos (k * π / (n + 1))
  have : U ℝ n ≠ 0 := by
    by_contra! h
    have : (U ℝ n).degree = n := by apply U_degree_nat; simp
    simp [h] at this
  rw [←(U ℝ n).mem_roots this, U_roots_eq n]
  unfold U_roots
  rw [Finset.mem_val, Finset.mem_image]
  constructor
  · intro ⟨k, hk, hx⟩
    replace hk := Finset.mem_Icc.mp hk
    use k
    exact ⟨hk.1, hk.2, hx.symm⟩
  · intro ⟨k, hk₁, hk₂, hx⟩
    use k
    exact ⟨Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩, hx.symm⟩

end Polynomial.Chebyshev
