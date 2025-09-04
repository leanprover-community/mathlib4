/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Mitchell Lee, Yuval Filmus
-/
import Mathlib.RingTheory.Polynomial.Chebyshev.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Rify

/-!
# Chebyshev polynomials

## Main statements

* Trigonometric identities satisfied by Chebyshev polynomials:
  `Polynomial.Chebyshev.T_cos`, `Polynomial.Chebyshev.U_cos`
* T_n(x) ∈ [-1, 1] iff x ∈ [-1, 1]
* Zeroes of T and U [COMPLETE!]
* Extrema of T

## TODO

* Prove orthonormality with respect to appropriate inner product.
* Prove minimax properties of Chebyshev polynomials.
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

theorem roots_of_zeroes_of_card'
  {R : Type _} [CommRing R] [IsDomain R] {p : Polynomial R} {S : Finset R}
  (hS : ∀ x ∈ S, p.eval x = 0) (hcard : S.card = p.degree) (x : R) :
  p.eval x = 0 ↔ x ∈ S := by
  change p.IsRoot x ↔ x ∈ S
  have hp : p ≠ 0 := by contrapose! hcard; simp [hcard]
  rw [←p.mem_roots hp]
  have h := roots_of_zeroes_of_card hS hcard
  simp [h]

end Polynomial

namespace Polynomial.Chebyshev

open Polynomial
open Real

theorem T_cos (n : ℤ) (θ : ℝ) : (T ℝ n).eval (cos θ) = cos (n * θ) := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    rw [T_add_two, eval_sub, eval_mul, eval_mul, eval_ofNat, eval_X, ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [Real.cos_add_cos, mul_assoc, mul_comm θ.cos, ←mul_assoc]
    push_cast; congr 3 <;> ring
  | neg n ih => simp [T_neg, ih]

theorem T_cosh (n : ℤ) (θ : ℝ) : (T ℝ n).eval (cosh θ) = cosh (n * θ) := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    rw [T_add_two, eval_sub, eval_mul, eval_mul, eval_ofNat, eval_X, ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    trans cosh ((n + 1) * θ + θ) + cosh ((n + 1) * θ - θ)
    · rw [cosh_add, cosh_sub]; push_cast; ring
    · congr <;> (push_cast; ring)
  | neg n ih => simp [T_neg, ih]

theorem T_bounded_of_bounded (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
  (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc] at hx
  rw [←cos_arccos hx.1 hx.2, T_cos]
  apply cos_mem_Icc

theorem T_bounded_of_bounded' (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
  |(T ℝ n).eval x| ≤ 1 := by
  apply abs_le.mpr
  rw [←Set.mem_Icc]
  apply T_bounded_of_bounded n
  rw [Set.mem_Icc]
  exact abs_le.mp hx

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
  rw [←cosh_arccosh hx, T_cosh]
  apply one_le_cosh

theorem T_gt_of_gt_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x > 1) :
  (T ℝ n).eval x > 1 := by
  rw [←cosh_arccosh (le_of_lt hx), T_cosh]
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
    · rw [←h, ←T_cos n (arccos x), cos_arccos (neg_le_of_abs_le hx) (le_of_abs_le hx)]
  · rintro ⟨θ, hx, hy⟩
    rw [← hx, T_cos n, hy]

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
    field_simp; ring

noncomputable def T_zeroes {n : ℕ} (hn : n ≠ 0) : Finset ℝ := Finset.map
  {
    toFun (k : Finset.Icc 0 (n - 1)) := cos ((2 * k + 1) * π / (2 * n))
    inj' k₁ k₂ := by
      have hk₁ := Finset.mem_Icc.mp k₁.property
      have hk₂ := Finset.mem_Icc.mp k₂.property
      intro h
      have : (2 * k₁ + 1) * π / (2 * n) = (2 * k₂ + 1) * π / (2 * n) := by
        apply injOn_cos
        · apply Set.mem_Icc.mpr
          constructor
          · positivity
          calc (2 * k₁ + 1) * π / (2 * n) ≤ (2 * (n - 1) + 1) * π / (2 * n) := by
            { gcongr
              have := hk₁.2; zify at this
              rw [Nat.cast_sub (by omega)] at this
              sorry }
            _ ≤ (2 * n) * π / (2 * n) := by gcongr; linarith
            _ = π := by field_simp
        · apply Set.mem_Icc.mpr
          constructor
          · positivity
          calc (2 * k₂ + 1) * π / (2 * n) ≤ (2 * (n - 1) + 1) * π / (2 * n) := by
            { gcongr
              have := hk₂.2; zify at this
              rw [Nat.cast_sub (by omega)] at this
              sorry }
            _ ≤ (2 * n) * π / (2 * n) := by gcongr; linarith
            _ = π := by field_simp
        exact h
      have : (2 * k₁.val + 1 : ℝ) = (2 * k₂.val + 1 : ℝ) := by
        linear_combination (norm := (field_simp; ring)) this * ((2 * n) / π)
      aesop
  }
  Finset.univ

@[simp]
theorem T_zeroes_card {n : ℕ} (hn : n ≠ 0) : (T_zeroes hn).card = n := by
  unfold T_zeroes
  simp; omega

theorem T_roots {n : ℕ} (hn : n ≠ 0) : (T ℝ n).roots = (T_zeroes hn).val := by
  have hS : ∀ x ∈ T_zeroes hn, (T ℝ n).eval x = 0 := by
    intro x hx
    unfold T_zeroes at hx
    simp [Finset.mem_map] at hx
    obtain ⟨k, hk, hx⟩ := hx
    have hn' : (n : ℤ) ≠ 0 := by contrapose! hn; norm_cast at hn
    apply (T_eq_zero_iff hn' x).mpr
    use k
    rw [←hx]
    push_cast; rfl
  have hcard : (T_zeroes hn).card = (T ℝ n).degree := by
    rw [T_zeroes_card hn, T_degree] <;> simp
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
    field_simp; ring

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
    obtain ⟨l, hl⟩ := Int.even_or_odd' k
    apply (abs_eq (by norm_num)).mpr
    cases hl with
    | inl hk => left; apply (T_eq_one_iff hn x).mpr; use l; rw [hx, hk]; push_cast; rfl
    | inr hk => right; apply (T_eq_neg_one_iff hn x).mpr; use l; rw [hx, hk]; push_cast; rfl

theorem U_cos (n : ℤ) (θ : ℝ) : (U ℝ n).eval (cos θ) * sin θ = sin ((n+1) * θ) := by
  induction n using Chebyshev.induct with
  | zero => simp
  | one => norm_num; rw [sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    norm_num
    rw [sub_mul]
    trans 2 * θ.cos * ((U ℝ (n+1)).eval θ.cos * θ.sin) - (U ℝ n).eval θ.cos * θ.sin
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [Real.sin_add_sin, mul_assoc, mul_comm θ.cos, ←mul_assoc]
    push_cast; congr 3 <;> ring
  | neg_add_one n ih1 ih2 =>
    rw [U_sub_one]
    norm_num
    rw [sub_mul]
    trans 2 * θ.cos * ((U ℝ (-n)).eval θ.cos * θ.sin) - (U ℝ (-n+1)).eval θ.cos * θ.sin
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [←sin_neg, ←cos_neg, sin_add_sin, mul_assoc, mul_comm (-θ).cos, ←mul_assoc]
    push_cast; congr 3 <;> ring

theorem U_cosh (n : ℤ) (θ : ℝ) : (U ℝ n).eval (cosh θ) * sinh θ = sinh ((n+1) * θ) := by
  induction n using Chebyshev.induct with
  | zero => simp
  | one => norm_num; rw [sinh_two_mul]; ring
  | add_two n ih1 ih2 =>
    norm_num
    rw [sub_mul]
    trans 2 * θ.cosh * ((U ℝ (n+1)).eval θ.cosh * θ.sinh) - (U ℝ n).eval θ.cosh * θ.sinh
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    trans sinh ((n + 2) * θ + θ) + sinh ((n + 2) * θ - θ)
    · rw [sinh_add, sinh_sub]; push_cast; ring_nf
    · congr <;> (push_cast; ring)
  | neg_add_one n ih1 ih2 =>
    rw [U_sub_one]
    norm_num
    rw [sub_mul]
    trans 2 * θ.cosh * ((U ℝ (-n)).eval θ.cosh * θ.sinh) - (U ℝ (-n+1)).eval θ.cosh * θ.sinh
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [←sinh_neg]
    trans sinh ((-n + 1) * θ - θ) + sinh ((-n + 1) * θ + θ)
    · rw [sinh_add, sinh_sub]; push_cast; ring
    · congr <;> (push_cast; ring)

theorem U_eq_zero_if (n : ℕ) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
  (U ℝ n).eval (cos (k * π / (n + 1))) = 0 := by
  have hn1 : (n + 1 : ℝ) ≠ 0 := by norm_cast
  have hpi := Real.pi_ne_zero
  have := U_cos n (k * π / (n + 1))
  push_cast at this
  rw [mul_div_cancel₀ _ hn1, (@sin_eq_zero_iff (k*π)).mpr ⟨k, rfl⟩] at this
  refine (mul_eq_zero_iff_right ?_).mp this
  apply sin_ne_zero_iff.mpr
  intro l
  field_simp
  suffices l * (n + 1) ≠ k by
    contrapose! this
    suffices l * (n + 1) = (k : ℝ) by norm_cast; norm_cast at this
    linear_combination (norm := (field_simp; ring)) this / π
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

noncomputable def U_zeroes (n : ℕ) : Finset ℝ := Finset.map
  {
    toFun (k : Finset.Icc 1 n) := cos (k * π / (n + 1))
    inj' k₁ k₂ := by
      have hk₁ := Finset.mem_Icc.mp k₁.property
      have hk₂ := Finset.mem_Icc.mp k₂.property
      intro h
      have : k₁ * π / (n + 1) = (k₂ * π) / (n + 1) := by
        apply injOn_cos
        · apply Set.mem_Icc.mpr
          constructor
          · positivity
          calc k₁ * π / (n + 1) ≤ n * π / (n + 1) := by gcongr; exact hk₁.2
            _ ≤ (n + 1) * π / (n + 1) := by gcongr; linarith
            _ = π := by field_simp
        · apply Set.mem_Icc.mpr
          constructor
          · positivity
          calc k₂ * π / (n + 1) ≤ n * π / (n + 1) := by gcongr; exact hk₂.2
            _ ≤ (n + 1) * π / (n + 1) := by gcongr; linarith
            _ = π := by field_simp
        exact h
      have : (k₁.val : ℝ) = (k₂.val : ℝ) := by
        linear_combination (norm := (field_simp; ring)) this * ((n + 1) / π)
      aesop
  }
  Finset.univ

@[simp]
theorem U_zeroes_card (n : ℕ) : (U_zeroes n).card = n := by
  unfold U_zeroes
  simp

theorem U_roots (n : ℕ) : (U ℝ n).roots = (U_zeroes n).val := by
  have hS : ∀ x ∈ U_zeroes n, (U ℝ n).eval x = 0 := by
    intro x hx
    unfold U_zeroes at hx
    simp [Finset.mem_map] at hx
    obtain ⟨k, hk, hx⟩ := hx
    rw [←hx]
    apply U_eq_zero_if n hk.1 hk.2
  have hcard : (U_zeroes n).card = (U ℝ n).degree := by
    rw [U_zeroes_card n, U_degree_nat]; simp
  apply roots_of_zeroes_of_card hS hcard

theorem U_eq_zero_iff (n : ℕ) (x : ℝ) :
  (U ℝ n).eval x = 0 ↔ ∃ (k : ℕ), 1 ≤ k ∧ k ≤ n ∧ x = cos (k * π / (n + 1)) := by
  change (U ℝ n).IsRoot x ↔ ∃ (k : ℕ), 1 ≤ k ∧ k ≤ n ∧ x = cos (k * π / (n + 1))
  have : U ℝ n ≠ 0 := by
    by_contra! h
    have : (U ℝ n).degree = n := by apply U_degree_nat; simp
    simp [h] at this
  rw [←(U ℝ n).mem_roots this, U_roots n]
  unfold U_zeroes
  rw [Finset.mem_val, Finset.mem_map]
  simp only [Finset.univ_eq_attach, Finset.mem_attach, Function.Embedding.coeFn_mk, true_and,
    Subtype.exists, Finset.mem_Icc, exists_prop]
  constructor
  · intro ⟨k, hk, hx⟩
    use k
    exact ⟨hk.1, hk.2, hx.symm⟩
  · intro ⟨k, hk₁, hk₂, hx⟩
    use k
    exact ⟨⟨hk₁, hk₂⟩, hx.symm⟩

end Polynomial.Chebyshev
