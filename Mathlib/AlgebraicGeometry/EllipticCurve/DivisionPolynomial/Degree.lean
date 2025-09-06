/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Division polynomials of Weierstrass curves

This file computes the leading terms of certain polynomials associated to division polynomials of
Weierstrass curves defined in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`.

## Mathematical background

Let `W` be a Weierstrass curve over a commutative ring `R`. By strong induction,
* `preΨₙ` has leading coefficient `n / 2` and degree `(n² - 4) / 2` if `n` is even,
* `preΨₙ` has leading coefficient `n` and degree `(n² - 1) / 2` if `n` is odd,
* `ΨSqₙ` has leading coefficient `n²` and degree `n² - 1`, and
* `Φₙ` has leading coefficient `1` and degree `n²`.

In particular, when `R` is an integral domain of characteristic different from `n`, the univariate
polynomials `preΨₙ`, `ΨSqₙ`, and `Φₙ` all have their expected leading terms.

## Main statements

* `WeierstrassCurve.natDegree_preΨ_le`: the degree bound `d` of `preΨₙ`.
* `WeierstrassCurve.coeff_preΨ`: the `d`-th coefficient of `preΨₙ`.
* `WeierstrassCurve.natDegree_preΨ`: the degree of `preΨₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_preΨ`: the leading coefficient of `preΨₙ` when `n ≠ 0`.
* `WeierstrassCurve.natDegree_ΨSq_le`: the degree bound `d` of `ΨSqₙ`.
* `WeierstrassCurve.coeff_ΨSq`: the `d`-th coefficient of `ΨSqₙ`.
* `WeierstrassCurve.natDegree_ΨSq`: the degree of `ΨSqₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_ΨSq`: the leading coefficient of `ΨSqₙ` when `n ≠ 0`.
* `WeierstrassCurve.natDegree_Φ_le`: the degree bound `d` of `Φₙ`.
* `WeierstrassCurve.coeff_Φ`: the `d`-th coefficient of `Φₙ`.
* `WeierstrassCurve.natDegree_Φ`: the degree of `Φₙ` when `n ≠ 0`.
* `WeierstrassCurve.leadingCoeff_Φ`: the leading coefficient of `Φₙ` when `n ≠ 0`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Ψ₂Sq

lemma natDegree_Ψ₂Sq_le : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [Ψ₂Sq]
  compute_degree

@[simp]
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [Ψ₂Sq]
  compute_degree!

lemma coeff_Ψ₂Sq_ne_zero (h : (4 : R) ≠ 0) : W.Ψ₂Sq.coeff 3 ≠ 0 := by
  rwa [coeff_Ψ₂Sq]

@[simp]
lemma natDegree_Ψ₂Sq (h : (4 : R) ≠ 0) : W.Ψ₂Sq.natDegree = 3 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le <| W.coeff_Ψ₂Sq_ne_zero h

lemma natDegree_Ψ₂Sq_pos (h : (4 : R) ≠ 0) : 0 < W.Ψ₂Sq.natDegree :=
  W.natDegree_Ψ₂Sq h ▸ three_pos

@[simp]
lemma leadingCoeff_Ψ₂Sq (h : (4 : R) ≠ 0) : W.Ψ₂Sq.leadingCoeff = 4 := by
  rw [leadingCoeff, W.natDegree_Ψ₂Sq h, coeff_Ψ₂Sq]

lemma Ψ₂Sq_ne_zero (h : (4 : R) ≠ 0) : W.Ψ₂Sq ≠ 0 :=
  ne_zero_of_natDegree_gt <| W.natDegree_Ψ₂Sq_pos h

end Ψ₂Sq

section Ψ₃

lemma natDegree_Ψ₃_le : W.Ψ₃.natDegree ≤ 4 := by
  rw [Ψ₃]
  compute_degree

@[simp]
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [Ψ₃]
  compute_degree!

lemma coeff_Ψ₃_ne_zero (h : (3 : R) ≠ 0) : W.Ψ₃.coeff 4 ≠ 0 := by
  rwa [coeff_Ψ₃]

@[simp]
lemma natDegree_Ψ₃ (h : (3 : R) ≠ 0) : W.Ψ₃.natDegree = 4 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le <| W.coeff_Ψ₃_ne_zero h

lemma natDegree_Ψ₃_pos (h : (3 : R) ≠ 0) : 0 < W.Ψ₃.natDegree :=
  W.natDegree_Ψ₃ h ▸ four_pos

@[simp]
lemma leadingCoeff_Ψ₃ (h : (3 : R) ≠ 0) : W.Ψ₃.leadingCoeff = 3 := by
  rw [leadingCoeff, W.natDegree_Ψ₃ h, coeff_Ψ₃]

lemma Ψ₃_ne_zero (h : (3 : R) ≠ 0) : W.Ψ₃ ≠ 0 :=
  ne_zero_of_natDegree_gt <| W.natDegree_Ψ₃_pos h

end Ψ₃

section preΨ₄

lemma natDegree_preΨ₄_le : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree

@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!

lemma coeff_preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄.coeff 6 ≠ 0 := by
  rwa [coeff_preΨ₄]

@[simp]
lemma natDegree_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le <| W.coeff_preΨ₄_ne_zero h

lemma natDegree_preΨ₄_pos (h : (2 : R) ≠ 0) : 0 < W.preΨ₄.natDegree := by
  linarith only [W.natDegree_preΨ₄ h]

@[simp]
lemma leadingCoeff_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.leadingCoeff = 2 := by
  rw [leadingCoeff, W.natDegree_preΨ₄ h, coeff_preΨ₄]

lemma preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄ ≠ 0 :=
  ne_zero_of_natDegree_gt <| W.natDegree_preΨ₄_pos h

end preΨ₄

section preΨ'

private def expDegree (n : ℕ) : ℕ :=
  (n ^ 2 - if Even n then 4 else 1) / 2

private lemma expDegree_cast {n : ℕ} (hn : n ≠ 0) :
    2 * (expDegree n : ℤ) = n ^ 2 - if Even n then 4 else 1 := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rcases n with _ | n
    · contradiction
    push_cast [expDegree, show (2 * (n + 1)) ^ 2 = 2 * (2 * n * (n + 2)) + 4 by ring1, even_two_mul,
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1
  · push_cast [expDegree, show (2 * n + 1) ^ 2 = 2 * (2 * n * (n + 1)) + 1 by ring1,
      n.not_even_two_mul_add_one, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos]
    ring1

private lemma expDegree_rec (m : ℕ) :
    (expDegree (2 * (m + 3)) = 2 * expDegree (m + 2) + expDegree (m + 3) + expDegree (m + 5) ∧
    expDegree (2 * (m + 3)) = expDegree (m + 1) + expDegree (m + 3) + 2 * expDegree (m + 4)) ∧
    (expDegree (2 * (m + 2) + 1) =
      expDegree (m + 4) + 3 * expDegree (m + 2) + (if Even m then 2 * 3 else 0) ∧
    expDegree (2 * (m + 2) + 1) =
      expDegree (m + 1) + 3 * expDegree (m + 3) + (if Even m then 0 else 2 * 3)) := by
  push_cast [← @Nat.cast_inj ℤ, ← mul_left_cancel_iff_of_pos (b := (expDegree _ : ℤ)) two_pos,
    mul_add, mul_left_comm (2 : ℤ)]
  repeat rw [expDegree_cast <| by omega]
  push_cast [Nat.even_add_one, ite_not, even_two_mul]
  constructor <;> constructor <;> split_ifs <;> ring1

private def expCoeff (n : ℕ) : ℤ :=
  if Even n then n / 2 else n

private lemma expCoeff_cast (n : ℕ) : (expCoeff n : ℚ) = if Even n then (n / 2 : ℚ) else n := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

private lemma expCoeff_rec (m : ℕ) :
    (expCoeff (2 * (m + 3)) =
      expCoeff (m + 2) ^ 2 * expCoeff (m + 3) * expCoeff (m + 5) -
        expCoeff (m + 1) * expCoeff (m + 3) * expCoeff (m + 4) ^ 2) ∧
    (expCoeff (2 * (m + 2) + 1) =
      expCoeff (m + 4) * expCoeff (m + 2) ^ 3 * (if Even m then 4 ^ 2 else 1) -
        expCoeff (m + 1) * expCoeff (m + 3) ^ 3 * (if Even m then 1 else 4 ^ 2)) := by
  push_cast [← @Int.cast_inj ℚ, expCoeff_cast, even_two_mul, m.not_even_two_mul_add_one,
    Nat.even_add_one, ite_not]
  constructor <;> split_ifs <;> ring1

private lemma natDegree_coeff_preΨ' (n : ℕ) :
    (W.preΨ' n).natDegree ≤ expDegree n ∧ (W.preΨ' n).coeff (expDegree n) = expCoeff n := by
  let dm {m n p q} : _ → _ → (p * q : R[X]).natDegree ≤ m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ → _ → (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let cp {m n p} : _ → (p ^ m : R[X]).coeff (m * n) = _ := coeff_pow_of_natDegree_le
  induction n using normEDSRec with
  | zero => simpa only [preΨ'_zero] using ⟨natDegree_zero.le, Int.cast_zero.symm⟩
  | one => simpa only [preΨ'_one] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃_le, W.coeff_Ψ₃ ▸ Int.cast_three.symm⟩
  | four => simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄_le, W.coeff_preΨ₄ ▸ Int.cast_two.symm⟩
  | even m h₁ h₂ h₃ h₄ h₅ =>
    constructor
    · nth_rw 1 [preΨ'_even, ← max_self <| expDegree _, (expDegree_rec m).1.1, (expDegree_rec m).1.2]
      exact natDegree_sub_le_of_le (dm (dm (dp h₂.1) h₃.1) h₅.1) (dm (dm h₁.1 h₃.1) (dp h₄.1))
    · nth_rw 1 [preΨ'_even, coeff_sub, (expDegree_rec m).1.1, cm (dm (dp h₂.1) h₃.1) h₅.1,
        cm (dp h₂.1) h₃.1, cp h₂.1, h₂.2, h₃.2, h₅.2, (expDegree_rec m).1.2,
        cm (dm h₁.1 h₃.1) (dp h₄.1), cm h₁.1 h₃.1, h₁.2, cp h₄.1, h₃.2, h₄.2, (expCoeff_rec m).1]
      norm_cast
  | odd m h₁ h₂ h₃ h₄ =>
    rw [preΨ'_odd]
    constructor
    · nth_rw 1 [← max_self <| expDegree _, (expDegree_rec m).2.1, (expDegree_rec m).2.2]
      refine natDegree_sub_le_of_le (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_) <;>
        split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]
    · nth_rw 1 [coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)), cm h₄.1 (dp h₂.1),
        h₄.2, cp h₂.1, h₂.2, apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_Ψ₂Sq, coeff_one_zero,
        (expDegree_rec m).2.2, cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
        apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq_le, coeff_one_zero, coeff_Ψ₂Sq, (expCoeff_rec m).2]
      · norm_cast
      all_goals split_ifs <;> simp only [natDegree_one.le, dp W.natDegree_Ψ₂Sq_le]

lemma natDegree_preΨ'_le (n : ℕ) : (W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2 :=
  (W.natDegree_coeff_preΨ' n).left

@[simp]
lemma coeff_preΨ' (n : ℕ) : (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  convert (W.natDegree_coeff_preΨ' n).right using 1
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

lemma coeff_preΨ'_ne_zero {n : ℕ} (h : (n : R) ≠ 0) :
    (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) ≠ 0 := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rw [coeff_preΨ', if_pos <| even_two_mul n, n.mul_div_cancel_left two_pos]
    exact right_ne_zero_of_mul <| by rwa [← Nat.cast_mul]
  · rwa [coeff_preΨ', if_neg n.not_even_two_mul_add_one]

@[simp]
lemma natDegree_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
    (W.preΨ' n).natDegree = (n ^ 2 - if Even n then 4 else 1) / 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ'_le n) <| W.coeff_preΨ'_ne_zero h

lemma natDegree_preΨ'_pos {n : ℕ} (hn : 2 < n) (h : (n : R) ≠ 0) : 0 < (W.preΨ' n).natDegree := by
  simp_rw [W.natDegree_preΨ' h, Nat.div_pos_iff, zero_lt_two, true_and]
  split_ifs <;> exact Nat.AtLeastTwo.prop.trans <| Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) _

@[simp]
lemma leadingCoeff_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
    (W.preΨ' n).leadingCoeff = if Even n then n / 2 else n := by
  rw [leadingCoeff, W.natDegree_preΨ' h, coeff_preΨ']

lemma preΨ'_ne_zero [Nontrivial R] {n : ℕ} (h : (n : R) ≠ 0) : W.preΨ' n ≠ 0 := by
  by_cases hn : 2 < n
  · exact ne_zero_of_natDegree_gt <| W.natDegree_preΨ'_pos hn h
  · rcases n with _ | _ | _ <;> aesop

end preΨ'

section preΨ

lemma natDegree_preΨ_le (n : ℤ) : (W.preΨ n).natDegree ≤
    (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n
  | neg ih => simp_rw [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]

@[simp]
lemma coeff_preΨ (n : ℤ) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n
  | neg ih n =>
    simp_rw [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]
    rcases ih n, n.even_or_odd' with ⟨ih, ⟨n, rfl | rfl⟩⟩ <;>
      push_cast [even_two_mul, Int.not_even_two_mul_add_one, Int.neg_ediv_of_dvd ⟨n, rfl⟩] at * <;>
      rw [ih]

lemma coeff_preΨ_ne_zero {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat, Int.even_coe_nat]
      using W.coeff_preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]
        using ih n <| neg_ne_zero.mp <| by exact_mod_cast h

@[simp]
lemma natDegree_preΨ {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).natDegree = (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ_le n) <| W.coeff_preΨ_ne_zero h

lemma natDegree_preΨ_pos {n : ℤ} (hn : 2 < n.natAbs) (h : (n : R) ≠ 0) :
    0 < (W.preΨ n).natDegree := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat] using W.natDegree_preΨ'_pos hn <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, natDegree_neg]
        using ih n (by rwa [← Int.natAbs_neg]) <| neg_ne_zero.mp <| by exact_mod_cast h

@[simp]
lemma leadingCoeff_preΨ {n : ℤ} (h : (n : R) ≠ 0) :
    (W.preΨ n).leadingCoeff = if Even n then n / 2 else n := by
  rw [leadingCoeff, W.natDegree_preΨ h, coeff_preΨ]

lemma preΨ_ne_zero [Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0) : W.preΨ n ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
        using ih n <| neg_ne_zero.mp <| by exact_mod_cast h

end preΨ

section ΨSq

private lemma natDegree_coeff_ΨSq_ofNat (n : ℕ) :
    (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℤ) := by
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | n
  · simp
  have hd : (n + 1) ^ 2 - 1 = 2 * expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj ℤ, add_sq, expDegree_cast n.succ_ne_zero]
    split_ifs <;> ring1
  have hc : (n + 1 : ℕ) ^ 2 = expCoeff (n + 1) ^ 2 * if Even (n + 1) then 4 else 1 := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast]
    split_ifs <;> ring1
  rw [ΨSq_ofNat, hd]
  constructor
  · refine natDegree_mul_le_of_le (dp h.1) ?_
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · rw [coeff_mul_add_eq_of_natDegree_le (dp h.1), coeff_pow_of_natDegree_le h.1, h.2,
      apply_ite₂ coeff, coeff_Ψ₂Sq, coeff_one_zero, hc]
    · norm_cast
    split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]

lemma natDegree_ΨSq_le (n : ℤ) : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg ih => simp_rw [ΨSq_neg, Int.natAbs_neg, ih]

@[simp]
lemma coeff_ΨSq (n : ℤ) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast (W.natDegree_coeff_ΨSq_ofNat n).right
  | neg ih => rw [ΨSq_neg, Int.natAbs_neg, ← Int.cast_pow, neg_sq, Int.cast_pow, ih]

lemma coeff_ΨSq_ne_zero [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0 := by
  simpa

@[simp]
lemma natDegree_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) <| W.coeff_ΨSq_ne_zero h

lemma natDegree_ΨSq_pos [NoZeroDivisors R] {n : ℤ} (hn : 1 < n.natAbs) (h : (n : R) ≠ 0) :
    0 < (W.ΨSq n).natDegree := by
  simpa [W.natDegree_ΨSq h]

@[simp]
lemma leadingCoeff_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).leadingCoeff = n ^ 2 := by
  rw [leadingCoeff, W.natDegree_ΨSq h, coeff_ΨSq]

lemma ΨSq_ne_zero [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) : W.ΨSq n ≠ 0 := by
  by_cases hn : 1 < n.natAbs
  · exact ne_zero_of_natDegree_gt <| W.natDegree_ΨSq_pos hn h
  · rcases hm : n.natAbs with _ | m
    · push_cast [Int.natAbs_eq_zero.mp hm, ne_self_iff_false] at h
    · rcases Int.natAbs_eq_iff.mp hm with rfl | rfl <;>
        rw [hm, Nat.lt_add_left_iff_pos, Nat.not_lt_eq, Nat.le_zero] at hn <;>
        push_cast [hn, ΨSq_neg, ΨSq_one] <;>
        exact fun h' => h <| C_injective <| by push_cast [hn, C_neg, C_1, h', neg_zero, C_0]; rfl

end ΨSq

section Φ

private lemma natDegree_coeff_Φ_ofNat (n : ℕ) :
    (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  let dm {m n p q} : _ → _ → (p * q : R[X]).natDegree ≤ m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ → _ → (p * q : R[X]).coeff (m + n) = _ := coeff_mul_add_eq_of_natDegree_le
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | _ | n
  iterate 2 simp [natDegree_X_le]
  have hd : (n + 1 + 1) ^ 2 = 1 + 2 * expDegree (n + 2) + if Even (n + 1) then 0 else 3 := by
    push_cast [← @Nat.cast_inj ℤ, expDegree_cast (n + 1).succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hd' : (n + 1 + 1) ^ 2 =
      expDegree (n + 3) + expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj ℤ, ← mul_left_cancel_iff_of_pos (b := (_ ^ 2 : ℤ)) two_pos, mul_add,
      expDegree_cast (n + 2).succ_ne_zero, expDegree_cast n.succ_ne_zero, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hc : (1 : ℤ) = 1 * expCoeff (n + 2) ^ 2 * (if Even (n + 1) then 1 else 4) -
      expCoeff (n + 3) * expCoeff (n + 1) * (if Even (n + 1) then 4 else 1) := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  rw [Nat.cast_add, Nat.cast_one, Φ_ofNat]
  constructor
  · nth_rw 1 [← max_self <| (_ + _) ^ 2, hd, hd']
    refine natDegree_sub_le_of_le (dm (dm natDegree_X_le (dp h.1)) ?_) (dm (dm h.1 h.1) ?_) <;>
      split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]
  · nth_rw 1 [coeff_sub, hd, hd', cm (dm natDegree_X_le (dp h.1)), cm natDegree_X_le (dp h.1),
      coeff_X_one, coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq,
      cm (dm h.1 h.1), cm h.1 h.1, h.2, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq]
    conv_rhs => rw [← Int.cast_one, hc]
    · norm_cast
    all_goals split_ifs <;> simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]

lemma natDegree_Φ_le (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp_rw [Φ_neg, Int.natAbs_neg, ih]

@[simp]
lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => rw [Φ_neg, Int.natAbs_neg, ih]

lemma coeff_Φ_ne_zero [Nontrivial R] (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) ≠ 0 :=
  W.coeff_Φ n ▸ one_ne_zero

@[simp]
lemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n

lemma natDegree_Φ_pos [Nontrivial R] {n : ℤ} (hn : n ≠ 0) : 0 < (W.Φ n).natDegree := by
  simpa [sq_pos_iff]

@[simp]
lemma leadingCoeff_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_Φ, coeff_Φ]

lemma Φ_ne_zero [Nontrivial R] (n : ℤ) : W.Φ n ≠ 0 := by
  by_cases hn : n = 0
  · simpa only [hn, Φ_zero] using one_ne_zero
  · exact ne_zero_of_natDegree_gt <| W.natDegree_Φ_pos hn

end Φ

end WeierstrassCurve
