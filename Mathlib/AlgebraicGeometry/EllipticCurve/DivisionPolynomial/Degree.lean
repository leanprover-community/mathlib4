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
Weierstrass curves defined in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
In particular, they can be computed by strong induction to be:
 * $\tilde{\Psi}_n = \tfrac{n}{2}X^{\tfrac{n^2 - 4}{2}} + \dots$ if $n$ is even,
 * $\tilde{\Psi}_n = nX^{\tfrac{n^2 - 1}{2}} + \dots$ if $n$ is odd,
 * $\Psi_n^{[2]} = n^2X^{n^2 - 1} + \dots$, and
 * $\Phi_n = X^{n^2} + \dots$.

## Main statements

 * `WeierstrassCurve.natDegree_preΨ`: the degree of $\tilde{\Psi}_n$.
 * `WeierstrassCurve.coeff_preΨ`: the leading coefficient of $\tilde{\Psi}_n$.
 * `WeierstrassCurve.natDegree_ΨSq`: the degree of $\Psi_n^{[2]}$.
 * `WeierstrassCurve.coeff_ΨSq`: the leading coefficient of $\Psi_n^{[2]}$.
 * `WeierstrassCurve.natDegree_Φ`: the degree of $\Phi_n$.
 * `WeierstrassCurve.coeff_Φ`: the leading coefficient of $\Phi_n$.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, division polynomial, torsion point
-/

open Polynomial PolynomialPolynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma natDegree_Ψ₂Sq : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [Ψ₂Sq]
  compute_degree

@[simp]
lemma coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4 := by
  rw [Ψ₂Sq]
  compute_degree!

lemma natDegree_Ψ₃ : W.Ψ₃.natDegree ≤ 4 := by
  rw [Ψ₃]
  compute_degree

@[simp]
lemma coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3 := by
  rw [Ψ₃]
  compute_degree!

lemma natDegree_preΨ₄ : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree

@[simp]
lemma coeff_preΨ₄ : W.preΨ₄.coeff 6 = 2 := by
  rw [preΨ₄]
  compute_degree!

private def expDegree (n : ℕ) : ℕ :=
  (n ^ 2 - if Even n then 4 else 1) / 2

private lemma expDegree_cast {n : ℕ} (hn : n ≠ 0) :
    2 * (expDegree n : ℤ) = n ^ 2 - if Even n then 4 else 1 := by
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩
  · rcases n with _ | n; contradiction
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
  let cm {m n p q} : _ → _ → (p * q : R[X]).coeff (m + n) = _ := coeff_mul_of_natDegree_le
  let cp {m n p} : _ → (p ^ m : R[X]).coeff (m * n) = _ := coeff_pow_of_natDegree_le
  induction n using normEDSRec with
  | zero => simpa only [preΨ'_zero] using ⟨by rfl, Int.cast_zero.symm⟩
  | one => simpa only [preΨ'_one] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | two => simpa only [preΨ'_two] using ⟨natDegree_one.le, coeff_one_zero.trans Int.cast_one.symm⟩
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃, W.coeff_Ψ₃ ▸ (Int.cast_ofNat 3).symm⟩
  | four =>
    simpa only [preΨ'_four] using ⟨W.natDegree_preΨ₄, W.coeff_preΨ₄ ▸ (Int.cast_ofNat 2).symm⟩
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
      refine natDegree_sub_le_of_le (dm (dm h₄.1 (dp h₂.1)) ?_) (dm (dm h₁.1 (dp h₃.1)) ?_)
      all_goals split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, dp W.natDegree_Ψ₂Sq]
    · nth_rw 1 [coeff_sub, (expDegree_rec m).2.1, cm (dm h₄.1 (dp h₂.1)), cm h₄.1 (dp h₂.1),
        h₄.2, cp h₂.1, h₂.2, apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq, coeff_Ψ₂Sq, coeff_one_zero,
        (expDegree_rec m).2.2, cm (dm h₁.1 (dp h₃.1)), cm h₁.1 (dp h₃.1), h₁.2, cp h₃.1, h₃.2,
        apply_ite₂ coeff, cp W.natDegree_Ψ₂Sq, coeff_one_zero, coeff_Ψ₂Sq, (expCoeff_rec m).2]
      · norm_cast
      all_goals split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, dp W.natDegree_Ψ₂Sq]

lemma natDegree_preΨ' (n : ℕ) : (W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2 :=
  (W.natDegree_coeff_preΨ' n).left

lemma coeff_preΨ' (n : ℕ) : (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  convert (W.natDegree_coeff_preΨ' n).right using 1
  rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;> simp [expCoeff, n.not_even_two_mul_add_one]

lemma natDegree_preΨ (n : ℤ) : (W.preΨ n).natDegree ≤
    (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ' n
  | neg => simpa only [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg]

lemma coeff_preΨ (n : ℤ) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) =
    if Even n then n / 2 else n := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.coeff_preΨ' n
  | neg n hn =>
    simp only [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]
    rcases n.even_or_odd' with ⟨n, rfl | rfl⟩ <;>
      push_cast [even_two_mul, Int.not_even_two_mul_add_one, Int.neg_ediv_of_dvd ⟨n, rfl⟩] at * <;>
      rw [hn]

private lemma natDegree_coeff_ΨSq_ofNat (n : ℕ) :
    (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℤ) := by
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | n; simp
  have hd : (n + 1) ^ 2 - 1 = 2 * expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj ℤ, add_sq, expDegree_cast (by omega : n + 1 ≠ 0)]
    split_ifs <;> ring1
  have hc : (n + 1) ^ 2 = expCoeff (n + 1) ^ 2 * if Even (n + 1) then 4 else 1 := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast]
    split_ifs <;> ring1
  rw [ΨSq_ofNat, hd]
  constructor
  · refine natDegree_mul_le_of_le (dp h.1) ?_
    split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq]
  · erw [coeff_mul_of_natDegree_le (dp h.1), coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff,
      coeff_Ψ₂Sq, coeff_one_zero, hc]
    norm_cast
    split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq]

lemma natDegree_ΨSq (n : ℤ) : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg n => rwa [ΨSq_neg, Int.natAbs_neg]

lemma coeff_ΨSq (n : ℤ) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast (W.natDegree_coeff_ΨSq_ofNat n).right
  | neg => rwa [ΨSq_neg, Int.natAbs_neg, ← Int.cast_pow, neg_sq, Int.cast_pow]

private lemma natDegree_coeff_Φ_ofNat (n : ℕ) :
    (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  let dm {m n p q} : _ → _ → (p * q : R[X]).natDegree ≤ m + n := natDegree_mul_le_of_le
  let dp {m n p} : _ → (p ^ n : R[X]).natDegree ≤ n * m := natDegree_pow_le_of_le n
  let cm {m n p q} : _ → _ → (p * q : R[X]).coeff (m + n) = _ := coeff_mul_of_natDegree_le
  let h {n} := W.natDegree_coeff_preΨ' n
  rcases n with _ | _ | n; simp; simp [natDegree_X_le]
  have hd : (n + 1 + 1) ^ 2 = 1 + 2 * expDegree (n + 2) + if Even (n + 1) then 0 else 3 := by
    push_cast [← @Nat.cast_inj ℤ, expDegree_cast (by omega : n + 2 ≠ 0), Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hd' : (n + 1 + 1) ^ 2 =
      expDegree (n + 3) + expDegree (n + 1) + if Even (n + 1) then 3 else 0 := by
    push_cast [← @Nat.cast_inj ℤ, ← mul_left_cancel_iff_of_pos (b := (_ ^ 2 : ℤ)) two_pos, mul_add,
      expDegree_cast (by omega : n + 3 ≠ 0), expDegree_cast (by omega : n + 1 ≠ 0),
      Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  have hc : (1 : ℤ) = 1 * expCoeff (n + 2) ^ 2 * (if Even (n + 1) then 1 else 4) -
      expCoeff (n + 3) * expCoeff (n + 1) * (if Even (n + 1) then 4 else 1) := by
    push_cast [← @Int.cast_inj ℚ, expCoeff_cast, Nat.even_add_one, ite_not]
    split_ifs <;> ring1
  erw [Φ_ofNat]
  constructor
  · nth_rw 1 [← max_self <| (_ + _) ^ 2, hd, hd']
    refine natDegree_sub_le_of_le (dm (dm natDegree_X_le (dp h.1)) ?_) (dm (dm h.1 h.1) ?_)
    all_goals split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq]
  · nth_rw 1 [coeff_sub, hd, hd', cm (dm natDegree_X_le (dp h.1)), cm natDegree_X_le (dp h.1),
      coeff_X_one, coeff_pow_of_natDegree_le h.1, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq,
      cm (dm h.1 h.1), cm h.1 h.1, h.2, h.2, apply_ite₂ coeff, coeff_one_zero, coeff_Ψ₂Sq]
    conv_rhs => rw [← Int.cast_one, hc]
    · norm_cast
    all_goals split_ifs <;> simp only [apply_ite natDegree, natDegree_one.le, W.natDegree_Ψ₂Sq]

lemma natDegree_Φ (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg n => rwa [Φ_neg, Int.natAbs_neg]

lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg n => rwa [Φ_neg, Int.natAbs_neg]

end WeierstrassCurve
