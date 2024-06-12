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

section

variable {a b c d e f : R[X]} {da db dc dd de df n : ℕ}
  (ha : a.natDegree ≤ da) (hb : b.natDegree ≤ db) (hc : c.natDegree ≤ dc)
  (hd : d.natDegree ≤ dd) (he : e.natDegree ≤ de) (hf : f.natDegree ≤ df)

private lemma natDegree_odd (habc : n = da + 3 * db + 2 * dc) (hdef : n = dd + 3 * de + 2 * df) :
    (a * b ^ 3 * c ^ 2 - d * e ^ 3 * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le ha <| natDegree_pow_le_of_le 3 hb) <|
      natDegree_pow_le_of_le 2 hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd <| natDegree_pow_le_of_le 3 he) <|
      natDegree_pow_le_of_le 2 hf

private lemma coeff_odd (habc : n = da + 3 * db + 2 * dc) (hdef : n = dd + 3 * de + 2 * df) :
    (a * b ^ 3 * c ^ 2 - d * e ^ 3 * f ^ 2).coeff n = a.coeff da * b.coeff db ^ 3 * c.coeff dc ^ 2 -
      d.coeff dd * e.coeff de ^ 3 * f.coeff df ^ 2 := by
  rw [coeff_sub, habc, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le ha <| natDegree_pow_le_of_le 3 hb) <| natDegree_pow_le_of_le 2 hc,
    coeff_pow_of_natDegree_le hc, coeff_mul_of_natDegree_le ha <| natDegree_pow_le_of_le 3 hb,
    coeff_pow_of_natDegree_le hb, ← habc, hdef, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le hd <| natDegree_pow_le_of_le 3 he) <| natDegree_pow_le_of_le 2 hf,
    coeff_mul_of_natDegree_le hd <| natDegree_pow_le_of_le 3 he, coeff_pow_of_natDegree_le he,
    coeff_pow_of_natDegree_le hf]

private lemma natDegree_even (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).natDegree ≤ n := by
  nth_rw 1 [← max_self n, habc, hdef]
  convert natDegree_sub_le_of_le .. using 1
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc
  · exact natDegree_mul_le_of_le (natDegree_mul_le_of_le hd he) <| natDegree_pow_le_of_le 2 hf

private lemma coeff_even (habc : n = 2 * da + db + dc) (hdef : n = dd + de + 2 * df) :
    (a ^ 2 * b * c - d * e * f ^ 2).coeff n =
      a.coeff da ^ 2 * b.coeff db * c.coeff dc - d.coeff dd * e.coeff de * f.coeff df ^ 2 := by
  rw [coeff_sub, habc, coeff_mul_of_natDegree_le
      (natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 ha) hb) hc,
    coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 ha) hb, coeff_pow_of_natDegree_le ha,
    ← habc, hdef, coeff_mul_of_natDegree_le (natDegree_mul_le_of_le hd he) <|
      natDegree_pow_le_of_le 2 hf, coeff_mul_of_natDegree_le hd he, coeff_pow_of_natDegree_le hf]

end

private def expectedDegree (n : ℕ) : ℕ := (n ^ 2 - if Even n then 4 else 1) / 2
private def expectedCoeff (n : ℕ) : ℤ := if Even n then n / 2 else n

private lemma two_mul_expectedDegree {n : ℕ} (hn : n ≠ 0 := by omega) :
    2 * (expectedDegree n : ℤ) = n ^ 2 - if Even n then 4 else 1 := by
  rw [expectedDegree]
  obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
  · simp_rw [if_pos (even_two_mul _), Int.ofNat_ediv]
    rw [Nat.cast_sub, Nat.cast_two, Nat.cast_pow, Int.mul_ediv_cancel', Nat.cast_ofNat]
    · apply Int.dvd_sub ⟨2 * k ^ 2, _⟩ ⟨2, rfl⟩; rw [Nat.cast_mul]; ring
    · rw [mul_pow]; exact Nat.le_mul_of_pos_right _
        (Nat.pow_pos <| Nat.pos_of_ne_zero <| Nat.ne_zero_of_mul_ne_zero_right hn)
  · simp_rw [if_neg k.not_even_two_mul_add_one, Int.ofNat_ediv, Nat.cast_two]
    rw [Nat.cast_sub, Int.mul_ediv_cancel', Nat.cast_pow, Nat.cast_one]
    · use 2 * (k ^ 2 + k); push_cast; ring
    · rw [add_sq]; omega

private lemma expectedCoeff_eq (n : ℕ) :
    (expectedCoeff n : ℚ) = if Even n then (n / 2 : ℚ) else n := by
  rw [expectedCoeff]; split_ifs with hn
  exacts [Nat.cast_div hn.two_dvd two_ne_zero, rfl]

-- these probably can be inlined ...
private lemma natDegree_preΨ'_zero : (W.preΨ' 0).natDegree = expectedDegree 0 := by
  rw [preΨ'_zero]; rfl

private lemma coeff_preΨ'_zero : (W.preΨ' 0).coeff (expectedDegree 0) = expectedCoeff 0 := by
  rw [preΨ'_zero, coeff_zero]; exact Int.cast_zero.symm

private lemma natDegree_preΨ'_one : (W.preΨ' 1).natDegree = expectedDegree 1 := by
  rw [preΨ'_one, natDegree_one]; rfl

private lemma coeff_preΨ'_one : (W.preΨ' 1).coeff (expectedDegree 1) = expectedCoeff 1 := by
  rw [preΨ'_one]; exact coeff_one_zero.trans Int.cast_one.symm

private lemma natDegree_preΨ'_two : (W.preΨ' 2).natDegree = expectedDegree 2 := by
  rw [preΨ'_two, natDegree_one]; rfl

private lemma coeff_preΨ'_two : (W.preΨ' 2).coeff (expectedDegree 2) = expectedCoeff 2 := by
  rw [preΨ'_two]; exact coeff_one_zero.trans Int.cast_one.symm

private lemma natDegree_preΨ'_three : (W.preΨ' 3).natDegree ≤ expectedDegree 3 := by
  rw [preΨ'_three]; apply natDegree_Ψ₃

private lemma coeff_preΨ'_three : (W.preΨ' 3).coeff (expectedDegree 3) = expectedCoeff 3 := by
  rw [preΨ'_three]; exact W.coeff_Ψ₃.trans (Int.cast_ofNat _).symm

private lemma natDegree_preΨ'_four : (W.preΨ' 4).natDegree ≤ expectedDegree 4 := by
  rw [preΨ'_four]; apply natDegree_preΨ₄

private lemma coeff_preΨ'_four : (W.preΨ' 4).coeff (expectedDegree 4) = expectedCoeff 4 := by
  rw [preΨ'_four]; exact W.coeff_preΨ₄.trans (Int.cast_ofNat _).symm

private lemma expectedDegree_rec (m : ℕ) :
    ((expectedDegree (2 * (m + 2) + 1) =
      expectedDegree (m + 4) + 3 * expectedDegree (m + 2) + 2 * if Even m then 3 else 0) ∧
    expectedDegree (2 * (m + 2) + 1) =
      expectedDegree (m + 1) + 3 * expectedDegree (m + 3) + 2 * if Even m then 0 else 3) ∧
    (expectedDegree (2 * (m + 3)) =
      2 * expectedDegree (m + 2) + expectedDegree (m + 3) + expectedDegree (m + 5)) ∧
    expectedDegree (2 * (m + 3)) =
      expectedDegree (m + 1) + expectedDegree (m + 3) + 2 * expectedDegree (m + 4) := by
  simp_rw [← Nat.cast_inj (R := ℤ),
    ← mul_left_cancel_iff_of_pos (b := (expectedDegree _ : ℤ)) two_pos]
  push_cast
  simp_rw [left_distrib (R := ℤ), mul_left_comm (2 : ℤ)]
  rw [two_mul_expectedDegree, two_mul_expectedDegree, two_mul_expectedDegree,
    two_mul_expectedDegree, two_mul_expectedDegree, two_mul_expectedDegree, two_mul_expectedDegree]
    -- iterate/repeat malfunctioning
  simp_rw [if_neg (Nat.not_even_two_mul_add_one _), if_pos (even_two_mul _), Nat.even_add,
    Nat.not_even_one, even_two, show ¬ Even 3 by decide, show Even 4 by decide,
    show ¬ Even 5 by decide, iff_false, iff_true]
  push_cast; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> split_ifs <;> ring

private lemma expectedCoeff_rec (m : ℕ) :
    (expectedCoeff (2 * (m + 2) + 1) =
      expectedCoeff (m + 4) * expectedCoeff (m + 2) ^ 3 * (if Even m then 4 else 1) ^ 2 -
      expectedCoeff (m + 1) * expectedCoeff (m + 3) ^ 3 * (if Even m then 1 else 4) ^ 2) ∧
    expectedCoeff (2 * (m + 3)) =
      expectedCoeff (m + 2) ^ 2 * expectedCoeff (m + 3) * expectedCoeff (m + 5) -
      expectedCoeff (m + 1) * expectedCoeff (m + 3) * expectedCoeff (m + 4) ^ 2 := by
  sorry

private lemma natDegree_ite_le (P : Prop) [Decidable P] :
    ((if P then W.Ψ₂Sq else 1).natDegree ≤ if P then 3 else 0) ∧
      (if P then 1 else W.Ψ₂Sq).natDegree ≤ if P then 0 else 3 := by
  rw [apply_ite natDegree]; split_ifs
  on_goal 1 => rw [and_comm]
  all_goals exact ⟨natDegree_one.le, W.natDegree_Ψ₂Sq⟩

private lemma natDegree_coeff_preΨ' (n : ℕ) :
    (W.preΨ' n).natDegree ≤ expectedDegree n ∧
      (W.preΨ' n).coeff (expectedDegree n) = expectedCoeff n := by
  induction n using normEDSRec with
  | zero => exact ⟨W.natDegree_preΨ'_zero.le, W.coeff_preΨ'_zero⟩
  | one => exact ⟨W.natDegree_preΨ'_one.le, W.coeff_preΨ'_one⟩
  | two => exact ⟨W.natDegree_preΨ'_two.le, W.coeff_preΨ'_two⟩
  | three => exact ⟨W.natDegree_preΨ'_three, W.coeff_preΨ'_three⟩
  | four => exact ⟨W.natDegree_preΨ'_four, W.coeff_preΨ'_four⟩
  | even m h₁ h₂ h₃ h₄ h₅ =>
    rw [preΨ', preNormEDS'_even]
    have h := (expectedDegree_rec m).2
    refine ⟨natDegree_even h₂.1 h₃.1 h₅.1 h₁.1 h₃.1 h₄.1 h.1 h.2,
      (coeff_even h₂.1 h₃.1 h₅.1 h₁.1 h₃.1 h₄.1 h.1 h.2).trans ?_⟩
    rw [h₁.2, h₂.2, h₃.2, h₄.2, h₅.2, (expectedCoeff_rec m).2]
    push_cast; rfl
  | odd m h₁ h₂ h₃ h₄ =>
    rw [preΨ', preNormEDS'_odd, ← one_pow (M := R[X]) 2]
    simp_rw [← apply_ite (· ^ 2)]
    have h := (expectedDegree_rec m).1
    have h' := W.natDegree_ite_le (Even m)
    refine ⟨natDegree_odd h₄.1 h₂.1 h'.1 h₁.1 h₃.1 h'.2 h.1 h.2,
      (coeff_odd h₄.1 h₂.1 h'.1 h₁.1 h₃.1 h'.2 h.1 h.2).trans ?_⟩
    rw [h₁.2, h₂.2, h₃.2, h₄.2, (expectedCoeff_rec m).1]
    push_cast; congr <;> split_ifs <;> simp

lemma natDegree_preΨ' (n : ℕ) : (W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2 :=
  (W.natDegree_coeff_preΨ' n).1

lemma coeff_preΨ' (n : ℕ) :
    if Even n then (W.preΨ' n).coeff ((n ^ 2 - 4) / 2) = (n / 2 : ℕ)
      else (W.preΨ' n).coeff ((n ^ 2 - 1) / 2) = n := by
  split_ifs with hn
  · exact (imp_of_if_pos (W.natDegree_coeff_preΨ' n) hn).right
  · exact (imp_of_if_neg (W.natDegree_coeff_preΨ' n) hn).right

private lemma natDegree_coeff_preΨ (n : ℤ) :
    if Even n then (W.preΨ n).natDegree ≤ (n.natAbs ^ 2 - 4) / 2 ∧
        (W.preΨ n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
      else (W.preΨ n).natDegree ≤ (n.natAbs ^ 2 - 1) / 2 ∧
          (W.preΨ n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · norm_cast
    exact W.preΨ_ofNat n ▸ W.natDegree_coeff_preΨ' n
  · simp only [even_neg, Int.even_coe_nat, preΨ_neg, natDegree_neg, preΨ_ofNat, Int.natAbs_neg,
      Int.natAbs_cast, coeff_neg, neg_eq_iff_eq_neg, Int.cast_neg, Int.cast_natCast, neg_neg]
    convert W.natDegree_coeff_preΨ' n using 3 with hn
    rcases even_iff_exists_two_mul.mp hn with ⟨_, rfl⟩
    rw [Nat.cast_mul, neg_mul_eq_mul_neg, Nat.cast_ofNat, Int.mul_ediv_cancel_left _ two_ne_zero,
      Int.cast_neg, neg_neg, Int.cast_natCast, Nat.mul_div_cancel_left _ two_pos]

lemma natDegree_Ψ' (n : ℤ) :
    (W.preΨ n).natDegree ≤ if Even n then (n.natAbs ^ 2 - 4) / 2 else (n.natAbs ^ 2 - 1) / 2 := by
  split_ifs with hn
  · exact (imp_of_if_pos (W.natDegree_coeff_preΨ n) hn).left
  · exact (imp_of_if_neg (W.natDegree_coeff_preΨ n) hn).left

lemma coeff_Ψ' (n : ℤ) :
    if Even n then (W.preΨ n).coeff ((n.natAbs ^ 2 - 4) / 2) = (n / 2 : ℤ)
      else (W.preΨ n).coeff ((n.natAbs ^ 2 - 1) / 2) = n := by
  split_ifs with hn
  · exact (imp_of_if_pos (W.natDegree_coeff_preΨ n) hn).right
  · exact (imp_of_if_neg (W.natDegree_coeff_preΨ n) hn).right

private lemma natDegree_coeff_ΨSq_ofNat (n : ℕ) :
    (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℕ) := by
  rcases n with _ | n
  · erw [ΨSq_zero]
    exact ⟨natDegree_zero.le, Nat.cast_zero.symm⟩
  · have h := W.natDegree_coeff_preΨ' <| n + 1
    simp only [ΨSq, preΨ_ofNat, Int.even_coe_nat, Nat.even_add_one, ite_not] at h ⊢
    by_cases hn : Even n
    · rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
      rw [if_pos hn, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos] at h
      rw [if_pos hn, mul_one, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1,
        Nat.add_sub_cancel]
      constructor
      · exact natDegree_pow_le_of_le 2 h.left
      · rw [coeff_pow_of_natDegree_le h.left, h.right]
        push_cast
        ring1
    · rcases Nat.odd_iff_not_even.mpr hn with ⟨m, rfl⟩
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos, show (2 * m + 2) / 2 = 2 * (m + 1) / 2 by rfl,
        Nat.mul_div_cancel_left _ two_pos] at h
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.succ_sub_one]
      constructor
      · exact natDegree_mul_le_of_le (natDegree_pow_le_of_le 2 h.left) W.natDegree_Ψ₂Sq
      · rw [coeff_mul_of_natDegree_le (natDegree_pow_le_of_le 2 h.left) W.natDegree_Ψ₂Sq,
          coeff_pow_of_natDegree_le h.left, h.right, coeff_Ψ₂Sq]
        push_cast
        ring1

private lemma natDegree_coeff_ΨSq (n : ℤ) :
    (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 ∧
      (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_ΨSq_ofNat n
  · simpa only [ΨSq_neg, Int.natAbs_neg] using W.natDegree_coeff_ΨSq_ofNat n

lemma natDegree_ΨSq (n : ℤ) : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 :=
  (W.natDegree_coeff_ΨSq n).left

lemma coeff_ΨSq (n : ℤ) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = (n.natAbs ^ 2 : ℕ) :=
  (W.natDegree_coeff_ΨSq n).right

private lemma natDegree_coeff_Φ_ofNat (n : ℕ) :
    (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1 := by
  rcases n with _ | _ | n
  · erw [Φ_zero]
    exact ⟨natDegree_one.le, coeff_one_zero⟩
  · erw [Φ_one]
    exact ⟨natDegree_X_le, coeff_X⟩
  · have h1 := W.natDegree_coeff_preΨ' <| n + 1
    have h2 := W.natDegree_coeff_ΨSq (n + 2 : ℕ)
    have h3 := W.natDegree_coeff_preΨ' <| n + 3
    simp only [WeierstrassCurve.Φ, Int.even_coe_nat, Nat.even_add_one, ite_not] at h1 h3 ⊢
    erw [preΨ_ofNat, ← Nat.cast_sub <| by linarith only, preΨ_ofNat, Nat.add_sub_cancel]
    by_cases hn : Even n
    · rcases even_iff_exists_two_mul.mp hn with ⟨m, rfl⟩
      rw [if_pos hn, show (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos] at h1
      rw [Int.natAbs_cast, show (2 * m + 2) ^ 2 = 4 * m * (m + 2) + 4 by ring1, Nat.succ_sub_one]
        at h2
      rw [if_pos hn, show (2 * m + 3) ^ 2 = 2 * (2 * (m + 1) * (m + 2)) + 1 by ring1,
        Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos] at h3
      rw [if_pos hn, mul_one]
      constructor
      · convert natDegree_sub_le_of_le (natDegree_mul_le_of_le natDegree_X_le h2.left) <|
          natDegree_mul_le_of_le h3.left h1.left using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 2) ^ 2 = 4 * m * (m + 2) + 4 by ring1, coeff_X_mul, h2.right,
          show _ + _ = (2 * (m + 1) * (m + 2)) + (2 * m * (m + 1)) by ring1,
          coeff_mul_of_natDegree_le h3.left h1.left, h3.right, h1.right]
        push_cast
        ring1
    · rcases Nat.odd_iff_not_even.mpr hn with ⟨m, rfl⟩
      rw [if_neg hn, show (2 * m + 2) ^ 2 = 2 * (2 * m * (m + 2)) + 4 by ring1, Nat.add_sub_cancel,
        Nat.mul_div_cancel_left _ two_pos, show (2 * m + 2) / 2 = 2 * (m + 1) / 2 by rfl,
        Nat.mul_div_cancel_left _ two_pos] at h1
      rw [Int.natAbs_cast, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1,
        Nat.add_sub_cancel] at h2
      rw [if_neg hn, show (2 * m + 4) ^ 2 = 2 * (2 * (m + 1) * (m + 3)) + 4 by ring1,
        Nat.add_sub_cancel, Nat.mul_div_cancel_left _ two_pos,
        show (2 * m + 4) / 2 = 2 * (m + 2) / 2 by rfl, Nat.mul_div_cancel_left _ two_pos] at h3
      rw [if_neg hn]
      constructor
      · convert natDegree_sub_le_of_le (natDegree_mul_le_of_le natDegree_X_le h2.left) <|
          natDegree_mul_le_of_le (natDegree_mul_le_of_le h3.left h1.left) W.natDegree_Ψ₂Sq using 1
        convert (max_self _).symm using 2 <;> ring1
      · rw [coeff_sub, show (2 * m + 3) ^ 2 = 4 * (m + 1) * (m + 2) + 1 by ring1, coeff_X_mul,
          h2.right, show _ + _ = (2 * (m + 1) * (m + 3)) + (2 * m * (m + 2)) + 3 by ring1,
          coeff_mul_of_natDegree_le (natDegree_mul_le_of_le h3.left h1.left) W.natDegree_Ψ₂Sq,
          coeff_mul_of_natDegree_le h3.left h1.left, h3.right, h1.right, coeff_Ψ₂Sq]
        push_cast
        ring1

private lemma natDegree_coeff_Φ (n : ℤ) :
    (W.Φ n).natDegree ≤ n.natAbs ^ 2 ∧ (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · exact W.natDegree_coeff_Φ_ofNat n
  · simpa only [Φ_neg, Int.natAbs_neg] using W.natDegree_coeff_Φ_ofNat n

lemma natDegree_Φ (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 :=
  (W.natDegree_coeff_Φ n).left

lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 :=
  (W.natDegree_coeff_Φ n).right

end WeierstrassCurve
