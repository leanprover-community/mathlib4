/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.GreensRelations.Classes
public import Mathlib.Data.Fintype.Pigeonhole

/-!
# Multiplication Sequences and Helper Lemmas

This file provides tools for analyzing finite semigroups using iterated multiplication
sequences (`leftMulSeq`, `rightMulSeq`). It contains intermediate structural lemmas
required to prove the main theorems of Green's relations.

## Main definitions

* `MulSeq.rightMulSeq a c n`: The element obtained by multiplying `a` by `c` on the right `n` times.
* `MulSeq.leftMulSeq c a n`: The element obtained by multiplying `a` by `c` on the left `n` times.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

public section

variable {S : Type*} [Semigroup S]

/-- The opposite semigroup construction gives an equivalence between `S` and `Sᵐᵒᵖ`
  that preserves Green's relations, so finiteness of `S` implies finiteness of `Sᵐᵒᵖ`. -/
instance instFiniteMulOpposite [Finite S] : Finite Sᵐᵒᵖ :=
  Finite.of_equiv S MulOpposite.opEquiv

namespace MulSeq

/-- The sequence defined by repeatedly multiplying `a` by `c` on the right. -/
def rightMulSeq (a c : S) : ℕ → S
  | 0 => a
  | n + 1 => rightMulSeq a c n * c

/-- Left multiplication can be pulled out of a `rightMulSeq`. -/
lemma rightMulSeq_mul_pull (c : S) (m : ℕ) (x u : S) :
    rightMulSeq (u * x) c m = u * rightMulSeq x c m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [rightMulSeq, ih, mul_assoc]

/-- Extracting a right multiplication from the base of a `rightMulSeq`. -/
lemma rightMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    rightMulSeq x c (n + 1) = rightMulSeq (x * c) c n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (· * c) ih

/-- The sequence defined by repeatedly multiplying `a` by `c` on the left. -/
def leftMulSeq (c a : S) : ℕ → S
  | 0 => a
  | n + 1 => c * leftMulSeq c a n

/-- Right multiplication can be pulled out of a `leftMulSeq`. -/
lemma leftMulSeq_mul_pull (c : S) (m : ℕ) (x v : S) :
    leftMulSeq c (x * v) m = leftMulSeq c x m * v := by
  induction m with
  | zero => rfl
  | succ m ih => exact (congrArg (c * ·) ih).trans (mul_assoc ..).symm

/-- Extracting a left multiplication from the base of a `leftMulSeq`. -/
lemma leftMulSeq_pull_c (c : S) (n : ℕ) (x : S) :
    leftMulSeq c x (n + 1) = leftMulSeq c (c * x) n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (c * ·) ih

/-- In a finite semigroup, a `leftMulSeq` eventually repeats. -/
lemma leftMulSeq_pigeonhole [Finite S] (c a : S) :
    ∃ i j : ℕ, i < j ∧ leftMulSeq c a i = leftMulSeq c a j := by
  obtain ⟨i, j, h_neq, heq⟩ := Finite.exists_ne_map_eq_of_infinite (leftMulSeq c a)
  rcases lt_trichotomy i j with h_lt | h_eq | h_gt
  · exact ⟨i, j, h_lt, heq⟩
  · nomatch (h_neq h_eq)
  · exact ⟨j, i, h_gt, heq.symm⟩

/-- Any element in a `leftMulSeq` starting from `a` is a left multiple of `a`. -/
lemma leftMulSeq_isGreenLeftDvd (c a : S) (m : ℕ) :
    IsGreenLeftDvd (leftMulSeq c a m) a := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    rcases ih with h | ⟨w, hw⟩
    · exact Or.inr ⟨c, by rw [leftMulSeq, h]⟩
    · exact Or.inr ⟨c * w, by rw [leftMulSeq, hw, mul_assoc]⟩

/-- Left divisibility is preserved by left multiplication. -/
lemma isGreenLeftDvd_mul_left (a b x : S) (h : IsGreenLeftDvd a b) :
    IsGreenLeftDvd (x * a) b := by
  rcases h with rfl | ⟨w, rfl⟩
  · exact Or.inr ⟨x, rfl⟩
  · exact Or.inr ⟨x * w, by simp [mul_assoc]⟩

/-- Left and right multiplication sequences commute. -/
lemma leftMulSeq_rightMulSeq_comm (c x d : S) (i k : ℕ) :
    leftMulSeq c (rightMulSeq x d k) i = rightMulSeq (leftMulSeq c x i) d k := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [leftMulSeq, ih, ← rightMulSeq_mul_pull]

/-- If `b = c * b * d`, applying `n` left steps then `n` right steps yields `b`. -/
lemma b_eq_right_left_seq (c b d : S) (h : b = c * b * d) (n : ℕ) :
    b = rightMulSeq (leftMulSeq c b n) d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [h, ih]
    grind [rightMulSeq_mul_pull, leftMulSeq, rightMulSeq, mul_assoc]

/-- Left multiplication sequence addition of indices. -/
lemma leftMulSeq_add (c a : S) (n m : ℕ) :
    leftMulSeq c a (n + m) = leftMulSeq c (leftMulSeq c a n) m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (c * ·) ih

/-- If `b = c * b * d` in a finite semigroup, `b` is equivalent to some left multiple sequence. -/
lemma eq_leftMulSeq_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) :
    ∃ k > 0, b = leftMulSeq c b k := by
  rcases leftMulSeq_pigeonhole c b with ⟨i, j, hij, heq⟩
  have h_fi_k : leftMulSeq c (leftMulSeq c b i) (j - i) = leftMulSeq c b i := by
    rw [← leftMulSeq_add, Nat.add_sub_of_le (le_of_lt hij), heq]
  have h_b_eq := b_eq_right_left_seq c b d h i
  exact ⟨j - i, Nat.sub_pos_of_lt hij, by
    conv_lhs => rw [h_b_eq]
    rw [← h_fi_k, ← leftMulSeq_rightMulSeq_comm, ← h_b_eq]⟩

/-- If `b = c * b * d`, then `b` is L-related to `c * b`. -/
lemma greenL_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenL b (c * b) := by
  obtain ⟨k, hk_pos, hk_eq⟩ := eq_leftMulSeq_of_eq_mul_mul h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
  constructor
  · conv_lhs => rw [hk_eq, leftMulSeq_pull_c]
    exact leftMulSeq_isGreenLeftDvd c (c * b) m
  · exact Or.inr ⟨c, rfl⟩

open MulOpposite in
/-- If `b = c * b * d`, then `b` is R-related to `b * d`. -/
lemma greenR_of_eq_mul_mul [Finite S] {b c d : S} (h : b = c * b * d) : IsGreenR b (b * d) := by
  rw [isGreenR_iff_isGreenL_op]
  grind [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, greenL_of_eq_mul_mul]

/-- Green's L relation holds when a left multiplier is dropped from an already L-related element. -/
lemma isGreenL_of_isGreenL_mul {b x z : S} (h : IsGreenL b (x * (z * b))) : IsGreenL b (z * b) :=
  ⟨IsGreenLeftDvd.trans h.left (Or.inr ⟨x, rfl⟩), Or.inr ⟨z, rfl⟩⟩

open MulOpposite in
/-- Green's R relation holds when a right multiplier
  is dropped from an already R-related element. -/
lemma isGreenR_of_isGreenR_mul {b u y : S} (h : IsGreenR b ((b * u) * y)) : IsGreenR b (b * u) := by
  rw [isGreenR_iff_isGreenL_op] at h ⊢
  grind [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, isGreenL_of_isGreenL_mul]

/-- If `b = x * z * b * d`, then `b` is L-related to `z * b`. -/
lemma isGreenL_of_eq_mul_mul_mul [Finite S] {b x z d : S} (h : b = (x * z) * b * d) :
    IsGreenL b (z * b) :=
  isGreenL_of_isGreenL_mul (mul_assoc x z b ▸ greenL_of_eq_mul_mul h)

open MulOpposite in
/-- If `b = c * b * (u * y)`, then `b` is R-related to `b * u`. -/
lemma isGreenR_of_eq_mul_mul_mul [Finite S] {b c u y : S} (h : b = c * b * (u * y)) :
    IsGreenR b (b * u) := by
  rw [isGreenR_iff_isGreenL_op]
  grind [op_mul, mul_assoc, isGreenR_iff_isGreenL_op, isGreenL_of_eq_mul_mul_mul]

/-- If `a` is a two-sided multiple of `b`, and `b` is a two-sided multiple of `a`,
  then `a` and `b` are Green's D-related. -/
lemma isGreenD_of_JRel_both [Finite S] {a b x y z u : S}
    (h1 : a = z * b * u) (h2 : b = x * a * y) : IsGreenD a b := by
  rw [h1] at h2
  have h : b = (x * z) * b * (u * y) := by
    conv_lhs => rw [h2]
    simp only [mul_assoc]
  exact ⟨b * u, (by
    simpa [h1, mul_assoc] using (IsGreenL.mul_right u
      (isGreenL_of_eq_mul_mul_mul h)).symm),
    (isGreenR_of_eq_mul_mul_mul h).symm⟩

/-- If `a` is a left multiple of `b` and `b` is a two-sided multiple of `a`,
  they are D-related. -/
lemma isGreenD_of_JRel_left_both [Finite S] {a b x y z : S}
    (h1 : a = z * b) (h2 : b = x * a * y) : IsGreenD a b := by
  simp only [h1, ← mul_assoc] at h2 ⊢
  exact ⟨b, (isGreenL_of_isGreenL_mul (by
    simpa [mul_assoc] using greenL_of_eq_mul_mul h2)).symm, IsGreenR.refl b⟩

open MulOpposite in
/-- If `a` is a right multiple of `b` and `b` is a two-sided multiple of `a`, they are D-related. -/
lemma isGreenD_of_JRel_right_both [Finite S] {a b x y u : S}
    (h1 : a = b * u) (h2 : b = x * a * y) : IsGreenD a b := by
  rw [IsGreenD.isGreenD_iff_isGreenD_op]
  have h1_op : op a = op u * op b := by simp only [h1, ← op_mul]
  have h2_op : op b = op y * op a * op x := by simp [h2, ← op_mul, mul_assoc]
  exact isGreenD_of_JRel_left_both h1_op h2_op

/-- If `a` is a left multiple of `b` and `b` is a right multiple of `a`, they are D-related. -/
lemma isGreenD_of_left_right [Finite S] {a b u y : S} (h1 : a = u * b) (h2 : b = a * y) :
    IsGreenD a b :=
  ⟨a, IsGreenL.refl a, h2.symm ▸ greenR_of_eq_mul_mul ((h2 ▸ h1).trans (mul_assoc u a y).symm)⟩

/-- If `a` is a right multiple of `b` and `b` is a left multiple of `a`, they are D-related. -/
lemma isGreenD_of_right_left [Finite S] {a b v x : S} (h1 : a = b * v) (h2 : b = x * a) :
    IsGreenD a b :=
  ⟨b, h2.symm ▸ greenL_of_eq_mul_mul (h2 ▸ h1), IsGreenR.refl b⟩

/-- If `a` is a left multiple of `b` and `b` is a left multiple of `a`, they are D-related. -/
lemma isGreenD_of_left_left {a b u x : S} (h1 : a = u * b) (h2 : b = x * a) :
  IsGreenD a b :=
  ⟨b, ⟨Or.inr ⟨u, h1⟩, Or.inr ⟨x, h2⟩⟩, IsGreenR.refl b⟩

/-- If `a` is a right multiple of `b` and `b` is a right multiple of `a`, they are D-related. -/
lemma isGreenD_of_right_right {a b v y : S} (h1 : a = b * v) (h2 : b = a * y) :
  IsGreenD a b :=
  ⟨a, IsGreenL.refl a, ⟨Or.inr ⟨v, h1⟩, Or.inr ⟨y, h2⟩⟩⟩

/-- A regular element `a` has an idempotent in its L-class. -/
lemma exists_idempotent_in_greenL_of_regular {S : Type*} [Semigroup S] {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenL.eqvClass a, e * e = e := by
  obtain ⟨s, hs⟩ := hReg
  exact ⟨s * a, ⟨Or.inr ⟨s, rfl⟩, Or.inr ⟨a, by rw [← mul_assoc, hs]⟩⟩, by
    simp only [mul_assoc]
    rw [← mul_assoc a, hs]⟩

open MulOpposite in
/-- A regular element `a` has an idempotent in its R-class. -/
lemma exists_idempotent_in_greenR_of_regular {S : Type*} [Semigroup S] {a : S}
    (hReg : IsGreenRegular a) : ∃ e ∈ IsGreenR.eqvClass a, e * e = e := by
  have hReg_op : IsGreenRegular (op a) := by
    obtain ⟨s, hs⟩ := hReg
    use op s
    simp only [← op_mul, ← mul_assoc, hs]
  obtain ⟨e_op, he_L, he_idem⟩ := exists_idempotent_in_greenL_of_regular hReg_op
  use unop e_op
  constructor
  · simpa [isGreenR_iff_isGreenL_op] using he_L
  · exact op_injective (by simp only [op_mul, op_unop, he_idem])

/-- Two H-related idempotents must be equal. -/
lemma eq_of_isGreenH_of_idempotent {S : Type*} [Semigroup S] {a b : S}
    (h : IsGreenH a b) (ha : a * a = a) (hb : b * b = b) : a = b :=
  have h1 : a * b = b := by
    rcases h.right.right with rfl | ⟨x, rfl⟩ <;> simp only [← mul_assoc, ha]
  have h2 : a * b = a := by
    rcases h.left.left with rfl | ⟨y, rfl⟩ <;> simp only [mul_assoc, hb]
  h2.symm.trans h1

/-- If `a` is H-related to an idempotent `e`,
  multiplying `a` by `e` leaves `a` unchanged. -/
lemma mul_eq_self_of_isGreenH_idempotent {S : Type*} [Semigroup S] {a e : S}
    (h : IsGreenH a e) (he : e * e = e) : a * e = a ∧ e * a = a :=
  ⟨by rcases h.left.left with rfl | ⟨w, rfl⟩ <;> simp only [mul_assoc, he],
   by rcases h.right.left with rfl | ⟨v, rfl⟩ <;> simp only [← mul_assoc, he]⟩

end MulSeq
