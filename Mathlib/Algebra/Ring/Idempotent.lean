/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Notation
import Mathlib.Tactic.Convert
import Mathlib.Algebra.Group.Torsion

/-!
# Idempotent elements of a ring

This file proves result about idempotent elements of a ring, like:
* `IsIdempotentElem.one_sub_iff`: In a (non-associative) ring, `a` is an idempotent if and only if
  `1 - a` is an idempotent.
-/

variable {R : Type*}

namespace IsIdempotentElem
section NonAssocRing
variable [NonAssocRing R] {a : R}

lemma one_sub (h : IsIdempotentElem a) : IsIdempotentElem (1 - a) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]

@[simp]
lemma one_sub_iff : IsIdempotentElem (1 - a) ↔ IsIdempotentElem a :=
  ⟨fun h => sub_sub_cancel 1 a ▸ h.one_sub, IsIdempotentElem.one_sub⟩

@[simp]
lemma mul_one_sub_self (h : IsIdempotentElem a) : a * (1 - a) = 0 := by
  rw [mul_sub, mul_one, h.eq, sub_self]

@[simp]
lemma one_sub_mul_self (h : IsIdempotentElem a) : (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, h.eq, sub_self]

instance : HasCompl {a : R // IsIdempotentElem a} where compl a := ⟨1 - a, a.prop.one_sub⟩

@[simp] lemma coe_compl (a : {a : R // IsIdempotentElem a}) : ↑aᶜ = (1 : R) - ↑a := rfl

@[simp] lemma compl_compl (a : {a : R // IsIdempotentElem a}) : aᶜᶜ = a := by ext; simp
@[simp] lemma zero_compl : (0 : {a : R // IsIdempotentElem a})ᶜ = 1 := by ext; simp
@[simp] lemma one_compl : (1 : {a : R // IsIdempotentElem a})ᶜ = 0 := by ext; simp

end NonAssocRing

section Semiring
variable [Semiring R] {a b : R}

lemma of_mul_add (mul : a * b = 0) (add : a + b = 1) : IsIdempotentElem a ∧ IsIdempotentElem b := by
  simp_rw [IsIdempotentElem]; constructor
  · conv_rhs => rw [← mul_one a, ← add, mul_add, mul, add_zero]
  · conv_rhs => rw [← one_mul b, ← add, add_mul, mul, zero_add]

end Semiring

section Ring
variable [Ring R] {a b : R}

lemma add_sub_mul_of_commute (h : Commute a b) (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by
  convert (hp.one_sub.mul_of_commute ?_ hq.one_sub).one_sub using 1
  · simp_rw [sub_mul, mul_sub, one_mul, mul_one, sub_sub, sub_sub_cancel, add_sub, add_comm]
  · simp_rw [commute_iff_eq, sub_mul, mul_sub, one_mul, mul_one, sub_sub, add_sub, add_comm, h.eq]

end Ring

section CommRing
variable [CommRing R] {a b : R}

lemma add_sub_mul (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := add_sub_mul_of_commute (.all ..) hp hq

end CommRing

lemma sub_of [NonAssocRing R] {p q : R} (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hpq : p * q = p) (hqp : q * p = p) : IsIdempotentElem (q - p) := by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hpq, hqp, hp.eq, hq.eq, sub_self, sub_zero]

end IsIdempotentElem


lemma commutes_of_isIdempotentElem_sub [Ring R] [IsAddTorsionFree R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hqp : IsIdempotentElem (q - p)) :
    p * q = p ∧ q * p = p := by
  simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] at hqp
  have h' : (2 : ℕ) • p = q * p + p * q := by
    simp_rw [two_nsmul]
    calc p + p = p + (p * q + q * p - p) := by rw [hqp]
      _ = q * p + p * q := by simp_rw [add_sub_cancel, add_comm]
  have H : ((2 : ℕ) • p) * q = q * (p * q) + p * q := by
    simp_rw [h', add_mul, mul_assoc, hq.eq]
  simp_rw [add_comm, two_nsmul, add_mul, add_right_inj] at H
  have H' : q * ((2 : ℕ) • p) = q * p + q * (p * q) := by
    simp_rw [h', mul_add, ← mul_assoc, hq.eq]
  simp_rw [two_nsmul, mul_add, add_right_inj] at H'
  have H'' : q * p = p * q := by
    simp_rw [H']
    exact H.symm
  rw [← H'', and_self_iff]
  rw [← H'', ← two_nsmul, nsmul_right_inj (Nat.zero_ne_add_one 1).symm] at h'
  exact h'.symm

theorem isIdempotentElem_sub_iff [Ring R] [IsAddTorsionFree R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (q - p) ↔ p * q = p ∧ q * p = p :=
  ⟨commutes_of_isIdempotentElem_sub hp hq, fun ⟨h1, h2⟩ => hp.sub_of hq h1 h2⟩
