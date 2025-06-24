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

lemma _root_.isIdempotentElem_iff_mul_one_sub_self :
    IsIdempotentElem a ↔ a * (1 - a) = 0 := by
  rw [mul_sub, mul_one, sub_eq_zero, eq_comm, IsIdempotentElem]

lemma _root_.isIdempotentElem_iff_one_sub_mul_self :
    IsIdempotentElem a ↔ (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, sub_eq_zero, eq_comm, IsIdempotentElem]

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

/-- `a + b` is idempotent when `a` and `b` anti-commute. -/
theorem add [NonUnitalNonAssocSemiring R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b + b * a = 0) : IsIdempotentElem (a + b) := by
  simp_rw [IsIdempotentElem, mul_add, add_mul, ha.eq, hb.eq, add_add_add_comm, ← add_assoc,
    add_assoc a, hab, zero_add]

/-- If idempotent `p` and element `q` anti-commute, then their product is zero. -/
theorem mul_eq_zero_of_anticommute {p q : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (hp : IsIdempotentElem p) (hpq : p * q + q * p = 0) : p * q = 0 := by
  have h : p * q * p + p * q * p = 0 := by
    have : p * (p * q + q * p) * p = 0 := by rw [hpq, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, hp.eq, ← mul_assoc, hp.eq] at this
    exact this
  replace h : p * q * p = 0 := by rwa [← two_nsmul, ← nsmul_zero 2,
    nsmul_right_inj ((Nat.zero_ne_add_one 1).symm)] at h
  suffices p * p * q + p * q * p = 0 by rwa [h, add_zero, hp.eq] at this
  rw [mul_assoc, mul_assoc, ← mul_add, hpq, mul_zero]

end IsIdempotentElem
