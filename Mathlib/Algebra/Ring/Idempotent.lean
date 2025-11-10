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

section NonUnitalRing
variable [NonUnitalRing R] {a b : R}

lemma add_sub_mul_of_commute (h : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by
  simp only [IsIdempotentElem, h.eq, mul_sub, mul_add, sub_mul, add_mul, ha.eq,
    mul_assoc, add_sub_cancel_right, hb.eq, hb.mul_self_mul, add_sub_cancel_left, sub_right_inj]
  rw [← h.eq, ha.mul_self_mul, h.eq, hb.mul_self_mul, add_sub_cancel_right]

end NonUnitalRing

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

/-- `a + b` is idempotent if and only if `a` and `b` anti-commute. -/
theorem add_iff [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b) ↔ a * b + b * a = 0 := by
  refine ⟨fun h ↦ ?_, ha.add hb⟩
  rw [← add_right_cancel_iff (a := b), add_assoc, ← add_left_cancel_iff (a := a),
    ← add_assoc, add_add_add_comm]
  simpa [add_mul, mul_add, ha.eq, hb.eq] using h.eq

/-- `b - a` is idempotent when `a * b = a` and `b * a = a`. -/
lemma sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) (hab : a * b = a) (hba : b * a = a) : IsIdempotentElem (b - a) := by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hab, hba, ha.eq, hb.eq, sub_self, sub_zero]

/-- If idempotent `a` and element `b` anti-commute, then their product is zero. -/
theorem mul_eq_zero_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : a * b = 0 := by
  have h : a * b * a = 0 := by
    rw [← nsmul_right_inj ((Nat.zero_ne_add_one 1).symm), nsmul_zero]
    have : a * (a * b + b * a) * a = 0 := by rw [hab, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, ha.eq, ← mul_assoc, ha.eq, ← two_nsmul] at this
    exact this
  suffices a * a * b + a * b * a = 0 by rwa [h, add_zero, ha.eq] at this
  rw [mul_assoc, mul_assoc, ← mul_add, hab, mul_zero]

/-- If idempotent `a` and element `b` anti-commute, then they commute.
So anti-commutativity implies commutativity when one of them is idempotent. -/
lemma commute_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : Commute a b := by
  have := mul_eq_zero_of_anticommute ha hab
  rw [this, zero_add] at hab
  rw [Commute, SemiconjBy, hab, this]

theorem sub_iff [NonUnitalRing R] [IsAddTorsionFree R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (q - p) ↔ p * q = p ∧ q * p = p := by
  refine ⟨fun hqp ↦ ?_, fun ⟨h1, h2⟩ => hp.sub hq h1 h2⟩
  have h : p * (q - p) + (q - p) * p = 0 := hp.add_iff hqp |>.mp ((add_sub_cancel p q).symm ▸ hq)
  have hpq : Commute p q := by
    simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] at hqp
    have h1 := congr_arg (q * ·) hqp
    have h2 := congr_arg (· * q) hqp
    simp_rw [mul_sub, mul_add, ← mul_assoc, hq.eq, add_sub_cancel_right] at h1
    simp_rw [sub_mul, add_mul, mul_assoc, hq.eq, add_sub_cancel_left, ← mul_assoc] at h2
    exact h2.symm.trans h1
  rw [hpq.eq, and_self, ← nsmul_right_inj (by simp : 2 ≠ 0), ← zero_add (2 • p)]
  convert congrArg (· + 2 • p) h using 1
  simp [sub_mul, mul_sub, hp.eq, hpq.eq, two_nsmul, sub_add, sub_sub]

end IsIdempotentElem
