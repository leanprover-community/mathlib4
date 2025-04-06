/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.Subtype
import Mathlib.Tactic.Conv
import Mathlib.Tactic.MinImports

/-!
# Idempotents

This file defines idempotents for an arbitrary multiplication and proves some basic results,
including:

* `IsIdempotentElem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `IsIdempotentElem.pow_succ_eq`: In a monoid `a ^ (n+1) = a` for `a` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/

assert_not_exists GroupWithZero

variable {M N S : Type*}

/-- An element `a` is said to be idempotent if `a * a = a`. -/
def IsIdempotentElem [Mul M] (a : M) : Prop := a * a = a

namespace IsIdempotentElem
section Mul
variable [Mul M] {a : M}

lemma of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a

lemma eq (ha : IsIdempotentElem a) : a * a = a := ha

end Mul

section Semigroup
variable [Semigroup S] {a b : S}

lemma mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, ha.eq, hb.eq]

end Semigroup

section CommSemigroup
variable [CommSemigroup S] {a b : S}

lemma mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b) :=
  ha.mul_of_commute (.all ..) hb

end CommSemigroup

section MulOneClass
variable [MulOneClass M] {a : M}

lemma one : IsIdempotentElem (1 : M) := mul_one _

instance : One {a : M // IsIdempotentElem a} where one := ⟨1, one⟩

@[simp, norm_cast] lemma coe_one : ↑(1 : {a : M // IsIdempotentElem a}) = (1 : M) := rfl

end MulOneClass

section Monoid
variable [Monoid M] {a : M}

lemma pow (n : ℕ) (h : IsIdempotentElem a) : IsIdempotentElem (a ^ n) :=
  Nat.recOn n ((pow_zero a).symm ▸ one) fun n _ =>
    show a ^ n.succ * a ^ n.succ = a ^ n.succ by
      conv_rhs => rw [← h.eq]
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']

lemma pow_succ_eq (n : ℕ) (h : IsIdempotentElem a) : a ^ (n + 1) = a :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, h.eq]

theorem iff_eq_one_of_isUnit (h : IsUnit a) : IsIdempotentElem a ↔ a = 1 :=
  ⟨fun idem ↦ have ⟨q, eq⟩ := h.exists_left_inv
    by rw [← eq, ← idem.eq, ← mul_assoc, eq, one_mul, idem.eq], by rintro rfl; exact .one⟩

end Monoid

section CancelMonoid
variable [CancelMonoid M] {a : M}

@[simp] lemma iff_eq_one : IsIdempotentElem a ↔ a = 1 := by simp [IsIdempotentElem]

end CancelMonoid

lemma map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, he.eq]

end IsIdempotentElem
