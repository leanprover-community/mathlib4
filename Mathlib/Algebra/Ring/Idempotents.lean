/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Subtype
import Mathlib.Order.Notation

/-!
# Idempotents

This file defines idempotents for an arbitrary multiplication and proves some basic results,
including:

* `IsIdempotentElem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `IsIdempotentElem.one_sub_iff`: In a (non-associative) ring, `p` is an idempotent if and only if
  `1-p` is an idempotent.
* `IsIdempotentElem.pow_succ_eq`: In a monoid `p ^ (n+1) = p` for `p` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/


variable {M N S M₀ M₁ R G G₀ : Type*}
variable [Mul M] [Monoid N] [Semigroup S] [MulZeroClass M₀] [MulOneClass M₁] [NonAssocRing R]
  [Group G] [CancelMonoidWithZero G₀]

/-- An element `p` is said to be idempotent if `p * p = p`
-/
def IsIdempotentElem (p : M) : Prop :=
  p * p = p

namespace IsIdempotentElem

theorem of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a

theorem eq {p : M} (h : IsIdempotentElem p) : p * p = p :=
  h

theorem mul_of_commute {p q : S} (h : Commute p q) (h₁ : IsIdempotentElem p)
    (h₂ : IsIdempotentElem q) : IsIdempotentElem (p * q) := by
  rw [IsIdempotentElem, mul_assoc, ← mul_assoc q, ← h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq]

lemma mul {M} [CommSemigroup M] {e₁ e₂ : M}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) : IsIdempotentElem (e₁ * e₂) :=
  he₁.mul_of_commute (.all e₁ e₂) he₂

theorem zero : IsIdempotentElem (0 : M₀) :=
  mul_zero _

theorem one : IsIdempotentElem (1 : M₁) :=
  mul_one _

theorem one_sub {p : R} (h : IsIdempotentElem p) : IsIdempotentElem (1 - p) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]

@[simp]
theorem one_sub_iff {p : R} : IsIdempotentElem (1 - p) ↔ IsIdempotentElem p :=
  ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, IsIdempotentElem.one_sub⟩

theorem add_sub_mul_of_commute {R} [Ring R] {p q : R} (h : Commute p q)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (p + q - p * q) := by
  convert (hp.one_sub.mul_of_commute ?_ hq.one_sub).one_sub using 1
  · simp_rw [sub_mul, mul_sub, one_mul, mul_one, sub_sub, sub_sub_cancel, add_sub, add_comm]
  · simp_rw [commute_iff_eq, sub_mul, mul_sub, one_mul, mul_one, sub_sub, add_sub, add_comm, h.eq]

theorem add_sub_mul {R} [CommRing R] {p q : R} (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (p + q - p * q) :=
  add_sub_mul_of_commute (mul_comm p q) hp hq

theorem pow {p : N} (n : ℕ) (h : IsIdempotentElem p) : IsIdempotentElem (p ^ n) :=
  Nat.recOn n ((pow_zero p).symm ▸ one) fun n _ =>
    show p ^ n.succ * p ^ n.succ = p ^ n.succ by
      conv_rhs => rw [← h.eq] -- Porting note: was `nth_rw 3 [← h.eq]`
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']

theorem pow_succ_eq {p : N} (n : ℕ) (h : IsIdempotentElem p) : p ^ (n + 1) = p :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one p) fun n ih => by rw [pow_succ, ih, h.eq]

@[simp]
theorem iff_eq_one {p : G} : IsIdempotentElem p ↔ p = 1 :=
  Iff.intro (fun h => mul_left_cancel ((mul_one p).symm ▸ h.eq : p * p = p * 1)) fun h =>
    h.symm ▸ one

@[simp]
theorem iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 := by
  refine
    Iff.intro (fun h => or_iff_not_imp_left.mpr fun hp => ?_) fun h =>
      h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one
  exact mul_left_cancel₀ hp (h.trans (mul_one p).symm)

lemma map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, he.eq]

/-! ### Instances on `Subtype IsIdempotentElem` -/


section Instances

instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩

@[simp]
theorem coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) :=
  rfl

instance : One { p : M₁ // IsIdempotentElem p } where one := ⟨1, one⟩

@[simp]
theorem coe_one : ↑(1 : { p : M₁ // IsIdempotentElem p }) = (1 : M₁) :=
  rfl

instance : HasCompl { p : R // IsIdempotentElem p } :=
  ⟨fun p => ⟨1 - p, p.prop.one_sub⟩⟩

@[simp]
theorem coe_compl (p : { p : R // IsIdempotentElem p }) : ↑pᶜ = (1 : R) - ↑p :=
  rfl

@[simp]
theorem compl_compl (p : { p : R // IsIdempotentElem p }) : pᶜᶜ = p :=
  Subtype.ext <| sub_sub_cancel _ _

@[simp]
theorem zero_compl : (0 : { p : R // IsIdempotentElem p })ᶜ = 1 :=
  Subtype.ext <| sub_zero _

@[simp]
theorem one_compl : (1 : { p : R // IsIdempotentElem p })ᶜ = 0 :=
  Subtype.ext <| sub_self _

end Instances

end IsIdempotentElem
