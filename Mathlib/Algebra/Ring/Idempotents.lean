/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Subtype
import Mathlib.Order.Notation

#align_import algebra.ring.idempotents from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

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
#align is_idempotent_elem IsIdempotentElem

namespace IsIdempotentElem

theorem of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a
#align is_idempotent_elem.of_is_idempotent IsIdempotentElem.of_isIdempotent

theorem eq {p : M} (h : IsIdempotentElem p) : p * p = p :=
  h
#align is_idempotent_elem.eq IsIdempotentElem.eq

theorem mul_of_commute {p q : S} (h : Commute p q) (h₁ : IsIdempotentElem p)
    (h₂ : IsIdempotentElem q) : IsIdempotentElem (p * q) := by
  rw [IsIdempotentElem, mul_assoc, ← mul_assoc q, ← h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq]
#align is_idempotent_elem.mul_of_commute IsIdempotentElem.mul_of_commute

theorem zero : IsIdempotentElem (0 : M₀) :=
  mul_zero _
#align is_idempotent_elem.zero IsIdempotentElem.zero

theorem one : IsIdempotentElem (1 : M₁) :=
  mul_one _
#align is_idempotent_elem.one IsIdempotentElem.one

theorem one_sub {p : R} (h : IsIdempotentElem p) : IsIdempotentElem (1 - p) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]
#align is_idempotent_elem.one_sub IsIdempotentElem.one_sub

@[simp]
theorem one_sub_iff {p : R} : IsIdempotentElem (1 - p) ↔ IsIdempotentElem p :=
  ⟨fun h => sub_sub_cancel 1 p ▸ h.one_sub, IsIdempotentElem.one_sub⟩
#align is_idempotent_elem.one_sub_iff IsIdempotentElem.one_sub_iff

theorem pow {p : N} (n : ℕ) (h : IsIdempotentElem p) : IsIdempotentElem (p ^ n) :=
  Nat.recOn n ((pow_zero p).symm ▸ one) fun n _ =>
    show p ^ n.succ * p ^ n.succ = p ^ n.succ by
      conv_rhs => rw [← h.eq] -- Porting note: was `nth_rw 3 [← h.eq]`
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']
#align is_idempotent_elem.pow IsIdempotentElem.pow

theorem pow_succ_eq {p : N} (n : ℕ) (h : IsIdempotentElem p) : p ^ (n + 1) = p :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one p) fun n ih => by rw [pow_succ, ih, h.eq]
#align is_idempotent_elem.pow_succ_eq IsIdempotentElem.pow_succ_eq

@[simp]
theorem iff_eq_one {p : G} : IsIdempotentElem p ↔ p = 1 :=
  Iff.intro (fun h => mul_left_cancel ((mul_one p).symm ▸ h.eq : p * p = p * 1)) fun h =>
    h.symm ▸ one
#align is_idempotent_elem.iff_eq_one IsIdempotentElem.iff_eq_one

@[simp]
theorem iff_eq_zero_or_one {p : G₀} : IsIdempotentElem p ↔ p = 0 ∨ p = 1 := by
  refine
    Iff.intro (fun h => or_iff_not_imp_left.mpr fun hp => ?_) fun h =>
      h.elim (fun hp => hp.symm ▸ zero) fun hp => hp.symm ▸ one
  exact mul_left_cancel₀ hp (h.trans (mul_one p).symm)
#align is_idempotent_elem.iff_eq_zero_or_one IsIdempotentElem.iff_eq_zero_or_one

/-! ### Instances on `Subtype IsIdempotentElem` -/


section Instances

instance : Zero { p : M₀ // IsIdempotentElem p } where zero := ⟨0, zero⟩

@[simp]
theorem coe_zero : ↑(0 : { p : M₀ // IsIdempotentElem p }) = (0 : M₀) :=
  rfl
#align is_idempotent_elem.coe_zero IsIdempotentElem.coe_zero

instance : One { p : M₁ // IsIdempotentElem p } where one := ⟨1, one⟩

@[simp]
theorem coe_one : ↑(1 : { p : M₁ // IsIdempotentElem p }) = (1 : M₁) :=
  rfl
#align is_idempotent_elem.coe_one IsIdempotentElem.coe_one

instance : HasCompl { p : R // IsIdempotentElem p } :=
  ⟨fun p => ⟨1 - p, p.prop.one_sub⟩⟩

@[simp]
theorem coe_compl (p : { p : R // IsIdempotentElem p }) : ↑pᶜ = (1 : R) - ↑p :=
  rfl
#align is_idempotent_elem.coe_compl IsIdempotentElem.coe_compl

@[simp]
theorem compl_compl (p : { p : R // IsIdempotentElem p }) : pᶜᶜ = p :=
  Subtype.ext <| sub_sub_cancel _ _
#align is_idempotent_elem.compl_compl IsIdempotentElem.compl_compl

@[simp]
theorem zero_compl : (0 : { p : R // IsIdempotentElem p })ᶜ = 1 :=
  Subtype.ext <| sub_zero _
#align is_idempotent_elem.zero_compl IsIdempotentElem.zero_compl

@[simp]
theorem one_compl : (1 : { p : R // IsIdempotentElem p })ᶜ = 0 :=
  Subtype.ext <| sub_self _
#align is_idempotent_elem.one_compl IsIdempotentElem.one_compl

end Instances

end IsIdempotentElem
