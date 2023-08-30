/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import Mathlib.Algebra.Group.Units

#align_import algebra.group.semiconj from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`SemiconjBy a x y`), if `a * x = y * a`.
In this file we provide operations on `SemiconjBy _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `Commute a b = SemiconjBy a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

set_option autoImplicit true

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
@[to_additive AddSemiconjBy "`x` is additive semiconjugate to `y` by `a` if `a + x = y + a`"]
def SemiconjBy [Mul M] (a x y : M) : Prop :=
  a * x = y * a
#align semiconj_by SemiconjBy
#align add_semiconj_by AddSemiconjBy

namespace SemiconjBy

/-- Equality behind `SemiconjBy a x y`; useful for rewriting. -/
@[to_additive "Equality behind `AddSemiconjBy a x y`; useful for rewriting."]
protected theorem eq [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a :=
  h
#align semiconj_by.eq SemiconjBy.eq
#align add_semiconj_by.eq AddSemiconjBy.eq

section Semigroup

variable [Semigroup S] {a b x y z x' y' : S}

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[to_additive (attr := simp) "If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x + x'` to `y + y'`."]
theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [←mul_assoc, h.eq, mul_assoc, h'.eq, ←mul_assoc]
#align semiconj_by.mul_right SemiconjBy.mul_right
#align add_semiconj_by.add_right AddSemiconjBy.add_right

/-- If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a * b`
semiconjugates `x` to `z`. -/
@[to_additive "If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a + b`
semiconjugates `x` to `z`."]
theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy
  rw [mul_assoc, hb.eq, ←mul_assoc, ha.eq, mul_assoc]
#align semiconj_by.mul_left SemiconjBy.mul_left
#align add_semiconj_by.add_left AddSemiconjBy.add_left

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a semigroup
is transitive. -/
@[to_additive "The relation “there exists an element that semiconjugates `a` to `b`” on an additive
semigroup is transitive."]
protected theorem transitive : Transitive fun a b : S ↦ ∃ c, SemiconjBy c a b
  | _, _, _, ⟨x, hx⟩, ⟨y, hy⟩ => ⟨y * x, hy.mul_left hx⟩
#align semiconj_by.transitive SemiconjBy.transitive
#align add_semiconj_by.transitive SemiconjBy.transitive

end Semigroup

section MulOneClass

variable [MulOneClass M]

/-- Any element semiconjugates `1` to `1`. -/
@[to_additive (attr := simp) "Any element semiconjugates `0` to `0`."]
theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]
#align semiconj_by.one_right SemiconjBy.one_right
#align add_semiconj_by.zero_right AddSemiconjBy.zero_right

/-- One semiconjugates any element to itself. -/
@[to_additive (attr := simp) "Zero semiconjugates any element to itself."]
theorem one_left (x : M) : SemiconjBy 1 x x :=
  Eq.symm <| one_right x
#align semiconj_by.one_left SemiconjBy.one_left
#align add_semiconj_by.zero_left AddSemiconjBy.zero_left

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a monoid (or, more
generally, on `MulOneClass` type) is reflexive. -/
@[to_additive "The relation “there exists an element that semiconjugates `a` to `b`” on an additive
monoid (or, more generally, on an `AddZeroClass` type) is reflexive."]
protected theorem reflexive : Reflexive fun a b : M ↦ ∃ c, SemiconjBy c a b
  | a => ⟨1, one_left a⟩
#align semiconj_by.reflexive SemiconjBy.reflexive
#align add_semiconj_by.reflexive AddSemiconjBy.reflexive

end MulOneClass

section Monoid

variable [Monoid M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive "If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it
semiconjugates `-x` to `-y`."]
theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ :=
  calc
    a * ↑x⁻¹ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _        = ↑y⁻¹ * a              := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]
#align semiconj_by.units_inv_right SemiconjBy.units_inv_right
#align add_semiconj_by.add_units_neg_right AddSemiconjBy.addUnits_neg_right

@[to_additive (attr := simp)]
theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y :=
  ⟨units_inv_right, units_inv_right⟩
#align semiconj_by.units_inv_right_iff SemiconjBy.units_inv_right_iff
#align add_semiconj_by.add_units_neg_right_iff AddSemiconjBy.addUnits_neg_right_iff

/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive "If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to
`x`."]
theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x :=
  calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]
#align semiconj_by.units_inv_symm_left SemiconjBy.units_inv_symm_left
#align add_semiconj_by.add_units_neg_symm_left AddSemiconjBy.addUnits_neg_symm_left

@[to_additive (attr := simp)]
theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y :=
  ⟨units_inv_symm_left, units_inv_symm_left⟩
#align semiconj_by.units_inv_symm_left_iff SemiconjBy.units_inv_symm_left_iff
#align add_semiconj_by.add_units_neg_symm_left_iff AddSemiconjBy.addUnits_neg_symm_left_iff

@[to_additive]
theorem units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y :=
  congr_arg Units.val h
#align semiconj_by.units_coe SemiconjBy.units_val
#align add_semiconj_by.add_units_coe AddSemiconjBy.addUnits_val

@[to_additive]
theorem units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y :=
  Units.ext h
#align semiconj_by.units_of_coe SemiconjBy.units_of_val
#align add_semiconj_by.add_units_of_coe AddSemiconjBy.addUnits_of_val

@[to_additive (attr := simp)]
theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y :=
  ⟨units_of_val, units_val⟩
#align semiconj_by.units_coe_iff SemiconjBy.units_val_iff
#align add_semiconj_by.add_units_coe_iff AddSemiconjBy.addUnits_val_iff

@[to_additive (attr := simp)]
theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction' n with n ih
  · rw [pow_zero, pow_zero]
    exact SemiconjBy.one_right _
  · rw [pow_succ, pow_succ]
    exact h.mul_right ih
#align semiconj_by.pow_right SemiconjBy.pow_right
#align add_semiconj_by.nsmul_right AddSemiconjBy.nsmul_right

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a x y : G}

@[to_additive (attr := simp)]
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x :=
  inv_involutive.injective.eq_iff.symm.trans <| by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, inv_inv, eq_comm, SemiconjBy]
#align semiconj_by.inv_inv_symm_iff SemiconjBy.inv_inv_symm_iff
#align add_semiconj_by.neg_neg_symm_iff AddSemiconjBy.neg_neg_symm_iff

@[to_additive]
theorem inv_inv_symm : SemiconjBy a x y → SemiconjBy a⁻¹ y⁻¹ x⁻¹ :=
  inv_inv_symm_iff.2
#align semiconj_by.inv_inv_symm SemiconjBy.inv_inv_symm
#align add_semiconj_by.neg_neg_symm AddSemiconjBy.neg_neg_symm

end DivisionMonoid

section Group

variable [Group G] {a x y : G}

@[to_additive (attr := simp)]
theorem inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  @units_inv_right_iff G _ a ⟨x, x⁻¹, mul_inv_self x, inv_mul_self x⟩
    ⟨y, y⁻¹, mul_inv_self y, inv_mul_self y⟩
#align semiconj_by.inv_right_iff SemiconjBy.inv_right_iff
#align add_semiconj_by.neg_right_iff AddSemiconjBy.neg_right_iff

@[to_additive]
theorem inv_right : SemiconjBy a x y → SemiconjBy a x⁻¹ y⁻¹ :=
  inv_right_iff.2
#align semiconj_by.inv_right SemiconjBy.inv_right
#align add_semiconj_by.neg_right AddSemiconjBy.neg_right

@[to_additive (attr := simp)]
theorem inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y :=
  @units_inv_symm_left_iff G _ ⟨a, a⁻¹, mul_inv_self a, inv_mul_self a⟩ _ _
#align semiconj_by.inv_symm_left_iff SemiconjBy.inv_symm_left_iff
#align add_semiconj_by.neg_symm_left_iff AddSemiconjBy.neg_symm_left_iff

@[to_additive]
theorem inv_symm_left : SemiconjBy a x y → SemiconjBy a⁻¹ y x :=
  inv_symm_left_iff.2
#align semiconj_by.inv_symm_left SemiconjBy.inv_symm_left
#align add_semiconj_by.neg_symm_left AddSemiconjBy.neg_symm_left

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_self, mul_one]
#align semiconj_by.conj_mk SemiconjBy.conj_mk
#align add_semiconj_by.conj_mk AddSemiconjBy.conj_mk

end Group

end SemiconjBy

@[to_additive (attr := simp) addSemiconjBy_iff_eq]
theorem semiconjBy_iff_eq [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x = y :=
  ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩
#align semiconj_by_iff_eq semiconjBy_iff_eq
#align add_semiconj_by_iff_eq addSemiconjBy_iff_eq

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive AddUnits.mk_addSemiconjBy "`a` semiconjugates `x` to `a + x + -a`."]
theorem Units.mk_semiconjBy [Monoid M] (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]
#align units.mk_semiconj_by Units.mk_semiconjBy
#align add_units.mk_semiconj_by AddUnits.mk_addSemiconjBy
