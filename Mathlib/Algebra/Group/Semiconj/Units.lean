/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import Mathlib.Algebra.Group.Semiconj.Defs
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

namespace SemiconjBy

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

end Monoid

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

end Group

end SemiconjBy

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive AddUnits.mk_addSemiconjBy "`a` semiconjugates `x` to `a + x + -a`."]
theorem Units.mk_semiconjBy [Monoid M] (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]
#align units.mk_semiconj_by Units.mk_semiconjBy
#align add_units.mk_semiconj_by AddUnits.mk_addSemiconjBy
