/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Basic

#align_import algebra.group.semiconj from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Lemmas about semiconjugate elements of a semigroup

-/

set_option autoImplicit true

namespace SemiconjBy

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

end SemiconjBy
