/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Semiconj.Basic

#align_import algebra.group.commute from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Additional lemmas about commuting pairs of elements in monoids

-/


variable {G : Type*}

namespace Commute

section DivisionMonoid

variable [DivisionMonoid G] {a b c d: G}

@[to_additive]
protected theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm

@[to_additive (attr := simp)]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff

@[to_additive]
protected theorem div_mul_div_comm (hbd : Commute b d) (hbc : Commute b⁻¹ c) :
    a / b * (c / d) = a * c / (b * d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]

@[to_additive]
protected theorem mul_div_mul_comm (hcd : Commute c d) (hbc : Commute b c⁻¹) :
    a * b / (c * d) = a / c * (b / d) :=
  (hcd.div_mul_div_comm hbc.symm).symm

@[to_additive]
protected theorem div_div_div_comm (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d) :
    a / b / (c / d) = a / c / (b / d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]

end DivisionMonoid

end Commute
