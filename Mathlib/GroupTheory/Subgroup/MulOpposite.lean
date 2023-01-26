/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich

! This file was ported from Lean 3 source module group_theory.subgroup.mul_opposite
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.GroupTheory.Subgroup.Actions

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/


variable {G : Type _} [Group G]

namespace Subgroup

/-- A subgroup `H` of `G` determines a subgroup `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive "An additive subgroup `H` of `G` determines an additive subgroup `H.opposite` of the
 opposite additive group `Gᵃᵒᵖ`."]
def opposite : Subgroup G ≃ Subgroup Gᵐᵒᵖ
    where
  toFun H :=
    { carrier := MulOpposite.unop ⁻¹' (H : Set G)
      one_mem' := H.one_mem
      mul_mem' := fun ha hb => H.mul_mem hb ha
      inv_mem' := H.inv_mem }
  invFun H :=
    { carrier := MulOpposite.op ⁻¹' (H : Set Gᵐᵒᵖ)
      one_mem' := H.one_mem
      mul_mem' := fun ha hb => H.mul_mem hb ha
      inv_mem' := H.inv_mem }
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl
#align subgroup.opposite Subgroup.opposite
#align add_subgroup.opposite AddSubgroup.opposite

/-- Bijection between a subgroup `H` and its opposite. -/
@[to_additive "Bijection between an additive subgroup `H` and its opposite.", simps]
def oppositeEquiv (H : Subgroup G) : H ≃ opposite H :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#align subgroup.opposite_equiv Subgroup.oppositeEquiv
#align add_subgroup.opposite_equiv AddSubgroup.oppositeEquiv

@[to_additive]
instance (H : Subgroup G) [Encodable H] : Encodable (opposite H) :=
  Encodable.ofEquiv H H.oppositeEquiv.symm

@[to_additive]
instance (H : Subgroup G) [Countable H] : Countable (opposite H) :=
  Countable.of_equiv H H.oppositeEquiv

@[to_additive]
theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : opposite H) :
    h • (g * x) = g * h • x :=
  mul_assoc _ _ _
#align subgroup.smul_opposite_mul Subgroup.smul_opposite_mul
#align add_subgroup.vadd_opposite_add AddSubgroup.vadd_opposite_add

end Subgroup
