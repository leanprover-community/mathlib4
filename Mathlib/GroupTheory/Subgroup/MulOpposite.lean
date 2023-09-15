/-
Copyright (c) 2022 Alex Kontorovich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich
-/
import Mathlib.GroupTheory.Subgroup.Actions

#align_import group_theory.subgroup.mul_opposite from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

/-!
# Mul-opposite subgroups

## Tags
subgroup, subgroups

-/


variable {G : Type*} [Group G]
variable {M : Type*} [MulOneClass M]

namespace Submonoid


/-- pull a submonoid back to an opposite submonoid along `unop`-/
@[to_additive (attr := simps)]
def op {M : Type*} [MulOneClass M] (x : Submonoid M) : Submonoid (MulOpposite M) where
  carrier := MulOpposite.unop ⁻¹' x.1
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_preimage, MulOpposite.unop_mul, SetLike.mem_coe] at ha hb ⊢
    exact mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

/-- pull an opposite submonoid back to a submonoid along `op`-/
@[to_additive (attr := simps)]
def unop {M : Type*} [MulOneClass M] (x : Submonoid (MulOpposite M)) : Submonoid M where
  carrier := MulOpposite.op ⁻¹' x.1
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_preimage, MulOpposite.unop_mul, SetLike.mem_coe] at ha hb ⊢
    exact mul_mem hb ha
  one_mem' := Submonoid.one_mem' _

/-- A submonoid `H` of `G` determines a submonoid `H.opposite` of the opposite group `Gᵐᵒᵖ`. -/
@[to_additive (attr := simps) "A additive submonoid `H` of `G` determines an additive submonoid
`H.opposite` of the opposite group `Gᵐᵒᵖ`."]
def opposite : Submonoid M ≃ Submonoid Mᵐᵒᵖ where
  toFun := op
  invFun := unop
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl

/-- Bijection between a submonoid `H` and its opposite. -/
@[to_additive (attr := simps!) "Bijection between an additive submonoid `H` and its opposite."]
def oppositeEquiv (H : Submonoid M) : H ≃ opposite H :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl

@[to_additive]
instance (H : Submonoid M) [Encodable H] : Encodable (opposite H) :=
  Encodable.ofEquiv H H.oppositeEquiv.symm

@[to_additive]
instance (H : Submonoid M) [Countable H] : Countable (opposite H) :=
  Countable.of_equiv H H.oppositeEquiv

end Submonoid

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
@[to_additive (attr := simps!) "Bijection between an additive subgroup `H` and its opposite."]
def oppositeEquiv (H : Subgroup G) : H ≃ opposite H :=
  MulOpposite.opEquiv.subtypeEquiv fun _ => Iff.rfl
#align subgroup.opposite_equiv Subgroup.oppositeEquiv
#align add_subgroup.opposite_equiv AddSubgroup.oppositeEquiv
#align subgroup.opposite_equiv_symm_apply_coe Subgroup.oppositeEquiv_symm_apply_coe

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
