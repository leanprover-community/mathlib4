/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Equiv
import Mathlib.GroupTheory.GroupAction.Opposite

#align_import algebra.module.opposites from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`GroupTheory.GroupAction.Opposite`.
-/


namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- `MulOpposite.distribMulAction` extends to a `Module` -/
instance instModule : Module R Mᵐᵒᵖ where
  add_smul _ _ _ := unop_injective <| add_smul _ _ _
  zero_smul _ := unop_injective <| zero_smul _ _

/-- The function `op` is a linear equivalence. -/
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }
#align mul_opposite.op_linear_equiv MulOpposite.opLinearEquiv

@[simp]
theorem coe_opLinearEquiv : (opLinearEquiv R : M → Mᵐᵒᵖ) = op :=
  rfl
#align mul_opposite.coe_op_linear_equiv MulOpposite.coe_opLinearEquiv

@[simp]
theorem coe_opLinearEquiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ → M) = unop :=
  rfl
#align mul_opposite.coe_op_linear_equiv_symm MulOpposite.coe_opLinearEquiv_symm

@[simp]
theorem coe_opLinearEquiv_toLinearMap : ((opLinearEquiv R).toLinearMap : M → Mᵐᵒᵖ) = op :=
  rfl
#align mul_opposite.coe_op_linear_equiv_to_linear_map MulOpposite.coe_opLinearEquiv_toLinearMap

@[simp]
theorem coe_opLinearEquiv_symm_toLinearMap :
    ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ → M) = unop :=
  rfl
#align mul_opposite.coe_op_linear_equiv_symm_to_linear_map MulOpposite.coe_opLinearEquiv_symm_toLinearMap

-- Porting note: LHS simplifies; added new simp lemma below @[simp]
theorem opLinearEquiv_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv :=
  rfl
#align mul_opposite.op_linear_equiv_to_add_equiv MulOpposite.opLinearEquiv_toAddEquiv

@[simp]
theorem coe_opLinearEquiv_addEquiv : ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv :=
  rfl

-- Porting note: LHS simplifies; added new simp lemma below @[simp]
theorem opLinearEquiv_symm_toAddEquiv :
    (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl
#align mul_opposite.op_linear_equiv_symm_to_add_equiv MulOpposite.opLinearEquiv_symm_toAddEquiv

@[simp]
theorem coe_opLinearEquiv_symm_addEquiv :
    ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm : Mᵐᵒᵖ ≃+ M) = opAddEquiv.symm :=
  rfl

end MulOpposite
