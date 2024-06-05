/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Algebra.Module.Defs

#align_import algebra.ring.add_aut from "leanprover-community/mathlib"@"a437a2499163d85d670479f69f625f461cc5fef9"

/-!
# Multiplication on the left/right as additive automorphisms

In this file we define `AddAut.mulLeft` and `AddAut.mulRight`.

See also `AddMonoidHom.mulLeft`, `AddMonoidHom.mulRight`, `AddMonoid.End.mulLeft`, and
`AddMonoid.End.mulRight` for multiplication by `R` as an endomorphism instead of multiplication by
`Rˣ` as an automorphism.
-/


namespace AddAut

variable {R : Type*} [Semiring R]

/-- Left multiplication by a unit of a semiring as an additive automorphism. -/
@[simps! (config := { simpRhs := true })]
def mulLeft : Rˣ →* AddAut R :=
  DistribMulAction.toAddAut _ _
#align add_aut.mul_left AddAut.mulLeft
#align add_aut.mul_left_apply_apply AddAut.mulLeft_apply_apply
#align add_aut.mul_left_apply_symm_apply AddAut.mulLeft_apply_symm_apply

/-- Right multiplication by a unit of a semiring as an additive automorphism. -/
def mulRight (u : Rˣ) : AddAut R :=
  DistribMulAction.toAddAut Rᵐᵒᵖˣ R (Units.opEquiv.symm <| MulOpposite.op u)
#align add_aut.mul_right AddAut.mulRight

@[simp]
theorem mulRight_apply (u : Rˣ) (x : R) : mulRight u x = x * u :=
  rfl
#align add_aut.mul_right_apply AddAut.mulRight_apply

@[simp]
theorem mulRight_symm_apply (u : Rˣ) (x : R) : (mulRight u).symm x = x * u⁻¹ :=
  rfl
#align add_aut.mul_right_symm_apply AddAut.mulRight_symm_apply

end AddAut
