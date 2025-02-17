/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Tensor products of Hopf algebras

We define the Hopf algebra instance on the tensor product of two Hopf algebras.

-/

universe u
namespace TensorProduct
variable {R A B : Type u} [CommRing R] [Ring A] [Ring B] [HopfAlgebra R A] [HopfAlgebra R B]

open HopfAlgebra

noncomputable instance instHopfAlgebra : HopfAlgebra R (A ⊗[R] B) :=
  { antipode := map antipode antipode
    mul_antipode_rTensor_comul := by
      simp only [instCoalgebraStruct_comul, instCoalgebraStruct_counit, LinearMap.rTensor_def,
        ← map_id, ← LinearMap.comp_assoc (map _ _), ← tensorTensorTensorComm_comp_map,
        Algebra.mul'_comp_tensorTensorTensorComm, ← map_comp]
      simp only [← LinearMap.rTensor_def, LinearMap.comp_assoc, mul_antipode_rTensor_comul,
        map_comp, Algebra.linearMap_comp_mul']
    mul_antipode_lTensor_comul := by
      simp only [instCoalgebraStruct_comul, instCoalgebraStruct_counit, LinearMap.lTensor_def,
        ← map_id, ← LinearMap.comp_assoc (map _ _), ← tensorTensorTensorComm_comp_map,
        Algebra.mul'_comp_tensorTensorTensorComm, ← map_comp]
      simp only [← LinearMap.lTensor_def, LinearMap.comp_assoc, mul_antipode_lTensor_comul,
        map_comp, Algebra.linearMap_comp_mul'] }

@[simp]
theorem antipode_def :
    HopfAlgebra.antipode (R := R) (A := A ⊗[R] B) = map antipode antipode := rfl

end TensorProduct
