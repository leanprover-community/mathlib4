/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# MulOpposite of coalgebras

Suppose `R` is a commutative semiring, and `A` is an `R`-coalgebra,
then `Aᵐᵒᵖ` is an `R`-coalgebra, where we define the comultiplication and counit maps naturally.
-/

namespace MulOpposite

open scoped TensorProduct

open TensorProduct Coalgebra LinearMap

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

noncomputable instance [CoalgebraStruct R A] : CoalgebraStruct R Aᵐᵒᵖ where
  comul := map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
    comul ∘ₗ (opLinearEquiv R).symm.toLinearMap
  counit := counit ∘ₗ (opLinearEquiv R).symm.toLinearMap

lemma comul_def [CoalgebraStruct R A] :
    comul (R := R) (A := Aᵐᵒᵖ) = map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
      comul ∘ₗ (opLinearEquiv R).symm.toLinearMap := rfl

lemma counit_def [CoalgebraStruct R A] :
    counit (R := R) (A := Aᵐᵒᵖ) = counit ∘ₗ (opLinearEquiv R).symm.toLinearMap := rfl

noncomputable instance [Coalgebra R A] : Coalgebra R Aᵐᵒᵖ where
  coassoc := ext fun _ => by
    rw [comul_def, rTensor_comp, rTensor_comp]
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, lTensor_map, rTensor_def]
    simp_rw [← map_map_assoc, map_map, comp_assoc, ← lTensor_comp_rTensor]
    simp [lTensor_tensor, comp_assoc]
  rTensor_counit_comp_comul := ext fun _ => by
    simp only [counit_def, comul_def, coe_comp, Function.comp_apply, rTensor_map, comp_assoc]
    simp [← lTensor_comp_rTensor]
  lTensor_counit_comp_comul := ext fun _ => by
    simp only [counit_def, comul_def, coe_comp, Function.comp_apply, lTensor_map, comp_assoc]
    simp [← rTensor_comp_lTensor]

end MulOpposite
