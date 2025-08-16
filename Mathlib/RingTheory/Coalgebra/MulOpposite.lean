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

open TensorProduct Coalgebra

variable {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

noncomputable instance [CoalgebraStruct R A] :
    CoalgebraStruct R Aᵐᵒᵖ where
  comul := map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap ∘ₗ
    comul ∘ₗ (opLinearEquiv R).symm.toLinearMap
  counit := counit ∘ₗ (opLinearEquiv R).symm.toLinearMap

lemma comul_def [CoalgebraStruct R A] :
    comul (R := R) (A := Aᵐᵒᵖ) = map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap
      ∘ₗ comul ∘ₗ (opLinearEquiv R).symm.toLinearMap := rfl

lemma counit_def [CoalgebraStruct R A] :
    counit (R := R) (A := Aᵐᵒᵖ) = counit ∘ₗ (opLinearEquiv R).symm.toLinearMap := rfl

private lemma coassoc_aux_1 :
    TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ ∘ₗ
      (map (opLinearEquiv R (M:=A)).toLinearMap (opLinearEquiv R (M:=A)).toLinearMap).rTensor _
    = map (opLinearEquiv R).toLinearMap ((opLinearEquiv R).toLinearMap.rTensor _)
      ∘ₗ (TensorProduct.assoc R A A Aᵐᵒᵖ).toLinearMap := by
  apply TensorProduct.ext_threefold
  simp

private lemma coassoc_aux_2 :
    (opLinearEquiv R).symm.toLinearMap.rTensor _
      ∘ₗ map (opLinearEquiv R (M:=A)).toLinearMap (opLinearEquiv R (M:=A)).toLinearMap
    = (MulOpposite.opLinearEquiv R).toLinearMap.lTensor A := by
  apply TensorProduct.ext'
  simp

private lemma coassoc_aux_3 :
    map (opLinearEquiv R (M:=A)).toLinearMap
      ((opLinearEquiv R (M:=A)).toLinearMap.rTensor Aᵐᵒᵖ)
        ∘ₗ (TensorProduct.assoc R A A Aᵐᵒᵖ).toLinearMap
        ∘ₗ (opLinearEquiv R (M:=A)).toLinearMap.lTensor _
    = map (opLinearEquiv R).toLinearMap
        (map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap)
      ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap := by
  apply TensorProduct.ext_threefold
  simp

noncomputable instance [Coalgebra R A] :
    Coalgebra R Aᵐᵒᵖ where
  coassoc := by
    simp_rw [comul_def, LinearMap.rTensor_comp, ← LinearMap.comp_assoc, coassoc_aux_1]
    nth_rw 5 [LinearMap.comp_assoc]
    nth_rw 3 [LinearMap.comp_assoc]
    rw [coassoc_aux_2]
    nth_rw 3 [LinearMap.comp_assoc]
    nth_rw 3 [LinearMap.comp_assoc]
    rw [LinearMap.rTensor_comp_lTensor]
    nth_rw 2 [← LinearMap.lTensor_comp_rTensor]
    simp only [← LinearMap.comp_assoc]
    nth_rw 4 [LinearMap.comp_assoc]
    rw [coassoc_aux_3]
    nth_rw 3 [LinearMap.comp_assoc]
    nth_rw 2 [LinearMap.comp_assoc]
    nth_rw 2 [LinearMap.comp_assoc]
    rw [Coalgebra.coassoc]
    simp only [LinearMap.comp_assoc, LinearMap.lTensor_comp_map, LinearEquiv.symm_comp,
      LinearMap.comp_id]
    simp only [← LinearMap.comp_assoc, LinearMap.map_comp_lTensor]
  rTensor_counit_comp_comul := by
    rw [comul_def, counit_def, ← LinearMap.comp_assoc,
      LinearMap.rTensor_comp_map, LinearMap.comp_assoc,
      LinearEquiv.symm_comp, LinearMap.comp_id,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc]
    nth_rw 2 [← LinearMap.comp_assoc]
    rw [Coalgebra.rTensor_counit_comp_comul]
    rfl
  lTensor_counit_comp_comul := by
    rw [comul_def, counit_def, ← LinearMap.comp_assoc,
      LinearMap.lTensor_comp_map, LinearMap.comp_assoc,
      LinearEquiv.symm_comp, LinearMap.comp_id,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc]
    nth_rw 2 [← LinearMap.comp_assoc]
    rw [Coalgebra.lTensor_counit_comp_comul]
    rfl

end MulOpposite
