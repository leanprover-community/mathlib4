/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-!
# MulOpposite of coalgebras

Suppose `R` is a commutative semiring, and `A` is an `R`-coalgebra,
then `Aᵐᵒᵖ` is an `R`-coalgebra, where we define the comultiplication and counit maps naturally.
-/

open scoped TensorProduct

noncomputable instance MulOpposite.coalgebraStruct
  {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] :
  CoalgebraStruct R Aᵐᵒᵖ where
  comul := (TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap) ∘ₗ
    Coalgebra.comul ∘ₗ (opLinearEquiv R).symm.toLinearMap
  counit := Coalgebra.counit ∘ₗ (opLinearEquiv R).symm.toLinearMap

lemma MulOpposite.comul_def
  {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] :
  (CoalgebraStruct.comul (R := R) (A := Aᵐᵒᵖ)) =
    (TensorProduct.map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap) ∘ₗ
      CoalgebraStruct.comul ∘ₗ (opLinearEquiv R).symm.toLinearMap :=
rfl
lemma MulOpposite.counit_def
  {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [CoalgebraStruct R A] :
  (CoalgebraStruct.counit (R := R) (A := Aᵐᵒᵖ)) =
    CoalgebraStruct.counit ∘ₗ (opLinearEquiv R).symm.toLinearMap :=
rfl

open MulOpposite TensorProduct in
private lemma coassoc_aux_1 {R A : Type*} [CommSemiring R][AddCommMonoid A] [Module R A] :
  (TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ).toLinearMap ∘ₗ
    (map (opLinearEquiv R (M:=A)).toLinearMap (opLinearEquiv R (M:=A)).toLinearMap).rTensor _
  = (map (opLinearEquiv R).toLinearMap (((opLinearEquiv R).toLinearMap.rTensor _)))
    ∘ₗ (TensorProduct.assoc R A A _).toLinearMap :=
by
    apply TensorProduct.ext_threefold
    intro x y z
    simp

open MulOpposite TensorProduct in
private lemma coassoc_aux_2 {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] :
  (opLinearEquiv R).symm.toLinearMap.rTensor _
    ∘ₗ (map (opLinearEquiv R (M:=A)).toLinearMap (opLinearEquiv R (M:=A)).toLinearMap)
  = (MulOpposite.opLinearEquiv R).toLinearMap.lTensor A :=
by
    apply TensorProduct.ext'
    intro x y
    simp

open MulOpposite TensorProduct in
private lemma coassoc_aux_3 {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] :
  (map (opLinearEquiv R (M:=A)).toLinearMap
      (((opLinearEquiv R (M:=A)).toLinearMap.rTensor Aᵐᵒᵖ)))
        ∘ₗ ((TensorProduct.assoc R A A Aᵐᵒᵖ).toLinearMap)
        ∘ₗ (opLinearEquiv R (M:=A)).toLinearMap.lTensor _
    = map (opLinearEquiv R).toLinearMap
        ((map (opLinearEquiv R).toLinearMap (opLinearEquiv R).toLinearMap))
      ∘ₗ (TensorProduct.assoc R _ _ _).toLinearMap :=
by
    apply TensorProduct.ext_threefold
    intro x y z
    simp

open CoalgebraStruct TensorProduct MulOpposite in
private lemma MulOpposite_coassoc {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Coalgebra R A] :
    (TensorProduct.assoc R Aᵐᵒᵖ Aᵐᵒᵖ Aᵐᵒᵖ) ∘ₗ
      (comul (R := R) (A := Aᵐᵒᵖ)).rTensor Aᵐᵒᵖ ∘ₗ
        (comul (R := R) (A := Aᵐᵒᵖ)) =
    (comul (R := R) (A := Aᵐᵒᵖ)).lTensor Aᵐᵒᵖ ∘ₗ
      (comul (R := R) (A := Aᵐᵒᵖ)) :=
by
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

@[instance]
noncomputable def MulOpposite.coalgebra
  {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A] :
    Coalgebra R Aᵐᵒᵖ where
  coassoc := MulOpposite_coassoc
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
