/-
Copyright (c) 2026 Jon Bannon, Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic

/-! # Unitary maps in C⋆-algebras

This file defines some basic maps by unitaries in C⋆-algebras. -/

@[expose] public section

namespace Unitary
variable {R A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Ring R] [Module R A]

section mulLeft
variable [SMulCommClass R A A]

variable (R A) in
/-- Left multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulLeft : unitary A →* A ≃ₗᵢ[R] A where
  toFun u :=
    { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

variable (R) in
@[simp] lemma mulLeft_apply (u : unitary A) (x : A) :
    mulLeft R A u x = u * x := rfl

variable (R) in
lemma symm_mulLeft_apply (u : unitary A) (x : A) :
    (mulLeft R A u).symm x = (star u : A) * x := rfl

@[simp] lemma symm_mulLeft (u : unitary A) :
    (mulLeft R A u).symm = mulLeft R A (star u) := by ext; rfl

lemma mulLeft_trans_mulLeft (u v : unitary A) :
    (mulLeft R A u).trans (mulLeft R A v) = mulLeft R A (v * u) := map_mul _ _ _ |>.symm

lemma mulLeft_mul_apply (u v : unitary A) (x : A) :
    mulLeft R A (u * v) x = mulLeft R A u (mulLeft R A v x) := by simp

@[simp] lemma toLinearEquiv_mulLeft (u : unitary A) :
    (mulLeft R A u).toLinearMap = (toUnits u).mulLeftLinearEquiv R A := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R) in
/-- Right multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulRight (u : unitary A) : A ≃ₗᵢ[R] A where
  toLinearEquiv := (toUnits u).mulRightLinearEquiv R
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

variable (R) in
@[simp] lemma mulRight_apply (u : unitary A) (x : A) :
    mulRight R u x = x * u := rfl

variable (R) in
lemma symm_mulRight_apply (u : unitary A) (x : A) :
    (mulRight R u).symm x = x * (star u : A) := rfl

@[simp] lemma symm_mulRight (u : unitary A) :
    (mulRight R u).symm = mulRight R (star u) := by
  ext; rfl

lemma mulRight_trans_mulRight (u v : unitary A) :
    (mulRight R u).trans (mulRight R v) = mulRight R (u * v) := by ext; simp [mul_assoc]

lemma mulRight_mul_apply (u v : unitary A) (x : A) :
    mulRight R (u * v) x = mulRight R v (mulRight R u x) := by simp [mul_assoc]

@[simp] lemma toLinearMap_mulRight (u : unitary A) :
    (mulRight R u).toLinearMap = LinearMap.mulRight R (u : A) := rfl

@[simp] lemma mulRight_one : mulRight R 1 = .refl R A := by
  ext; simp

@[simp] lemma toLinearEquiv_mulRight (u : unitary A) :
    (mulRight R u).toLinearMap = (toUnits u).mulRightLinearEquiv R A := rfl

end mulRight

end Unitary
