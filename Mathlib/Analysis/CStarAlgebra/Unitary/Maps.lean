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
noncomputable def mulLeftLinearIsometryEquiv : unitary A →* A ≃ₗᵢ[R] A where
  toFun u :=
    { toLinearMap := LinearMap.mulLeft R (u : A)
      invFun := LinearMap.mulLeft R (star u : A)
      left_inv _ := by simp [← mul_assoc]
      right_inv _ := by simp [← mul_assoc]
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

variable (R) in
@[simp] lemma mulLeftLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    mulLeftLinearIsometryEquiv R A u x = u * x := rfl

variable (R) in
lemma symm_mulLeftLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    (mulLeftLinearIsometryEquiv R A u).symm x = star u * x := rfl

@[simp] lemma symm_mulLeftLinearIsometryEquiv (u : unitary A) :
    (mulLeftLinearIsometryEquiv R A u).symm = mulLeftLinearIsometryEquiv R A (star u) := by ext; rfl

lemma mulLeftLinearIsometryEquiv_trans_mulLeftLinearIsometryEquiv (u v : unitary A) :
    (mulLeftLinearIsometryEquiv R A u).trans (mulLeftLinearIsometryEquiv R A v) =
      mulLeftLinearIsometryEquiv R A (v * u) := map_mul _ _ _ |>.symm

lemma mulLeftLinearIsometryEquiv_mul_apply (u v : unitary A) (x : A) :
    mulLeftLinearIsometryEquiv R A (u * v) x =
      mulLeftLinearIsometryEquiv R A u (mulLeftLinearIsometryEquiv R A v x) := by simp

@[simp] lemma toLinearMap_mulLeftLinearIsometryEquiv (u : unitary A) :
    (mulLeftLinearIsometryEquiv R A u).toLinearMap = LinearMap.mulLeft R (u : A) := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R A) in
/-- Right multiplication by a unitary as a linear isometric equivalence. -/
noncomputable def mulRightLinearIsometryEquiv (u : unitary A) : A ≃ₗᵢ[R] A where
  toLinearMap := LinearMap.mulRight R (u : A)
  invFun := LinearMap.mulRight R (star u : A)
  left_inv _ := by simp [mul_assoc]
  right_inv _ := by simp [mul_assoc]
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

variable (R) in
@[simp] lemma mulRightLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    mulRightLinearIsometryEquiv R A u x = x * u := rfl

variable (R) in
lemma symm_mulRightLinearIsometryEquiv_apply (u : unitary A) (x : A) :
    (mulRightLinearIsometryEquiv R A u).symm x = x * star u := rfl

@[simp] lemma symm_mulRightLinearIsometryEquiv (u : unitary A) :
    (mulRightLinearIsometryEquiv R A u).symm = mulRightLinearIsometryEquiv R A (star u) := by
  ext; rfl

lemma mulRightLinearIsometryEquiv_trans_mulRightLinearIsometryEquiv (u v : unitary A) :
    (mulRightLinearIsometryEquiv R A u).trans (mulRightLinearIsometryEquiv R A v) =
      mulRightLinearIsometryEquiv R A (u * v) := by ext; simp [mul_assoc]

lemma mulRightLinearIsometryEquiv_mul_apply (u v : unitary A) (x : A) :
    mulRightLinearIsometryEquiv R A (u * v) x =
      mulRightLinearIsometryEquiv R A v (mulRightLinearIsometryEquiv R A u x) := by simp [mul_assoc]

@[simp] lemma toLinearMap_mulRightLinearIsometryEquiv (u : unitary A) :
    (mulRightLinearIsometryEquiv R A u).toLinearMap = LinearMap.mulRight R (u : A) := rfl

@[simp] lemma mulRightLinearIsometryEquiv_one : mulRightLinearIsometryEquiv R A 1 = .refl R A := by
  ext; simp

end mulRight

end Unitary
