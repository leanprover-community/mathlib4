/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary

/-!
# The ⋆-algebra automorphism given by a unitary

This file defines the ⋆-algebra automorphism on `R` given by a unitary `u` such that
`x ↦ u * x * star u`.
-/

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

variable (S R) in
/-- Each unitary element `u` defines a ⋆-algebra automorphism such that
`x ↦ u * x * star u`.

This is the ⋆-algebra automorphism version of a specialized version of
`MulSemiringAction.toRingEquiv` (see `unitary.toRingEquiv_toStarAlgAut`). -/
@[simps]
def unitary.toStarAlgAut : (unitary R) →* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toFun x := u * x * (star u : R)
    invFun x := (star u : R) * x * u
    left_inv _ := by simp [← mul_assoc, mul_assoc _ _ (u : R)]
    right_inv _ := by simp [← mul_assoc, mul_assoc _ _ (star u : R)]
    map_add' _ _ := by simp [mul_add, add_mul]
    map_smul' _ _ := by simp [mul_smul_comm, smul_mul_assoc]
    map_mul' _ _ := by simp [mul_assoc _ (star u : R), ← mul_assoc (star u : R), mul_assoc]
    map_star' _ := by simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [StarAlgEquiv.aut_mul, mul_assoc]

@[simp]
theorem unitary.toStarAlgAut_trans_toStarAlgAut (u₁ u₂ : unitary R) :
    (toStarAlgAut S R u₁).trans (toStarAlgAut S R u₂) = toStarAlgAut S R (u₂ * u₁) :=
  map_mul _ _ _ |>.symm

theorem unitary.toStarAlgAut_conj_symm (u : unitary R) :
    (toStarAlgAut S R u).symm = toStarAlgAut S R (star u) := by
  ext; simp

@[simp]
theorem unitary.toRingEquiv_toStarAlgAut (u : unitary R) :
    (toStarAlgAut S R u).toRingEquiv =
      MulSemiringAction.toRingEquiv (ConjAct Rˣ) R (toUnits u) :=
  rfl
