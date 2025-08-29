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

namespace unitary
variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

variable (S R) in
/-- Each unitary element `u` defines a ⋆-algebra automorphism such that
`x ↦ u * x * star u`.

This is the ⋆-algebra automorphism version of a specialized version of
`MulSemiringAction.toAlgAut`. -/
def toStarAlgAut : (unitary R) →* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
    map_smul' _ _ := smul_comm _ _ _ |>.symm
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

@[simp]
theorem toStarAlgAut_apply (u : unitary R) (x : R) :
    toStarAlgAut S R u x = u * x * (star u : R) := rfl

@[simp]
theorem toStarAlgAut_symm_apply (u : unitary R) (x : R) :
    (toStarAlgAut S R u).symm x = (star u : R) * x * u := rfl

@[simp]
theorem toStarAlgAut_trans_toStarAlgAut (u₁ u₂ : unitary R) :
    (toStarAlgAut S R u₁).trans (toStarAlgAut S R u₂) = toStarAlgAut S R (u₂ * u₁) :=
  map_mul _ _ _ |>.symm

theorem toStarAlgAut_symm (u : unitary R) :
    (toStarAlgAut S R u).symm = toStarAlgAut S R (star u) := by
  ext; simp

theorem toRingEquiv_toStarAlgAut (u : unitary R) :
    (toStarAlgAut S R u).toRingEquiv = MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

end unitary
