/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary

/-!
# The ⋆-algebra automorphism given by a unitary element

This file defines the ⋆-algebra automorphism on `R` given by a unitary `u`,
which is `Unitary.conjStarAlgAut S R u`, defined to be `x ↦ u * x * star u`.
-/

namespace Unitary
variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

variable (S R) in
/-- Each unitary element `u` defines a ⋆-algebra automorphism such that
`x ↦ u * x * star u`.

This is the ⋆-algebra automorphism version of a specialized version of
`MulSemiringAction.toAlgAut`. -/
def conjStarAlgAut : unitary R →* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
    map_smul' _ _ := smul_comm _ _ _ |>.symm
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

@[simp]
theorem conjStarAlgAut_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R u x = u * x * (star u : R) := rfl

@[simp]
theorem conjStarAlgAut_symm_apply (u : unitary R) (x : R) :
    (conjStarAlgAut S R u).symm x = (star u : R) * x * u := rfl

theorem conjStarAlgAut_trans_toStarAlgAut (u₁ u₂ : unitary R) :
    (conjStarAlgAut S R u₁).trans (conjStarAlgAut S R u₂) = conjStarAlgAut S R (u₂ * u₁) :=
  map_mul _ _ _ |>.symm

theorem conjStarAlgAut_symm (u : unitary R) :
    (conjStarAlgAut S R u).symm = conjStarAlgAut S R (star u) := by
  ext; simp

theorem toRingEquiv_conjStarAlgAut (u : unitary R) :
    (conjStarAlgAut S R u).toRingEquiv
    = MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

theorem toAlgEquiv_conjStarAlgAut {S : Type*} [CommSemiring S] [Algebra S R] (u : unitary R) :
    (conjStarAlgAut S R u).toAlgEquiv
    = MulSemiringAction.toAlgEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

end Unitary
