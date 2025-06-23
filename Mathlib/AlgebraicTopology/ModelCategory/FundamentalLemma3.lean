/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma2

/-!
# The fundamental lemma of homotopical algebra

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category C] [ModelCategory C] {H : Type*} [Category H]
  (L : C ⥤ H) [L.IsLocalization (weakEquivalences _)]
  {X Y : C}

def leftHomotopyClassToHom : LeftHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ (factorsThroughLocalization_leftHomotopyRel h).map_eq _)

@[simp]
lemma leftHomotopyClassToHom_mk (f : X ⟶ Y) :
    leftHomotopyClassToHom L (.mk f) = L.map f := rfl

def rightHomotopyClassToHom : RightHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ (factorsThroughLocalization_rightHomotopyRel h).map_eq _)

@[simp]
lemma rightHomotopyClassToHom_mk (f : X ⟶ Y) :
    rightHomotopyClassToHom L (.mk f) = L.map f := rfl

section

variable [IsCofibrant X] [IsFibrant Y]

def leftHomotopyClassEquivRightHomotopyClass :
    LeftHomotopyClass X Y ≃ RightHomotopyClass X Y where
  toFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    dsimp
    rw [RightHomotopyClass.mk_eq_mk_iff]
    exact h.rightHomotopyRel)
  invFun := Quot.lift (fun f ↦ .mk f) (fun _ _ h ↦ by
    dsimp
    rw [LeftHomotopyClass.mk_eq_mk_iff]
    exact h.leftHomotopyRel)
  left_inv := by rintro ⟨f⟩; rfl
  right_inv := by rintro ⟨f⟩; rfl

@[simp]
lemma leftHomotopyClassEquivRightHomotopyClass_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass (.mk f) = .mk f := rfl

@[simp]
lemma leftHomotopyClassEquivRightHomotopyClass_symm_mk (f : X ⟶ Y) :
    leftHomotopyClassEquivRightHomotopyClass.symm (.mk f) = .mk f := rfl

end

lemma bijective_leftHomotopyClassToHom [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (leftHomotopyClassToHom L : LeftHomotopyClass X Y → _) := by
  sorry

lemma bijective_rightHomotopyClassToHom [IsCofibrant X] [IsFibrant Y] :
    Function.Bijective (rightHomotopyClassToHom L : RightHomotopyClass X Y → _) := by
  sorry

end HomotopicalAlgebra
