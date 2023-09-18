/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries

/-!
# The monoidal category structure on quadratic R-modules
-/

open CategoryTheory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

namespace instMonoidalCategory

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
def tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R :=
  of (X.form.tmul Y.form)

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
def tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ⟨(f.toIsometry.tmul g.toIsometry :)⟩

/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
def tensorUnit : QuadraticModuleCat.{u} R := of (sq (R := R))

set_option maxHeartbeats 3200000 in
/-- Auxiliary definition used to fight a tmieout when building
`QuadraticModuleCat.instMonoidalCategory`. -/
def associator (X Y Z : QuadraticModuleCat.{u} R) :
    tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z) := by
  refine ofIso ?_
  dsimp
  have := tensorAssoc X.form Y.form Z.form
  exact this
#check MonoidalCategory.associator

end instMonoidalCategory

count_heartbeats in
instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (F := forget₂ (QuadraticModuleCat R) (ModuleCat R))
    (tensorObj := instMonoidalCategory.tensorObj)
    (μIsoSymm := fun X Y => eqToIso rfl)
    (whiskerLeft := fun X _ _ f => tensorHom (𝟙 _) f)
    -- (whiskerLeft_eq := sorry)
    (whiskerRight := @fun X₁ X₂ (f : X₁ ⟶ X₂) Y => tensorHom f (𝟙 _))
    -- (whiskerRight_eq := sorry)
    (tensorHom := tensorHom)
    -- (tensorHom_eq := sorry)
    (tensorUnit' := tensorUnit)
    (εIsoSymm := eqToIso rfl)
    (associator := associator)
    -- (associator_eq := sorry)
    (leftUnitor := fun X => ofIso (tensorLId X.form))
    -- (leftUnitor_eq := sorry)
    (rightUnitor := fun X => ofIso (tensorRId X.form))
    -- (rightUnitor_eq := sorry)

end QuadraticModuleCat
