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

variable (R : Type u) [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticForm

instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (F := forget₂ (QuadraticModuleCat R) (ModuleCat R))
    (tensorObj := fun X Y => of (X.form.tmul Y.form))
    (μIsoSymm := fun X Y => eqToIso rfl)
    (whiskerLeft := fun X _ _ f => ⟨(Isometry.id X.form).tmul f.toIsometry⟩)
    (whiskerLeft_eq := sorry)
    (whiskerRight := @fun X₁ X₂ (f : X₁ ⟶ X₂) Y => ⟨f.toIsometry.tmul (Isometry.id Y.form)⟩)
    (whiskerRight_eq := sorry)
    (tensorHom := fun f g => ⟨f.toIsometry.tmul g.toIsometry⟩)
    (tensorHom_eq := sorry)
    (tensorUnit' := of (sq (R := R)))
    (εIsoSymm := eqToIso rfl)
    (associator := fun X Y Z => ofIso (tensorAssoc X.form Y.form Z.form))
    (associator_eq := sorry)
    (leftUnitor := fun X => ofIso (tensorLId X.form))
    (leftUnitor_eq := sorry)
    (rightUnitor := fun X => ofIso (tensorRId X.form))
    (rightUnitor_eq := sorry)

end QuadraticModuleCat
