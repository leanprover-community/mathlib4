/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat

/-!
# The monoidal category structure on quadratic R-modules
-/

open CategoryTheory

universe v u

variable (R : Type u) [CommRing R]

namespace QuadraticModuleCat

instance : MonoidalCategory (QuadraticModuleCat.{v} R) :=
  Monoidal.induced
    (F := forget₂ (QuadraticModuleCat R) (ModuleCat R))
    (tensorObj := fun X Y => of (X.form.tmul Y.form))
    (μIsoSymm := fun X Y => eqToIso rfl)
    (whiskerLeft := fun X _ _ f ↦ X.1 ◁ f)
    (whiskerRight := @fun X₁ X₂ (f : X₁.1 ⟶ X₂.1) Y ↦ (f ▷ Y.1 :))
    (tensorHom := fun f g => f ⊗ g)
    (tensorUnit' := _)
    (εIsoSymm := eqToIso rfl)
    (associator := fun X Y Z => _)
    (leftUnitor := fun X => _)
    (rightUnitor := fun X => _)
