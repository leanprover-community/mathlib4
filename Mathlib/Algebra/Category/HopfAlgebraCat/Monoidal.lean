/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.Algebra.Category.BialgebraCat.Monoidal
import Mathlib.Algebra.Category.HopfAlgebraCat.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# The monoidal structure on the category of Hopf algebras

In `Mathlib.RingTheory.HopfAlgebra.TensorProduct`, given two Hopf `R`-algebras `A, B`, we define a
Hopf `R`-algebra instance on `A ⊗[R] B`.

Here, we use this to declare a `MonoidalCategory` instance on the category of Hopf algebras, via
the existing monoidal structure on `BialgebraCat`.

-/

universe v u

namespace HopfAlgebraCat
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (HopfAlgebraCat R) where
  tensorObj := fun X Y => HopfAlgebraCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => HopfAlgebraCat.ofHom (f.lTensor X)
  whiskerRight := fun f X => HopfAlgebraCat.ofHom (f.rTensor X)
  tensorHom := fun f g => HopfAlgebraCat.ofHom (Bialgebra.TensorProduct.map f g)
  tensorUnit := HopfAlgebraCat.of R R
  associator := fun X Y Z => (Bialgebra.TensorProduct.assoc R X Y Z).toHopfAlgebraIso
  leftUnitor := fun X => (Bialgebra.TensorProduct.lid R X).toHopfAlgebraIso
  rightUnitor := fun X => (Bialgebra.TensorProduct.rid R X).toHopfAlgebraIso

/-- The data needed to induce a `MonoidalCategory` structure via
`HopfAlgebraCat.instMonoidalCategoryStruct` and the forgetful functor to bialgebras. -/
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (HopfAlgebraCat R) (BialgebraCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => BialgHom.coe_linearMap_injective <|
    TensorProduct.ext <| TensorProduct.ext (by ext; rfl)
  leftUnitor_eq := fun X => BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)
  rightUnitor_eq := fun X => BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)

noncomputable instance instMonoidalCategory : MonoidalCategory (HopfAlgebraCat R) :=
  Monoidal.induced (forget₂ _ (BialgebraCat R)) (MonoidalCategory.inducingFunctorData R)

end HopfAlgebraCat
