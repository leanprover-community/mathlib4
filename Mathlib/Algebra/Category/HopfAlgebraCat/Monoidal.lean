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

In `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean`, given two Hopf `R`-algebras `A, B`, we
define a Hopf `R`-algebra instance on `A ⊗[R] B`.

Here, we use this to declare a `MonoidalCategory` instance on the category of Hopf algebras, via
the existing monoidal structure on `BialgebraCat`.
-/

universe u

namespace HopfAlgebraCat
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (HopfAlgebraCat R) where
  tensorObj X Y := of R (X ⊗[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R X Y Z).toHopfAlgebraCatIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toHopfAlgebraCatIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R X).toHopfAlgebraCatIso

/-- The data needed to induce a `MonoidalCategory` structure via
`HopfAlgebraCat.instMonoidalCategoryStruct` and the forgetful functor to bialgebras. -/
@[simps]
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (HopfAlgebraCat R) (BialgebraCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
  associator_eq _ _ _ := BialgebraCat.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext <| TensorProduct.ext (by ext; rfl)
  leftUnitor_eq _ := BialgebraCat.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)
  rightUnitor_eq _ := BialgebraCat.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)

noncomputable instance instMonoidalCategory : MonoidalCategory (HopfAlgebraCat R) :=
  Monoidal.induced (forget₂ _ (BialgebraCat R)) (MonoidalCategory.inducingFunctorData R)

/-- `forget₂ (HopfAlgebraCat R) (BialgebraCat R)` is a monoidal functor. -/
noncomputable instance : (forget₂ (HopfAlgebraCat R) (BialgebraCat R)).Monoidal where

end HopfAlgebraCat
