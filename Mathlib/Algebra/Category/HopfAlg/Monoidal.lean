/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.Bialg.Monoidal
import Mathlib.Algebra.Category.HopfAlg.Basic
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# The monoidal structure on the category of Hopf algebras

In `Mathlib/RingTheory/HopfAlgebra/TensorProduct.lean`, given two Hopf `R`-algebras `A, B`, we
define a Hopf `R`-algebra instance on `A ⊗[R] B`.

Here, we use this to declare a `MonoidalCategory` instance on the category of Hopf algebras, via
the existing monoidal structure on `Bialg`.
-/

universe u

namespace HopfAlg
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (HopfAlg R) where
  tensorObj X Y := of R (X ⊗[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R X Y Z).toHopfAlgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toHopfAlgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R X).toHopfAlgIso

/-- The data needed to induce a `MonoidalCategory` structure via
`HopfAlg.instMonoidalCategoryStruct` and the forgetful functor to bialgebras. -/
@[simps]
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (HopfAlg R) (Bialg R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
  associator_eq _ _ _ := Bialg.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext <| TensorProduct.ext (by ext; rfl)
  leftUnitor_eq _ := Bialg.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)
  rightUnitor_eq _ := Bialg.Hom.ext <| BialgHom.coe_linearMap_injective <|
    TensorProduct.ext (by ext; rfl)

noncomputable instance instMonoidalCategory : MonoidalCategory (HopfAlg R) :=
  Monoidal.induced (forget₂ _ (Bialg R)) (MonoidalCategory.inducingFunctorData R)

/-- `forget₂ (HopfAlg R) (Bialg R)` is a monoidal functor. -/
noncomputable instance : (forget₂ (HopfAlg R) (Bialg R)).Monoidal where

end HopfAlg
