/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.AlgebraCat.Monoidal
import Mathlib.Algebra.Category.BialgebraCat.Basic
import Mathlib.Algebra.Category.CoalgebraCat.Monoidal
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The monoidal structure on the category of bialgebras

In `Mathlib.RingTheory.Bialgebra.TensorProduct`, given two `R`-bialgebras `A, B`, we define a
bialgebra instance on `A ⊗[R] B` as well as the tensor product of two `BialgHom`s as a
`BialgHom`, and the associator and left/right unitors for bialgebras as `BialgEquiv`s.
In this file, we declare a `MonoidalCategory` instance on the category of bialgebras, with data
fields given by the definitions in `Mathlib.RingTheory.Bialgebra.TensorProduct`, and Prop
fields proved by pulling back the `MonoidalCategory` instance on the category of algebras,
using `Monoidal.induced`.

-/

universe u

namespace BialgebraCat
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

@[simps]
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (BialgebraCat R) where
  tensorObj X Y := of R (X ⊗[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R X Y Z).toBialgebraCatIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toBialgebraCatIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R X).toBialgebraCatIso

/-- The data needed to induce a `MonoidalCategory` structure via
`BialgebraCat.instMonoidalCategoryStruct` and the forgetful functor to algebras. -/
@[simps]
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (BialgebraCat R) (AlgebraCat R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
  associator_eq _ _ _ := AlgebraCat.hom_ext _ <| Algebra.TensorProduct.ext
    (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
  leftUnitor_eq _ := AlgebraCat.hom_ext _ <| Algebra.TensorProduct.ext rfl (by ext; rfl)
  rightUnitor_eq _ := AlgebraCat.hom_ext _ <| Algebra.TensorProduct.ext (by ext; rfl) rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (BialgebraCat R) :=
  Monoidal.induced (forget₂ _ (AlgebraCat R)) (MonoidalCategory.inducingFunctorData R)

/-- `forget₂ (BialgebraCat R) (AlgebraCat R)` as a monoidal functor. -/
noncomputable instance : (forget₂ (BialgebraCat R) (AlgebraCat R)).Monoidal where

/-- `forget₂ (BialgebraCat R) (CoalgebraCat R)` as a monoidal functor. -/
noncomputable instance : (forget₂ (BialgebraCat R) (CoalgebraCat R)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _ }

 end BialgebraCat
