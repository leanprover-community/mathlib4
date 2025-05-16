/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.Alg.Monoidal
import Mathlib.Algebra.Category.Bialg.Basic
import Mathlib.Algebra.Category.Coalg.Monoidal
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

namespace Bialg
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

@[simps]
noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (Bialg R) where
  tensorObj X Y := of R (X ⊗[R] Y)
  whiskerLeft X _ _ f := ofHom (f.1.lTensor X)
  whiskerRight f X := ofHom (f.1.rTensor X)
  tensorHom f g := ofHom (Bialgebra.TensorProduct.map f.1 g.1)
  tensorUnit := of R R
  associator X Y Z := (Bialgebra.TensorProduct.assoc R X Y Z).toBialgIso
  leftUnitor X := (Bialgebra.TensorProduct.lid R X).toBialgIso
  rightUnitor X := (Bialgebra.TensorProduct.rid R X).toBialgIso

/-- The data needed to induce a `MonoidalCategory` structure via
`Bialg.instMonoidalCategoryStruct` and the forgetful functor to algebras. -/
@[simps]
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (Bialg R) (Alg R)) where
  μIso _ _ := Iso.refl _
  whiskerLeft_eq _ _ _ _ := by ext; rfl
  whiskerRight_eq _ _ := by ext; rfl
  tensorHom_eq _ _ := by ext; rfl
  εIso := Iso.refl _
  associator_eq _ _ _ := Alg.hom_ext _ <| Algebra.TensorProduct.ext
    (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
  leftUnitor_eq _ := Alg.hom_ext _ <| Algebra.TensorProduct.ext rfl (by ext; rfl)
  rightUnitor_eq _ := Alg.hom_ext _ <| Algebra.TensorProduct.ext (by ext; rfl) rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (Bialg R) :=
  Monoidal.induced (forget₂ _ (Alg R)) (MonoidalCategory.inducingFunctorData R)

/-- `forget₂ (Bialg R) (Alg R)` as a monoidal functor. -/
noncomputable instance : (forget₂ (Bialg R) (Alg R)).Monoidal where

set_option maxHeartbeats 400000 in
-- nightly-2025-02-18: added `maxHeartbeats`
/-- `forget₂ (Bialg R) (Coalg R)` as a monoidal functor. -/
noncomputable instance : (forget₂ (Bialg R) (Coalg R)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _ }

end Bialg
