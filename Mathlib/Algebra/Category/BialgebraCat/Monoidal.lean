/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.Algebra.Category.AlgebraCat.Monoidal
import Mathlib.Algebra.Category.CoalgebraCat.Monoidal
import Mathlib.RingTheory.Bialgebra.TensorProduct

universe v u

namespace BialgebraCat
open CategoryTheory MonoidalCategory TensorProduct

variable (R : Type u) [CommRing R]

set_option trace.profiler true

@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (BialgebraCat R) where
  tensorObj := fun X Y => BialgebraCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => BialgebraCat.ofHom (f.lTensor X)
  whiskerRight := fun f X => BialgebraCat.ofHom (f.rTensor X)
  tensorHom := fun f g => BialgebraCat.ofHom (Bialgebra.TensorProduct.map f g)
  tensorUnit := BialgebraCat.of R R
  associator := fun X Y Z => (Bialgebra.TensorProduct.assoc R X Y Z).toBialgebraIso
  leftUnitor := fun X => (Bialgebra.TensorProduct.lid R X).toBialgebraIso
  rightUnitor := fun X => (Bialgebra.TensorProduct.rid R X).toBialgebraIso

@[simps]
noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (BialgebraCat R) (AlgebraCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => Algebra.TensorProduct.ext
      (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
  leftUnitor_eq := fun X => Algebra.TensorProduct.ext rfl (by ext; rfl)
  rightUnitor_eq := fun X => Algebra.TensorProduct.ext (by ext; rfl) rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (BialgebraCat R) :=
  Monoidal.induced (forget₂ _ (AlgebraCat R)) (MonoidalCategory.inducingFunctorData R)

end BialgebraCat
