/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.RingTheory.Coalgebra.TensorProduct

universe v u

namespace CoalgebraCat
variable (R : Type u) [CommRing R]
open CategoryTheory Coalgebra
open scoped TensorProduct MonoidalCategory

@[simps] noncomputable instance instMonoidalCategoryStruct :
    MonoidalCategoryStruct.{u} (CoalgebraCat R) where
  tensorObj := fun X Y => CoalgebraCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => CoalgebraCat.ofHom (f.lTensor X)
  whiskerRight := fun f X => CoalgebraCat.ofHom (f.rTensor X)
  tensorHom := fun f g => CoalgebraCat.ofHom (Coalgebra.TensorProduct.map f g)
  tensorUnit := CoalgebraCat.of R R
  associator := fun X Y Z => (Coalgebra.TensorProduct.assoc R X Y Z).toCoalgebraIso
  leftUnitor := fun X => (Coalgebra.TensorProduct.lid R X).toCoalgebraIso
  rightUnitor := fun X => (Coalgebra.TensorProduct.rid R X).toCoalgebraIso

@[simps] noncomputable def MonoidalCategory.inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (CoalgebraCat R) (ModuleCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => TensorProduct.ext <| TensorProduct.ext <| by ext; rfl
  leftUnitor_eq := fun X => TensorProduct.ext <| by ext; rfl
  rightUnitor_eq := fun X => TensorProduct.ext <| by ext; rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (CoalgebraCat R) :=
  Monoidal.induced (forget₂ _ (ModuleCat R)) (MonoidalCategory.inducingFunctorData R)

end CoalgebraCat
