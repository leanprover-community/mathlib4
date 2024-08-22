/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax

/-!
# The bicategory of pseudofunctors between two bicategories

Given bicategories `B` and `C`, we give a bicategory structure on `Pseudofunctor B C` whose
* objects are pseudofunctors,
* 1-morphisms are strong natural transformations, and
* 2-morphisms are modifications.
-/


namespace CategoryTheory

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace Pseudofunctor.Bicategory

variable {F G H I : Pseudofunctor B C}

/-- Left whiskering of a strong natural transformation between pseudofunctors
and a modification. -/
@[simps!]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι :=
  OplaxNatTrans.whiskerLeft η.toOplax Γ

/-- Right whiskering of an strong natural transformation between pseudofunctors
and a modification. -/
@[simps!]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι :=
  OplaxNatTrans.whiskerRight Γ ι.toOplax

/-- Associator for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  { OplaxNatTrans.associator η.toOplax θ.toOplax ι.toOplax with }

/-- Left unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  { OplaxNatTrans.leftUnitor η.toOplax with }

/-- Right unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  { OplaxNatTrans.rightUnitor η.toOplax with }

end Pseudofunctor.Bicategory

variable (B C)


/-- A bicategory structure on the pseudofunctors between two bicategories. -/
@[simps!]
instance Pseudofunctor.bicategory : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := Pseudofunctor.Bicategory.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := Pseudofunctor.Bicategory.whiskerRight Γ η
  associator {F G H} I := Pseudofunctor.Bicategory.associator
  leftUnitor {F G} := Pseudofunctor.Bicategory.leftUnitor
  rightUnitor {F G} := Pseudofunctor.Bicategory.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _
  pentagon f g h i := by ext; exact pentagon _ _ _ _
  triangle f g := by ext; exact triangle _ _

end CategoryTheory
