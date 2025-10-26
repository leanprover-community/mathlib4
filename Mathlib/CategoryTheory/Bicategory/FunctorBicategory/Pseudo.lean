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


namespace CategoryTheory.Pseudofunctor

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

namespace StrongTrans

variable {F G H I : Pseudofunctor B C}

/-- Left whiskering of a strong natural transformation between pseudofunctors
and a modification. -/
@[simps!]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι :=
  -- TODO: should I have a bicategory of strong trans (of oplax functors), or not?
  Modification.mkOfOplax <|
    Oplax.StrongTrans.Modification.mkOfOplax <|
      Oplax.OplaxTrans.whiskerLeft η.toOplax.toOplax Γ.toOplax.toOplax

/-- Right whiskering of an strong natural transformation between pseudofunctors
and a modification. -/
@[simps!]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι :=
  Modification.mkOfOplax <|
    Oplax.StrongTrans.Modification.mkOfOplax <|
      Oplax.OplaxTrans.whiskerRight Γ.toOplax.toOplax ι.toOplax.toOplax

/-- Associator for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a => α_ (η.app a) (θ.app a) (ι.app a))

/-- Left unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a => λ_ (η.app a))

/-- Right unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a => ρ_ (η.app a))

variable (B C)

/-- A bicategory structure on the pseudofunctors between two bicategories. -/
@[simps! whiskerLeft_app whiskerRight_app associator_hom_app associator_inv_app
rightUnitor_hom_app rightUnitor_inv_app leftUnitor_hom_app leftUnitor_inv_app]
instance bicategory : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongTrans.whiskerRight Γ η
  associator {F G H} I := StrongTrans.associator
  leftUnitor {F G} := StrongTrans.leftUnitor
  rightUnitor {F G} := StrongTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end StrongTrans

end CategoryTheory.Pseudofunctor
