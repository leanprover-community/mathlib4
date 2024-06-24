/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Strong
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Oplax

-- probably optional?
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Tactic.CategoryTheory.Coherence
import Mathlib.CategoryTheory.Bicategory.Coherence

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

namespace StrongNatTrans

-- TODO: these hold for oplax functors too (but then we don't have bicategory structure)
variable {F G H I : Pseudofunctor B C}

-- TODO: need locally fully faithful sub-bicategory structure/API....

/-- Left whiskering of a strong natural transformation and a modification. -/
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι :=
  OplaxNatTrans.whiskerLeft η.toOplax Γ

/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι :=
  OplaxNatTrans.whiskerRight Γ ι.toOplax

/-- Associator for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
-- @[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  { OplaxNatTrans.associator η.toOplax θ.toOplax ι.toOplax with}

/-- Left unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  { OplaxNatTrans.leftUnitor η.toOplax with }
  --OplaxNatTrans.ModificationIso.ofComponents (fun a => λ_ (η.app a)) (by aesop_cat)

/-- Right unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  { OplaxNatTrans.rightUnitor η.toOplax with }

end StrongNatTrans

variable (B C)

#check Bicategory.comp_whiskerLeft

/-- A bicategory structure on the oplax functors between bicategories. -/
@[simps!]
instance Pseudofunctor.bicategory : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongNatTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongNatTrans.whiskerRight Γ η
  associator {F G H} I := StrongNatTrans.associator
  leftUnitor {F G} := StrongNatTrans.leftUnitor
  rightUnitor {F G} := StrongNatTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _
  pentagon f g h i := by ext; exact pentagon _ _ _ _
  triangle f g := by ext; exact triangle _ _


end CategoryTheory
