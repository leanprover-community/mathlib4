/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Modification.Oplax

/-!
# The bicategory of oplax functors between two bicategories

Given bicategories `B` and `C`, we give a bicategory structure on `OplaxFunctor B C` whose
* objects are oplax functors,
* 1-morphisms are oplax natural transformations, and
* 2-morphisms are modifications.
-/


namespace CategoryTheory

open Category Bicategory Oplax

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {F G H I : OplaxFunctor B C}

namespace OplaxNatTrans

/-- Left whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  app a := η.app a ◁ Γ.app a
  naturality {a b} f := by
    dsimp
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    simp

/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  app a := Γ.app a ▷ ι.app a
  naturality {a b} f := by
    dsimp
    simp_rw [assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
    simp

/-- Associator for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  ModificationIso.ofComponents (fun a => α_ (η.app a) (θ.app a) (ι.app a)) (by aesop_cat)

/-- Left unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  ModificationIso.ofComponents (fun a => λ_ (η.app a)) (by aesop_cat)

/-- Right unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  ModificationIso.ofComponents (fun a => ρ_ (η.app a)) (by aesop_cat)

end OplaxNatTrans

variable (B C)

/-- A bicategory structure on the oplax functors between bicategories. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
instance OplaxFunctor.bicategory : Bicategory (OplaxFunctor B C) where
  whiskerLeft {_ _ _} η _ _ Γ := OplaxNatTrans.whiskerLeft η Γ
  whiskerRight {_ _ _} _ _ Γ η := OplaxNatTrans.whiskerRight Γ η
  associator {_ _ _} _ := OplaxNatTrans.associator
  leftUnitor {_ _} := OplaxNatTrans.leftUnitor
  rightUnitor {_ _} := OplaxNatTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by
    ext
    exact whisker_exchange _ _

end CategoryTheory
