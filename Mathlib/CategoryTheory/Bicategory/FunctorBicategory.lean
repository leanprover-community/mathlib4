/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation

#align_import category_theory.bicategory.functor_bicategory from "leanprover-community/mathlib"@"4ff75f5b8502275a4c2eb2d2f02bdf84d7fb8993"

/-!
# The bicategory of oplax functors between two bicategories

Given bicategories `B` and `C`, we give a bicategory structure on `OplaxFunctor B C` whose
* objects are oplax functors,
* 1-morphisms are oplax natural transformations, and
* 2-morphisms are modifications.
-/


namespace CategoryTheory

open Category Bicategory

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
    -- ⊢ (↑F.toPrelaxFunctor).map f ◁ η.app b ◁ Γ.app b ≫ (α_ ((↑F.toPrelaxFunctor).m …
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    -- ⊢ (α_ ((↑F.toPrelaxFunctor).map f) (η.app b) (θ.app b)).inv ≫ naturality η f ▷ …
    simp
    -- 🎉 no goals
#align category_theory.oplax_nat_trans.whisker_left CategoryTheory.OplaxNatTrans.whiskerLeft

/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  app a := Γ.app a ▷ ι.app a
  naturality {a b} f := by
    dsimp
    -- ⊢ (↑F.toPrelaxFunctor).map f ◁ Γ.app b ▷ ι.app b ≫ (α_ ((↑F.toPrelaxFunctor).m …
    simp_rw [assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
    -- ⊢ (↑F.toPrelaxFunctor).map f ◁ Γ.app b ▷ ι.app b ≫ (α_ ((↑F.toPrelaxFunctor).m …
    simp
    -- 🎉 no goals
#align category_theory.oplax_nat_trans.whisker_right CategoryTheory.OplaxNatTrans.whiskerRight

/-- Associator for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  ModificationIso.ofComponents (fun a => α_ (η.app a) (θ.app a) (ι.app a)) (by aesop_cat)
                                                                               -- 🎉 no goals
#align category_theory.oplax_nat_trans.associator CategoryTheory.OplaxNatTrans.associator

/-- Left unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  ModificationIso.ofComponents (fun a => λ_ (η.app a)) (by aesop_cat)
                                                           -- 🎉 no goals
#align category_theory.oplax_nat_trans.left_unitor CategoryTheory.OplaxNatTrans.leftUnitor

/-- Right unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  ModificationIso.ofComponents (fun a => ρ_ (η.app a)) (by aesop_cat)
                                                           -- 🎉 no goals
#align category_theory.oplax_nat_trans.right_unitor CategoryTheory.OplaxNatTrans.rightUnitor

end OplaxNatTrans

variable (B C)

/-- A bicategory structure on the oplax functors between bicategories. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
instance OplaxFunctor.bicategory : Bicategory (OplaxFunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := OplaxNatTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := OplaxNatTrans.whiskerRight Γ η
  associator {F G H} I := OplaxNatTrans.associator
  leftUnitor {F G} := OplaxNatTrans.leftUnitor
  rightUnitor {F G} := OplaxNatTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by
    ext
    -- ⊢ ((fun {F G H} η x x_1 Γ => OplaxNatTrans.whiskerLeft η Γ) f h i θ ≫ (fun {F  …
    exact whisker_exchange _ _
    -- 🎉 no goals
#align category_theory.oplax_functor.bicategory CategoryTheory.OplaxFunctor.bicategory

end CategoryTheory
