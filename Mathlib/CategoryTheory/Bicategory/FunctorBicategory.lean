/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno

! This file was ported from Lean 3 source module category_theory.bicategory.functor_bicategory
! leanprover-community/mathlib commit 4ff75f5b8502275a4c2eb2d2f02bdf84d7fb8993
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation

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
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    -- Porting note: used to be `simp`
    simp only [comp_whiskerLeft, assoc, Iso.inv_hom_id_assoc,
      Modification.whiskerLeft_naturality_assoc, whisker_assoc]
#align category_theory.oplax_nat_trans.whisker_left CategoryTheory.OplaxNatTrans.whiskerLeft

/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  app a := Γ.app a ▷ ι.app a
  naturality {a b} f := by
    dsimp
    simp_rw [assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
    -- Porting note: used to be `simp`
    simp only [Modification.whiskerRight_naturality_assoc, whiskerRight_comp, assoc,
      Iso.hom_inv_id_assoc]
#align category_theory.oplax_nat_trans.whisker_right CategoryTheory.OplaxNatTrans.whiskerRight

/-- Associator for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  ModificationIso.ofComponents (fun a => α_ (η.app a) (θ.app a) (ι.app a)) (by aesop_cat)
#align category_theory.oplax_nat_trans.associator CategoryTheory.OplaxNatTrans.associator

/-- Left unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  ModificationIso.ofComponents (fun a => λ_ (η.app a)) (by aesop_cat)
#align category_theory.oplax_nat_trans.left_unitor CategoryTheory.OplaxNatTrans.leftUnitor

/-- Right unitor for the vertical composition of oplax natural transformations. -/
-- Porting note: verified that projections are correct and changed @[simps] to @[simps!]
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  ModificationIso.ofComponents (fun a => ρ_ (η.app a)) (by aesop_cat)
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
    -- Porting note: broken ext
    refine' OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => whisker_exchange _ _)
  whiskerLeft_id {a b c} f g := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => whiskerLeft_id _ _)
  whiskerLeft_comp {a b c} f g h i η θ := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => whiskerLeft_comp _ _ _)
  id_whiskerLeft {a b f g} η := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => id_whiskerLeft _)
  comp_whiskerLeft {a b c d} f g {h h'} η := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => comp_whiskerLeft _ _ _)
  id_whiskerRight {a b c} f g := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => id_whiskerRight _ _)
  comp_whiskerRight {a b c f g h} η θ i := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => comp_whiskerRight _ _ _)
  whiskerRight_id {a b f g} η := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => whiskerRight_id _)
  whiskerRight_comp {a b c d f f'} η g h := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => whiskerRight_comp _ _ _)
  whisker_assoc {a b c d} f {g g'} η h := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => whisker_assoc _ _ _)
  pentagon {a b c d e} f g h i := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => pentagon _ _ _ _)
  triangle {a b c} f g := by
    -- Porting note: tidy used to be able to do this
    exact OplaxNatTrans.Modification.ext _ _ (funext <| fun _ => triangle _ _)
#align category_theory.oplax_functor.bicategory CategoryTheory.OplaxFunctor.bicategory

end CategoryTheory
