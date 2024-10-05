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
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  app a := η.app a ◁ Γ.app a
  naturality {a b} f := by
    dsimp
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    simp
  -- Modification.mkOfOplax <| OplaxTrans.whiskerLeft η.toOplax Γ.toOplax

/-- Right whiskering of an strong natural transformation between pseudofunctors
and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  app a := Γ.app a ▷ ι.app a
  naturality {a b} f := by
    dsimp
    simp_rw [assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
    simp
  -- Modification.mkOfOplax <| OplaxTrans.whiskerRight Γ.toOplax ι.toOplax

/-- Associator for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  ModificationIso.ofComponents (fun a => α_ (η.app a) (θ.app a) (ι.app a)) (by aesop_cat)

/-- Left unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  ModificationIso.ofComponents (fun a => λ_ (η.app a)) (by aesop_cat)
  -- { Modification.mkOfOplax (OplaxTrans.leftUnitor η.toOplax) with }

/-- Right unitor for the vertical composition of strong natural transformations
between pseudofunctors. -/
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  ModificationIso.ofComponents (fun a => ρ_ (η.app a)) (by aesop_cat)
  -- { OplaxTrans.rightUnitor η.toOplax with }

end StrongTrans

variable (B C)

example (B : Type u₁) [inst : CategoryTheory.Bicategory B] (C : Type u₂)
  [inst_1 : CategoryTheory.Bicategory C] {X Y Z : CategoryTheory.Pseudofunctor B C}
  (η : X ⟶ Y) (θ : Y ⟶ Z) {a b : B} (f : a ⟶ b) :
    ((η ≫ θ).naturality f).inv =
      (α_ (η.app a) (θ.app a) (Z.map f)).hom ≫
        η.app a ◁ (θ.naturality f).inv ≫
          (α_ (η.app a) (Y.map f) (θ.app b)).inv ≫
            (η.naturality f).inv ▷ θ.app b ≫ (α_ (X.map f) (η.app b) (θ.app b)).hom := by
  simp only [instCategoryStructPseudofunctor_comp, StrongTrans.vcomp_app,
    StrongTrans.vcomp_naturality, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, assoc,
    whiskerRightIso_inv]

/-- A bicategory structure on the pseudofunctors between two bicategories. -/
@[simps!? comp_naturality_inv]
instance bicategory : Bicategory (Pseudofunctor B C) where
  whiskerLeft {F G H} η _ _ Γ := StrongTrans.whiskerLeft η Γ
  whiskerRight {F G H} _ _ Γ η := StrongTrans.whiskerRight Γ η
  associator {F G H} I := StrongTrans.associator
  leftUnitor {F G} := StrongTrans.leftUnitor
  rightUnitor {F G} := StrongTrans.rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end CategoryTheory.Pseudofunctor

#lint
