/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Modification.Oplax

/-!
# Bicategories of oplax functors

Given bicategories `B` and `C`, we give bicategory structures on `B ⥤ᵒᵖᴸ C` whose
* objects are oplax functors,
* 1-morphisms are lax or oplax natural transformations, and
* 2-morphisms are modifications.
-/

@[expose] public section

namespace CategoryTheory.Oplax

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {F G H I : B ⥤ᵒᵖᴸ C}

namespace LaxTrans

set_option backward.defeqAttrib.useBackward true in
/-- Left whiskering of a lax natural transformation and a modification. -/
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ η.app a ◁ (Γ.as.app a ▷ H.map f ≫ ι.naturality f) ⊗≫
                η.naturality f ▷ ι.app b ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫ ((η.app a ≫ G.map f) ◁ Γ.as.app b ≫
              η.naturality f ▷ ι.app b) ⊗≫ 𝟙 _ := by
          rw [Γ.as.naturality]
          bicategory
        _ = _ := by
          rw [whisker_exchange]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of a lax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp only [comp_app, comp_naturality]
      calc
        _ = 𝟙 _ ⊗≫ (Γ.as.app a ▷ (ι.app a ≫ H.map f) ≫ θ.app a ◁ ι.naturality f) ⊗≫
              θ.naturality f ▷ ι.app b ⊗≫ 𝟙 _ := by
          bicategory
        _ = 𝟙 _ ⊗≫ η.app a ◁ ι.naturality f ⊗≫ (Γ.as.app a ▷ G.map f ≫
              θ.naturality f) ▷ ι.app b ⊗≫ 𝟙 _ := by
          rw [← whisker_exchange]
          bicategory
        _ = _ := by
          rw [Γ.as.naturality]
          bicategory }

set_option backward.defeqAttrib.useBackward true in
/-- Associator for the vertical composition of lax natural transformations. -/
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι := by
  exact isoMk (fun a ↦ α_ (η.app a) (θ.app a) (ι.app a)) <| by
    intro a b f
    dsimp only [comp_app, comp_naturality]
    bicategory

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor for the vertical composition of lax natural transformations. -/
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a ↦ λ_ (η.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor for the vertical composition of lax natural transformations. -/
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a ↦ ρ_ (η.app a))

variable (B C)

set_option backward.defeqAttrib.useBackward true in
/-- A bicategory structure on the oplax functors between bicategories, with lax transformations. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
  rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance OplaxFunctor.bicategory : Bicategory (B ⥤ᵒᵖᴸ C) where
  whiskerLeft {_ _ _} η _ _ Γ := whiskerLeft η Γ
  whiskerRight {_ _ _} _ _ Γ η := whiskerRight Γ η
  associator {_ _ _} _ := associator
  leftUnitor {_ _} := leftUnitor
  rightUnitor {_ _} := rightUnitor
  whisker_exchange {a b c f g h i} η Γ := by ext; exact whisker_exchange _ _

end LaxTrans

namespace OplaxTrans

set_option backward.defeqAttrib.useBackward true in
/-- Left whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerLeft (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) : η ≫ θ ⟶ η ≫ ι where
  as := {
    app a := η.app a ◁ Γ.as.app a
    naturality {a b} f := by
      dsimp
      rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
      simp }

set_option backward.defeqAttrib.useBackward true in
/-- Right whiskering of an oplax natural transformation and a modification. -/
@[simps]
def whiskerRight {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) : η ≫ ι ⟶ θ ≫ ι where
  as := {
    app a := Γ.as.app a ▷ ι.app a
    naturality {a b} f := by
      dsimp
      simp_rw [assoc, ← associator_inv_naturality_left, whisker_exchange_assoc]
      simp }

set_option backward.defeqAttrib.useBackward true in
/-- Associator for the vertical composition of oplax natural transformations. -/
@[simps!]
def associator (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) : (η ≫ θ) ≫ ι ≅ η ≫ θ ≫ ι :=
  isoMk (fun a ↦ α_ (η.app a) (θ.app a) (ι.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Left unitor for the vertical composition of oplax natural transformations. -/
@[simps!]
def leftUnitor (η : F ⟶ G) : 𝟙 F ≫ η ≅ η :=
  isoMk (fun a ↦ λ_ (η.app a))

set_option backward.defeqAttrib.useBackward true in
/-- Right unitor for the vertical composition of oplax natural transformations. -/
@[simps!]
def rightUnitor (η : F ⟶ G) : η ≫ 𝟙 G ≅ η :=
  isoMk (fun a ↦ ρ_ (η.app a))

variable (B C)

set_option backward.defeqAttrib.useBackward true in
/-- A bicategory structure on the oplax functors between bicategories. -/
@[simps! whiskerLeft_as_app whiskerRight_as_app associator_hom_as_app associator_inv_as_app
  rightUnitor_hom_as_app rightUnitor_inv_as_app leftUnitor_hom_as_app leftUnitor_inv_as_app]
scoped instance OplaxFunctor.bicategory : Bicategory (B ⥤ᵒᵖᴸ C) where
  whiskerLeft {_ _ _} η _ _ Γ := whiskerLeft η Γ
  whiskerRight {_ _ _} _ _ Γ η := whiskerRight Γ η
  associator {_ _ _} _ := associator
  leftUnitor {_ _} := leftUnitor
  rightUnitor {_ _} := rightUnitor
  whisker_exchange {a b c f g h i} η θ := by ext; exact whisker_exchange _ _

end OplaxTrans

end CategoryTheory.Oplax
