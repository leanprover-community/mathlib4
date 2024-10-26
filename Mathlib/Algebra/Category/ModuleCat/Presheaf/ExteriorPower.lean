/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.FunctorOfNatTrans
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Exterior powers of presheaves of modules

-/

universe v v₁ u₁ u

namespace CategoryTheory

open Bicategory

-- to be moved
@[simps!]
def oplaxNatTransOfIsLocallyDiscrete
    {B C : Type*} [Bicategory B] [Bicategory C] [IsLocallyDiscrete B]
    {F G : OplaxFunctor B C}
    (app : ∀ (b : B), F.obj b ⟶ G.obj b)
    (naturality : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁), F.map f ≫ app b₁ ⟶ app b₀ ≫ G.map f)
    (naturality_id : ∀ (b : B), naturality (𝟙 b) ≫ app b ◁ G.mapId b =
      F.mapId b ▷ app b ≫ (λ_ (app b)).hom ≫ (ρ_ (app b)).inv := by aesop_cat)
    (naturality_comp : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂),
      naturality (f ≫ g) ≫ app b₀ ◁ G.mapComp f g =
      F.mapComp f g ▷ app b₂ ≫ (α_ (F.map f) (F.map g) (app b₂)).hom ≫
      F.map f ◁ naturality g ≫ (α_ (F.map f) (app b₁) (G.map g)).inv ≫
      naturality f ▷ G.map g ≫ (α_ (app b₀) (G.map f) (G.map g)).hom := by aesop_cat) :
    OplaxNatTrans F G where
  app := app
  naturality := naturality
  naturality_naturality := by
    rintro a b f g η
    obtain rfl := obj_ext_of_isDiscrete η
    obtain rfl := Subsingleton.elim η (𝟙 _)
    simp only [PrelaxFunctor.map₂_id, id_whiskerRight, Category.id_comp,
      Bicategory.whiskerLeft_id, Category.comp_id]
  naturality_id := naturality_id
  naturality_comp := naturality_comp

-- to be moved
@[simps!]
def LocallyDiscrete.mkOplaxNatTrans
    {B C : Type*} [Category B] [Bicategory C]
    {F G : OplaxFunctor (LocallyDiscrete B) C}
    (app : ∀ (b : B), F.obj ⟨b⟩ ⟶ G.obj ⟨b⟩)
    (naturality : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁), F.map ⟨f⟩ ≫ app b₁ ⟶ app b₀ ≫ G.map ⟨f⟩)
    (naturality_id : ∀ (b : B), naturality (𝟙 b) ≫ app b ◁ G.mapId ⟨b⟩ =
      F.mapId ⟨b⟩ ▷ app b ≫ (λ_ (app b)).hom ≫ (ρ_ (app b)).inv := by aesop_cat)
    (naturality_comp : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂),
      naturality (f ≫ g) ≫ app b₀ ◁ G.mapComp ⟨f⟩ ⟨g⟩  =
      F.mapComp ⟨f⟩ ⟨g⟩ ▷ app b₂ ≫ (α_ (F.map ⟨f⟩) (F.map ⟨g⟩) (app b₂)).hom ≫
      F.map ⟨f⟩ ◁ naturality g ≫ (α_ (F.map ⟨f⟩) (app b₁) (G.map ⟨g⟩)).inv ≫
      naturality f ▷ G.map ⟨g⟩ ≫ (α_ (app b₀) (G.map ⟨f⟩) (G.map ⟨g⟩)).hom := by aesop_cat) :
    OplaxNatTrans F G :=
  oplaxNatTransOfIsLocallyDiscrete (fun b ↦ app b.as) (fun f ↦ naturality f.as)
    (by intros; apply naturality_id) (by intros; apply naturality_comp)

end CategoryTheory

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace CommRingCat

open ModuleCat exteriorPower

noncomputable def exteriorPowerOplaxNatTrans (n : ℕ) :
    OplaxNatTrans CommRingCat.moduleCatRestrictScalarsPseudofunctor.{u}.toOplax
      CommRingCat.moduleCatRestrictScalarsPseudofunctor.{u}.toOplax :=
  LocallyDiscrete.mkOplaxNatTrans (fun _ ↦ exteriorPower.functor _ n)
    (fun _ ↦ restrictScalarsCompFunctorNatTrans _ _)
    (fun ⟨R⟩ ↦ by
      apply NatTrans.ext
      ext (M : ModuleCat R) : 1
      dsimp [Bicategory.leftUnitor, Bicategory.rightUnitor]
      simp only [Category.comp_id]
      ext m
      dsimp
      simp only [fromRestrictScalarsObjExteriorPower_mk, map_mk]
      erw [restrictScalarsId'App_hom_apply]
      rfl)
    (by
      rintro ⟨R₂⟩ ⟨R₁⟩ ⟨R₀⟩ ⟨f⟩ ⟨g⟩
      dsimp at f g ⊢
      apply NatTrans.ext
      ext (M : ModuleCat R₂) : 1
      dsimp [Bicategory.associator]
      simp only [Category.comp_id, Category.id_comp]
      ext m
      dsimp
      simp only [fromRestrictScalarsObjExteriorPower_mk, map_mk]
      rfl)

end CommRingCat

namespace PresheafOfModules

noncomputable def exteriorPowerFunctor (n : ℕ):
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{u} (R ⋙ forget₂ _ _) :=
  functorOfOplaxNatTrans (CommRingCat.exteriorPowerOplaxNatTrans n) _


end PresheafOfModules
