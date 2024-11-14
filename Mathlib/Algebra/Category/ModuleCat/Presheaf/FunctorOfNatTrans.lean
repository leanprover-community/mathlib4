/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# The endofunctor of presheaves of modules induced by an oplax natural transformation

In this file, we show that any oplax natural transformation from
`CommRingCat.moduleCatRestrictScalarsPseudofunctor` to itself induces
a functor `PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R`
for any presheaf of commutative rings.

-/

universe v v₁ u₁ u

open CategoryTheory

@[simp]
lemma CommRingCat.forgetToRingCat_map {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (forget₂ _ RingCat).map f = f := rfl

namespace CategoryTheory

open Bicategory

namespace OplaxFunctor

variable {B C : Type*} [Bicategory B] [Bicategory C]
  (F : OplaxFunctor B C)

section

/-- More flexible variant of `mapId`. -/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b) :
    F.map f ⟶ 𝟙 _ :=
  F.map₂ (eqToHom (by rw [hf])) ≫ F.mapId _

lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/-- More flexible variant of `mapComp`. -/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂) (h : fg = f ≫ g) :
    F.map fg ⟶ F.map f ≫ F.map g :=
  F.map₂ (eqToHom (by rw [h])) ≫ F.mapComp f g

lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

end

end OplaxFunctor

namespace OplaxNatTrans

variable {B C : Type*} [Bicategory B] [Bicategory C]
  {F G : OplaxFunctor B C} (τ : OplaxNatTrans F G)

/-- Variant of `naturality_id` involving `mapId`. -/
lemma naturality_id' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b) :
    τ.naturality f ≫ τ.app _ ◁ G.mapId' f hf =
      F.mapId' f hf ▷ τ.app b ≫ (λ_ _).hom ≫ (ρ_ _).inv := by
  subst hf
  simp only [OplaxFunctor.mapId'_eq_mapId, naturality_id]

/-- Variant of `naturality_comp` involving `mapComp'`. -/
lemma naturality_comp' {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : fg = f ≫ g) :
    τ.naturality fg ≫ _ ◁ G.mapComp' f g fg h =
      F.mapComp' f g fg h ▷ _ ≫ (α_ _ _ _).hom ≫
        _ ◁ τ.naturality g ≫ (α_ _ _ _).inv ≫ τ.naturality f ▷ _≫
          (α_ _ _ _).hom := by
  subst h
  simp only [OplaxFunctor.mapComp'_eq_mapComp, naturality_comp]

end OplaxNatTrans

end CategoryTheory

open CategoryTheory Category Limits Opposite

/-- `ModuleCat.restrictScalarsPseudofunctor.toOplax.mapId'` identifies to
`ModuleCat.restrictScalarsId'`. -/
lemma CommRingCat.moduleCatRestrictScalarsPseudofunctor_mapId' {R : CommRingCat.{u}} (f : R ⟶ R)
    (hf : f = 𝟙 _) :
  CommRingCat.moduleCatRestrictScalarsPseudofunctor.toOplax.mapId'
    ⟨f.op⟩ (by subst hf; rfl) = (ModuleCat.restrictScalarsId' f hf).hom := by
  subst hf
  apply OplaxFunctor.mapId'_eq_mapId

/-- `ModuleCat.restrictScalarsPseudofunctor.toOplax.mapComp'` identifies to
`ModuleCat.restrictScalarsComp'`. -/
lemma CommRingCat.moduleCatRestrictScalarsPseudofunctor_mapComp' {R₀ R₁ R₂ : CommRingCat.{u}}
    (f : R₀ ⟶ R₁) (g : R₁ ⟶ R₂) (fg : R₀ ⟶ R₂) (h : fg = f ≫ g) :
  CommRingCat.moduleCatRestrictScalarsPseudofunctor.toOplax.mapComp'
    ⟨g.op⟩ ⟨f.op⟩ ⟨fg.op⟩ (by subst h; rfl) =
    (ModuleCat.restrictScalarsComp' f g fg h).hom := by
  subst h
  apply OplaxFunctor.mapComp'_eq_mapComp

namespace PresheafOfModules

variable (τ : OplaxNatTrans CommRingCat.moduleCatRestrictScalarsPseudofunctor.{v, u}.toOplax
  CommRingCat.moduleCatRestrictScalarsPseudofunctor.{v, u}.toOplax)
  {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

set_option maxHeartbeats 400000 in
@[simps]
noncomputable def functorOfOplaxNatTransObj (M : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{v} (R ⋙ forget₂ _ _) where
  obj X := (τ.app (LocallyDiscrete.mk (op (R.obj X)))).obj (M.obj X)
  map {X Y} f := (τ.app _).map (M.map f) ≫
    (τ.naturality (Quiver.Hom.toLoc (R.map f).op)).app (M.obj Y)
  map_id X := by
    dsimp only [Functor.comp_map, CommRingCat.forgetToRingCat_map]
    rw [map_id, ← cancel_mono ((ModuleCat.restrictScalarsId' _ (R.map_id X)).hom.app _),
      assoc, Iso.inv_hom_id_app]
    have := NatTrans.congr_app
      (τ.naturality_id' (b := ⟨⟨R.obj X⟩⟩) ⟨⟨R.map (𝟙 X)⟩⟩ (by rw [R.map_id]; rfl)) (M.obj X)
    dsimp at this
    erw [CommRingCat.moduleCatRestrictScalarsPseudofunctor_mapId'] at this
    erw [this, Iso.hom_inv_id_app]
    dsimp
    rw [comp_id, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  map_comp {X Y Z} f g := by
    dsimp only [Functor.comp_map, CommRingCat.forgetToRingCat_map]
    have := NatTrans.congr_app (τ.naturality_comp' (a := ⟨⟨R.obj Z⟩⟩)
      (b := ⟨⟨R.obj Y⟩⟩) (c := ⟨⟨R.obj X⟩⟩) ⟨⟨R.map g⟩⟩ ⟨⟨R.map f⟩⟩ ⟨⟨R.map (f ≫ g)⟩⟩
        (by rw [R.map_comp]; rfl)) (M.obj Z)
    dsimp at this
    erw [CommRingCat.moduleCatRestrictScalarsPseudofunctor_mapComp' _ _ _ (by simp)] at this
    dsimp [Bicategory.associator] at this
    rw [id_comp, id_comp, comp_id] at this
    rw [assoc, ← cancel_mono ((ModuleCat.restrictScalarsComp' _ _ _ (R.map_comp f g)).hom.app _),
      assoc, assoc, assoc, assoc, Iso.inv_hom_id_app]
    erw [this, comp_id, map_comp]
    dsimp
    rw [← Functor.map_comp_assoc, assoc, assoc, Iso.inv_hom_id, comp_id,
      Functor.map_comp_assoc, Functor.map_comp]
    erw [← NatTrans.naturality_assoc]
    rfl

variable (R)

/-- Any oplax natural transformation from
`CommRingCat.moduleCatRestrictScalarsPseudofunctor` to itself induces a functor
`PresheafOfModules (R ⋙ forget₂ _ _) ⥤ PresheafOfModules (R ⋙ forget₂ _ _)`
for any presheaf of commutative rings `R`. -/
@[simps]
noncomputable def functorOfOplaxNatTrans :
  PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤ PresheafOfModules.{v} (R ⋙ forget₂ _ _) where
  obj := functorOfOplaxNatTransObj τ
  map {M N} φ :=
    { app := fun X ↦ (τ.app _).map (φ.app X)
      naturality := fun {X Y} f ↦ by
        dsimp [functorOfOplaxNatTransObj]
        rw [assoc, ← Functor.map_comp_assoc, ← φ.naturality,
          Functor.map_comp_assoc]
        erw [← NatTrans.naturality]
        rfl }

end PresheafOfModules
