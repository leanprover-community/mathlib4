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
`ModuleCat.restrictScalarsPseudofunctor` to itself induces
a functor `PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R`
for any presheaf of rings.

TODO: the commutative case seems more useful

-/

universe v v₁ u₁ u

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

lemma naturality_id' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b) :
    τ.naturality f ≫ τ.app _ ◁ G.mapId' f hf =
      F.mapId' f hf ▷ τ.app b ≫ (λ_ _).hom ≫ (ρ_ _).inv := by
  subst hf
  simp only [OplaxFunctor.mapId'_eq_mapId, naturality_id]

end OplaxNatTrans

end CategoryTheory

open CategoryTheory Category Limits Opposite

lemma ModuleCat.restrictScalarsPseudofunctor_mapId' {R : RingCat.{u}} (f : R ⟶ R) (hf : f = 𝟙 _) :
  ModuleCat.restrictScalarsPseudofunctor.toOplax.mapId'
    ⟨f.op⟩ (by subst hf; rfl) = (ModuleCat.restrictScalarsId' f hf).hom := by
  subst hf
  apply OplaxFunctor.mapId'_eq_mapId

namespace PresheafOfModules

variable (τ : OplaxNatTrans ModuleCat.restrictScalarsPseudofunctor.{v, u}.toOplax
  ModuleCat.restrictScalarsPseudofunctor.{v, u}.toOplax)
  {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

@[simps]
noncomputable def functorOfOplaxNatTransObj (M : PresheafOfModules.{v} R) :
    PresheafOfModules.{v} R where
  obj := fun X ↦ (τ.app (LocallyDiscrete.mk (op (R.obj X)))).obj (M.obj X)
  map := fun {X Y} f ↦ (τ.app _).map (M.map f) ≫
    (τ.naturality (Quiver.Hom.toLoc (R.map f).op)).app (M.obj Y)
  map_id := fun X ↦ by
    dsimp only
    rw [map_id, ← cancel_mono ((ModuleCat.restrictScalarsId' _ (R.map_id X)).hom.app _),
      assoc, Iso.inv_hom_id_app]
    have := NatTrans.congr_app
      (τ.naturality_id' (b := ⟨⟨R.obj X⟩⟩) ⟨⟨R.map (𝟙 X)⟩⟩ (by rw [R.map_id]; rfl)) (M.obj X)
    dsimp at this
    erw [ModuleCat.restrictScalarsPseudofunctor_mapId'] at this
    erw [this]
    erw [Iso.hom_inv_id_app]
    dsimp
    rw [comp_id, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  map_comp := sorry

variable (R)

/-- Any oplax natural transformation from `ModuleCat.restrictScalarsPseudofunctor`
to itself induces a functor `PresheafOfModules R ⥤ PresheafOfModules R`. -/
@[simps! obj_obj]
noncomputable def functorOfOplaxNatTrans :
  PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} R where
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
