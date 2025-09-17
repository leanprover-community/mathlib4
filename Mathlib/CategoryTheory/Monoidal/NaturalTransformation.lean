/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

-/

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]
  {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']

variable {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.LaxMonoidal] [F₂.LaxMonoidal] [F₃.LaxMonoidal]

namespace NatTrans

open Functor.LaxMonoidal

/-- A natural transformation between (lax) monoidal functors is monoidal if it satisfies
`ε F ≫ τ.app (𝟙_ C) = ε G` and `μ F X Y ≫ app (X ⊗ Y) = (app X ⊗ₘ app Y) ≫ μ G X Y`. -/
class IsMonoidal : Prop where
  unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂ := by cat_disch
  tensor (X Y : C) : μ F₁ _ _ ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ₘ τ.app Y) ≫ μ F₂ _ _ := by cat_disch

namespace IsMonoidal

attribute [reassoc (attr := simp)] unit tensor

instance id : IsMonoidal (𝟙 F₁) where

instance comp (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ'] :
    IsMonoidal (τ ≫ τ') where

instance hcomp {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂)
    [IsMonoidal τ] [IsMonoidal τ'] : IsMonoidal (τ ◫ τ') where
  unit := by
    simp only [comp_obj, comp_ε, hcomp_app, assoc, naturality_assoc, unit_assoc, ← map_comp, unit]
  tensor X Y := by
    simp only [comp_obj, comp_μ, hcomp_app, assoc, naturality_assoc,
      tensor_assoc, tensor_comp, μ_natural_assoc]
    simp only [← map_comp, tensor]

instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.leftUnitor.hom where

instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.rightUnitor.hom where

instance (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal] :
    NatTrans.IsMonoidal (Functor.associator F G H).hom where
  unit := by
    simp only [comp_obj, comp_ε, assoc, Functor.map_comp, associator_hom_app, comp_id,
      Functor.comp_map]
  tensor X Y := by
    simp only [comp_obj, comp_μ, associator_hom_app, Functor.comp_map, map_comp,
      comp_id, tensorHom_id, id_whiskerRight, assoc, id_comp]

end IsMonoidal

instance {F G : C ⥤ D} {H K : C ⥤ E} (α : F ⟶ G) (β : H ⟶ K)
    [F.LaxMonoidal] [G.LaxMonoidal] [IsMonoidal α]
    [H.LaxMonoidal] [K.LaxMonoidal] [IsMonoidal β] :
    IsMonoidal (NatTrans.prod' α β) where
  unit := by
    ext
    · rw [prod_comp_fst, prod'_ε_fst, prod'_ε_fst, prod'_app_fst, IsMonoidal.unit]
    · rw [prod_comp_snd, prod'_ε_snd, prod'_ε_snd, prod'_app_snd, IsMonoidal.unit]
  tensor X Y := by
    ext
    · simp only [prod_comp_fst, prod'_μ_fst, prod'_app_fst,
        prodMonoidal_tensorHom, IsMonoidal.tensor]
    · simp only [prod_comp_snd, prod'_μ_snd, prod'_app_snd,
        prodMonoidal_tensorHom, IsMonoidal.tensor]

end NatTrans

namespace Iso

variable (e : F₁ ≅ F₂) [NatTrans.IsMonoidal e.hom]

instance : NatTrans.IsMonoidal e.inv where
  unit := by rw [← NatTrans.IsMonoidal.unit (τ := e.hom), assoc, hom_inv_id_app, comp_id]
  tensor X Y := by
    rw [← cancel_mono (e.hom.app (X ⊗ Y)), assoc, assoc, inv_hom_id_app, comp_id,
      NatTrans.IsMonoidal.tensor, ← MonoidalCategory.tensor_comp_assoc,
      inv_hom_id_app, inv_hom_id_app, tensorHom_id, id_whiskerRight, id_comp]

end Iso

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

namespace IsMonoidal

variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

instance : NatTrans.IsMonoidal adj.unit where
  unit := by
    dsimp
    rw [id_comp, ← unit_app_unit_comp_map_η adj, assoc, Monoidal.map_η_ε]
    dsimp
    rw [comp_id]
  tensor X Y := by
    dsimp
    rw [← unit_app_tensor_comp_map_δ_assoc, id_comp, Monoidal.map_δ_μ, comp_id]

instance : NatTrans.IsMonoidal adj.counit where
  unit := by
    dsimp
    rw [assoc, map_ε_comp_counit_app_unit adj, ε_η]
  tensor X Y := by
    dsimp
    rw [assoc, map_μ_comp_counit_app_tensor, μ_δ_assoc, comp_id]

end IsMonoidal

namespace Equivalence

variable (e : C ≌ D) [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

instance : NatTrans.IsMonoidal e.unit :=
  inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.unit)

instance : NatTrans.IsMonoidal e.counit :=
  inferInstanceAs (NatTrans.IsMonoidal e.toAdjunction.counit)

end Equivalence

end Adjunction

namespace LaxMonoidalFunctor

/-- The type of monoidal natural transformations between (bundled) lax monoidal functors. -/
structure Hom (F G : LaxMonoidalFunctor C D) where
  /-- the natural transformation between the underlying functors -/
  hom : F.toFunctor ⟶ G.toFunctor
  isMonoidal : NatTrans.IsMonoidal hom := by infer_instance

attribute [instance] Hom.isMonoidal

instance : Category (LaxMonoidalFunctor C D) where
  Hom := Hom
  comp α β := ⟨α.1 ≫ β.1, by have := α.2; have := β.2; infer_instance⟩
  id _ := ⟨𝟙 _, inferInstance⟩

@[simp]
lemma id_hom (F : LaxMonoidalFunctor C D) : Hom.hom (𝟙 F) = 𝟙 _ := rfl

@[reassoc, simp]
lemma comp_hom {F G H : LaxMonoidalFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := rfl

@[ext]
lemma hom_ext {F G : LaxMonoidalFunctor C D} {α β : F ⟶ G} (h : α.hom = β.hom) : α = β := by
  cases α; cases β; subst h; rfl

/-- Constructor for morphisms in the category `LaxMonoidalFunctor C D`. -/
@[simps]
def homMk {F G : LaxMonoidalFunctor C D} (f : F.toFunctor ⟶ G.toFunctor) [NatTrans.IsMonoidal f] :
    F ⟶ G := ⟨f, inferInstance⟩

/-- Constructor for isomorphisms in the category `LaxMonoidalFunctor C D`. -/
@[simps]
def isoMk {F G : LaxMonoidalFunctor C D} (e : F.toFunctor ≅ G.toFunctor)
    [NatTrans.IsMonoidal e.hom] :
    F ≅ G where
  hom := homMk e.hom
  inv := homMk e.inv

open Functor.LaxMonoidal

/-- Constructor for isomorphisms between lax monoidal functors. -/
@[simps!]
def isoOfComponents {F G : LaxMonoidalFunctor C D} (e : ∀ X, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (e Y).hom = (e X).hom ≫ G.map f := by
      cat_disch)
    (unit : ε F.toFunctor ≫ (e (𝟙_ C)).hom = ε G.toFunctor := by cat_disch)
    (tensor : ∀ X Y, μ F.toFunctor X Y ≫ (e (X ⊗ Y)).hom =
      ((e X).hom ⊗ₘ (e Y).hom) ≫ μ G.toFunctor X Y := by cat_disch) :
    F ≅ G :=
  @isoMk _ _ _ _ _ _ _ _ (NatIso.ofComponents e naturality) (by constructor <;> assumption)

end LaxMonoidalFunctor

end CategoryTheory
