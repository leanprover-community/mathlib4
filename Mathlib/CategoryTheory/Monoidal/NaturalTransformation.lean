/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.FullSubcategory

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

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

variable {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) [F₁.LaxMonoidal] [F₂.LaxMonoidal] [F₃.LaxMonoidal]

namespace NatTrans

open Functor.LaxMonoidal

/-- A natural transformation between (lax) monoidal functors is monoidal if it satisfies
`ε F ≫ τ.app (𝟙_ C) = ε G` and `μ F X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ μ G X Y`. -/
class IsMonoidal : Prop where
  unit : ε F₁ ≫ τ.app (𝟙_ C) = ε F₂ := by aesop_cat
  tensor (X Y : C) : μ F₁ _ _ ≫ τ.app (X ⊗ Y) = (τ.app X ⊗ τ.app Y) ≫ μ F₂ _ _ := by aesop_cat

namespace IsMonoidal

attribute [reassoc (attr := simp)] unit tensor

instance id : IsMonoidal (𝟙 F₁) where

instance comp (τ' : F₂ ⟶ F₃) [IsMonoidal τ] [IsMonoidal τ'] :
    IsMonoidal (τ ≫ τ') where

instance {G₁ G₂ : D ⥤ E} [G₁.LaxMonoidal] [G₂.LaxMonoidal] (τ' : G₁ ⟶ G₂)
    [IsMonoidal τ] [IsMonoidal τ'] : IsMonoidal (τ ◫ τ') where
  unit := by
    simp only [comp_obj, comp_ε, hcomp_app, assoc, naturality_assoc, unit_assoc, ← map_comp, unit]
  tensor X Y := by
    simp only [comp_obj, comp_μ, hcomp_app, assoc, naturality_assoc,
      tensor_assoc, tensor_comp, μ_natural_assoc]
    simp only [← map_comp, tensor]

instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.leftUnitor.hom where
instance (F : C ⥤ D) [F.LaxMonoidal] : NatTrans.IsMonoidal F.rightUnitor.hom where

instance {E' : Type u₄} [Category.{v₄} E'] [MonoidalCategory E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]:
    NatTrans.IsMonoidal (Functor.associator F G H).hom where
  unit := by
    simp only [comp_obj, comp_ε, assoc, Functor.map_comp, associator_hom_app, comp_id,
      Functor.comp_map]
  tensor X Y := by
    simp only [comp_obj, comp_μ, associator_hom_app, Functor.comp_map, map_comp,
      comp_id, tensorHom_id, id_whiskerRight, assoc, id_comp]

end IsMonoidal

end NatTrans

--/-- The cartesian product of two monoidal natural transformations is monoidal. -/
--@[simps]
--def prod {F G : LaxMonoidalFunctor C D} {H K : LaxMonoidalFunctor C E} (α : MonoidalNatTrans F G)
--    (β : MonoidalNatTrans H K) : MonoidalNatTrans (F.prod' H) (G.prod' K) where
--  app X := (α.app X, β.app X)

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

section

variable [F.OplaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal]

@[reassoc]
lemma unit_app_unit_comp_map_η : adj.unit.app (𝟙_ C) ≫ G.map (η F) = ε G :=
  Adjunction.IsMonoidal.leftAdjoint_ε.symm

@[reassoc]
lemma unit_app_tensor_comp_map_δ (X Y : C) :
    adj.unit.app (X ⊗ Y) ≫ G.map (δ F X Y) = (adj.unit.app X ⊗ adj.unit.app Y) ≫ μ G _ _ := by
  rw [leftAdjoint_μ (adj := adj), homEquiv_unit]
  dsimp
  simp only [← adj.unit_naturality_assoc, ← Functor.map_comp, ← δ_natural_assoc,
    ← tensor_comp, left_triangle_components, tensorHom_id, id_whiskerRight, comp_id]

@[reassoc]
lemma map_ε_comp_counit_app_unit : F.map (ε G) ≫ adj.counit.app (𝟙_ D) = η F := by
  rw [leftAdjoint_ε (adj := adj), homEquiv_unit, map_comp,
    assoc, counit_naturality, left_triangle_components_assoc]

@[reassoc]
lemma map_μ_comp_counit_app_tensor (X Y : D) :
    F.map (μ G X Y) ≫ adj.counit.app (X ⊗ Y) =
      δ F _ _ ≫ (adj.counit.app X ⊗ adj.counit.app Y) := by
  rw [leftAdjoint_μ (adj := adj), homEquiv_unit]
  simp

end

section

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

end

end IsMonoidal

end Adjunction

end CategoryTheory
