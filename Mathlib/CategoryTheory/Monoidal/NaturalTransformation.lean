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
class IsMonoidal where
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

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

instance : NatTrans.IsMonoidal adj.unit where
  unit := by
    dsimp only [comp_obj, id_obj, Functor.id_map, comp_id, id_comp, implies_true, tensorHom_id,
      id_whiskerRight, whiskerRight_tensor, Iso.inv_hom_id, MonoidalCategory.whiskerRight_id,
      Iso.hom_inv_id, LaxMonoidal.ofTensorHom_ε, LaxMonoidal.comp_ε]
    simp only [id_comp, Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj), homEquiv_apply,
      assoc, Monoidal.map_η_ε, comp_obj, comp_id]
  tensor X Y := by
    dsimp only [id_obj, comp_obj, LaxMonoidal.id_μ, LaxMonoidal.comp_μ]
    simp only [id_comp]
    rw [Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj)]
    sorry
    --dsimp
    --simp only [id_comp, comp_id, assoc, Adjunction.homEquiv_unit,
    --  ← h.unit_naturality_assoc, ← Functor.map_comp,
    --  F.map_tensor, IsIso.hom_inv_id_assoc, ← tensor_comp_assoc,
    --  Adjunction.left_triangle_components, tensorHom_id, id_whiskerRight,
    --  IsIso.inv_hom_id, map_id]

instance : NatTrans.IsMonoidal adj.counit where
  unit := by
    dsimp only [id_obj, comp_obj, LaxMonoidal.comp_ε, Functor.id_map, comp_id, id_comp,
      implies_true, tensorHom_id, id_whiskerRight, whiskerRight_tensor, Iso.inv_hom_id,
      MonoidalCategory.whiskerRight_id, Iso.hom_inv_id, LaxMonoidal.ofTensorHom_ε]
    simp only [Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj),
      homEquiv_apply, comp_obj, map_comp, assoc, counit_naturality, id_obj,
      left_triangle_components_assoc, Monoidal.ε_η]
  tensor X Y := sorry
  --  have eq := h.counit_naturality (F.μ (G.obj X) (G.obj Y)) =≫ inv (F.μ _ _)
  --  simp only [assoc, IsIso.hom_inv_id, comp_id] at eq
  --  dsimp
  --  simp only [Adjunction.homEquiv_unit, comp_id, assoc,
  --    map_comp, map_inv, h.counit_naturality, ← eq,
  --    h.left_triangle_components_assoc,
  --    IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc]

end Adjunction

end CategoryTheory
