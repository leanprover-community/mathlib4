/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# ...

-/

@[expose] public section

universe w

namespace CategoryTheory

open Category Limits

namespace MorphismProperty

variable {J C D : Type*} [Category* J] [Category* C] [Category* D]

lemma map_pushouts (W : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
    (hf : W.pushouts f) (F : C ⥤ D) [PreservesColimitsOfShape WalkingSpan F] :
    (W.map F).pushouts (F.map f) := by
  obtain ⟨_, _, l, _, _, hl, sq⟩ := hf
  exact ⟨_, _, _, _, _, W.map_mem_map F l hl, sq.map F⟩

lemma map_pushouts_le (W : MorphismProperty C) (F : C ⥤ D)
    [PreservesColimitsOfShape WalkingSpan F] :
    W.pushouts.map F ≤ (W.map F).pushouts := by
  rw [map_le_iff]
  intro _ _ _ hf
  exact W.map_pushouts hf F

lemma map_colimitsOfShape (W : MorphismProperty C)
    {X Y : C} {f : X ⟶ Y} (hf : W.colimitsOfShape J f) (F : C ⥤ D)
    [PreservesColimitsOfShape J F] :
    (W.map F).colimitsOfShape J (F.map f) := by
  obtain ⟨_, _, c₁, c₂, hc₁, hc₂, φ, hφ⟩ := hf
  let hc₁' := isColimitOfPreserves F hc₁
  have : F.map (hc₁.desc { pt := _, ι := φ ≫ c₂.ι }) =
    hc₁'.desc { pt := _, ι := Functor.whiskerRight φ F ≫ (F.mapCocone c₂).ι } :=
      hc₁'.hom_ext (fun j ↦ by
        rw [IsColimit.fac]
        dsimp
        rw [← F.map_comp, IsColimit.fac, NatTrans.comp_app, Functor.map_comp])
  rw [this]
  exact ⟨_, _, _, _, _, isColimitOfPreserves F hc₂, _,
    fun j ↦ W.map_mem_map F (φ.app j) (hφ j)⟩

lemma map_colimitsOfShape_le (W : MorphismProperty C) (F : C ⥤ D)
    (J : Type*) [Category* J] [PreservesColimitsOfShape J F] :
    (W.colimitsOfShape J).map F ≤ (W.map F).colimitsOfShape J := by
  rintro X Y f ⟨_, _, g, hg, ⟨e⟩⟩
  rw [← ((W.map F).colimitsOfShape J).arrow_mk_iso_iff e]
  exact W.map_colimitsOfShape hg F

lemma map_coproducts (W : MorphismProperty C) {X Y : C} {f : X ⟶ Y}
    (hf : coproducts.{w} W f) (F : C ⥤ D)
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) F] :
    coproducts.{w} (W.map F) (F.map f) := by
  rw [coproducts_iff] at hf ⊢
  obtain ⟨J, hf⟩ := hf
  exact ⟨J, W.map_colimitsOfShape hf F⟩

lemma map_coproducts_le (W : MorphismProperty C) (F : C ⥤ D)
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) F] :
    (coproducts.{w} W).map F ≤ coproducts.{w} (W.map F) := by
  rw [map_le_iff]
  intro _ _ _ hf
  exact W.map_coproducts hf F

instance (W : MorphismProperty D) [W.RespectsIso] [W.IsStableUnderColimitsOfShape J]
    (F : C ⥤ D) [PreservesColimitsOfShape J F] :
    (W.inverseImage F).IsStableUnderColimitsOfShape J := by
  rw [isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  intro X Y f hf
  have hW := W.map_inverseImage_le F
  rw [W.isoClosure_eq_self] at hW
  exact W.colimitsOfShape_le _ (colimitsOfShape_monotone hW J _ (map_colimitsOfShape _ hf F))

instance (W : MorphismProperty D) [W.RespectsIso] [IsStableUnderCoproducts.{w} W] (F : C ⥤ D)
    [∀ (J : Type w), PreservesColimitsOfShape (Discrete J) F] :
    IsStableUnderCoproducts.{w} (W.inverseImage F) where

instance (W : MorphismProperty D)
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
    [W.IsStableUnderTransfiniteCompositionOfShape J] (F : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J F] [PreservesColimitsOfShape J F] :
    (W.inverseImage F).IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    intro X Y f ⟨hf⟩
    exact W.transfiniteCompositionsOfShape_le _ _ hf.map.mem

end MorphismProperty

end CategoryTheory
