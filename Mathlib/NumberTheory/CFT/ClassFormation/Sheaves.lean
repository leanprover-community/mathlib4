/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover

/-!
# Sheaves on the site of connected objects in a Galois category

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory

namespace GaloisCategory

variable [GaloisCategory C]

open Limits

lemma not_isInitial_pullback_of_isConnected
    {X₁ X₂ S : C}
    [PreGaloisCategory.IsConnected X₁] [PreGaloisCategory.IsConnected X₂]
    [PreGaloisCategory.IsConnected S]
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) (h : IsInitial (pullback f₁ f₂)) :
    False := by
  sorry

lemma exists_pullbackCone_isConnected {X₁ X₂ S : C}
    [PreGaloisCategory.IsConnected X₁] [PreGaloisCategory.IsConnected X₂]
    [PreGaloisCategory.IsConnected S]
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) :
    ∃ (Y : C) (_ : PreGaloisCategory.IsConnected Y) (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂),
      p₁ ≫ f₁ = p₂ ≫ f₂ := by
  obtain ⟨Y, f, _, _⟩ := has_connected_component _ (not_isInitial_pullback_of_isConnected f₁ f₂)
  exact ⟨Y, inferInstance, f ≫ pullback.fst _ _, f ≫ pullback.snd _ _,by
    simp [pullback.condition]⟩

lemma isSheafFor_singleton (P : (isConnected C).FullSubcategoryᵒᵖ ⥤ Type w)
    (hP : Presieve.IsSheaf (isConnectedTopology C) P)
    {Y X : (isConnected C).FullSubcategory} (f : Y ⟶ X) :
    Presieve.IsSheafFor P (.singleton f) :=
  hP.isSheafFor _ (generate_singleton_mem_isConnectedTopology f)

lemma isSheaf_type_iff (P : (isConnected C).FullSubcategoryᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (isConnectedTopology C) P ↔
      ∀ ⦃Y X : C⦄ [PreGaloisCategory.IsConnected Y]
        [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) [IsGaloisCover f],
          Presieve.IsSheafFor P (.singleton (isConnectedHomMk f)) :=
  ⟨fun hP _ _ _ _ _ _ ↦ isSheafFor_singleton _ hP _, fun hP ↦ by
    have H {Y X : (isConnected C).FullSubcategory} (f : Y ⟶ X) :
        Presieve.IsSeparatedFor P (.singleton f) := by
      obtain ⟨Z, g, _, _⟩ := exists_isGaloisCover f.hom
      exact Presieve.IsSeparatedFor.of_singleton_comp _ _ (hP (g ≫ f.hom)).isSeparatedFor
    intro X R hR
    obtain ⟨Y, _, f, _, hf⟩ := exists_isGaloisCover_of_mem_isConnectedTopology R hR
    refine Presieve.IsSheafFor.of_singleton (hP f) hf (fun {Z} g hg ↦ ?_)
    obtain ⟨W, _, p₁, p₂, fac⟩ := exists_pullbackCone_isConnected g.hom f
    exact ⟨isConnectedMk W, isConnectedHomMk p₁, isConnectedHomMk p₂,
      by ext; exact fac, H _⟩⟩

end GaloisCategory

end CategoryTheory
