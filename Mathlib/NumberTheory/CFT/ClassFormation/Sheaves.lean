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
    refine Presieve.IsSheafFor.of_singleton (hP f) hf ?_
    sorry⟩

end GaloisCategory

end CategoryTheory
