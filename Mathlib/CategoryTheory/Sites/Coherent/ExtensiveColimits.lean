/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
import Mathlib.CategoryTheory.Sites.Limits
/-!

# Colimits in categories of extensive sheaves

This file proves that `J`-shaped colimits of `A`-valued sheaves for the extensive topology are
computed objectwise if `colim : J ⥤ A ⥤ A` preserves finite products.

This holds for all shapes `J` if `A` is a preadditive category.

This can also easily be applied to filtered `J` in the case when `A` is a category of sets, and
eventually to sifted `J` once that API is developed.
-/

namespace CategoryTheory

open Limits Sheaf GrothendieckTopology Opposite

section

variable {A C J : Type*} [Category A] [Category C] [Category J]
  [FinitaryExtensive C] [HasColimitsOfShape J A]

lemma isSheaf_pointwiseColimit [PreservesFiniteProducts (colim (J := J) (C := A))]
    (G : J ⥤ Sheaf (extensiveTopology C) A) :
    Presheaf.IsSheaf (extensiveTopology C) (pointwiseCocone (G ⋙ sheafToPresheaf _ A)).pt := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  dsimp only [pointwiseCocone_pt]
  apply (config := { allowSynthFailures := true } ) comp_preservesFiniteProducts
  have : ∀ (i : J), PreservesFiniteProducts ((G ⋙ sheafToPresheaf _ A).obj i) := fun i ↦ by
    rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]
    exact Sheaf.cond _
  exact ⟨fun _ ↦ preservesLimitsOfShape_of_evaluation _ _ fun d ↦
    inferInstanceAs (PreservesLimitsOfShape _ ((G ⋙ sheafToPresheaf _ _).obj d))⟩

instance [Preadditive A] : PreservesFiniteProducts (colim (J := J) (C := A)) where
  preserves _ := by
    apply (config := { allowSynthFailures := true })
      preservesProductsOfShape_of_preservesBiproductsOfShape
    apply preservesBiproductsOfShape_of_preservesCoproductsOfShape

instance [PreservesFiniteProducts (colim (J := J) (C := A))] :
    PreservesColimitsOfShape J (sheafToPresheaf (extensiveTopology C) A) where
  preservesColimit {G} := by
    suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
    refine createsColimitOfIsSheaf _ (fun c hc ↦ ?_)
    let i : c.pt ≅ (G ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
    rw [Presheaf.isSheaf_of_iso_iff i]
    exact isSheaf_pointwiseColimit _

instance [Preadditive A] [HasFiniteColimits A] :
    PreservesFiniteColimits (sheafToPresheaf (extensiveTopology C) A) where
  preservesFiniteColimits _ := inferInstance

end

end CategoryTheory
