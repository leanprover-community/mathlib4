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

namespace PreGaloisCategory

/-- Constructor for objects in the full subcategory of connected objects in a Galois category. -/
abbrev isConnectedMk (X : C) [PreGaloisCategory.IsConnected X] :
    (isConnected C).FullSubcategory := ⟨X, inferInstance⟩

/-- Constructor for morphisms in the full subcategory of connected objects
in a Galois category. -/
abbrev isConnectedHomMk {X Y : C} (f : X ⟶ Y) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] :
    isConnectedMk X ⟶ isConnectedMk Y :=
  ObjectProperty.homMk f

end PreGaloisCategory

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
    sorry⟩


end GaloisCategory

end CategoryTheory
