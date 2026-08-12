/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology

/-!
# Sheaves on the site of connected objects in a Galois category

-/

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

namespace GaloisCategory

lemma isSheaf_type_iff (F : (isConnected C).FullSubcategoryᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (isConnectedTopology C) F ↔
      ∀ ⦃Y X : C⦄ [PreGaloisCategory.IsConnected Y]
        [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) [IsGaloisCover f],
          Presieve.IsSheafFor P (.single f) := sorry

end GaloisCategory

end CategoryTheory
