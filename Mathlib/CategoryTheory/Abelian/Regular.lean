/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.RegularCategory.Basic

/-!
# Abelian categories are regular

Every abelian category is a regular category: regular epimorphisms are stable under base change
because in an abelian category every epimorphism is regular and epimorphisms are stable under
pullback.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every abelian category is regular. -/
instance (priority := 100) abelianRegular : Regular C where
  hasCoequalizer_of_isKernelPair := fun _ ↦ inferInstance
  regularEpiIsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.mk' (fun _ _ _ _ g _ hg ↦ by
      rw [MorphismProperty.regularEpi_iff] at hg ⊢
      letI : IsRegularEpi g := hg
      letI : Epi g := inferInstance
      exact IsRegularEpiCategory.regularEpiOfEpi _)

end CategoryTheory.Abelian
