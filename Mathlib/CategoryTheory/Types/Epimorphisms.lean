/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Stability properties of epimorphisms in `Type`

In this file, we show that in the category `Type u`, epimorphisms
are stable under base change.

-/

@[expose] public section

universe u

namespace CategoryTheory.Types

open MorphismProperty Limits

instance : (epimorphisms (Type u)).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _} b r t l sq hr := by
    simp only [epimorphisms.iff, epi_iff_surjective] at hr ⊢
    intro x
    obtain ⟨y, hy⟩ := hr (b x)
    obtain ⟨z, _, hz⟩ := Types.exists_of_isPullback sq _ _ hy
    exact ⟨z, hz⟩

end CategoryTheory.Types
