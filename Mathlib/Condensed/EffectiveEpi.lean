/-
Copyright (c) 2025 Jonas van der Schaaf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas van der Schaaf, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.Condensed.Epi
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Limits

/-!

# The functor from compact Hausdorff spaces to condensed sets preserves effective epimorphisms
-/

@[expose] public section

open CategoryTheory CompHausLike

universe u

instance : compHausToCondensed.PreservesEpimorphisms where
  preserves f hf := by
    rw [CondensedSet.epi_iff_locallySurjective_on_compHaus]
    intro S g
    refine ⟨pullback f g.down, pullback.snd _ _, fun y ↦ ?_, ⟨pullback.fst _ _⟩,
      ULift.ext _ _ <| pullback.condition _ _⟩
    rw [CompHaus.epi_iff_surjective] at hf
    obtain ⟨x, hx⟩ := hf (g.down.hom y)
    exact ⟨⟨⟨x, y⟩, hx⟩, rfl⟩

instance : IsRegularEpiCategory CondensedSet.{u} :=
  inferInstanceAs <| IsRegularEpiCategory (Sheaf _ _)

example : compHausToCondensed.PreservesEffectiveEpis := inferInstance
