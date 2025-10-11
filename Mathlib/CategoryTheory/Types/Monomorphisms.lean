/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Stability properties of monomorphisms in `Type`

In this file, we show that in the category `Type u`, monomorphisms
are stable under cobase change, filtered colimits.
After importing `CategoryTheory.MorphismProperty.TransfiniteComposition`,
the fact that monomorphisms are stable under transfinite composition
will also be inferred automatically.

(The stability by retracts holds in any category: it is shown
in the file `CategoryTheory.MorphismProperty.Retract`.)

-/

universe v' u' u

namespace CategoryTheory.Types

open MorphismProperty Limits

instance : (monomorphisms (Type u)).IsStableUnderCobaseChange where
  of_isPushout {X₁ X₂ X₃ X₄ t l r b} sq ht := by
    simp only [monomorphisms.iff] at ht ⊢
    exact Limits.Types.pushoutCocone_inr_mono_of_isColimit sq.flip.isColimit

instance : MorphismProperty.IsStableUnderFilteredColimits.{v', u'} (monomorphisms (Type u)) where
  isStableUnderColimitsOfShape J _ _ := ⟨fun F₁ F₂ c₁ c₂ hc₁ hc₂ f hf φ hφ ↦ by
    simp only [functorCategory, monomorphisms.iff, mono_iff_injective] at hf ⊢
    replace hφ (j : J) := congr_fun (hφ j)
    dsimp at hφ
    intro x₁ y₁ h
    obtain ⟨j, x₁, y₁, rfl, rfl⟩ : ∃ (j : J) (x₁' y₁' : F₁.obj j),
        x₁ = c₁.ι.app j x₁' ∧ y₁ = c₁.ι.app j y₁' := by
      obtain ⟨j, x₁, rfl⟩ := Types.jointly_surjective_of_isColimit hc₁ x₁
      obtain ⟨l, y₁, rfl⟩ := Types.jointly_surjective_of_isColimit hc₁ y₁
      exact ⟨_,  _, _, congr_fun (c₁.w (IsFiltered.leftToMax j l)).symm _,
        congr_fun (c₁.w (IsFiltered.rightToMax j l)).symm _⟩
    rw [hφ, hφ] at h
    obtain ⟨k, α, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₂ _ _).1 h
    simp only [← FunctorToTypes.naturality] at hk
    rw [← c₁.w α, types_comp_apply, types_comp_apply, hf _ hk]⟩

end CategoryTheory.Types
