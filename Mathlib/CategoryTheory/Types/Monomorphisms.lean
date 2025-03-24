/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Stability properties of monomorphisms in Type

In this file, we show that in the category `Type u`, monomorphisms
are stable under cobase change and filtered colimits.

-/

universe v' u' u

namespace CategoryTheory

open MorphismProperty Limits Types

namespace Types

example : (monomorphisms (Type u)).IsStableUnderRetracts := inferInstance

instance : (monomorphisms (Type u)).IsStableUnderCobaseChange where
  of_isPushout {X₁ X₂ X₃ X₄ t l r b} sq ht := by
    simp only [monomorphisms.iff, mono_iff_injective] at ht ⊢
    exact Limits.Types.pushoutCocone_injective_inr_of_isColimit sq.flip.isColimit ht

lemma isStableUnderColimitsOfShape_monomorphisms_of_isFiltered
    (J : Type u') [Category.{v'} J] [IsFiltered J] :
    (monomorphisms (Type u)).IsStableUnderColimitsOfShape J := by
  intro F₁ F₂ c₁ c₂ hc₁ hc₂ f hf
  simp only [functorCategory, monomorphisms.iff, mono_iff_injective] at hf
  let φ : c₁.pt ⟶ c₂.pt := hc₁.desc { ι := f ≫ c₂.ι }
  have hφ (j : J) : c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j := hc₁.fac _ j
  replace hφ (j : J) := congr_fun (hφ j)
  dsimp at hφ
  change Mono φ
  rw [mono_iff_injective]
  intro x₁ y₁ h
  obtain ⟨j, x₁, y₁, rfl, rfl⟩ : ∃ (j : J) (x₁' y₁' : F₁.obj j),
      x₁ = c₁.ι.app j x₁' ∧ y₁ = c₁.ι.app j y₁' := by
    obtain ⟨j, x₁, rfl⟩ := jointly_surjective_of_isColimit hc₁ x₁
    obtain ⟨l, y₁, rfl⟩ := jointly_surjective_of_isColimit hc₁ y₁
    exact ⟨_,  _, _, congr_fun (c₁.w (IsFiltered.leftToMax j l)).symm _,
      congr_fun (c₁.w (IsFiltered.rightToMax j l)).symm _⟩
  rw [hφ, hφ] at h
  obtain ⟨k, α, hk⟩ := (FilteredColimit.isColimit_eq_iff' hc₂ _ _).1 h
  simp only [← FunctorToTypes.naturality] at hk
  rw [← c₁.w α, types_comp_apply, types_comp_apply, hf _ hk]

end Types

end CategoryTheory
