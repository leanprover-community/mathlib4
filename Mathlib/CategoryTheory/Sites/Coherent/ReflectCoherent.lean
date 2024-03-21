/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Enough
import Mathlib.CategoryTheory.EffectiveEpi.Preserves
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
/-!

# Reflecting the property of being precoherent

We prove that given a fully faitful functor `F : C ⥤ D` which preserves and reflects finite
effective epimorphic families, such that for every object `X` of `D` there exists an object `W` of
`C` with an effective epi `π : F.obj W ⟶ X`, the category `C` is `Precoherent` whenever `D` is.
-/

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  [F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]
  [F.EffectivelyEnough]
  [Precoherent D] [Full F] [Faithful F]

lemma reflects_precoherent : Precoherent C where
  pullback {B₁ B₂} f α _ X₁ π₁ _ := by
    let Y₁ := fun a ↦ F.obj (X₁ a)
    let τ₁ := fun a ↦ F.map (π₁ a)
    have : EffectiveEpiFamily Y₁ τ₁ := inferInstance
    obtain ⟨β, _, Y₂, τ₂, H, i, ι, hh⟩ := Precoherent.pullback (F.map f) _ Y₁ τ₁ this
    -- let X₂ : β → C := fun b ↦ (h (Y₂ b)).choose
    let π₂ := fun b ↦ Full.preimage (F.π (Y₂ b) ≫ τ₂ b)
    refine ⟨β, inferInstance, _, π₂, F.finite_effectiveEpiFamily_of_map _ π₂ ?_, ⟨i,
      fun b ↦ Full.preimage (F.π (Y₂ b) ≫ ι b), ?_⟩⟩
    · have : ∀ b, EffectiveEpi (F.π (Y₂ b)) := inferInstance
      simp_rw [effectiveEpi_iff_effectiveEpiFamily] at this
      apply EffectiveEpiFamily.reindex (e := Equiv.sigmaPUnit β) _ (fun a ↦ F.map (π₂ a))
      simp only [Equiv.sigmaPUnit_apply, Full.witness, π₂]
      exact EffectiveEpiFamily.transitive_of_finite _ H _ this
    · intro b
      apply Faithful.map_injective (F := F)
      simp [π₂, hh b]
