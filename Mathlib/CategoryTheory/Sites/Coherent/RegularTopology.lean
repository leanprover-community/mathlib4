/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.RegularSheaves
/-!

# Description of the covering sieves of the regular topology

This file characterises the covering sieves of the regular topology.

## Main result

* `regularTopology.mem_sieves_iff_hasEffectiveEpi`: a sieve is a covering sieve for the
  regular topology if and only if it contains an effective epi.
-/

namespace CategoryTheory.regularTopology

open Limits

variable {C : Type*} [Category C] [Preregular C] {X : C}

/--
For a preregular category, any sieve that contains an `EffectiveEpi` is a covering sieve of the
regular topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpi`, but is needed for the proof.
-/
theorem mem_sieves_of_hasEffectiveEpi (S : Sieve X) :
    (∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ S.arrows π) → (S ∈ (regularTopology C).sieves X) := by
  rintro ⟨Y, π, h⟩
  have h_le : Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun _ ↦ π)) ≤ S := by
    rw [Sieve.sets_iff_generate (Presieve.ofArrows _ _) S]
    apply Presieve.le_of_factorsThru_sieve (Presieve.ofArrows _ _) S _
    intro W g f
    refine ⟨W, 𝟙 W, ?_⟩
    cases f
    exact ⟨π, ⟨h.2, Category.id_comp π⟩⟩
  apply Coverage.saturate_of_superset (regularCoverage C) h_le
  exact Coverage.saturate.of X _ ⟨Y, π, rfl, h.1⟩

/-- Effective epis in a preregular category are stable under composition. -/
instance {Y Y' : C} (π : Y ⟶ X) [EffectiveEpi π]
    (π' : Y' ⟶ Y) [EffectiveEpi π'] : EffectiveEpi (π' ≫ π) := by
  rw [effectiveEpi_iff_effectiveEpiFamily, ← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows _ _)) ∈
      GrothendieckTopology.sieves (regularTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => regularTopology.isSheaf_yoneda_obj W _ h₂
  apply Coverage.saturate.transitive X (Sieve.generate (Presieve.ofArrows (fun () ↦ Y)
      (fun () ↦ π)))
  · apply Coverage.saturate.of
    use Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (regularTopology C).pullback_stable'
    apply regularTopology.mem_sieves_of_hasEffectiveEpi
    cases hY
    exact ⟨Y', π', inferInstance, Y', (𝟙 _), π' ≫ π, Presieve.ofArrows.mk (), (by simp)⟩

/-- A sieve is a cover for the regular topology if and only if it contains an `EffectiveEpi`. -/
theorem mem_sieves_iff_hasEffectiveEpi (S : Sieve X) :
    (S ∈ (regularTopology C).sieves  X) ↔
    ∃ (Y : C) (π : Y ⟶ X), EffectiveEpi π ∧ (S.arrows π) := by
  constructor
  · intro h
    induction' h with Y T hS Y Y R S _ _ a b
    · rcases hS with ⟨Y', π, h'⟩
      refine ⟨Y', π, h'.2, ?_⟩
      rcases h' with ⟨rfl, _⟩
      exact ⟨Y', 𝟙 Y', π, Presieve.ofArrows.mk (), (by simp)⟩
    · exact ⟨Y, (𝟙 Y), inferInstance, by simp only [Sieve.top_apply, forall_const]⟩
    · rcases a with ⟨Y₁, π, ⟨h₁,h₂⟩⟩
      choose Y' π' _ H using b h₂
      exact ⟨Y', π' ≫ π, inferInstance, (by simpa using H)⟩
  · exact regularTopology.mem_sieves_of_hasEffectiveEpi S

end CategoryTheory.regularTopology
