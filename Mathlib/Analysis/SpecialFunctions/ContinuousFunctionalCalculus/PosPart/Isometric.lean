/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! # Facts about `CFC.posPart` and `CFC.negPart` involving norms

This file collects various facts about the positive and negative parts of elements of a
C⋆-algebra that involve the norm.

## Main results

* `CFC.norm_eq_max_norm_posPart_negPart`: states that `‖a‖ = max ‖a⁺‖ ‖a⁻‖`
* `CFC.norm_posPart_le` and `CFC.norm_negPart_le`: state that `‖a⁺‖ ≤ ‖a‖` and `‖a⁻‖ ≤ ‖a‖`
  respectively.
-/

namespace CFC

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [StarRing A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A (IsSelfAdjoint : A → Prop)]

lemma norm_eq_max_norm_posPart_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    ‖a‖ = max ‖a⁺‖ ‖a⁻‖ := by
  have hsubset₁ :
      (fun x => ‖x⁺‖) '' quasispectrum ℝ a ⊆ (fun x => ‖x‖) '' quasispectrum ℝ a := by
    intro x hx
    rw [Set.mem_image] at hx ⊢
    obtain ⟨z, hz₁, hz₂⟩ := hx
    by_cases hz₃ : z ≤ 0
    · refine ⟨0, quasispectrum.zero_mem ℝ a, ?_⟩
      rw [← posPart_eq_zero] at hz₃
      simp only [hz₃, norm_zero] at hz₂
      simp [← hz₂]
    · refine ⟨z, hz₁, ?_⟩
      replace hz₃ : 0 ≤ z := le_of_not_ge hz₃
      rw [← _root_.posPart_eq_self] at hz₃
      rwa [hz₃] at hz₂
  have hsubset₂ :
      (fun x => ‖x⁻‖) '' quasispectrum ℝ a ⊆ (fun x => ‖x‖) '' quasispectrum ℝ a := by
    intro x hx
    rw [Set.mem_image] at hx ⊢
    obtain ⟨z, hz₁, hz₂⟩ := hx
    by_cases hz₃ : 0 ≤ z
    · refine ⟨0, quasispectrum.zero_mem ℝ a, ?_⟩
      rw [← negPart_eq_zero] at hz₃
      simp only [hz₃, norm_zero] at hz₂
      simp [← hz₂]
    · refine ⟨z, hz₁, ?_⟩
      replace hz₃ : z ≤ 0 := le_of_not_ge hz₃
      rw [← _root_.negPart_eq_neg] at hz₃
      simpa [hz₃] using hz₂
  have hmain : IsGreatest ((fun x => ‖x‖) '' quasispectrum ℝ a) (‖a⁺‖ ⊔ ‖a⁻‖) := by
    refine ⟨?_, ?_⟩
    · rcases max_cases ‖a⁺‖ ‖a⁻‖ with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
      · rw [h₁, CFC.posPart_def]
        refine Set.mem_of_subset_of_mem hsubset₁ ?_
        exact (IsGreatest.norm_cfcₙ (𝕜 := ℝ) (fun x => x⁺) a).1
      · rw [h₁]
        refine Set.mem_of_subset_of_mem hsubset₂ ?_
        exact (IsGreatest.norm_cfcₙ (𝕜 := ℝ) (fun x => x⁻) a).1
    · intro x hx
      rw [le_max_iff]
      rw [Set.mem_image] at hx
      obtain ⟨z, hz₁, hz₂⟩ := hx
      by_cases hz_neg : z < 0
      · refine Or.inr ?_
        have := _root_.negPart_eq_neg.mpr (le_of_lt hz_neg)
        rw [← norm_neg z, ← this] at hz₂
        rw [CFC.negPart_def, ← hz₂]
        exact norm_apply_le_norm_cfcₙ _ _ hz₁
      · refine Or.inl ?_
        push_neg at hz_neg
        have := _root_.posPart_eq_self.mpr hz_neg
        rw [← this] at hz₂
        rw [CFC.posPart_def, ← hz₂]
        exact norm_apply_le_norm_cfcₙ _ _ hz₁
  exact IsGreatest.unique
    (NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_norm_quasispectrum a ha) hmain

lemma norm_posPart_le (a : A) : ‖a⁺‖ ≤ ‖a‖ := by
  by_cases ha : IsSelfAdjoint a
  · rw [norm_eq_max_norm_posPart_negPart a ha]
    exact le_max_left ‖a⁺‖ ‖a⁻‖
  · simp [posPart_eq_zero_of_not_isSelfAdjoint ha]

lemma norm_negPart_le (a : A) : ‖a⁻‖ ≤ ‖a‖ := by
  by_cases ha : IsSelfAdjoint a
  · rw [norm_eq_max_norm_posPart_negPart a ha]
    exact le_max_right ‖a⁺‖ ‖a⁻‖
  · simp [negPart_eq_zero_of_not_isSelfAdjoint ha]

end CFC
