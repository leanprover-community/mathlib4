/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite dimisionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex MatrixGroups


lemma SlashInvariantForm.exists_norm_le {k : ℤ} (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ⊤ k] (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1/2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ := by
  obtain ⟨γ, hγ, hdenom⟩ := exists_translate' τ
  refine ⟨γ • τ, hγ, ?_⟩
  rw [slash_action_eqn'' _ (show γ ∈ ⊤ by tauto), norm_mul, norm_zpow]
  have h3 : 1 ≤ ‖denom (γ : SL(2, ℤ)) τ‖ ^ k := by
    apply one_le_zpow_of_nonpos₀ _ hdenom hk
    exact norm_pos_iff.2 (denom_ne_zero _ _)
  exact le_mul_of_one_le_left (norm_nonneg (f τ)) h3

-- find_home suggests Mathlib.Topology.ContinuousMap.StarOrdered which seems wrong..
lemma Complex.zpow_eq_one (k : ℤ) {n : ℝ} (hn : 1 < n) (h : (n : ℂ) ^ k = 1) : k = 0 := by
  have : (n : ℂ)^k = (n : ℝ)^k := by simp only [ofReal_natCast]
  rw [this] at h
  norm_cast at h
  replace h : (n : ℝ) ^ k = (n : ℝ) ^ (0 : ℤ) := by simp only [zpow_zero, ← h]
  exact zpow_right_injective₀ (a := (n : ℝ)) (by norm_cast at *; linarith) (by aesop) h

/-- If a non-zero constant is modular of weight `k`, then we must have `k = 0`.  -/
lemma SlashInvariantForm.wt_const_eq_zero {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) (f : F) (c : ℂ)
    [SlashInvariantFormClass F ⊤ k] (hf : ⇑f = (fun _ => c)) : k = 0 ∨ c = 0 := by
  have hI := slash_action_eqn'' f (by tauto : ModularGroup.S ∈ ⊤) I
  have h2I2 := slash_action_eqn'' f (by tauto : ModularGroup.S ∈ ⊤) ⟨2 * Complex.I, by simp⟩
  simp only [hf, sl_moeb, denom_S] at *
  nth_rw 1 [h2I2] at hI
  simp only [mul_eq_mul_right_iff] at hI
  rcases hI with H | H
  · left
    rw [UpperHalfPlane.I, mul_zpow, mul_left_eq_self₀] at H
    rcases H with H | H
    · apply Complex.zpow_eq_one k (one_lt_two) H
    · exact False.elim (zpow_ne_zero k I_ne_zero H)
  · exact Or.inr H
