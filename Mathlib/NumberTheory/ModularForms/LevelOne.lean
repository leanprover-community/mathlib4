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

TODO: Add finite-dimensionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex MatrixGroups

lemma SlashInvariantForm.exists_one_half_le_im_and_norm_le {k : ℤ} (hk : k ≤ 0) {F : Type*}
    [FunLike F ℍ ℂ] [SlashInvariantFormClass F ⊤ k] (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1/2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ :=
  let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by simpa only [slash_action_eqn'' _ (show γ ∈ ⊤ by tauto), norm_mul, norm_zpow]
    using le_mul_of_one_le_left (norm_nonneg _) <|
      one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

/-- If a constant function is modular of weight `k`, then either `k = 0`, or the constant is `0`. -/
lemma SlashInvariantForm.wt_eq_zero_of_eq_const
    {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) [SlashInvariantFormClass F ⊤ k]
    {f : F} {c : ℂ} (hf : ∀ τ, f τ = c) : k = 0 ∨ c = 0 := by
  have hI := slash_action_eqn'' f (by tauto : ModularGroup.S ∈ ⊤) I
  have h2I2 := slash_action_eqn'' f (by tauto : ModularGroup.S ∈ ⊤) ⟨2 * Complex.I, by simp⟩
  simp only [sl_moeb, hf, denom_S, coe_mk_subtype] at hI h2I2
  nth_rw 1 [h2I2] at hI
  simp only [mul_zpow, coe_I, mul_eq_mul_right_iff, mul_left_eq_self₀] at hI
  refine hI.imp_left (Or.casesOn · (fun H ↦ ?_) (False.elim ∘ zpow_ne_zero k I_ne_zero))
  rwa [← Complex.ofReal_ofNat, ← ofReal_zpow, ← ofReal_one, ofReal_inj,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at H
