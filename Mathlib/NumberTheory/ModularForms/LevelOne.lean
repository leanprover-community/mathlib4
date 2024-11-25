/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.QExpansion
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite-dimensionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex MatrixGroups
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass

local notation "𝕢" => Periodic.qParam

lemma SlashInvariantForm.exists_one_half_le_im_and_norm_le {k : ℤ} (hk : k ≤ 0) {F : Type*}
    [FunLike F ℍ ℂ] [SlashInvariantFormClass F Γ(1) k] (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1/2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ :=
  let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by simpa only [slash_action_eqn'' _ (show γ ∈ Γ(1) by rw [Gamma_one_top]; tauto),
    norm_mul, norm_zpow] using le_mul_of_one_le_left (norm_nonneg _) <|
      one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

/-- If a constant function is modular of weight `k`, then either `k = 0`, or the constant is `0`. -/
lemma SlashInvariantForm.wt_eq_zero_of_eq_const
    {F : Type*} [FunLike F ℍ ℂ] (k : ℤ) [SlashInvariantFormClass F Γ(1) k]
    {f : F} {c : ℂ} (hf : ∀ τ, f τ = c) : k = 0 ∨ c = 0 := by
  have hI := slash_action_eqn'' f (show ModularGroup.S ∈ Γ(1) by rw [Gamma_one_top]; tauto) I
  have h2I2 := slash_action_eqn'' f (show ModularGroup.S ∈ Γ(1) by rw [Gamma_one_top]; tauto)
    ⟨2 * Complex.I, by simp⟩
  simp only [sl_moeb, hf, denom_S, coe_mk_subtype] at hI h2I2
  nth_rw 1 [h2I2] at hI
  simp only [mul_zpow, coe_I, mul_eq_mul_right_iff, mul_left_eq_self₀] at hI
  refine hI.imp_left (Or.casesOn · (fun H ↦ ?_) (False.elim ∘ zpow_ne_zero k I_ne_zero))
  rwa [← Complex.ofReal_ofNat, ← ofReal_zpow, ← ofReal_one, ofReal_inj,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at H

lemma neg_wt_modform_zero (k : ℤ) (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) k] (f : F) : ⇑f = 0 ∨ (k = 0 ∧ ∃ c : ℂ, ⇑f = fun _ => c) := by
  have hdiff : DifferentiableOn ℂ (cuspFunction 1 f) (Metric.ball 0 1) := by
    apply fun z hz ↦ DifferentiableAt.differentiableWithinAt (differentiableAt_cuspFunction 1 f ?_)
    rw [@mem_ball_zero_iff] at hz
    exact hz
  have heq : Set.EqOn (cuspFunction 1 f) (Function.const ℂ ((cuspFunction 1 f) 0))
    (Metric.ball 0 1) := by
    apply eq_const_of_exists_le (r := exp (-(π * √3 * (1 / 2)))) hdiff
    · exact exp_nonneg _
    · simp only [one_div, exp_lt_one_iff, Left.neg_neg_iff, pi_pos, mul_pos_iff_of_pos_left,
      sqrt_pos, Nat.ofNat_pos, inv_pos]
    · intro z hz
      rcases eq_or_ne z 0 with rfl | hz'
      · refine ⟨0, by simpa using exp_nonneg _, by rfl⟩
      · let t : ℍ := ⟨(Function.Periodic.invQParam 1 z), by
          apply  Function.Periodic.im_invQParam_pos_of_abs_lt_one Real.zero_lt_one
            (mem_ball_zero_iff.mp hz) hz'⟩
        obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f t
        use 𝕢 1 ξ
        simp only [Metric.mem_closedBall, dist_zero_right]
        refine ⟨qParam_image_bound ξ hξ, ?_⟩
        rw [← eq_cuspFunction 1 f ξ, ← eq_cuspFunction 1 f t] at hξ₂
        simp at hξ₂
        convert hξ₂
        rw [← (Function.Periodic.qParam_right_inv one_ne_zero hz')]
        congr
  have H : ∀ z, ⇑f z = Function.const ℍ ((cuspFunction 1 f) 0) z:= by
    intro z
    have hQ : 𝕢 1 z ∈ (Metric.ball 0 1) := by
      simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_eq_abs, neg_mul, mul_zero, div_one,
        Real.exp_zero] using (Function.Periodic.abs_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
    simpa only [← eq_cuspFunction 1 f z, Nat.cast_one, const_apply] using heq hQ
  have HF := SlashInvariantForm.wt_eq_zero_of_eq_const k (c := cuspFunction 1 f 0) H
  rcases HF with HF | HF
  · right
    refine ⟨HF, (cuspFunction 1 (f) 0), by ext z; exact H z⟩
  · left
    rw [HF] at H
    ext z
    simpa using H z

lemma ModularForm_neg_weight_eq_zero (k : ℤ) (hk : k < 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) k] (f : F) : ⇑f = 0 := by
  rcases neg_wt_modform_zero k hk.le f with h | ⟨rfl, _, _⟩
  · exact h
  · aesop

lemma ModularForm_weight_zero_constant {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) 0] (f : F) : ∃ c : ℂ, ⇑f = fun _ => c := by
  rcases neg_wt_modform_zero 0 (by rfl) f with h1 | h2
  · refine ⟨0, ?_⟩
    simp only [h1]
    rfl
  · aesop

lemma weight_zero_rank_eq_one : Module.rank ℂ (ModularForm Γ(1) 0) = 1 := by
  let f := ModularForm.const 1 (Γ := Γ(1))
  have hf : f ≠ 0 := by
    rw [@DFunLike.ne_iff]
    use I
    simp only [ModularForm.const_toFun, const_apply, zero_apply, ne_eq, one_ne_zero,
      not_false_eq_true, f]
  apply rank_eq_one f hf
  intro g
  rw [@DFunLike.ne_iff] at hf
  obtain ⟨c', hc'⟩ := ModularForm_weight_zero_constant g
  use c'
  ext z
  simp only [zero_apply, ne_eq, SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe,
   smul_eq_mul] at *
  have : f z = 1 := rfl
  simp only [ModularForm.smul_apply, this, smul_eq_mul, mul_one]
  exact (congrFun hc' z).symm

lemma neg_weight_rank_zero (k : ℤ) (hk : k < 0) : Module.rank ℂ (ModularForm Γ(1) k) = 0 := by
  rw [rank_eq_zero_iff]
  intro f
  refine ⟨1, by simp, ?_⟩
  exact
    Eq.mpr (id (congrArg (fun x ↦ x = 0) (one_smul ℂ f)))
      (ModularForm.ext_iff.mpr (congrFun (ModularForm_neg_weight_eq_zero k hk f)))
