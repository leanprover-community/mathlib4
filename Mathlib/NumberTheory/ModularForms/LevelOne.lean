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
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic

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
  rwa [← ofReal_ofNat, ← ofReal_zpow, ← ofReal_one, ofReal_inj,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at H

namespace ModularFormClass

theorem neg_wt_cuspFunction_EqOn_const {k : ℤ} (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) k] (f : F) :
    Set.EqOn (cuspFunction 1 f) (const ℂ (cuspFunction 1 f 0)) (Metric.ball 0 1) := by
  have hdiff : DifferentiableOn ℂ (cuspFunction 1 f) (Metric.ball 0 1) := by
    exact fun z hz ↦ DifferentiableAt.differentiableWithinAt (differentiableAt_cuspFunction 1 f
      (mem_ball_zero_iff.mp hz))
  apply eq_const_of_exists_le (r := exp (-π)) hdiff (exp_nonneg _)
  · simp only [one_div, exp_lt_one_iff, Left.neg_neg_iff, pi_pos, mul_pos_iff_of_pos_left,
      sqrt_pos, Nat.ofNat_pos, inv_pos]
  · intro z hz
    rcases eq_or_ne z 0 with rfl | hz'
    · refine ⟨0, by simpa using exp_nonneg _, by rfl⟩
    · let t : ℍ := ⟨(invQParam 1 z), im_invQParam_pos_of_abs_lt_one Real.zero_lt_one
        (mem_ball_zero_iff.mp hz) hz'⟩
      obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f t
      use 𝕢 1 ξ
      rw [Metric.mem_closedBall, dist_zero_right]
      refine ⟨qParam_abs_le_of_one_half_le_abs hξ, ?_⟩
      simp only [one_div, ← eq_cuspFunction 1 f t, Nat.cast_one, Complex.norm_eq_abs, ←
        eq_cuspFunction 1 f ξ] at *
      rw [← qParam_right_inv one_ne_zero hz']
      exact hξ₂

theorem levelOne_neg_wt_const {k : ℤ} (hk : k ≤ 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) k] (f : F) (z : ℍ) :
    f z = Function.const ℍ (SlashInvariantFormClass.cuspFunction 1 f 0) z := by
  have hQ : 𝕢 1 z ∈ (Metric.ball 0 1) := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_eq_abs, neg_mul, mul_zero, div_one,
      Real.exp_zero] using (abs_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
  simpa only [← eq_cuspFunction 1 f z, Nat.cast_one, const_apply] using
    (neg_wt_cuspFunction_EqOn_const hk f) hQ

lemma levelOne_non_pos_weight_eq_zero {k : ℤ} (hk : k < 0) {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) k] (f : F) : ⇑f = 0 := by
  have H := (levelOne_neg_wt_const hk.le f)
  rcases (wt_eq_zero_of_eq_const k (c := cuspFunction 1 f 0) H) with rfl | HF
  · omega
  · rw [HF] at H
    exact funext fun z ↦ id (H z)

lemma levelOne_weight_zero_const {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ(1) 0] (f : F) : ∃ c : ℂ, ⇑f = fun _ => c := by
  refine ⟨(cuspFunction 1 (f) 0), funext fun z ↦ ((levelOne_neg_wt_const (show 0 ≤ 0 by rfl) f)) z⟩

end ModularFormClass

lemma ModularForm.levelOne_weight_zero_rank_one : Module.rank ℂ (ModularForm Γ(1) 0) = 1 := by
  let f := ModularForm.const 1 (Γ := Γ(1))
  have hf : f ≠ 0 := by
    rw [DFunLike.ne_iff]
    refine ⟨I, by simp only [const_toFun, const_apply, zero_apply, ne_eq, one_ne_zero,
      not_false_eq_true, f]⟩
  apply rank_eq_one f hf
  intro g
  obtain ⟨c', hc'⟩ := levelOne_weight_zero_const g
  use c'
  ext z
  simp only [zero_apply, ne_eq, (congrFun hc' z).symm, smul_apply, show f z = 1 by rfl, smul_eq_mul,
    mul_one] at *

lemma ModularForm.levelOne_non_pos_weight_rank_zero {k : ℤ} (hk : k < 0) :
    Module.rank ℂ (ModularForm Γ(1) k) = 0 := by
  rw [rank_eq_zero_iff]
  intro f
  refine ⟨1, (zero_ne_one' ℂ).symm, Eq.mpr (id (congrArg (fun x ↦ x = 0) (one_smul ℂ f)))
      (ModularForm.ext_iff.mpr (congrFun (levelOne_non_pos_weight_eq_zero hk f)))⟩
