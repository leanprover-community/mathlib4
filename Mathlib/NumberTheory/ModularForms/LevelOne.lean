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

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic

local notation "𝕢" => qParam

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

namespace SlashInvariantForm

variable [SlashInvariantFormClass F Γ(1) k]

lemma exists_one_half_le_im_and_norm_le (hk : k ≤ 0) (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1 / 2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ :=
  let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by simpa only [slash_action_eqn'' _ (mem_Gamma_one γ),
    norm_mul, norm_zpow] using le_mul_of_one_le_left (norm_nonneg _) <|
      one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

variable (k) in
/-- If a constant function is modular of weight `k`, then either `k = 0`, or the constant is `0`. -/
lemma wt_eq_zero_of_eq_const {f : F} {c : ℂ} (hf : ⇑f = Function.const _ c) :
    k = 0 ∨ c = 0 := by
  have hI := slash_action_eqn'' f (mem_Gamma_one S) I
  have h2I2 := slash_action_eqn'' f (mem_Gamma_one S) ⟨2 * Complex.I, by norm_num⟩
  simp_rw [sl_moeb, hf, Function.const, denom_S, coe_mk_subtype] at hI h2I2
  nth_rw 1 [h2I2] at hI
  simp only [mul_zpow, coe_I, mul_eq_mul_right_iff, mul_left_eq_self₀] at hI
  refine hI.imp_left (Or.casesOn · (fun H ↦ ?_) (False.elim ∘ zpow_ne_zero k I_ne_zero))
  rwa [← ofReal_ofNat, ← ofReal_zpow, ← ofReal_one, ofReal_inj,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at H

end SlashInvariantForm

namespace ModularFormClass

variable [ModularFormClass F Γ(1) k]

private theorem cuspFunction_eqOn_const_of_nonpos_wt (hk : k ≤ 0) (f : F) :
    Set.EqOn (cuspFunction 1 f) (const ℂ (cuspFunction 1 f 0)) (Metric.ball 0 1) := by
  refine eq_const_of_exists_le (fun q hq ↦ ?_) (exp_nonneg (-π)) ?_ (fun q hq ↦ ?_)
  · exact (differentiableAt_cuspFunction 1 f (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  · simp only [exp_lt_one_iff, Left.neg_neg_iff, pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f
        ⟨_, im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'⟩
      exact ⟨_, norm_qParam_le_of_one_half_le_im hξ,
        by simpa only [← eq_cuspFunction 1 f, Nat.cast_one, coe_mk_subtype,
          qParam_right_inv one_ne_zero hq'] using hξ₂⟩

private theorem levelOne_nonpos_wt_const (hk : k ≤ 0) (f : F) :
    ⇑f = Function.const _ (cuspFunction 1 f 0) := by
  ext z
  have hQ : 𝕢 1 z ∈ (Metric.ball 0 1) := by
    simpa only [Metric.mem_ball, dist_zero_right, neg_mul, mul_zero, div_one, Real.exp_zero]
      using (norm_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
  simpa only [← eq_cuspFunction 1 f z, Nat.cast_one, Function.const_apply] using
    (cuspFunction_eqOn_const_of_nonpos_wt hk f) hQ

lemma levelOne_neg_weight_eq_zero (hk : k < 0) (f : F) : ⇑f = 0 := by
  have hf := levelOne_nonpos_wt_const hk.le f
  rcases wt_eq_zero_of_eq_const k hf with rfl | hf₀
  · exact (lt_irrefl _ hk).elim
  · rw [hf, hf₀, const_zero]

lemma levelOne_weight_zero_const [ModularFormClass F Γ(1) 0] (f : F) :
    ∃ c, ⇑f = Function.const _ c :=
  ⟨_, levelOne_nonpos_wt_const le_rfl f⟩

end ModularFormClass

lemma ModularForm.levelOne_weight_zero_rank_one : Module.rank ℂ (ModularForm Γ(1) 0) = 1 := by
  refine rank_eq_one (const 1) (by simp [DFunLike.ne_iff]) fun g ↦ ?_
  obtain ⟨c', hc'⟩ := levelOne_weight_zero_const g
  aesop

lemma ModularForm.levelOne_neg_weight_rank_zero (hk : k < 0) :
    Module.rank ℂ (ModularForm Γ(1) k) = 0 := by
  refine rank_eq_zero_iff.mpr fun f ↦ ⟨_, one_ne_zero, ?_⟩
  simpa only [one_smul, ← DFunLike.coe_injective.eq_iff] using levelOne_neg_weight_eq_zero hk f
