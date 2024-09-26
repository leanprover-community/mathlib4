/-
Copyright (c) 2024 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Differentiabilty of the norm in a real normed vector space

This file provides basic results about the differentiability of the norm in a real vector space.
Typically, we give the links between differentiability as `x` and `t • x`, and also prove
that if the norm is differentiable at `x` then `fderiv ℝ (‖·‖) x x = ‖x‖` (`fderiv_norm_self`)
and `‖fderiv ℝ (‖·‖) x‖ = 1` (`norm_fderiv_norm`).

## Tags

differentiability, norm

-/

open Filter Real Set NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x : E} {t : ℝ}

theorem hasFDerivAt_norm_smul (ht : t ≠ 0) {f : E →L[ℝ] ℝ} (hx : HasFDerivAt (‖·‖) f x) :
    HasFDerivAt (‖·‖) ((SignType.sign t : ℝ) • f) (t • x) := by
  replace hx := (hx.hasFDerivAtFilter le_rfl).isLittleO
  constructor
  rw [Asymptotics.isLittleO_iff] at *
  intro c hc
  have := hx hc
  rw [eventually_iff, ← smul_mem_nhds_smul_iff₀ ht] at this
  filter_upwards [this]
  rintro - ⟨ε, hε, rfl⟩
  simp only
  rw [norm_smul, norm_smul, ← smul_sub, _root_.map_smul, ← ContinuousLinearMap.smul_apply,
    smul_smul, self_mul_sign, ContinuousLinearMap.smul_apply, ← norm_eq_abs, smul_eq_mul,
    ← mul_sub, ← mul_sub, norm_mul, norm_norm, norm_smul, ← mul_assoc, mul_comm c, mul_assoc,
    _root_.mul_le_mul_left]
  · exact hε
  · exact norm_pos_iff.2 ht

theorem differentiableAt_norm_smul (ht : t ≠ 0) :
    DifferentiableAt ℝ (‖·‖) x ↔ DifferentiableAt ℝ (‖·‖) (t • x) where
  mp hd := (hasFDerivAt_norm_smul ht hd.hasFDerivAt).differentiableAt
  mpr hd := by
    convert (hasFDerivAt_norm_smul (inv_ne_zero ht) hd.hasFDerivAt).differentiableAt
    rw [smul_smul, inv_mul_cancel₀ ht, one_smul]

variable (E) in
theorem not_differentiableAt_norm_zero [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ E 0
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := DifferentiableAt.comp _ (by simpa) (by simp)
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have aux : abs = fun t ↦ (1 / ‖x‖) * (|t| * ‖x‖) := by field_simp
    rw [aux]
    exact this.const_mul _
  exact not_differentiableAt_abs_zero this

theorem differentiableAt_norm_of_smul (h : DifferentiableAt ℝ (‖·‖) (t • x)) :
    DifferentiableAt ℝ (‖·‖) x := by
  obtain rfl | ht := eq_or_ne t 0
  · by_cases hE : Nontrivial E
    · rw [zero_smul] at h
      exact not_differentiableAt_norm_zero E h |>.elim
    · rw [not_nontrivial_iff_subsingleton] at hE
      exact (hasFDerivAt_of_subsingleton _ _).differentiableAt
  · exact differentiableAt_norm_smul ht |>.2 h

theorem fderiv_norm_self {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [← h.lineDeriv_eq_fderiv, lineDeriv]
  have this (t : ℝ) : ‖x + t • x‖ = |1 + t| * ‖x‖ := by
    rw [← norm_eq_abs, ← norm_smul, add_smul, one_smul]
  simp_rw [this]
  rw [deriv_mul_const]
  · conv_lhs => enter [1, 1]; change abs ∘ (fun t ↦ 1 + t)
    rw [deriv.comp, deriv_abs, deriv_const_add]
    · simp
    · exact differentiableAt_abs (by norm_num)
    · exact differentiableAt_id.const_add _
  · exact (differentiableAt_abs (by norm_num)).comp _ (differentiableAt_id.const_add _)

theorem fderiv_norm_smul (x : E) (t : ℝ) :
    fderiv ℝ (‖·‖) (t • x) = (SignType.sign t : ℝ) • (fderiv ℝ (‖·‖) x) := by
  by_cases hE : Nontrivial E
  · by_cases hd : DifferentiableAt ℝ (‖·‖) x
    · obtain rfl | ht := eq_or_ne t 0
      · simp only [zero_smul, _root_.sign_zero, SignType.coe_zero]
        exact fderiv_zero_of_not_differentiableAt <| not_differentiableAt_norm_zero E
      · rw [(hasFDerivAt_norm_smul ht hd.hasFDerivAt).fderiv]
    · rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt]
      · simp
      · exact mt differentiableAt_norm_of_smul hd
  · rw [not_nontrivial_iff_subsingleton] at hE
    simp_rw [(hasFDerivAt_of_subsingleton _ _).fderiv, smul_zero]

theorem fderiv_norm_smul_pos (ht : 0 < t) :
    fderiv ℝ (‖·‖) (t • x) = fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

theorem fderiv_norm_smul_neg (ht : t < 0) :
    fderiv ℝ (‖·‖) (t • x) = -fderiv ℝ (‖·‖) x := by
  simp [fderiv_norm_smul, ht]

theorem norm_fderiv_norm [Nontrivial E] (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := by
    refine fun hx ↦ not_differentiableAt_norm_zero E ?_
    rwa [← hx]
  apply le_antisymm
  · rw [show (1 : ℝ) = ↑(1 : ℝ≥0) by rfl]
    exact norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm
  · apply le_of_mul_le_mul_right _ (norm_pos_iff.2 this)
    calc
      1 * ‖x‖ = fderiv ℝ (‖·‖) x x := by rw [one_mul, fderiv_norm_self h]
      _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
      _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _

/-- On a real finite-dimensional normed vector space,
  the norm is almost everywhere differentiable. -/
theorem ae_differentiableAt_norm [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure] :
  ∀ᵐ x ∂μ, DifferentiableAt ℝ (‖·‖) x := lipschitzWith_one_norm.ae_differentiableAt
