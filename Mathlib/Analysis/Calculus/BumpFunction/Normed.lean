/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

#align_import analysis.calculus.bump_function_inner from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Normed bump function

In this file we define `ContDiffBump.normed f μ` to be the bump function `f` normalized so that
`∫ x, f.normed μ x ∂μ = 1` and prove some properties of this function.
-/

noncomputable section

open Function Filter Set Metric MeasureTheory
open scoped Topology

namespace ContDiffBump

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞} {μ : Measure E}

/-- A bump function normed so that `∫ x, f.normed μ x ∂μ = 1`. -/
protected def normed (μ : Measure E) : E → ℝ := fun x => f x / ∫ x, f x ∂μ
#align cont_diff_bump.normed ContDiffBump.normed

theorem normed_def {μ : Measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
  rfl
#align cont_diff_bump.normed_def ContDiffBump.normed_def

theorem nonneg_normed (x : E) : 0 ≤ f.normed μ x :=
  div_nonneg f.nonneg <| integral_nonneg f.nonneg'
#align cont_diff_bump.nonneg_normed ContDiffBump.nonneg_normed

theorem contDiff_normed {n : ℕ∞} : ContDiff ℝ n (f.normed μ) :=
  f.contDiff.div_const _
#align cont_diff_bump.cont_diff_normed ContDiffBump.contDiff_normed

theorem continuous_normed : Continuous (f.normed μ) :=
  f.continuous.div_const _
#align cont_diff_bump.continuous_normed ContDiffBump.continuous_normed

theorem normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) := by
  simp_rw [f.normed_def, f.sub]
#align cont_diff_bump.normed_sub ContDiffBump.normed_sub

theorem normed_neg (f : ContDiffBump (0 : E)) (x : E) : f.normed μ (-x) = f.normed μ x := by
  simp_rw [f.normed_def, f.neg]
#align cont_diff_bump.normed_neg ContDiffBump.normed_neg

variable [BorelSpace E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

protected theorem integrable : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
#align cont_diff_bump.integrable ContDiffBump.integrable

protected theorem integrable_normed : Integrable (f.normed μ) μ :=
  f.integrable.div_const _
#align cont_diff_bump.integrable_normed ContDiffBump.integrable_normed

variable [μ.IsOpenPosMeasure]

theorem integral_pos : 0 < ∫ x, f x ∂μ := by
  refine' (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr _
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos
#align cont_diff_bump.integral_pos ContDiffBump.integral_pos

theorem integral_normed : ∫ x, f.normed μ x ∂μ = 1 := by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel f.integral_pos.ne'
#align cont_diff_bump.integral_normed ContDiffBump.integral_normed

theorem support_normed_eq : Function.support (f.normed μ) = Metric.ball c f.rOut := by
  unfold ContDiffBump.normed
  rw [support_div, f.support_eq, support_const f.integral_pos.ne', inter_univ]
#align cont_diff_bump.support_normed_eq ContDiffBump.support_normed_eq

theorem tsupport_normed_eq : tsupport (f.normed μ) = Metric.closedBall c f.rOut := by
  rw [tsupport, f.support_normed_eq, closure_ball _ f.rOut_pos.ne']
#align cont_diff_bump.tsupport_normed_eq ContDiffBump.tsupport_normed_eq

theorem hasCompactSupport_normed : HasCompactSupport (f.normed μ) := by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]
#align cont_diff_bump.has_compact_support_normed ContDiffBump.hasCompactSupport_normed

theorem tendsto_support_normed_smallSets {ι} {φ : ι → ContDiffBump c} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => Function.support fun x => (φ i).normed μ x) l (𝓝 c).smallSets := by
  simp_rw [NormedAddCommGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε ↦ (hφ ε hε).mono fun i hi ↦ ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le
#align cont_diff_bump.tendsto_support_normed_small_sets ContDiffBump.tendsto_support_normed_smallSets

variable (μ)

theorem integral_normed_smul {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (z : X) : ∫ x, f.normed μ x • z ∂μ = z := by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]
#align cont_diff_bump.integral_normed_smul ContDiffBump.integral_normed_smul

end ContDiffBump
