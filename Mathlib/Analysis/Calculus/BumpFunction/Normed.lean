/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Normed bump function

In this file we define `ContDiffBump.normed f μ` to be the bump function `f` normalized so that
`∫ x, f.normed μ x ∂μ = 1` and prove some properties of this function.
-/

noncomputable section

open Function Filter Set Metric MeasureTheory Module Measure
open scoped Topology

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [MeasurableSpace E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞} {μ : Measure E}

/-- A bump function normed so that `∫ x, f.normed μ x ∂μ = 1`. -/
protected def normed (μ : Measure E) : E → ℝ := fun x ↦ f x / ∫ x, f x ∂μ

theorem normed_def {μ : Measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
  rfl

theorem nonneg_normed (x : E) : 0 ≤ f.normed μ x :=
  div_nonneg f.nonneg <| integral_nonneg f.nonneg'

theorem contDiff_normed {n : ℕ∞} : ContDiff ℝ n (f.normed μ) :=
  f.contDiff.div_const _

theorem continuous_normed : Continuous (f.normed μ) :=
  f.continuous.div_const _

theorem normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) := by
  simp_rw [f.normed_def, f.sub]

theorem normed_neg (f : ContDiffBump (0 : E)) (x : E) : f.normed μ (-x) = f.normed μ x := by
  simp_rw [f.normed_def, f.neg]

variable [BorelSpace E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

protected theorem integrable : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

protected theorem integrable_normed : Integrable (f.normed μ) μ :=
  f.integrable.div_const _

section
variable [μ.IsOpenPosMeasure]

theorem integral_pos : 0 < ∫ x, f x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr ?_
  rw [f.support_eq]
  exact measure_ball_pos μ c f.rOut_pos

theorem integral_normed : ∫ x, f.normed μ x ∂μ = 1 := by
  simp_rw [ContDiffBump.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ f.integral_pos.ne'

theorem support_normed_eq : Function.support (f.normed μ) = Metric.ball c f.rOut := by
  unfold ContDiffBump.normed
  rw [support_div, f.support_eq, support_const f.integral_pos.ne', inter_univ]

theorem tsupport_normed_eq : tsupport (f.normed μ) = Metric.closedBall c f.rOut := by
  rw [tsupport, f.support_normed_eq, closure_ball _ f.rOut_pos.ne']

theorem hasCompactSupport_normed : HasCompactSupport (f.normed μ) := by
  simp only [HasCompactSupport, f.tsupport_normed_eq (μ := μ), isCompact_closedBall]

theorem tendsto_support_normed_smallSets {ι} {φ : ι → ContDiffBump c} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i ↦ Function.support fun x ↦ (φ i).normed μ x) l (𝓝 c).smallSets := by
  simp_rw [NormedAddCommGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).rOut_pos.le] at hφ
  rw [nhds_basis_ball.smallSets.tendsto_right_iff]
  refine fun ε hε ↦ (hφ ε hε).mono fun i hi ↦ ?_
  rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le

variable (μ)

theorem integral_normed_smul {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (z : X) : ∫ x, f.normed μ x • z ∂μ = z := by
  simp_rw [integral_smul_const, f.integral_normed (μ := μ), one_smul]

end

variable (μ)

theorem measure_closedBall_le_integral : μ.real (closedBall c f.rIn) ≤ ∫ x, f x ∂μ := by calc
  μ.real (closedBall c f.rIn) = ∫ x in closedBall c f.rIn, 1 ∂μ := by simp
  _ = ∫ x in closedBall c f.rIn, f x ∂μ := setIntegral_congr_fun measurableSet_closedBall
        (fun x hx ↦ (one_of_mem_closedBall f hx).symm)
  _ ≤ ∫ x, f x ∂μ := setIntegral_le_integral f.integrable (Eventually.of_forall (fun x ↦ f.nonneg))

theorem normed_le_div_measure_closedBall_rIn [μ.IsOpenPosMeasure] (x : E) :
    f.normed μ x ≤ 1 / μ.real (closedBall c f.rIn) := by
  rw [normed_def]
  gcongr
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rIn_pos).ne' measure_closedBall_lt_top.ne
  · exact f.le_one
  · exact f.measure_closedBall_le_integral μ

theorem integral_le_measure_closedBall : ∫ x, f x ∂μ ≤ μ.real (closedBall c f.rOut) := by calc
  ∫ x, f x ∂μ = ∫ x in closedBall c f.rOut, f x ∂μ := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_)).symm
    apply f.zero_of_le_dist (le_of_lt _)
    simpa using hx
  _ ≤ ∫ x in closedBall c f.rOut, 1 ∂μ := by
    apply setIntegral_mono f.integrable.integrableOn _ (fun x ↦ f.le_one)
    simp [measure_closedBall_lt_top]
  _ = μ.real (closedBall c f.rOut) := by simp

theorem measure_closedBall_div_le_integral [IsAddHaarMeasure μ] (K : ℝ) (h : f.rOut ≤ K * f.rIn) :
    μ.real (closedBall c f.rOut) / K ^ finrank ℝ E ≤ ∫ x, f x ∂μ := by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  apply le_trans _ (f.measure_closedBall_le_integral μ)
  rw [div_le_iff₀ (pow_pos K_pos _), addHaar_real_closedBall' _ _ f.rIn_pos.le,
    addHaar_real_closedBall' _ _ f.rOut_pos.le, mul_assoc, mul_comm _ (K ^ _), ← mul_assoc,
    ← mul_pow, mul_comm _ K]
  gcongr
  exact f.rOut_pos.le

theorem normed_le_div_measure_closedBall_rOut [IsAddHaarMeasure μ] (K : ℝ) (h : f.rOut ≤ K * f.rIn)
    (x : E) :
    f.normed μ x ≤ K ^ finrank ℝ E / μ.real (closedBall c f.rOut) := by
  have K_pos : 0 < K := by
    simpa [f.rIn_pos, not_lt.2 f.rIn_pos.le] using mul_pos_iff.1 (f.rOut_pos.trans_le h)
  have : f x / ∫ y, f y ∂μ ≤ 1 / ∫ y, f y ∂μ := by
    gcongr
    · exact f.integral_pos.le
    · exact f.le_one
  apply this.trans
  rw [div_le_div_iff₀ f.integral_pos, one_mul, ← div_le_iff₀' (pow_pos K_pos _)]
  · exact f.measure_closedBall_div_le_integral μ K h
  · exact ENNReal.toReal_pos (measure_closedBall_pos _ _ f.rOut_pos).ne'
      measure_closedBall_lt_top.ne

end ContDiffBump
