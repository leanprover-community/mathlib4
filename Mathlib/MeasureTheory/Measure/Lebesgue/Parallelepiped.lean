/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Justus Springer
-/
module

public import Mathlib.Analysis.Convex.Measure

/-!
# Measure of parallelepipeds

We compute additive Haar measures of half-open parallelepipeds, by comparing them with the closed
parallelepipeds.

## Main statements

* `halfOpenParallelepiped_ae_eq_parallelepiped`: a half-open parallelepiped is almost everywhere
  equal to the closed one, for any additive Haar measure.
* `addHaar_halfOpenParallelepiped_eq`: `μ (halfOpenParallelepiped ℝ v)` is
  `|b₀.det v| * μ (halfOpenParallelepiped ℝ b₀)`.
-/

@[expose] public section

open MeasureTheory Measure Set

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

@[measurability]
theorem measurableSet_halfOpenParallelepiped [OpensMeasurableSpace E] (b : Module.Basis ι ℝ E) :
    MeasurableSet (halfOpenParallelepiped ℝ b) := by
  rw [halfOpenParallelepiped_basis_eq, ofPred_forall]
  exact MeasurableSet.iInter fun i ↦
    ((continuous_apply i).comp b.equivFunL.continuous).measurable measurableSet_Ico

variable [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]

theorem halfOpenParallelepiped_ae_eq_parallelepiped (v : ι → E) :
    halfOpenParallelepiped ℝ v =ᵐ[μ] parallelepiped ℝ v := by
  refine (halfOpenParallelepiped_subset_parallelepiped v).eventuallyLE.antisymm (ae_le_set.mpr ?_)
  refine measure_mono_null ?_ ((convex_parallelepiped v).addHaar_frontier μ)
  rw [(isClosed_parallelepiped v).frontier_eq]
  exact sdiff_subset_sdiff_right (interior_parallelepiped_subset_halfOpenParallelepiped v)

theorem addHaar_halfOpenParallelepiped (v : ι → E) :
    μ (halfOpenParallelepiped ℝ v) = μ (parallelepiped ℝ v) :=
  measure_congr (halfOpenParallelepiped_ae_eq_parallelepiped μ v)

theorem addHaar_halfOpenParallelepiped_ne_zero (b : Module.Basis ι ℝ E) :
    μ (halfOpenParallelepiped ℝ b) ≠ 0 := by
  rw [addHaar_halfOpenParallelepiped]
  exact (measure_pos_of_nonempty_interior μ b.parallelepiped.interior_nonempty).ne'

theorem addHaar_halfOpenParallelepiped_eq [DecidableEq ι] (b₀ : Module.Basis ι ℝ E) (v : ι → E) :
    μ (halfOpenParallelepiped ℝ v) =
      ENNReal.ofReal |b₀.det v| * μ (halfOpenParallelepiped ℝ b₀) := by
  rw [addHaar_halfOpenParallelepiped, addHaar_halfOpenParallelepiped,
    addHaarMeasure_unique μ b₀.parallelepiped, ← Module.Basis.addHaar_def]
  simp [addHaar_parallelepiped, Module.Basis.det_self, mul_comm]

theorem addHaar_real_halfOpenParallelepiped_eq [DecidableEq ι] (b₀ : Module.Basis ι ℝ E)
    (v : ι → E) :
    μ.real (halfOpenParallelepiped ℝ v) = |b₀.det v| * μ.real (halfOpenParallelepiped ℝ b₀) := by
  simp [measureReal_def, addHaar_halfOpenParallelepiped_eq μ b₀ v]

@[simp]
theorem volume_halfOpenParallelepiped [DecidableEq ι] (v : ι → ι → ℝ) :
    volume (halfOpenParallelepiped ℝ v) = ENNReal.ofReal |(Matrix.of v).det| := by
  rw [addHaar_halfOpenParallelepiped_eq volume (Pi.basisFun ℝ ι) v, halfOpenParallelepiped_basisFun,
    Pi.basisFun_det_apply]
  simp [volume_pi]

@[simp]
theorem volume_real_halfOpenParallelepiped [DecidableEq ι] (v : ι → ι → ℝ) :
    volume.real (halfOpenParallelepiped ℝ v) = |(Matrix.of v).det| := by
  simp [measureReal_def]
