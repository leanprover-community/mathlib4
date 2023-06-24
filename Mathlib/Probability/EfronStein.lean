/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import Mathlib.Probability.Variance

open MeasureTheory Filter Finset

noncomputable section

open scoped BigOperators MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type _} [MeasurableSpace Ω]

def covariance (X Y : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  μ[(X - (fun _ => μ[X] : Ω → ℝ)) * (Y - (fun _ => μ[Y] : Ω → ℝ))]

scoped notation "Cov[" X "," Y "]" => ProbabilityTheory.covariance X Y MeasureTheory.MeasureSpace.volume

variable {X Y : Ω → ℝ} {μ : Measure Ω}

lemma covariance_self_eq_variance [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
  covariance X X μ = variance X μ := by
  simp [hX.variance_eq, covariance, pow_two]

local notation "⟪" x ", " y "⟫" => @inner ℝ ℝ _ x y

lemma Memℒp_two_mul_integrable (hX : Memℒp X 2 μ) (hY : Memℒp Y 2 μ) :
  Integrable (X * Y) μ := by
  sorry
  -- change Integrable (fun ω => ⟪hX.toLp X ω, hY.toLp Y ω⟫) μ


lemma covariance_def' [IsProbabilityMeasure μ] (hX : Memℒp X 2 μ) (hY : Memℒp Y 2 μ) :
  covariance X Y μ = μ[X * Y] - μ[X] * μ[Y] := by
  simp only [covariance, Pi.mul_apply, Pi.sub_apply, mul_sub, sub_mul]
  rw [integral_sub, integral_sub, integral_sub, integral_mul_left, integral_mul_left,
    integral_const, IsProbabilityMeasure.measure_univ, integral_mul_right]
  simp only [ENNReal.one_toReal, smul_eq_mul, one_mul, sub_sub_sub_cancel_right, sub_right_inj]
  . exact (hX.integrable one_le_two).mul_const _
  . exact integrable_const _
  . exact Memℒp_two_mul_integrable hX hY
  . exact (hY.integrable one_le_two).const_mul _
  . exact (Memℒp_two_mul_integrable hX hY).sub $ (hY.integrable one_le_two).const_mul _
  . exact Integrable.sub ((hX.integrable one_le_two).mul_const _) $ integrable_const _


end ProbabilityTheory
