/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
#  Riesz–Markov–Kakutani representation theorem for `ℝ≥0`

This file proves the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `ℝ≥0`-linear functionals `Λ`.

## Implementation notes

The proof depends on the version of the theorem for `ℝ`-linear functional Λ because in a standard
proof one has to prove the inequalities by `le_antisymm`, yet for `C_c(X, ℝ≥0)` there is no `Neg`.
Here we prove the result by writing `ℝ≥0`-linear `Λ` in terms of `ℝ`-linear `toRealLinear Λ` and by
reducing the statement to the `ℝ`-version of the theorem.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

open scoped NNReal

open CompactlySupported CompactlySupportedContinuousMap MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

namespace NNRealRMK

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (Bochner) integral of `f` (as a `ℝ`-valued function) with respect to the `rieszMeasure`
associated to `Λ` is equal to `Λ f`. -/
theorem integral_rieszMeasure (f : C_c(X, ℝ≥0)) : ∫ (x : X), (f x : ℝ) ∂(rieszMeasure Λ) = Λ f := by
  rw [← eq_toRealPositiveLinear_toReal Λ f,
      ← RealRMK.integral_rieszMeasure (toRealPositiveLinear Λ) f.toReal]
  simp [RealRMK.rieszMeasure, NNRealRMK.rieszMeasure]

/-- The **Riesz-Markov-Kakutani representation theorem**: given a positive linear functional `Λ`,
the (lower) Lebesgue integral of `f` with respect to the `rieszMeasure` associated to `Λ` is equal
to `Λ f`. -/
theorem lintegral_rieszMeasure (f : C_c(X, ℝ≥0)) : ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f := by
  rw [lintegral_coe_eq_integral, ← ENNReal.ofNNReal_toNNReal]
  · rw [ENNReal.coe_inj, Real.toNNReal_of_nonneg (MeasureTheory.integral_nonneg (by intro a; simp)),
       NNReal.eq_iff, NNReal.coe_mk]
    exact integral_rieszMeasure Λ f
  rw [rieszMeasure]
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.comp_left f.hasCompactSupport rfl)

/-If two regular measures give the same integral for every function in `C_c(X, ℝ≥0)`, then they
are equal.-/
theorem eq_of_integral_eq_on_Cc {μ ν : Measure X} [Measure.Regular μ] [Measure.Regular ν]
    (hμν : ∀ (f : C_c(X, ℝ≥0)), ∫ (x : X), (f x : ℝ) ∂μ = ∫ (x : X), (f x : ℝ) ∂ν) : μ = ν := by
  apply RealRMK.eq_of_integral_eq_on_Cc
  intro f
  calc
    ∫ (x : X), f x ∂μ
      = ∫ (x : X), ↑(f x).toNNReal ∂μ - ∫ (x : X), ↑(-f x).toNNReal ∂μ := by
      apply integral_eq_integral_pos_part_sub_integral_neg_part
      exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2
    _ = ∫ (x : X), ↑(f x).toNNReal ∂ν - ∫ (x : X), ↑(-f x).toNNReal ∂ν:= by
      have h1 : ∫ (x : X), ((f x).toNNReal : ℝ) ∂μ = ∫ (x : X), ((f x).toNNReal : ℝ) ∂ν := by
        refine hμν ⟨⟨Real.toNNReal ∘ f, ?_⟩, ?_⟩
        · exact continuous_real_toNNReal.comp f.1.2
        · exact HasCompactSupport.comp_left (g := Real.toNNReal) f.2 Real.toNNReal_zero
      have h2 : ∫ (x : X), ((-f x).toNNReal : ℝ) ∂μ = ∫ (x : X), ((-f x).toNNReal : ℝ) ∂ν := by
        refine hμν ⟨⟨Real.toNNReal ∘ (-f), ?_⟩, ?_⟩
        · exact continuous_real_toNNReal.comp (-f).1.2
        · exact HasCompactSupport.comp_left (g := Real.toNNReal) (-f).2 Real.toNNReal_zero
      rw [h1, h2]
    _ = ∫ (x : X), f x ∂ν := by
      symm
      apply integral_eq_integral_pos_part_sub_integral_neg_part
      exact Continuous.integrable_of_hasCompactSupport f.1.2 f.2

/-- Let μ be a measure that is finite on compact sets. Then μ induces a linear functional on
`C_c(X, ℝ≥0)`. -/
noncomputable def integralLinearMap (μ : Measure X) [OpensMeasurableSpace X]
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] :
    C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 :=
  CompactlySupportedContinuousMap.toNNRealLinear (RealRMK.integralPositiveLinearMap μ)

/-If two regular measures induce the same linear functional on `C_c(X, ℝ≥0)`, then they are equal.-/
theorem eq_of_eq_integralLinearMap {μ ν : Measure X} [Measure.Regular μ]
    [Measure.Regular ν] (hμν : integralLinearMap μ = integralLinearMap ν) : μ = ν := by
  apply eq_of_integral_eq_on_Cc
  intro f
  simp only [integralLinearMap, RealRMK.integralPositiveLinearMap, PositiveLinearMap.mk₀,
    toNNRealLinear_inj, PositiveLinearMap.mk.injEq, LinearMap.mk.injEq, AddHom.mk.injEq] at hμν
  simpa using congr_fun hμν (CompactlySupportedContinuousMap.toReal f)

/-The Riesz measure induced by a linear functional on `C_c(X, ℝ≥0)` is regular.-/
instance rieszMeasure_regular (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : (rieszMeasure Λ).Regular :=
  Content.regular (rieszContent Λ)

/-- NNRealRMK.rieszMeasure is a surjective function. That is, every regular measure is induced by a
positive linear functional on `C_c(X, ℝ≥0)`. -/
theorem rieszMeasure_surjective {μ : Measure X} [Measure.Regular μ] :
    μ = rieszMeasure (integralLinearMap μ) := by
  apply eq_of_integral_eq_on_Cc
  intro f
  trans ((integralLinearMap μ) f : ℝ)
  · simp [← toReal_apply]
    rfl
  · exact (integral_rieszMeasure (integralLinearMap μ) f).symm

end NNRealRMK
