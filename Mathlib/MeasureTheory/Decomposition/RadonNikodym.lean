/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Decomposition.Lebesgue

#align_import measure_theory.decomposition.radon_nikodym from "leanprover-community/mathlib"@"fc75855907eaa8ff39791039710f567f37d4556f"

/-!
# Radon-Nikodym theorem

This file proves the Radon-Nikodym theorem. The Radon-Nikodym theorem states that, given measures
`μ, ν`, if `HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous with respect to
`ν` if and only if there exists a measurable function `f : α → ℝ≥0∞` such that `μ = fν`.
In particular, we have `f = rnDeriv μ ν`.

The Radon-Nikodym theorem will allow us to define many important concepts in probability theory,
most notably probability cumulative functions. It could also be used to define the conditional
expectation of a real function, but we take a different approach (see the file
`MeasureTheory/Function/ConditionalExpectation`).

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq` :
  the Radon-Nikodym theorem
* `MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq` :
  the Radon-Nikodym theorem for signed measures

## Tags

Radon-Nikodym theorem
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal

variable {α β : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

namespace Measure

theorem withDensity_rnDeriv_eq (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) :
    ν.withDensity (rnDeriv μ ν) = μ := by
  obtain ⟨_, ⟨E, hE₁, hE₂, hE₃⟩, hadd⟩ := haveLebesgueDecomposition_spec μ ν
  -- ⊢ withDensity ν (rnDeriv μ ν) = μ
  have : singularPart μ ν = 0 := by
    refine' le_antisymm (fun A (_ : MeasurableSet A) => _) (Measure.zero_le _)
    suffices singularPart μ ν Set.univ = 0 by
      rw [Measure.coe_zero, Pi.zero_apply, ← this]
      exact measure_mono (Set.subset_univ _)
    rw [← measure_add_measure_compl hE₁, hE₂, zero_add]
    have : (singularPart μ ν + ν.withDensity (rnDeriv μ ν)) Eᶜ = μ Eᶜ := by rw [← hadd]
    rw [Measure.coe_add, Pi.add_apply, h hE₃] at this
    exact (add_eq_zero_iff.1 this).1
  rw [this, zero_add] at hadd
  -- ⊢ withDensity ν (rnDeriv μ ν) = μ
  exact hadd.symm
  -- 🎉 no goals
#align measure_theory.measure.with_density_rn_deriv_eq MeasureTheory.Measure.withDensity_rnDeriv_eq

/-- **The Radon-Nikodym theorem**: Given two measures `μ` and `ν`, if
`HaveLebesgueDecomposition μ ν`, then `μ` is absolutely continuous to `ν` if and only if
`ν.withDensity (rnDeriv μ ν) = μ`. -/
theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq {μ ν : Measure α}
    [HaveLebesgueDecomposition μ ν] : μ ≪ ν ↔ ν.withDensity (rnDeriv μ ν) = μ :=
  ⟨withDensity_rnDeriv_eq μ ν, fun h => h ▸ withDensity_absolutelyContinuous _ _⟩
#align measure_theory.measure.absolutely_continuous_iff_with_density_rn_deriv_eq MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq

theorem withDensity_rnDeriv_toReal_eq {μ ν : Measure α} [IsFiniteMeasure μ]
    [HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) {i : Set α} (hi : MeasurableSet i) :
    (∫ x in i, (μ.rnDeriv ν x).toReal ∂ν) = (μ i).toReal := by
  rw [integral_toReal, ← withDensity_apply _ hi, withDensity_rnDeriv_eq μ ν h]
  -- ⊢ AEMeasurable fun x => rnDeriv μ ν x
  · measurability
    -- 🎉 no goals
  · refine' ae_lt_top (μ.measurable_rnDeriv ν)
      (lt_of_le_of_lt (lintegral_mono_set i.subset_univ) _).ne
    rw [← withDensity_apply _ MeasurableSet.univ, withDensity_rnDeriv_eq μ ν h]
    -- ⊢ ↑↑μ Set.univ < ⊤
    exact measure_lt_top _ _
    -- 🎉 no goals
#align measure_theory.measure.with_density_rn_deriv_to_real_eq MeasureTheory.Measure.withDensity_rnDeriv_toReal_eq

end Measure

namespace SignedMeasure

open Measure VectorMeasure

theorem withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α) [SigmaFinite μ]
    (h : s ≪ᵥ μ.toENNRealVectorMeasure) : μ.withDensityᵥ (s.rnDeriv μ) = s := by
  rw [absolutelyContinuous_ennreal_iff, (_ : μ.toENNRealVectorMeasure.ennrealToMeasure = μ),
    totalVariation_absolutelyContinuous_iff] at h
  · ext1 i hi
    -- ⊢ ↑(withDensityᵥ μ (rnDeriv s μ)) i = ↑s i
    rw [withDensityᵥ_apply (integrable_rnDeriv _ _) hi, rnDeriv, integral_sub,
      withDensity_rnDeriv_toReal_eq h.1 hi, withDensity_rnDeriv_toReal_eq h.2 hi]
    · conv_rhs => rw [← s.toSignedMeasure_toJordanDecomposition]
      -- ⊢ ENNReal.toReal (↑↑(toJordanDecomposition s).posPart i) - ENNReal.toReal (↑↑( …
      erw [VectorMeasure.sub_apply]
      -- ⊢ ENNReal.toReal (↑↑(toJordanDecomposition s).posPart i) - ENNReal.toReal (↑↑( …
      rw [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi]
      -- 🎉 no goals
    all_goals
      rw [← integrableOn_univ]
      refine' IntegrableOn.restrict _ MeasurableSet.univ
      refine' ⟨_, hasFiniteIntegral_toReal_of_lintegral_ne_top _⟩
      · apply Measurable.aestronglyMeasurable
        measurability
      · rw [set_lintegral_univ]
        exact (lintegral_rnDeriv_lt_top _ _).ne
  · exact equivMeasure.right_inv μ
    -- 🎉 no goals
#align measure_theory.signed_measure.with_densityᵥ_rn_deriv_eq MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq

/-- The Radon-Nikodym theorem for signed measures. -/
theorem absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq (s : SignedMeasure α) (μ : Measure α)
    [SigmaFinite μ] : s ≪ᵥ μ.toENNRealVectorMeasure ↔ μ.withDensityᵥ (s.rnDeriv μ) = s :=
  ⟨withDensityᵥ_rnDeriv_eq s μ, fun h => h ▸ withDensityᵥ_absolutelyContinuous _ _⟩
#align measure_theory.signed_measure.absolutely_continuous_iff_with_densityᵥ_rn_deriv_eq MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq

end SignedMeasure

end MeasureTheory
