/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Divergences.LogLikelihoodRatio
import Mathlib.Probability.Divergences.FDivergence

/-!
# Total Variation Divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

noncomputable
def TV (μ ν : Measure α) : ℝ≥0∞ := ⨆ s, μ s - ν s

def rnDerivGeOneSet (μ ν : Measure α) : Set α := {x | 1 ≤ μ.rnDeriv ν x}

lemma measurableSet_rnDerivGeOneSet (μ ν : Measure α) : MeasurableSet (rnDerivGeOneSet μ ν) :=
  Measure.measurable_rnDeriv _ _ measurableSet_Ici

lemma todo' [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {s : Set α} (hs : MeasurableSet s) :
    μ s - ν s = ENNReal.ofReal (∫ x in s, (μ.rnDeriv ν x).toReal - 1 ∂ν) := by
  rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn (integrable_const _),
    set_integral_const, smul_eq_mul, mul_one, Measure.set_integral_toReal_rnDeriv hμν hs,
    ENNReal.ofReal_sub, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp

lemma todo [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    {s : Set α} (hs : MeasurableSet s) :
    μ s - ν s ≤ μ (rnDerivGeOneSet μ ν) - ν (rnDerivGeOneSet μ ν) := by
  rw [todo' hμν hs]
  have : ∫ x in s, ENNReal.toReal (Measure.rnDeriv μ ν x) - 1 ∂ν
      ≤ ∫ x in s ∩ rnDerivGeOneSet μ ν, ENNReal.toReal (Measure.rnDeriv μ ν x) - 1 ∂ν := by
    sorry
  sorry

lemma tv_eq_sub_rnDerivGeOneSet [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    TV μ ν = μ (rnDerivGeOneSet μ ν) - ν (rnDerivGeOneSet μ ν) := by
  sorry

lemma tv_eq_integral [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    TV μ ν = 2⁻¹ * ENNReal.ofReal (∫ x, |(μ.rnDeriv ν x).toReal - 1| ∂ν) := by
  let s := {x | 1 ≤ μ.rnDeriv ν x}
  have hs : MeasurableSet s := Measure.measurable_rnDeriv μ ν measurableSet_Ici
  rw [← integral_add_compl hs]
  swap; · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).abs
  have h₁ : ∫ x in s, |(μ.rnDeriv ν x).toReal - 1| ∂ν
      = ∫ x in s, (μ.rnDeriv ν x).toReal - 1 ∂ν := by
    refine set_integral_congr_ae hs ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx_ne_top hxs
    simp only [Set.mem_setOf_eq] at hxs
    simp only [abs_eq_self, sub_nonneg]
    rw [← ENNReal.one_toReal, ENNReal.toReal_le_toReal]
    · exact hxs
    · simp
    · exact hx_ne_top
  have h₂ : ∫ x in sᶜ, |(μ.rnDeriv ν x).toReal - 1| ∂ν
      = ∫ x in sᶜ, 1 - (μ.rnDeriv ν x).toReal ∂ν := by
    refine set_integral_congr_ae hs.compl ?_
    filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx_ne_top hxs
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hxs
    rw [abs_of_nonpos]
    · simp
    · simp only [tsub_le_iff_right, zero_add]
      rw [← ENNReal.one_toReal, ENNReal.toReal_le_toReal]
      · exact hxs.le
      · exact hx_ne_top
      · simp
  rw [h₁, h₂, integral_sub _ (integrable_const _), integral_sub (integrable_const _)]
  rotate_left
  · exact Measure.integrable_toReal_rnDeriv.integrableOn
  · exact Measure.integrable_toReal_rnDeriv.integrableOn
  rw [Measure.set_integral_toReal_rnDeriv hμν hs, set_integral_const, set_integral_const,
    Measure.set_integral_toReal_rnDeriv hμν hs.compl, smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  have : (μ s).toReal - (ν s).toReal + ((ν sᶜ).toReal - (μ sᶜ).toReal)
      = 2 * ((μ s).toReal - (ν s).toReal) := by
    rw [prob_compl_eq_one_sub hs, prob_compl_eq_one_sub hs, ENNReal.toReal_sub_of_le,
      ENNReal.toReal_sub_of_le, ENNReal.one_toReal]
    · ring
    · exact prob_le_one
    · simp
    · exact prob_le_one
    · simp
  rw [this, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [tv_eq_sub_rnDerivGeOneSet hμν]
  rfl

end MeasureTheory
