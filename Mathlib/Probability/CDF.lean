/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.CondCdf

/-!
# Cumulative distribution function of a real probability measure

The cumulative distribution function (cdf) of a probability measure over `ℝ` is a monotone, right
continuous function with limit 0 at -∞ and 1 at +∞. Two probability measures are equal if and only
if they have the same cdf.

## Main definitions

* `ProbabilityTheory.cdf μ`: cumulative distribution function of `μ : Measure ℝ`, defined as the
  conditional cdf (`ProbabilityTheory.condCdf`) of the product measure
  `(Measure.dirac Unit.unit).prod μ` evaluated at `Unit.unit`.

## Main statements

* `ProbabilityTheory.ofReal_cdf`: for a probability measure `μ` and `x : ℝ`,
  `ENNReal.ofReal (cdf μ x) = μ (Iic x)`.
* `MeasureTheory.Measure.ext_of_cdf`: two probability measures are equal if and only if they have
  the same cdf.

## TODO

The definition could be extended to a finite measure by rescaling `condCdf`, but it would be nice
to have more structure on Stieltjes functions first. Right now, if `f` is a Stieltjes function,
`2 • f` makes no sense. We could define Stieltjes functions as a submodule.

The definition could be extended to `ℝⁿ`, either by extending the definition of `condCdf`, or by
using another construction here.
-/

open MeasureTheory Set Filter

open scoped Topology

namespace ProbabilityTheory

/-- Cumulative distribution function of a real measure. -/
noncomputable
def cdf (μ : Measure ℝ) : StieltjesFunction :=
  condCdf ((Measure.dirac Unit.unit).prod μ) Unit.unit

variable {μ : Measure ℝ}

/-- The cdf is non-negative. -/
lemma cdf_nonneg (x : ℝ) : 0 ≤ cdf μ x := condCdf_nonneg _ _ _

/-- The cdf is lower or equal to 1. -/
lemma cdf_le_one (x : ℝ) : cdf μ x ≤ 1 := condCdf_le_one _ _ _

/-- The cdf is monotone. -/
lemma monotone_cdf : Monotone (cdf μ) := (condCdf _ _).mono

/-- The cdf tends to 0 at -∞. -/
lemma tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0) := tendsto_condCdf_atBot _ _

/-- The cdf tends to 1 at +∞. -/
lemma tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1) := tendsto_condCdf_atTop _ _

lemma ofReal_cdf [IsProbabilityMeasure μ] (x : ℝ) : ENNReal.ofReal (cdf μ x) = μ (Iic x) := by
  have h := lintegral_condCdf ((Measure.dirac Unit.unit).prod μ) x
  simpa only [MeasureTheory.Measure.fst_prod, Measure.prod_prod, measure_univ, one_mul,
    lintegral_dirac] using h

instance instIsProbabilityMeasurecdf : IsProbabilityMeasure (cdf μ).measure := by
  constructor
  simp only [StieltjesFunction.measure_univ _ tendsto_cdf_atBot tendsto_cdf_atTop, sub_zero,
    ENNReal.ofReal_one]

/-- The measure associated to the cdf of a probability measure is the same probability measure. -/
lemma measure_cdf [IsProbabilityMeasure μ] : (cdf μ).measure = μ := by
  refine Measure.ext_of_Iic (cdf μ).measure μ (fun a ↦ ?_)
  rw [StieltjesFunction.measure_Iic _ tendsto_cdf_atBot, sub_zero, ofReal_cdf]

end ProbabilityTheory

open ProbabilityTheory

/-- If two real probability distributions have the same cdf, they are equal. -/
lemma MeasureTheory.Measure.ext_of_cdf (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : cdf μ = cdf ν) : μ = ν := by
  rw [← @measure_cdf μ, ← @measure_cdf ν, h]
