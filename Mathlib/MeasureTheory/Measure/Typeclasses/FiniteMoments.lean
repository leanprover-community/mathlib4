/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Class for measures with finite moments

We introduce typeclasses for finite measures with finite first or second moments.

## Main definitions

* `HasFiniteMean μ`: class for a finite measure such that `∫ x, ‖x‖ ∂μ < ∞`
* `HasFiniteVar μ`: class that states that `μ` is a finite measure and that `∫ x, ‖x‖ ^ 2 ∂μ < ∞`.

## Main statements

Statements about the identity function:
* `memLp_one_id`: if `μ` has finite mean, then `MemLp id 1 μ`.
* `integrable_id`: if `μ` has finite mean, then `Integrable id μ`.
* `memLp_two_id`: if `μ` has finite variance, then `MemLp id 2 μ`.

From those, we deduce that for a continuous linear map `L`,
* `ContinuousLinearMap.memLp_one`: if `μ` has finite mean, then `MemLp L 1 μ`,
* `ContinuousLinearMap.integrable`: if `μ` has finite mean, then `Integrable L μ`,
* `ContinuousLinearMap.memLp_two`: if `μ` has finite variance, then `MemLp L 2 μ`.

-/

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {ε : Type*} [TopologicalSpace ε] {mε : MeasurableSpace ε} {μ : Measure ε}

section Mean

class HasFiniteMean [ENorm ε] (μ : Measure ε) extends IsFiniteMeasure μ where
  memLp_one : MemLp id 1 μ

lemma memLp_one_id [ENorm ε] [HasFiniteMean μ] : MemLp id 1 μ := HasFiniteMean.memLp_one

lemma integrable_id [ContinuousENorm ε] [HasFiniteMean μ] : Integrable id μ :=
  memLp_one_id.integrable le_rfl

end Mean

section Variance

/-- A finite measure has finite variance if `∫ x, x ^ 2 ∂μ < ∞`, that is if `MemLp id 2 μ`. -/
class HasFiniteVar [ENorm ε] (μ : Measure ε) extends IsFiniteMeasure μ where
  memLp_two : MemLp id 2 μ

lemma memLp_two_id [ENorm ε] [HasFiniteVar μ] : MemLp id 2 μ := HasFiniteVar.memLp_two

instance [ContinuousENorm ε] [HasFiniteVar μ] : HasFiniteMean μ where
  memLp_one := memLp_two_id.mono_exponent (by simp)

end Variance

end MeasureTheory

namespace ContinuousLinearMap

variable {E F 𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {_ : MeasurableSpace E} {μ : Measure E}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma memLp_one [HasFiniteMean μ] (L : E →L[𝕜] F) :
    MemLp L 1 μ := L.comp_memLp' memLp_one_id

protected lemma integrable [HasFiniteMean μ] (L : E →L[𝕜] F) :
    Integrable L μ := L.memLp_one.integrable le_rfl

lemma memLp_two [HasFiniteVar μ] (L : E →L[𝕜] F) : MemLp L 2 μ := L.comp_memLp' memLp_two_id

end ContinuousLinearMap
