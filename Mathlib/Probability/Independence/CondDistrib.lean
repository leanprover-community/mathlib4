/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Independence and conditional distributions

This file characterizes independence of two random variables in terms of their conditional
distributions.

## Main results

* `indepFun_iff_condDistrib_ae_eq_const_of_hasLaw`: two random variables with specified laws are
  independent if and only if the conditional distribution of the second given the first is almost
  everywhere the constant kernel at the law of the second.
* `indepFun_iff_condDistrib_ae_eq_const`: two random variables are independent if and only if the
  conditional distribution of the second given the first is almost everywhere its marginal
  distribution.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 : Type*}
  [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {P : Measure Ω} [IsFiniteMeasure P]
  {X : Ω → 𝓧} {Y : Ω → 𝓨}

/-- Two random variables with specified laws are independent if and only if the conditional
distribution of the second given the first is almost everywhere the constant kernel at its law. -/
theorem indepFun_iff_condDistrib_ae_eq_const_of_hasLaw
    {μ : Measure 𝓧} {ν : Measure 𝓨}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
    X ⟂ᵢ[P] Y ↔ condDistrib Y X P =ᵐ[μ] Kernel.const 𝓧 ν := by
  let _ : IsFiniteMeasure ν := hY.isFiniteMeasure_iff.mp inferInstance
  rw [← hX.map_eq, condDistrib_ae_eq_iff_measure_eq_compProd X hY.aemeasurable,
    Measure.compProd_const,
    indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hY.map_eq]

/-- Two a.e.-measurable random variables are independent if and only if the conditional
distribution of the second given the first is almost everywhere its marginal distribution. -/
theorem indepFun_iff_condDistrib_ae_eq_const
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    X ⟂ᵢ[P] Y ↔ condDistrib Y X P =ᵐ[P.map X] Kernel.const 𝓧 (P.map Y) := by
  exact indepFun_iff_condDistrib_ae_eq_const_of_hasLaw ⟨hX, rfl⟩ ⟨hY, rfl⟩

end ProbabilityTheory
