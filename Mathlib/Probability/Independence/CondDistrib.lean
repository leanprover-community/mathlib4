/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Independence and conditional distributions

This file characterizes independence of two random variables in terms of their conditional
distributions.

## Main results

* `indepFun_iff_condDistrib_ae_eq_const`: two random variables are independent if and only if the
  conditional distribution of the second given the first is almost everywhere its marginal
  distribution.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 : Type*}
  [MeasurableSpace Ω] [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
  [StandardBorelSpace 𝓨] [Nonempty 𝓨]
  {P : Measure Ω} [IsFiniteMeasure P]
  {X : Ω → 𝓧} {Y : Ω → 𝓨}

/-- Two a.e.-measurable random variables are independent if and only if the conditional
distribution of the second given the first is almost everywhere its marginal distribution. -/
theorem indepFun_iff_condDistrib_ae_eq_const
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    IndepFun X Y P ↔
      condDistrib Y X P =ᵐ[P.map X] Kernel.const 𝓧 (P.map Y) := by
  rw [condDistrib_ae_eq_iff_measure_eq_compProd X hY, Measure.compProd_const,
    indepFun_iff_map_prod_eq_prod_map_map hX hY]

end ProbabilityTheory
