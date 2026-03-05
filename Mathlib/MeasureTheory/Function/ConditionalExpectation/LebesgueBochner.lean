/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Results about both conditional expectations

For non-negative real functions, we have two versions of the conditional expectation:
`condExp` and `condLExp`, built from the Bochner and Lebesgue integrals respectively.
In this file, we gather results that involve both versions.

## Main statements

*

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*}

/-- The two definitions of the conditional expectation agree. -/
lemma toReal_condLExp (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ≥0∞} (hf_meas : AEMeasurable f μ) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    (fun x ↦ (μ⁻[f | m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m] := by
  by_cases hm : m ≤ m𝓧
  swap; · simp [condLExp_of_not_le hm, condExp_of_not_le hm]; rfl
  by_cases hμ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hμ, condExp_of_not_sigmaFinite hm hμ]; rfl
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (E := ℝ) ?_ ?_ ?_ ?_ (μ := μ)
  · rwa [integrable_toReal_iff]
    · fun_prop
    · suffices ∀ᵐ (x : 𝓧) ∂μ, f x < ⊤ by filter_upwards [this] with x hx using hx.ne
      exact ae_lt_top' (by fun_prop) hf
  · intro s hs hsμ
    refine Integrable.integrableOn ?_
    rw [integrable_toReal_iff]
    · rwa [lintegral_condLExp]
    · fun_prop
    · exact condLExp_ne_top hf
  · intro s hs hsμ
    rw [integral_toReal, integral_toReal, setLIntegral_condLExp _ _ _ hs]
    · fun_prop
    · refine ae_lt_top' hf_meas.restrict ?_
      exact ((setLIntegral_le_lintegral _ _).trans_lt hf.lt_top).ne
    · fun_prop
    · exact ae_restrict_of_ae (condLExp_lt_top hf)
  · refine StronglyMeasurable.aestronglyMeasurable ?_
    fun_prop

end MeasureTheory
