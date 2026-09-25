/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Results about both conditional expectations

For non-negative real functions, we have two versions of the conditional expectation:
`condExp` and `condLExp`, built from the Bochner and Lebesgue integrals respectively.
In this file, we gather results that involve both versions.

## Main statements

* `MeasureTheory.toReal_condLExp`: the two definitions of the conditional expectation agree
  almost everywhere. That is, `(fun x ↦ (μ⁻[f | m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m]`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*}

/-- The two definitions of the conditional expectation `condExp` and `condLExp` (for Bochner and
Lebesgue integrals respectively) agree almost everywhere. -/
lemma toReal_condLExp (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ≥0∞} (hf_meas : AEMeasurable f μ) (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
    (fun x ↦ (μ⁻[f | m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m] := by
  by_cases hm : m ≤ m𝓧
  swap; · simp [condLExp_of_not_le hm, condExp_of_not_le hm]; rfl
  by_cases hμ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hμ, condExp_of_not_sigmaFinite hm hμ]; rfl
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (E := ℝ) ?_ ?_ ?_ ?_ (μ := μ)
  · rwa [integrable_toReal_iff (by fun_prop)]
    filter_upwards [ae_lt_top' (by fun_prop) hf] with x hx using hx.ne
  · refine fun s hs hsμ ↦ Integrable.integrableOn ?_
    rwa [integrable_toReal_iff (by fun_prop) (condLExp_ne_top hf), lintegral_condLExp]
  · intro s hs hsμ
    rw [integral_toReal (by fun_prop), integral_toReal (by fun_prop),
      setLIntegral_condLExp _ _ _ hs]
    · exact ae_lt_top' hf_meas.restrict ((setLIntegral_le_lintegral _ _).trans_lt hf.lt_top).ne
    · exact ae_restrict_of_ae (condLExp_lt_top hf)
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)

end MeasureTheory
