/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

module

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
    (fun x ↦ (μ⁻[f|m] x).toReal) =ᵐ[μ] μ[fun x ↦ (f x).toReal | m] := by
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

/-- The two definitions of the conditional expectation `condExp` and `condLExp` (for Bochner and
Lebesgue integrals respectively) agree almost everywhere. -/
lemma condLExp_ofReal (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ} (hf : Integrable f μ) (h'f : 0 ≤ᵐ[μ] f) :
    μ⁻[fun x ↦ ENNReal.ofReal (f x) | m] =ᵐ[μ] fun x ↦ ENNReal.ofReal (μ[f | m] x) := by
  by_cases hm : m ≤ m𝓧
  swap; · simp [condLExp_of_not_le hm, condExp_of_not_le hm]; rfl
  by_cases hμ : SigmaFinite (μ.trim hm)
  swap; · simp [condLExp_of_not_sigmaFinite hm hμ, condExp_of_not_sigmaFinite hm hμ]; rfl
  have A : μ[fun x ↦ (ENNReal.ofReal (f x)).toReal | m] =ᵐ[μ] μ[f | m] := by
    apply condExp_congr_ae
    filter_upwards [h'f] with x hx using ENNReal.toReal_ofReal hx
  have B : 0 ≤ᵐ[μ] μ[f | m] := condExp_nonneg h'f
  let g x := ENNReal.ofReal (f x)
  have I : ∫⁻ x, g x ∂μ ≠ ∞ := by
    have : ∫⁻ x, g x ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [h'f] with x hx using by simp [g, Real.enorm_eq_ofReal hx]
    rw [this]
    exact hf.2.ne
  have J : ∀ᵐ x ∂μ, μ⁻[g | m] x < ∞ := by
    apply ae_lt_top (by fun_prop)
    convert I using 1
    exact lintegral_condLExp _ _ _
  filter_upwards [toReal_condLExp m (f := g) (by fun_prop) I, h'f, A, B, J]
    with a ha h'a h''a h'''a C
  rw [← ENNReal.toReal_eq_toReal_iff' C.ne, ENNReal.toReal_ofReal h'''a, ha, h''a]
  simp

/-- The two definitions of the conditional expectation `condExp` and `condLExp` (for Bochner and
Lebesgue integrals respectively) agree almost everywhere. -/
lemma condLExp_enorm (m : MeasurableSpace 𝓧) {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧}
    {f : 𝓧 → ℝ} (hf : Integrable f μ) (h'f : 0 ≤ᵐ[μ] f) :
    μ⁻[fun x ↦ ‖f x‖ₑ | m] =ᵐ[μ] fun x ↦ ‖μ[f | m] x‖ₑ := by
  have A : μ⁻[fun x ↦ ENNReal.ofReal (f x) | m] =ᵐ[μ] μ⁻[fun x ↦ ‖f x‖ₑ | m] := by
    apply condLExp_congr_ae
    filter_upwards [h'f] with x hx using by simp [Real.enorm_eq_ofReal hx]
  grw [← A, condLExp_ofReal m hf h'f]
  filter_upwards [condExp_nonneg h'f (m := m)] with x hx using by simp [Real.enorm_eq_ofReal hx]

lemma lintegral_enorm_condExp_indicator
    {m : MeasurableSpace 𝓧} {m𝓧 : MeasurableSpace 𝓧} (hm : m ≤ m𝓧) {μ : Measure 𝓧}
    [SigmaFinite (μ.trim hm)] {s : Set 𝓧} (hs : MeasurableSet s) (h's : μ s ≠ ∞ := by finiteness) :
    ∫⁻ a, ‖μ[s.indicator (1 : 𝓧 → ℝ) | m] a‖ₑ ∂μ = μ s := calc
  _ = ∫⁻ a, μ⁻[fun x ↦ ‖s.indicator (1 : 𝓧 → ℝ) x‖ₑ | m] a ∂μ := by
    apply lintegral_congr_ae
    apply (condLExp_enorm _ _ _).symm
    · apply (integrable_indicator_iff hs).2
      apply integrableOn_const h's
    · filter_upwards with x
      simp only [Pi.zero_apply, Set.indicator, Pi.one_apply]
      grind
  _ = μ s := by
    simp [lintegral_condLExp hm, enorm_indicator_eq_indicator_enorm, lintegral_indicator hs]

end MeasureTheory
