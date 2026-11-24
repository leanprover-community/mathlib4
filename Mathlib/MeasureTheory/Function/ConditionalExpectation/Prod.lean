/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional expectation of a parameter integral

We identify the conditional expectation of an integral from an almost everywhere family of
conditional expectations, using Fubini on each measurable test set.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {ι Ω E : Type*} [MeasurableSpace ι] {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {ν : Measure ι} [SFinite ν] {μ : @Measure Ω mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integrating a family of versions of the conditional expectations gives a version of the
conditional expectation of the parameter integral, provided that the integrated version is a.e.
strongly measurable for the conditioning σ-algebra. -/
theorem condExp_integral_of_ae_eq (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {F G : ι → Ω → E}
    (hF : Integrable (Function.uncurry F) (ν.prod μ))
    (hG : Integrable (Function.uncurry G) (ν.prod μ))
    (hGm : AEStronglyMeasurable[m] (fun ω ↦ ∫ i, G i ω ∂ν) μ)
    (he : ∀ᵐ i ∂ν, μ[F i | m] =ᵐ[μ] G i) :
    μ[(fun ω ↦ ∫ i, F i ω ∂ν) | m] =ᵐ[μ] fun ω ↦ ∫ i, G i ω ∂ν := by
  have : SigmaFinite μ := SigmaFinite.of_trim hm
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hF.integral_prod_right
    (fun _ _ _ ↦ hG.integral_prod_right.integrableOn) ?_ hGm
  intro s hs _
  have hFr : Integrable (Function.uncurry F) (ν.prod (μ.restrict s)) :=
    hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hGr : Integrable (Function.uncurry G) (ν.prod (μ.restrict s)) :=
    hG.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    _ = ∫ i, ∫ ω in s, G i ω ∂μ ∂ν := (integral_integral_swap hGr).symm
    _ = ∫ i, ∫ ω in s, F i ω ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hF.prod_right_ae, he] with i hFi hei
      calc
        _ = ∫ ω in s, (μ[F i | m]) ω ∂μ := integral_congr_ae (ae_restrict_of_ae hei.symm)
        _ = _ := setIntegral_condExp hm hFi hs
    _ = _ := integral_integral_swap hFr

end MeasureTheory
