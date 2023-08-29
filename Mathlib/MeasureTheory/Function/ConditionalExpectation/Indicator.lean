/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

#align_import measure_theory.function.conditional_expectation.indicator from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!

# Conditional expectation of indicator functions

This file proves some results about the conditional expectation of an indicator function and
as a corollary, also proves several results about the behaviour of the conditional expectation on
a restricted measure.

## Main result

* `MeasureTheory.condexp_indicator`: If `s` is an `m`-measurable set, then the conditional
  expectation of the indicator function of `s` is almost everywhere equal to the indicator
  of `s` of the conditional expectation. Namely, `𝔼[s.indicator f | m] = s.indicator 𝔼[f | m]` a.e.

-/


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology BigOperators MeasureTheory

namespace MeasureTheory

variable {α 𝕜 E : Type*} {m m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {f : α → E} {s : Set α}

theorem condexp_ae_eq_restrict_zero (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
    μ[f|m] =ᵐ[μ.restrict s] 0 := by
  by_cases hm : m ≤ m0
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
  swap; · simp_rw [condexp_of_not_le hm]; rfl
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
          -- ⊢ 0 =ᵐ[Measure.restrict μ s] 0
                                          -- 🎉 no goals
  by_cases hμm : SigmaFinite (μ.trim hm)
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; rfl
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
          -- ⊢ 0 =ᵐ[Measure.restrict μ s] 0
                                                       -- 🎉 no goals
  haveI : SigmaFinite (μ.trim hm) := hμm
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
  have : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    exact Restrict.sigmaFinite _ s
  by_cases hf_int : Integrable f μ
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
  swap; · rw [condexp_undef hf_int]
  -- ⊢ μ[f|m] =ᵐ[Measure.restrict μ s] 0
          -- 🎉 no goals
  refine' ae_eq_of_forall_set_integral_eq_of_sigmaFinite' hm _ _ _ _ _
  · exact fun t _ _ => integrable_condexp.integrableOn.integrableOn
    -- 🎉 no goals
  · exact fun t _ _ => (integrable_zero _ _ _).integrableOn
    -- 🎉 no goals
  · intro t ht _
    -- ⊢ ∫ (x : α) in t, (μ[f|m]) x ∂Measure.restrict μ s = ∫ (x : α) in t, OfNat.ofN …
    rw [Measure.restrict_restrict (hm _ ht), set_integral_condexp hm hf_int (ht.inter hs), ←
      Measure.restrict_restrict (hm _ ht)]
    refine' set_integral_congr_ae (hm _ ht) _
    -- ⊢ ∀ᵐ (x : α) ∂Measure.restrict μ s, x ∈ t → f x = OfNat.ofNat 0 x
    filter_upwards [hf] with x hx _ using hx
    -- 🎉 no goals
  · exact stronglyMeasurable_condexp.aeStronglyMeasurable'
    -- 🎉 no goals
  · exact stronglyMeasurable_zero.aeStronglyMeasurable'
    -- 🎉 no goals
#align measure_theory.condexp_ae_eq_restrict_zero MeasureTheory.condexp_ae_eq_restrict_zero

/-- Auxiliary lemma for `condexp_indicator`. -/
theorem condexp_indicator_aux (hs : MeasurableSet[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
    μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) := by
  by_cases hm : m ≤ m0
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
  swap; · simp_rw [condexp_of_not_le hm, Set.indicator_zero']; rfl
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
          -- ⊢ 0 =ᵐ[μ] 0
                                                               -- 🎉 no goals
  have hsf_zero : ∀ g : α → E, g =ᵐ[μ.restrict sᶜ] 0 → s.indicator g =ᵐ[μ] g := fun g =>
    indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs)
  refine' ((hsf_zero (μ[f|m]) (condexp_ae_eq_restrict_zero hs.compl hf)).trans _).symm
  -- ⊢ μ[f|m] =ᵐ[μ] μ[Set.indicator s f|m]
  exact condexp_congr_ae (hsf_zero f hf).symm
  -- 🎉 no goals
#align measure_theory.condexp_indicator_aux MeasureTheory.condexp_indicator_aux

/-- The conditional expectation of the indicator of a function over an `m`-measurable set with
respect to the σ-algebra `m` is a.e. equal to the indicator of the conditional expectation. -/
theorem condexp_indicator (hf_int : Integrable f μ) (hs : MeasurableSet[m] s) :
    μ[s.indicator f|m] =ᵐ[μ] s.indicator (μ[f|m]) := by
  by_cases hm : m ≤ m0
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
  swap; · simp_rw [condexp_of_not_le hm, Set.indicator_zero']; rfl
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
          -- ⊢ 0 =ᵐ[μ] 0
                                                               -- 🎉 no goals
  by_cases hμm : SigmaFinite (μ.trim hm)
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm, Set.indicator_zero']; rfl
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
          -- ⊢ 0 =ᵐ[μ] 0
                                                                            -- 🎉 no goals
  haveI : SigmaFinite (μ.trim hm) := hμm
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] Set.indicator s (μ[f|m])
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f|m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f|m]) := by
    rw [Set.indicator_self_add_compl s f]
  refine' (this.trans _).symm
  -- ⊢ Set.indicator s (μ[Set.indicator s f + Set.indicator sᶜ f|m]) =ᵐ[μ] μ[Set.in …
  calc
    s.indicator (μ[s.indicator f + sᶜ.indicator f|m]) =ᵐ[μ]
        s.indicator (μ[s.indicator f|m] + μ[sᶜ.indicator f|m]) := by
      have : μ[s.indicator f + sᶜ.indicator f|m] =ᵐ[μ] μ[s.indicator f|m] + μ[sᶜ.indicator f|m] :=
        condexp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl))
      filter_upwards [this] with x hx
      classical rw [Set.indicator_apply, Set.indicator_apply, hx]
    _ = s.indicator (μ[s.indicator f|m]) + s.indicator (μ[sᶜ.indicator f|m]) :=
      (s.indicator_add' _ _)
    _ =ᵐ[μ] s.indicator (μ[s.indicator f|m]) +
        s.indicator (sᶜ.indicator (μ[sᶜ.indicator f|m])) := by
      refine' Filter.EventuallyEq.rfl.add _
      have : sᶜ.indicator (μ[sᶜ.indicator f|m]) =ᵐ[μ] μ[sᶜ.indicator f|m] := by
        refine' (condexp_indicator_aux hs.compl _).symm.trans _
        · exact indicator_ae_eq_restrict_compl (hm _ hs.compl)
        · rw [Set.indicator_indicator, Set.inter_self]
      filter_upwards [this] with x hx
      by_cases hxs : x ∈ s
      · simp only [hx, hxs, Set.indicator_of_mem]
      · simp only [hxs, Set.indicator_of_not_mem, not_false_iff]
    _ =ᵐ[μ] s.indicator (μ[s.indicator f|m]) := by
      rw [Set.indicator_indicator, Set.inter_compl_self, Set.indicator_empty', add_zero]
    _ =ᵐ[μ] μ[s.indicator f|m] := by
      refine' (condexp_indicator_aux hs _).symm.trans _
      · exact indicator_ae_eq_restrict_compl (hm _ hs)
      · rw [Set.indicator_indicator, Set.inter_self]
#align measure_theory.condexp_indicator MeasureTheory.condexp_indicator

theorem condexp_restrict_ae_eq_restrict (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs_m : MeasurableSet[m] s) (hf_int : Integrable f μ) :
    (μ.restrict s)[f|m] =ᵐ[μ.restrict s] μ[f|m] := by
  have : SigmaFinite ((μ.restrict s).trim hm) := by rw [← restrict_trim hm _ hs_m]; infer_instance
  -- ⊢ Measure.restrict μ s[f|m] =ᵐ[Measure.restrict μ s] μ[f|m]
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  -- ⊢ Set.indicator s (Measure.restrict μ s[f|m]) =ᵐ[μ] Set.indicator s (μ[f|m])
  refine' EventuallyEq.trans _ (condexp_indicator hf_int hs_m)
  -- ⊢ Set.indicator s (Measure.restrict μ s[f|m]) =ᵐ[μ] μ[Set.indicator s f|m]
  refine' ae_eq_condexp_of_forall_set_integral_eq hm (hf_int.indicator (hm _ hs_m)) _ _ _
  · intro t ht _
    -- ⊢ IntegrableOn (Set.indicator s (Measure.restrict μ s[f|m])) t
    rw [← integrable_indicator_iff (hm _ ht), Set.indicator_indicator, Set.inter_comm, ←
      Set.indicator_indicator]
    suffices h_int_restrict : Integrable (t.indicator ((μ.restrict s)[f|m])) (μ.restrict s)
    -- ⊢ Integrable (Set.indicator s (Set.indicator t (Measure.restrict μ s[f|m])))
    · rw [integrable_indicator_iff (hm _ hs_m), IntegrableOn]
      -- ⊢ Integrable (Set.indicator t (Measure.restrict μ s[f|m]))
      rw [integrable_indicator_iff (hm _ ht), IntegrableOn] at h_int_restrict ⊢
      -- ⊢ Integrable (Measure.restrict μ s[f|m])
      exact h_int_restrict
      -- 🎉 no goals
    exact integrable_condexp.indicator (hm _ ht)
    -- 🎉 no goals
  · intro t ht _
    -- ⊢ ∫ (x : α) in t, Set.indicator s (Measure.restrict μ s[f|m]) x ∂μ = ∫ (x : α) …
    calc
      ∫ x in t, s.indicator ((μ.restrict s)[f|m]) x ∂μ =
          ∫ x in t, ((μ.restrict s)[f|m]) x ∂μ.restrict s := by
        rw [integral_indicator (hm _ hs_m), Measure.restrict_restrict (hm _ hs_m),
          Measure.restrict_restrict (hm _ ht), Set.inter_comm]
      _ = ∫ x in t, f x ∂μ.restrict s := (set_integral_condexp hm hf_int.integrableOn ht)
      _ = ∫ x in t, s.indicator f x ∂μ := by
        rw [integral_indicator (hm _ hs_m), Measure.restrict_restrict (hm _ hs_m),
          Measure.restrict_restrict (hm _ ht), Set.inter_comm]
  · exact (stronglyMeasurable_condexp.indicator hs_m).aeStronglyMeasurable'
    -- 🎉 no goals
#align measure_theory.condexp_restrict_ae_eq_restrict MeasureTheory.condexp_restrict_ae_eq_restrict

/-- If the restriction to an `m`-measurable set `s` of a σ-algebra `m` is equal to the restriction
to `s` of another σ-algebra `m₂` (hypothesis `hs`), then `μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂]`. -/
theorem condexp_ae_eq_restrict_of_measurableSpace_eq_on {m m₂ m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm)]
    [SigmaFinite (μ.trim hm₂)] (hs_m : MeasurableSet[m] s)
    (hs : ∀ t, MeasurableSet[m] (s ∩ t) ↔ MeasurableSet[m₂] (s ∩ t)) :
    μ[f|m] =ᵐ[μ.restrict s] μ[f|m₂] := by
  rw [ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m)]
  -- ⊢ Set.indicator s (μ[f|m]) =ᵐ[μ] Set.indicator s (μ[f|m₂])
  have hs_m₂ : MeasurableSet[m₂] s := by rwa [← Set.inter_univ s, ← hs Set.univ, Set.inter_univ]
  -- ⊢ Set.indicator s (μ[f|m]) =ᵐ[μ] Set.indicator s (μ[f|m₂])
  by_cases hf_int : Integrable f μ
  -- ⊢ Set.indicator s (μ[f|m]) =ᵐ[μ] Set.indicator s (μ[f|m₂])
  swap; · simp_rw [condexp_undef hf_int]; rfl
  -- ⊢ Set.indicator s (μ[f|m]) =ᵐ[μ] Set.indicator s (μ[f|m₂])
          -- ⊢ Set.indicator s 0 =ᵐ[μ] Set.indicator s 0
                                          -- 🎉 no goals
  refine' ((condexp_indicator hf_int hs_m).symm.trans _).trans (condexp_indicator hf_int hs_m₂)
  -- ⊢ μ[Set.indicator s f|m] =ᵐ[μ] μ[Set.indicator s f|m₂]
  refine' ae_eq_of_forall_set_integral_eq_of_sigmaFinite' hm₂
    (fun s _ _ => integrable_condexp.integrableOn)
    (fun s _ _ => integrable_condexp.integrableOn) _ _
    stronglyMeasurable_condexp.aeStronglyMeasurable'
  swap
  -- ⊢ AEStronglyMeasurable' m₂ (μ[Set.indicator s f|m]) μ
  · have : StronglyMeasurable[m] (μ[s.indicator f|m]) := stronglyMeasurable_condexp
    -- ⊢ AEStronglyMeasurable' m₂ (μ[Set.indicator s f|m]) μ
    refine' this.aeStronglyMeasurable'.aeStronglyMeasurable'_of_measurableSpace_le_on hm hs_m
      (fun t => (hs t).mp) _
    exact condexp_ae_eq_restrict_zero hs_m.compl (indicator_ae_eq_restrict_compl (hm _ hs_m))
    -- 🎉 no goals
  intro t ht _
  -- ⊢ ∫ (x : α) in t, (μ[Set.indicator s f|m]) x ∂μ = ∫ (x : α) in t, (μ[Set.indic …
  have : ∫ x in t, (μ[s.indicator f|m]) x ∂μ = ∫ x in s ∩ t, (μ[s.indicator f|m]) x ∂μ := by
    rw [← integral_add_compl (hm _ hs_m) integrable_condexp.integrableOn]
    suffices ∫ x in sᶜ, (μ[s.indicator f|m]) x ∂μ.restrict t = 0 by
      rw [this, add_zero, Measure.restrict_restrict (hm _ hs_m)]
    rw [Measure.restrict_restrict (MeasurableSet.compl (hm _ hs_m))]
    suffices μ[s.indicator f|m] =ᵐ[μ.restrict sᶜ] 0 by
      rw [Set.inter_comm, ← Measure.restrict_restrict (hm₂ _ ht)]
      calc
        ∫ x : α in t, (μ[s.indicator f|m]) x ∂μ.restrict sᶜ =
            ∫ x : α in t, 0 ∂μ.restrict sᶜ := by
          refine' set_integral_congr_ae (hm₂ _ ht) _
          filter_upwards [this] with x hx _ using hx
        _ = 0 := integral_zero _ _
    refine' condexp_ae_eq_restrict_zero hs_m.compl _
    exact indicator_ae_eq_restrict_compl (hm _ hs_m)
  have hst_m : MeasurableSet[m] (s ∩ t) := (hs _).mpr (hs_m₂.inter ht)
  -- ⊢ ∫ (x : α) in t, (μ[Set.indicator s f|m]) x ∂μ = ∫ (x : α) in t, (μ[Set.indic …
  simp_rw [this, set_integral_condexp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
    set_integral_condexp hm (hf_int.indicator (hm _ hs_m)) hst_m, integral_indicator (hm _ hs_m),
    Measure.restrict_restrict (hm _ hs_m), ← Set.inter_assoc, Set.inter_self]
#align measure_theory.condexp_ae_eq_restrict_of_measurable_space_eq_on MeasureTheory.condexp_ae_eq_restrict_of_measurableSpace_eq_on

end MeasureTheory
