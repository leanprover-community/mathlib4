/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.conditional_expectation.basic
! leanprover-community/mathlib commit d8bbb04e2d2a44596798a9207ceefc0fb236e41e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.ConditionalExpectation.CondexpL1

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m0`) and a measurable space
structure `m` with `hm : m ≤ m0` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexp_L1_clm : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `measure_theory/integral/set_to_L1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condexp_L1_clm` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `measure_theory.function.conditional_expectation.condexp_L2`, the two
next steps in `measure_theory.function.conditional_expectation.condexp_L1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condexp (m : measurable_space α) (μ : measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `strongly_measurable_condexp` : `condexp` is `m`-strongly-measurable.
* `set_integral_condexp (hf : integrable f μ) (hs : measurable_set[m] s)` : if `m ≤ m0` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condexp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condexp` is function-valued, we also define `condexp_L1` with value in `L1` and a continuous
linear map `condexp_L1_clm` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condexp_of_forall_set_integral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condexp m μ f`.

## Tags

conditional expectation, conditional expected value

-/


open TopologicalSpace MeasureTheory.Lp Filter

open scoped ENNReal Topology BigOperators MeasureTheory

namespace MeasureTheory

variable {α F F' 𝕜 : Type _} {p : ℝ≥0∞} [IsROrC 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

open scoped Classical

variable {𝕜} {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function. It is defined as 0 if any one of the following conditions
is true:
- `m` is not a sub-σ-algebra of `m0`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
noncomputable irreducible_def condexp (m : MeasurableSpace α) {m0 : MeasurableSpace α}
    (μ : Measure α) (f : α → F') : α → F' :=
  if hm : m ≤ m0 then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if strongly_measurable[m] f then f
      else
        (@aEStronglyMeasurable'_condexpL1 _ _ _ _ _ m m0 μ hm h.1 _).mk
          (@condexpL1 _ _ _ _ _ _ _ hm μ h.1 f)
    else 0
  else 0
#align measure_theory.condexp MeasureTheory.condexp

-- We define notation `μ[f|m]` for the conditional expectation of `f` with respect to `m`.
scoped notation μ "[" f "|" m "]" => MeasureTheory.condexp m μ f

theorem condexp_of_not_le (hm_not : ¬m ≤ m0) : μ[f|m] = 0 := by rw [condexp, dif_neg hm_not]
#align measure_theory.condexp_of_not_le MeasureTheory.condexp_of_not_le

theorem condexp_of_not_sigmaFinite (hm : m ≤ m0) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ[f|m] = 0 := by rw [condexp, dif_pos hm, dif_neg]; push_neg; exact fun h => absurd h hμm_not
#align measure_theory.condexp_of_not_sigma_finite MeasureTheory.condexp_of_not_sigmaFinite

theorem condexp_of_sigmaFinite (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] :
    μ[f|m] =
      if Integrable f μ then
        if strongly_measurable[m] f then f
        else aEStronglyMeasurable'_condexpL1.mk (condexpL1 hm μ f)
      else 0 :=
  by
  rw [condexp, dif_pos hm]
  simp only [hμm, Ne.def, true_and_iff]
  by_cases hf : integrable f μ
  · rw [dif_pos hf, if_pos hf]
  · rw [dif_neg hf, if_neg hf]
#align measure_theory.condexp_of_sigma_finite MeasureTheory.condexp_of_sigmaFinite

theorem condexp_of_stronglyMeasurable (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : strongly_measurable[m] f) (hfi : Integrable f μ) : μ[f|m] = f := by
  rw [condexp_of_sigma_finite hm, if_pos hfi, if_pos hf]; infer_instance
#align measure_theory.condexp_of_strongly_measurable MeasureTheory.condexp_of_stronglyMeasurable

theorem condexp_const (hm : m ≤ m0) (c : F') [IsFiniteMeasure μ] :
    μ[fun x : α => c|m] = fun _ => c :=
  condexp_of_stronglyMeasurable hm (@stronglyMeasurable_const _ _ m _ _) (integrable_const c)
#align measure_theory.condexp_const MeasureTheory.condexp_const

theorem condexp_ae_eq_condexpL1 (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (f : α → F') :
    μ[f|m] =ᵐ[μ] condexpL1 hm μ f :=
  by
  rw [condexp_of_sigma_finite hm]
  by_cases hfi : integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : strongly_measurable[m] f
    · rw [if_pos hfm]
      exact
        (condexp_L1_of_ae_strongly_measurable' (strongly_measurable.ae_strongly_measurable' hfm)
            hfi).symm
    · rw [if_neg hfm]
      exact (ae_strongly_measurable'.ae_eq_mk ae_strongly_measurable'_condexp_L1).symm
  rw [if_neg hfi, condexp_L1_undef hfi]
  exact (coe_fn_zero _ _ _).symm
#align measure_theory.condexp_ae_eq_condexp_L1 MeasureTheory.condexp_ae_eq_condexpL1

theorem condexp_ae_eq_condexpL1Clm (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f|m] =ᵐ[μ] condexpL1Clm hm μ (hf.toL1 f) :=
  by
  refine' (condexp_ae_eq_condexp_L1 hm f).trans (eventually_of_forall fun x => _)
  rw [condexp_L1_eq hf]
#align measure_theory.condexp_ae_eq_condexp_L1_clm MeasureTheory.condexp_ae_eq_condexpL1Clm

theorem condexp_undef (hf : ¬Integrable f μ) : μ[f|m] = 0 :=
  by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · rw [condexp_of_not_sigma_finite hm hμm]
  haveI : sigma_finite (μ.trim hm) := hμm
  rw [condexp_of_sigma_finite, if_neg hf]
#align measure_theory.condexp_undef MeasureTheory.condexp_undef

@[simp]
theorem condexp_zero : μ[(0 : α → F')|m] = 0 :=
  by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · rw [condexp_of_not_sigma_finite hm hμm]
  haveI : sigma_finite (μ.trim hm) := hμm
  exact
    condexp_of_strongly_measurable hm (@strongly_measurable_zero _ _ m _ _) (integrable_zero _ _ _)
#align measure_theory.condexp_zero MeasureTheory.condexp_zero

theorem stronglyMeasurable_condexp : strongly_measurable[m] (μ[f|m]) :=
  by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]; exact strongly_measurable_zero
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · rw [condexp_of_not_sigma_finite hm hμm]; exact strongly_measurable_zero
  haveI : sigma_finite (μ.trim hm) := hμm
  rw [condexp_of_sigma_finite hm]
  swap; · infer_instance
  split_ifs with hfi hfm
  · exact hfm
  · exact ae_strongly_measurable'.strongly_measurable_mk _
  · exact strongly_measurable_zero
#align measure_theory.strongly_measurable_condexp MeasureTheory.stronglyMeasurable_condexp

theorem condexp_congr_ae (h : f =ᵐ[μ] g) : μ[f|m] =ᵐ[μ] μ[g|m] :=
  by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigma_finite hm hμm]
  haveI : sigma_finite (μ.trim hm) := hμm
  exact
    (condexp_ae_eq_condexp_L1 hm f).trans
      (Filter.EventuallyEq.trans (by rw [condexp_L1_congr_ae hm h])
        (condexp_ae_eq_condexp_L1 hm g).symm)
#align measure_theory.condexp_congr_ae MeasureTheory.condexp_congr_ae

theorem condexp_of_aEStronglyMeasurable' (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : AEStronglyMeasurable' m f μ) (hfi : Integrable f μ) : μ[f|m] =ᵐ[μ] f :=
  by
  refine' ((condexp_congr_ae hf.ae_eq_mk).trans _).trans hf.ae_eq_mk.symm
  rw [condexp_of_strongly_measurable hm hf.strongly_measurable_mk
      ((integrable_congr hf.ae_eq_mk).mp hfi)]
#align measure_theory.condexp_of_ae_strongly_measurable' MeasureTheory.condexp_of_aEStronglyMeasurable'

theorem integrable_condexp : Integrable (μ[f|m]) μ :=
  by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · rw [condexp_of_not_sigma_finite hm hμm]; exact integrable_zero _ _ _
  haveI : sigma_finite (μ.trim hm) := hμm
  exact (integrable_condexp_L1 f).congr (condexp_ae_eq_condexp_L1 hm f).symm
#align measure_theory.integrable_condexp MeasureTheory.integrable_condexp

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem set_integral_condexp (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hs : measurable_set[m] s) : ∫ x in s, (μ[f|m]) x ∂μ = ∫ x in s, f x ∂μ :=
  by
  rw [set_integral_congr_ae (hm s hs) ((condexp_ae_eq_condexp_L1 hm f).mono fun x hx _ => hx)]
  exact set_integral_condexp_L1 hf hs
#align measure_theory.set_integral_condexp MeasureTheory.set_integral_condexp

theorem integral_condexp (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    ∫ x, (μ[f|m]) x ∂μ = ∫ x, f x ∂μ :=
  by
  suffices ∫ x in Set.univ, (μ[f|m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
    simp_rw [integral_univ] at this ; exact this
  exact set_integral_condexp hm hf (@MeasurableSet.univ _ m)
#align measure_theory.integral_condexp MeasureTheory.integral_condexp

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condexp_of_forall_set_integral_eq (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, measurable_set[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, measurable_set[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable' m g μ) : g =ᵐ[μ] μ[f|m] :=
  by
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm hg_int_finite
      (fun s hs hμs => integrable_condexp.integrable_on) (fun s hs hμs => _) hgm
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
  rw [hg_eq s hs hμs, set_integral_condexp hm hf hs]
#align measure_theory.ae_eq_condexp_of_forall_set_integral_eq MeasureTheory.ae_eq_condexp_of_forall_set_integral_eq

theorem condexp_bot' [hμ : μ.ae.ne_bot] (f : α → F') :
    μ[f|⊥] = fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ :=
  by
  by_cases hμ_finite : is_finite_measure μ
  swap
  · have h : ¬sigma_finite (μ.trim bot_le) := by rwa [sigma_finite_trim_bot_iff]
    rw [not_is_finite_measure_iff] at hμ_finite 
    rw [condexp_of_not_sigma_finite bot_le h]
    simp only [hμ_finite, ENNReal.top_toReal, inv_zero, zero_smul]
    rfl
  haveI : is_finite_measure μ := hμ_finite
  by_cases hf : integrable f μ
  swap; · rw [integral_undef hf, smul_zero, condexp_undef hf]; rfl
  have h_meas : strongly_measurable[⊥] (μ[f|⊥]) := strongly_measurable_condexp
  obtain ⟨c, h_eq⟩ := strongly_measurable_bot_iff.mp h_meas
  rw [h_eq]
  have h_integral : ∫ x, (μ[f|⊥]) x ∂μ = ∫ x, f x ∂μ := integral_condexp bot_le hf
  simp_rw [h_eq, integral_const] at h_integral 
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul]
  rw [Ne.def, ENNReal.toReal_eq_zero_iff, Auto.not_or_eq, measure.measure_univ_eq_zero, ← ae_eq_bot,
    ← Ne.def, ← ne_bot_iff]
  exact ⟨hμ, measure_ne_top μ Set.univ⟩
#align measure_theory.condexp_bot' MeasureTheory.condexp_bot'

theorem condexp_bot_ae_eq (f : α → F') :
    μ[f|⊥] =ᵐ[μ] fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ :=
  by
  by_cases μ.ae.ne_bot
  · refine' eventually_of_forall fun x => _
    rw [condexp_bot' f]
    exact h
  · rw [ne_bot_iff, Classical.not_not, ae_eq_bot] at h 
    simp only [h, ae_zero]
#align measure_theory.condexp_bot_ae_eq MeasureTheory.condexp_bot_ae_eq

theorem condexp_bot [IsProbabilityMeasure μ] (f : α → F') : μ[f|⊥] = fun _ => ∫ x, f x ∂μ := by
  refine' (condexp_bot' f).trans _; rw [measure_univ, ENNReal.one_toReal, inv_one, one_smul]
#align measure_theory.condexp_bot MeasureTheory.condexp_bot

theorem condexp_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m] :=
  by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; simp
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigma_finite hm hμm]; simp
  haveI : sigma_finite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexp_L1 hm _).trans _
  rw [condexp_L1_add hf hg]
  exact
    (coe_fn_add _ _).trans
      ((condexp_ae_eq_condexp_L1 hm _).symm.add (condexp_ae_eq_condexp_L1 hm _).symm)
#align measure_theory.condexp_add MeasureTheory.condexp_add

theorem condexp_finset_sum {ι : Type _} {s : Finset ι} {f : ι → α → F'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : μ[∑ i in s, f i|m] =ᵐ[μ] ∑ i in s, μ[f i|m] :=
  by
  induction' s using Finset.induction_on with i s his heq hf
  · rw [Finset.sum_empty, Finset.sum_empty, condexp_zero]
  · rw [Finset.sum_insert his, Finset.sum_insert his]
    exact
      (condexp_add (hf i <| Finset.mem_insert_self i s) <|
            integrable_finset_sum' _ fun j hmem => hf j <| Finset.mem_insert_of_mem hmem).trans
        ((eventually_eq.refl _ _).add (HEq fun j hmem => hf j <| Finset.mem_insert_of_mem hmem))
#align measure_theory.condexp_finset_sum MeasureTheory.condexp_finset_sum

theorem condexp_smul (c : 𝕜) (f : α → F') : μ[c • f|m] =ᵐ[μ] c • μ[f|m] :=
  by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; simp
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigma_finite hm hμm]; simp
  haveI : sigma_finite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexp_L1 hm _).trans _
  rw [condexp_L1_smul c f]
  refine' (@condexp_ae_eq_condexp_L1 _ _ _ _ _ m _ _ hm _ f).mp _
  refine' (coe_fn_smul c (condexp_L1 hm μ f)).mono fun x hx1 hx2 => _
  rw [hx1, Pi.smul_apply, Pi.smul_apply, hx2]
#align measure_theory.condexp_smul MeasureTheory.condexp_smul

theorem condexp_neg (f : α → F') : μ[-f|m] =ᵐ[μ] -μ[f|m] := by
  letI : Module ℝ (α → F') := @Pi.module α (fun _ => F') ℝ _ _ fun _ => inferInstance <;>
    calc
      μ[-f|m] = μ[(-1 : ℝ) • f|m] := by rw [neg_one_smul ℝ f]
      _ =ᵐ[μ] (-1 : ℝ) • μ[f|m] := (condexp_smul (-1) f)
      _ = -μ[f|m] := neg_one_smul ℝ (μ[f|m])
#align measure_theory.condexp_neg MeasureTheory.condexp_neg

theorem condexp_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f - g|m] =ᵐ[μ] μ[f|m] - μ[g|m] :=
  by
  simp_rw [sub_eq_add_neg]
  exact (condexp_add hf hg.neg).trans (eventually_eq.rfl.add (condexp_neg g))
#align measure_theory.condexp_sub MeasureTheory.condexp_sub

theorem condexp_condexp_of_le {m₁ m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)] : μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] :=
  by
  by_cases hμm₁ : sigma_finite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condexp_of_not_sigma_finite (hm₁₂.trans hm₂) hμm₁]
  haveI : sigma_finite (μ.trim (hm₁₂.trans hm₂)) := hμm₁
  by_cases hf : integrable f μ
  swap; · simp_rw [condexp_undef hf, condexp_zero]
  refine'
    ae_eq_of_forall_set_integral_eq_of_sigma_finite' (hm₁₂.trans hm₂)
      (fun s hs hμs => integrable_condexp.integrable_on)
      (fun s hs hμs => integrable_condexp.integrable_on) _
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
      (strongly_measurable.ae_strongly_measurable' strongly_measurable_condexp)
  intro s hs hμs
  rw [set_integral_condexp (hm₁₂.trans hm₂) integrable_condexp hs]
  swap; · infer_instance
  rw [set_integral_condexp (hm₁₂.trans hm₂) hf hs, set_integral_condexp hm₂ hf (hm₁₂ s hs)]
#align measure_theory.condexp_condexp_of_le MeasureTheory.condexp_condexp_of_le

theorem condexp_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    μ[f|m] ≤ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]
  by_cases hμm : sigma_finite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigma_finite hm hμm]
  haveI : sigma_finite (μ.trim hm) := hμm
  exact
    (condexp_ae_eq_condexp_L1 hm _).trans_le
      ((condexp_L1_mono hf hg hfg).trans_eq (condexp_ae_eq_condexp_L1 hm _).symm)
#align measure_theory.condexp_mono MeasureTheory.condexp_mono

theorem condexp_nonneg {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f : α → E} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] μ[f|m] :=
  by
  by_cases hfint : integrable f μ
  · rw [(condexp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condexp_mono (integrable_zero _ _ _) hfint hf
  · rw [condexp_undef hfint]
#align measure_theory.condexp_nonneg MeasureTheory.condexp_nonneg

theorem condexp_nonpos {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f : α → E} (hf : f ≤ᵐ[μ] 0) : μ[f|m] ≤ᵐ[μ] 0 :=
  by
  by_cases hfint : integrable f μ
  · rw [(condexp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condexp_mono hfint (integrable_zero _ _ _) hf
  · rw [condexp_undef hfint]
#align measure_theory.condexp_nonpos MeasureTheory.condexp_nonpos

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condexp_L1`. -/
theorem tendsto_condexpL1_of_dominated_convergence (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → F'} {f : α → F'} (bound_fs : α → ℝ)
    (hfs_meas : ∀ n, AEStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
    (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => condexpL1 hm μ (fs n)) atTop (𝓝 (condexpL1 hm μ f)) :=
  tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs
#align measure_theory.tendsto_condexp_L1_of_dominated_convergence MeasureTheory.tendsto_condexpL1_of_dominated_convergence

/-- If two sequences of functions have a.e. equal conditional expectations at each step, converge
and verify dominated convergence hypotheses, then the conditional expectations of their limits are
a.e. equal. -/
theorem tendsto_condexp_unique (fs gs : ℕ → α → F') (f g : α → F')
    (hfs_int : ∀ n, Integrable (fs n) μ) (hgs_int : ∀ n, Integrable (gs n) μ)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hgs : ∀ᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α → ℝ)
    (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α → ℝ)
    (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x) (hfg : ∀ n, μ[fs n|m] =ᵐ[μ] μ[gs n|m]) :
    μ[f|m] =ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m0; swap; · simp_rw [condexp_of_not_le hm]
  by_cases hμm : sigma_finite (μ.trim hm); swap; · simp_rw [condexp_of_not_sigma_finite hm hμm]
  haveI : sigma_finite (μ.trim hm) := hμm
  refine' (condexp_ae_eq_condexp_L1 hm f).trans ((condexp_ae_eq_condexp_L1 hm g).trans _).symm
  rw [← Lp.ext_iff]
  have hn_eq : ∀ n, condexp_L1 hm μ (gs n) = condexp_L1 hm μ (fs n) :=
    by
    intro n
    ext1
    refine' (condexp_ae_eq_condexp_L1 hm (gs n)).symm.trans ((hfg n).symm.trans _)
    exact condexp_ae_eq_condexp_L1 hm (fs n)
  have hcond_fs : tendsto (fun n => condexp_L1 hm μ (fs n)) at_top (𝓝 (condexp_L1 hm μ f)) :=
    tendsto_condexp_L1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
      hfs_bound hfs
  have hcond_gs : tendsto (fun n => condexp_L1 hm μ (gs n)) at_top (𝓝 (condexp_L1 hm μ g)) :=
    tendsto_condexp_L1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
      hgs_bound hgs
  exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (eventually_of_forall hn_eq)
#align measure_theory.tendsto_condexp_unique MeasureTheory.tendsto_condexp_unique

end MeasureTheory

