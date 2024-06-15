/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1

#align_import measure_theory.function.conditional_expectation.basic from "leanprover-community/mathlib"@"d8bbb04e2d2a44596798a9207ceefc0fb236e41e"

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
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condexpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condexpL1CLM` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `MeasureTheory.Function.ConditionalExpectation.CondexpL2`, the two
next steps in `MeasureTheory.Function.ConditionalExpectation.CondexpL1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condexp (m : MeasurableSpace α) (μ : Measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condexp` : `condexp` is integrable.
* `stronglyMeasurable_condexp` : `condexp` is `m`-strongly-measurable.
* `setIntegral_condexp (hf : Integrable f μ) (hs : MeasurableSet[m] s)` : if `m ≤ m0` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condexp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condexp` is function-valued, we also define `condexpL1` with value in `L1` and a continuous
linear map `condexpL1CLM` from `L1` to `L1`. `condexp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condexp_of_forall_setIntegral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condexp`.

## Notations

For a measure `μ` defined on a measurable space structure `m0`, another measurable space structure
`m` with `hm : m ≤ m0` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condexp m μ f`.

## Tags

conditional expectation, conditional expected value

-/


open TopologicalSpace MeasureTheory.Lp Filter

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']

open scoped Classical

variable {m m0 : MeasurableSpace α} {μ : Measure α} {f g : α → F'} {s : Set α}

/-- Conditional expectation of a function. It is defined as 0 if any one of the following conditions
is true:
- `m` is not a sub-σ-algebra of `m0`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
noncomputable irreducible_def condexp (m : MeasurableSpace α) {m0 : MeasurableSpace α}
    (μ : Measure α) (f : α → F') : α → F' :=
  if hm : m ≤ m0 then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if StronglyMeasurable[m] f then f
      else (@aestronglyMeasurable'_condexpL1 _ _ _ _ _ m m0 μ hm h.1 _).mk
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
        if StronglyMeasurable[m] f then f
        else aestronglyMeasurable'_condexpL1.mk (condexpL1 hm μ f)
      else 0 := by
  rw [condexp, dif_pos hm]
  simp only [hμm, Ne, true_and_iff]
  by_cases hf : Integrable f μ
  · rw [dif_pos hf, if_pos hf]
  · rw [dif_neg hf, if_neg hf]
#align measure_theory.condexp_of_sigma_finite MeasureTheory.condexp_of_sigmaFinite

theorem condexp_of_stronglyMeasurable (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : StronglyMeasurable[m] f) (hfi : Integrable f μ) : μ[f|m] = f := by
  rw [condexp_of_sigmaFinite hm, if_pos hfi, if_pos hf]
#align measure_theory.condexp_of_strongly_measurable MeasureTheory.condexp_of_stronglyMeasurable

theorem condexp_const (hm : m ≤ m0) (c : F') [IsFiniteMeasure μ] :
    μ[fun _ : α => c|m] = fun _ => c :=
  condexp_of_stronglyMeasurable hm (@stronglyMeasurable_const _ _ m _ _) (integrable_const c)
#align measure_theory.condexp_const MeasureTheory.condexp_const

theorem condexp_ae_eq_condexpL1 (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (f : α → F') :
    μ[f|m] =ᵐ[μ] condexpL1 hm μ f := by
  rw [condexp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : StronglyMeasurable[m] f
    · rw [if_pos hfm]
      exact (condexpL1_of_aestronglyMeasurable' (StronglyMeasurable.aeStronglyMeasurable' hfm)
        hfi).symm
    · rw [if_neg hfm]
      exact (AEStronglyMeasurable'.ae_eq_mk aestronglyMeasurable'_condexpL1).symm
  rw [if_neg hfi, condexpL1_undef hfi]
  exact (coeFn_zero _ _ _).symm
set_option linter.uppercaseLean3 false in
#align measure_theory.condexp_ae_eq_condexp_L1 MeasureTheory.condexp_ae_eq_condexpL1

theorem condexp_ae_eq_condexpL1CLM (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f|m] =ᵐ[μ] condexpL1CLM F' hm μ (hf.toL1 f) := by
  refine (condexp_ae_eq_condexpL1 hm f).trans (eventually_of_forall fun x => ?_)
  rw [condexpL1_eq hf]
set_option linter.uppercaseLean3 false in
#align measure_theory.condexp_ae_eq_condexp_L1_clm MeasureTheory.condexp_ae_eq_condexpL1CLM

theorem condexp_undef (hf : ¬Integrable f μ) : μ[f|m] = 0 := by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  rw [condexp_of_sigmaFinite, if_neg hf]
#align measure_theory.condexp_undef MeasureTheory.condexp_undef

@[simp]
theorem condexp_zero : μ[(0 : α → F')|m] = 0 := by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hμm]
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact
    condexp_of_stronglyMeasurable hm (@stronglyMeasurable_zero _ _ m _ _) (integrable_zero _ _ _)
#align measure_theory.condexp_zero MeasureTheory.condexp_zero

theorem stronglyMeasurable_condexp : StronglyMeasurable[m] (μ[f|m]) := by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]; exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hμm]; exact stronglyMeasurable_zero
  haveI : SigmaFinite (μ.trim hm) := hμm
  rw [condexp_of_sigmaFinite hm]
  split_ifs with hfi hfm
  · exact hfm
  · exact AEStronglyMeasurable'.stronglyMeasurable_mk _
  · exact stronglyMeasurable_zero
#align measure_theory.strongly_measurable_condexp MeasureTheory.stronglyMeasurable_condexp

theorem condexp_congr_ae (h : f =ᵐ[μ] g) : μ[f|m] =ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact (condexp_ae_eq_condexpL1 hm f).trans
    (Filter.EventuallyEq.trans (by rw [condexpL1_congr_ae hm h])
      (condexp_ae_eq_condexpL1 hm g).symm)
#align measure_theory.condexp_congr_ae MeasureTheory.condexp_congr_ae

theorem condexp_of_aestronglyMeasurable' (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] {f : α → F'}
    (hf : AEStronglyMeasurable' m f μ) (hfi : Integrable f μ) : μ[f|m] =ᵐ[μ] f := by
  refine ((condexp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  rw [condexp_of_stronglyMeasurable hm hf.stronglyMeasurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi)]
#align measure_theory.condexp_of_ae_strongly_measurable' MeasureTheory.condexp_of_aestronglyMeasurable'

theorem integrable_condexp : Integrable (μ[f|m]) μ := by
  by_cases hm : m ≤ m0
  swap; · rw [condexp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condexp_of_not_sigmaFinite hm hμm]; exact integrable_zero _ _ _
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact (integrable_condexpL1 f).congr (condexp_ae_eq_condexpL1 hm f).symm
#align measure_theory.integrable_condexp MeasureTheory.integrable_condexp

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem setIntegral_condexp (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f|m]) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [setIntegral_congr_ae (hm s hs) ((condexp_ae_eq_condexpL1 hm f).mono fun x hx _ => hx)]
  exact setIntegral_condexpL1 hf hs
#align measure_theory.set_integral_condexp MeasureTheory.setIntegral_condexp

@[deprecated (since := "2024-04-17")] alias set_integral_condexp := setIntegral_condexp

theorem integral_condexp (hm : m ≤ m0) [hμm : SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    ∫ x, (μ[f|m]) x ∂μ = ∫ x, f x ∂μ := by
  suffices ∫ x in Set.univ, (μ[f|m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
    simp_rw [integral_univ] at this; exact this
  exact setIntegral_condexp hm hf (@MeasurableSet.univ _ m)
#align measure_theory.integral_condexp MeasureTheory.integral_condexp

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condexp_of_forall_setIntegral_eq (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → F'} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable' m g μ) : g =ᵐ[μ] μ[f|m] := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm hg_int_finite
    (fun s _ _ => integrable_condexp.integrableOn) (fun s hs hμs => ?_) hgm
    (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condexp)
  rw [hg_eq s hs hμs, setIntegral_condexp hm hf hs]
#align measure_theory.ae_eq_condexp_of_forall_set_integral_eq MeasureTheory.ae_eq_condexp_of_forall_setIntegral_eq

@[deprecated (since := "2024-04-17")]
alias ae_eq_condexp_of_forall_set_integral_eq := ae_eq_condexp_of_forall_setIntegral_eq

theorem condexp_bot' [hμ : NeZero μ] (f : α → F') :
    μ[f|⊥] = fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condexp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.top_toReal, inv_zero, zero_smul]
    rfl
  by_cases hf : Integrable f μ
  swap; · rw [integral_undef hf, smul_zero, condexp_undef hf]; rfl
  have h_meas : StronglyMeasurable[⊥] (μ[f|⊥]) := stronglyMeasurable_condexp
  obtain ⟨c, h_eq⟩ := stronglyMeasurable_bot_iff.mp h_meas
  rw [h_eq]
  have h_integral : ∫ x, (μ[f|⊥]) x ∂μ = ∫ x, f x ∂μ := integral_condexp bot_le hf
  simp_rw [h_eq, integral_const] at h_integral
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel, one_smul]
  rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩
#align measure_theory.condexp_bot' MeasureTheory.condexp_bot'

theorem condexp_bot_ae_eq (f : α → F') :
    μ[f|⊥] =ᵐ[μ] fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
  · exact eventually_of_forall <| congr_fun (condexp_bot' f)
#align measure_theory.condexp_bot_ae_eq MeasureTheory.condexp_bot_ae_eq

theorem condexp_bot [IsProbabilityMeasure μ] (f : α → F') : μ[f|⊥] = fun _ => ∫ x, f x ∂μ := by
  refine (condexp_bot' f).trans ?_; rw [measure_univ, ENNReal.one_toReal, inv_one, one_smul]
#align measure_theory.condexp_bot MeasureTheory.condexp_bot

theorem condexp_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m] := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  refine (condexp_ae_eq_condexpL1 hm _).trans ?_
  rw [condexpL1_add hf hg]
  exact (coeFn_add _ _).trans
    ((condexp_ae_eq_condexpL1 hm _).symm.add (condexp_ae_eq_condexpL1 hm _).symm)
#align measure_theory.condexp_add MeasureTheory.condexp_add

theorem condexp_finset_sum {ι : Type*} {s : Finset ι} {f : ι → α → F'}
    (hf : ∀ i ∈ s, Integrable (f i) μ) : μ[∑ i ∈ s, f i|m] =ᵐ[μ] ∑ i ∈ s, μ[f i|m] := by
  induction' s using Finset.induction_on with i s his heq hf
  · rw [Finset.sum_empty, Finset.sum_empty, condexp_zero]
  · rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (condexp_add (hf i <| Finset.mem_insert_self i s) <|
      integrable_finset_sum' _ fun j hmem => hf j <| Finset.mem_insert_of_mem hmem).trans
        ((EventuallyEq.refl _ _).add (heq fun j hmem => hf j <| Finset.mem_insert_of_mem hmem))
#align measure_theory.condexp_finset_sum MeasureTheory.condexp_finset_sum

theorem condexp_smul (c : 𝕜) (f : α → F') : μ[c • f|m] =ᵐ[μ] c • μ[f|m] := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; simp
  haveI : SigmaFinite (μ.trim hm) := hμm
  refine (condexp_ae_eq_condexpL1 hm _).trans ?_
  rw [condexpL1_smul c f]
  refine (@condexp_ae_eq_condexpL1 _ _ _ _ _ m _ _ hm _ f).mp ?_
  refine (coeFn_smul c (condexpL1 hm μ f)).mono fun x hx1 hx2 => ?_
  simp only [hx1, hx2, Pi.smul_apply]
#align measure_theory.condexp_smul MeasureTheory.condexp_smul

theorem condexp_neg (f : α → F') : μ[-f|m] =ᵐ[μ] -μ[f|m] := by
  letI : Module ℝ (α → F') := @Pi.module α (fun _ => F') ℝ _ _ fun _ => inferInstance
  calc
    μ[-f|m] = μ[(-1 : ℝ) • f|m] := by rw [neg_one_smul ℝ f]
    _ =ᵐ[μ] (-1 : ℝ) • μ[f|m] := condexp_smul (-1) f
    _ = -μ[f|m] := neg_one_smul ℝ (μ[f|m])
#align measure_theory.condexp_neg MeasureTheory.condexp_neg

theorem condexp_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ[f - g|m] =ᵐ[μ] μ[f|m] - μ[g|m] := by
  simp_rw [sub_eq_add_neg]
  exact (condexp_add hf hg.neg).trans (EventuallyEq.rfl.add (condexp_neg g))
#align measure_theory.condexp_sub MeasureTheory.condexp_sub

theorem condexp_condexp_of_le {m₁ m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m0) [SigmaFinite (μ.trim hm₂)] : μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] := by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condexp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  haveI : SigmaFinite (μ.trim (hm₁₂.trans hm₂)) := hμm₁
  by_cases hf : Integrable f μ
  swap; · simp_rw [condexp_undef hf, condexp_zero]; rfl
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm₁₂.trans hm₂)
    (fun s _ _ => integrable_condexp.integrableOn)
    (fun s _ _ => integrable_condexp.integrableOn) ?_
    (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condexp)
    (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condexp)
  intro s hs _
  rw [setIntegral_condexp (hm₁₂.trans hm₂) integrable_condexp hs]
  rw [setIntegral_condexp (hm₁₂.trans hm₂) hf hs, setIntegral_condexp hm₂ hf (hm₁₂ s hs)]
#align measure_theory.condexp_condexp_of_le MeasureTheory.condexp_condexp_of_le

theorem condexp_mono {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    μ[f|m] ≤ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m0
  swap; · simp_rw [condexp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  exact (condexp_ae_eq_condexpL1 hm _).trans_le
    ((condexpL1_mono hf hg hfg).trans_eq (condexp_ae_eq_condexpL1 hm _).symm)
#align measure_theory.condexp_mono MeasureTheory.condexp_mono

theorem condexp_nonneg {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f : α → E} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] μ[f|m] := by
  by_cases hfint : Integrable f μ
  · rw [(condexp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condexp_mono (integrable_zero _ _ _) hfint hf
  · rw [condexp_undef hfint]
#align measure_theory.condexp_nonneg MeasureTheory.condexp_nonneg

theorem condexp_nonpos {E} [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]
    [OrderedSMul ℝ E] {f : α → E} (hf : f ≤ᵐ[μ] 0) : μ[f|m] ≤ᵐ[μ] 0 := by
  by_cases hfint : Integrable f μ
  · rw [(condexp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condexp_mono hfint (integrable_zero _ _ _) hf
  · rw [condexp_undef hfint]
#align measure_theory.condexp_nonpos MeasureTheory.condexp_nonpos

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condexpL1`. -/
theorem tendsto_condexpL1_of_dominated_convergence (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → F'} {f : α → F'} (bound_fs : α → ℝ)
    (hfs_meas : ∀ n, AEStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
    (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => condexpL1 hm μ (fs n)) atTop (𝓝 (condexpL1 hm μ f)) :=
  tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs
set_option linter.uppercaseLean3 false in
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
  by_cases hm : m ≤ m0; swap; · simp_rw [condexp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap; · simp_rw [condexp_of_not_sigmaFinite hm hμm]; rfl
  haveI : SigmaFinite (μ.trim hm) := hμm
  refine (condexp_ae_eq_condexpL1 hm f).trans ((condexp_ae_eq_condexpL1 hm g).trans ?_).symm
  rw [← Lp.ext_iff]
  have hn_eq : ∀ n, condexpL1 hm μ (gs n) = condexpL1 hm μ (fs n) := by
    intro n
    ext1
    refine (condexp_ae_eq_condexpL1 hm (gs n)).symm.trans ((hfg n).symm.trans ?_)
    exact condexp_ae_eq_condexpL1 hm (fs n)
  have hcond_fs : Tendsto (fun n => condexpL1 hm μ (fs n)) atTop (𝓝 (condexpL1 hm μ f)) :=
    tendsto_condexpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
      hfs_bound hfs
  have hcond_gs : Tendsto (fun n => condexpL1 hm μ (gs n)) atTop (𝓝 (condexpL1 hm μ g)) :=
    tendsto_condexpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
      hgs_bound hgs
  exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (eventually_of_forall hn_eq)
#align measure_theory.tendsto_condexp_unique MeasureTheory.tendsto_condexp_unique

end MeasureTheory
