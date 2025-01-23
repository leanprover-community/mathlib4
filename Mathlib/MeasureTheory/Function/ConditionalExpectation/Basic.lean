/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1

/-! # Conditional expectation

We build the conditional expectation of an integrable function `f` with value in a Banach space
with respect to a measure `μ` (defined on a measurable space structure `m₀`) and a measurable space
structure `m` with `hm : m ≤ m₀` (a sub-sigma-algebra). This is an `m`-strongly measurable
function `μ[f|hm]` which is integrable and verifies `∫ x in s, μ[f|hm] x ∂μ = ∫ x in s, f x ∂μ`
for all `m`-measurable sets `s`. It is unique as an element of `L¹`.

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define a map `Set α → (E →L[ℝ] (α →₁[μ] E))` which to a set associates a linear
  map. That linear map sends `x ∈ E` to the conditional expectation of the indicator of the set
  with value `x`.
* Extend that map to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).
* Define the conditional expectation of a function `f : α → E`, which is an integrable function
  `α → E` equal to 0 if `f` is not integrable, and equal to an `m`-measurable representative of
  `condExpL1CLM` applied to `[f]`, the equivalence class of `f` in `L¹`.

The first step is done in `MeasureTheory.Function.ConditionalExpectation.CondexpL2`, the two
next steps in `MeasureTheory.Function.ConditionalExpectation.CondexpL1` and the final step is
performed in this file.

## Main results

The conditional expectation and its properties

* `condExp (m : MeasurableSpace α) (μ : Measure α) (f : α → E)`: conditional expectation of `f`
  with respect to `m`.
* `integrable_condExp` : `condExp` is integrable.
* `stronglyMeasurable_condExp` : `condExp` is `m`-strongly-measurable.
* `setIntegral_condExp (hf : Integrable f μ) (hs : MeasurableSet[m] s)` : if `m ≤ m₀` (the
  σ-algebra over which the measure is defined), then the conditional expectation verifies
  `∫ x in s, condExp m μ f x ∂μ = ∫ x in s, f x ∂μ` for any `m`-measurable set `s`.

While `condExp` is function-valued, we also define `condExpL1` with value in `L1` and a continuous
linear map `condExpL1CLM` from `L1` to `L1`. `condExp` should be used in most cases.

Uniqueness of the conditional expectation

* `ae_eq_condExp_of_forall_setIntegral_eq`: an a.e. `m`-measurable function which verifies the
  equality of integrals is a.e. equal to `condExp`.

## Notations

For a measure `μ` defined on a measurable space structure `m₀`, another measurable space structure
`m` with `hm : m ≤ m₀` (a sub-σ-algebra) and a function `f`, we define the notation
* `μ[f|m] = condExp m μ f`.

## Tags

conditional expectation, conditional expected value

-/

open TopologicalSpace MeasureTheory.Lp Filter
open scoped Classical ENNReal Topology MeasureTheory

namespace MeasureTheory
  -- 𝕜 for ℝ or ℂ
  -- E for integrals on a Lp submodule
variable {α β E 𝕜 : Type*} [RCLike 𝕜] {m m₀ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
  {s : Set α}

section NormedAddCommGroup
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable (m) in
/-- Conditional expectation of a function. It is defined as 0 if any one of the following conditions
is true:
- `m` is not a sub-σ-algebra of `m₀`,
- `μ` is not σ-finite with respect to `m`,
- `f` is not integrable. -/
noncomputable irreducible_def condExp (μ : Measure[m₀] α) (f : α → E) : α → E :=
  if hm : m ≤ m₀ then
    if h : SigmaFinite (μ.trim hm) ∧ Integrable f μ then
      if StronglyMeasurable[m] f then f
      else have := h.1; aestronglyMeasurable'_condExpL1.mk (condExpL1 hm μ f)
    else 0
  else 0

@[deprecated (since := "2025-01-21")] alias condexp := condExp

-- We define notation `μ[f|m]` for the conditional expectation of `f` with respect to `m`.
scoped notation μ "[" f "|" m "]" => MeasureTheory.condExp m μ f

theorem condExp_of_not_le (hm_not : ¬m ≤ m₀) : μ[f|m] = 0 := by rw [condExp, dif_neg hm_not]

@[deprecated (since := "2025-01-21")] alias condexp_of_not_le := condExp_of_not_le

theorem condExp_of_not_sigmaFinite (hm : m ≤ m₀) (hμm_not : ¬SigmaFinite (μ.trim hm)) :
    μ[f|m] = 0 := by rw [condExp, dif_pos hm, dif_neg]; push_neg; exact fun h => absurd h hμm_not

@[deprecated (since := "2025-01-21")] alias condexp_of_not_sigmaFinite := condExp_of_not_sigmaFinite

theorem condExp_of_sigmaFinite (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    μ[f|m] =
      if Integrable f μ then
        if StronglyMeasurable[m] f then f
        else aestronglyMeasurable'_condExpL1.mk (condExpL1 hm μ f)
      else 0 := by
  rw [condExp, dif_pos hm]
  simp only [hμm, Ne, true_and]
  by_cases hf : Integrable f μ
  · rw [dif_pos hf, if_pos hf]
  · rw [dif_neg hf, if_neg hf]

@[deprecated (since := "2025-01-21")] alias condexp_of_sigmaFinite := condExp_of_sigmaFinite

theorem condExp_of_stronglyMeasurable (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → E}
    (hf : StronglyMeasurable[m] f) (hfi : Integrable f μ) : μ[f|m] = f := by
  rw [condExp_of_sigmaFinite hm, if_pos hfi, if_pos hf]

@[deprecated (since := "2025-01-21")]
alias condexp_of_stronglyMeasurable := condExp_of_stronglyMeasurable

theorem condExp_const (hm : m ≤ m₀) (c : E) [IsFiniteMeasure μ] : μ[fun _ : α ↦ c|m] = fun _ ↦ c :=
  condExp_of_stronglyMeasurable hm stronglyMeasurable_const (integrable_const c)

@[deprecated (since := "2025-01-21")] alias condexp_const := condExp_const

theorem condExp_ae_eq_condExpL1 (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] (f : α → E) :
    μ[f|m] =ᵐ[μ] condExpL1 hm μ f := by
  rw [condExp_of_sigmaFinite hm]
  by_cases hfi : Integrable f μ
  · rw [if_pos hfi]
    by_cases hfm : StronglyMeasurable[m] f
    · rw [if_pos hfm]
      exact (condExpL1_of_aestronglyMeasurable' (StronglyMeasurable.aeStronglyMeasurable' hfm)
        hfi).symm
    · rw [if_neg hfm]
      exact (AEStronglyMeasurable'.ae_eq_mk aestronglyMeasurable'_condExpL1).symm
  rw [if_neg hfi, condExpL1_undef hfi]
  exact (coeFn_zero _ _ _).symm

@[deprecated (since := "2025-01-21")] alias condexp_ae_eq_condexpL1 := condExp_ae_eq_condExpL1

theorem condExp_ae_eq_condExpL1CLM (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    μ[f|m] =ᵐ[μ] condExpL1CLM E hm μ (hf.toL1 f) := by
  refine (condExp_ae_eq_condExpL1 hm f).trans (Eventually.of_forall fun x => ?_)
  rw [condExpL1_eq hf]

@[deprecated (since := "2025-01-21")] alias condexp_ae_eq_condexpL1CLM := condExp_ae_eq_condExpL1CLM

theorem condExp_undef (hf : ¬Integrable f μ) : μ[f|m] = 0 := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  rw [condExp_of_sigmaFinite, if_neg hf]

@[deprecated (since := "2025-01-21")] alias condexp_undef := condExp_undef

@[simp]
theorem condExp_zero : μ[(0 : α → E)|m] = 0 := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]
  exact condExp_of_stronglyMeasurable hm stronglyMeasurable_zero (integrable_zero _ _ _)

@[deprecated (since := "2025-01-21")] alias condexp_zero := condExp_zero

theorem stronglyMeasurable_condExp : StronglyMeasurable[m] (μ[f|m]) := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]; exact stronglyMeasurable_zero
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact stronglyMeasurable_zero
  rw [condExp_of_sigmaFinite hm]
  split_ifs with hfi hfm
  · exact hfm
  · exact AEStronglyMeasurable'.stronglyMeasurable_mk _
  · exact stronglyMeasurable_zero

@[deprecated (since := "2025-01-21")] alias stronglyMeasurable_condexp := stronglyMeasurable_condExp

theorem condExp_congr_ae (h : f =ᵐ[μ] g) : μ[f|m] =ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm f).trans
    (Filter.EventuallyEq.trans (by rw [condExpL1_congr_ae hm h])
      (condExp_ae_eq_condExpL1 hm g).symm)

@[deprecated (since := "2025-01-21")] alias condexp_congr_ae := condExp_congr_ae

theorem condExp_of_aestronglyMeasurable' (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] {f : α → E}
    (hf : AEStronglyMeasurable' m f μ) (hfi : Integrable f μ) : μ[f|m] =ᵐ[μ] f := by
  refine ((condExp_congr_ae hf.ae_eq_mk).trans ?_).trans hf.ae_eq_mk.symm
  rw [condExp_of_stronglyMeasurable hm hf.stronglyMeasurable_mk
    ((integrable_congr hf.ae_eq_mk).mp hfi)]

@[deprecated (since := "2025-01-21")]
alias condexp_of_aestronglyMeasurable' := condExp_of_aestronglyMeasurable'

@[fun_prop]
theorem integrable_condExp : Integrable (μ[f|m]) μ := by
  by_cases hm : m ≤ m₀
  swap; · rw [condExp_of_not_le hm]; exact integrable_zero _ _ _
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · rw [condExp_of_not_sigmaFinite hm hμm]; exact integrable_zero _ _ _
  exact (integrable_condExpL1 f).congr (condExp_ae_eq_condExpL1 hm f).symm

@[deprecated (since := "2025-01-21")] alias integrable_condexp := integrable_condExp

/-- The integral of the conditional expectation `μ[f|hm]` over an `m`-measurable set is equal to
the integral of `f` on that set. -/
theorem setIntegral_condExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hs : MeasurableSet[m] s) : ∫ x in s, (μ[f|m]) x ∂μ = ∫ x in s, f x ∂μ := by
  rw [setIntegral_congr_ae (hm s hs) ((condExp_ae_eq_condExpL1 hm f).mono fun x hx _ => hx)]
  exact setIntegral_condExpL1 hf hs

@[deprecated (since := "2025-01-21")] alias setIntegral_condexp := setIntegral_condExp

@[deprecated (since := "2024-04-17")] alias set_integral_condexp := setIntegral_condExp

theorem integral_condExp (hm : m ≤ m₀) [hμm : SigmaFinite (μ.trim hm)] :
    ∫ x, (μ[f|m]) x ∂μ = ∫ x, f x ∂μ := by
  by_cases hf : Integrable f μ
  · suffices ∫ x in Set.univ, (μ[f|m]) x ∂μ = ∫ x in Set.univ, f x ∂μ by
      simp_rw [setIntegral_univ] at this; exact this
    exact setIntegral_condExp hm hf .univ
  simp only [condExp_undef hf, Pi.zero_apply, integral_zero, integral_undef hf]

@[deprecated (since := "2025-01-21")] alias integral_condexp := integral_condExp

/-- **Law of total probability** using `condExp` as conditional probability. -/
theorem integral_condExp_indicator [mβ : MeasurableSpace β] {Y : α → β} (hY : Measurable Y)
    [SigmaFinite (μ.trim hY.comap_le)] {A : Set α} (hA : MeasurableSet A) :
    ∫ x, (μ[(A.indicator fun _ ↦ (1 : ℝ)) | mβ.comap Y]) x ∂μ = (μ A).toReal := by
  rw [integral_condExp, integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]

@[deprecated (since := "2025-01-21")] alias integral_condexp_indicator := integral_condExp_indicator

/-- **Uniqueness of the conditional expectation**
If a function is a.e. `m`-measurable, verifies an integrability condition and has same integral
as `f` on all `m`-measurable sets, then it is a.e. equal to `μ[f|hm]`. -/
theorem ae_eq_condExp_of_forall_setIntegral_eq (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {f g : α → E} (hf : Integrable f μ)
    (hg_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable' m g μ) : g =ᵐ[μ] μ[f|m] := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm hg_int_finite
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs hμs => ?_) hgm
    (StronglyMeasurable.aeStronglyMeasurable' stronglyMeasurable_condExp)
  rw [hg_eq s hs hμs, setIntegral_condExp hm hf hs]

@[deprecated (since := "2025-01-21")]
alias ae_eq_condexp_of_forall_setIntegral_eq := ae_eq_condExp_of_forall_setIntegral_eq

@[deprecated (since := "2024-04-17")]
alias ae_eq_condExp_of_forall_set_integral_eq := ae_eq_condExp_of_forall_setIntegral_eq

@[deprecated (since := "2025-01-21")]
alias ae_eq_condexp_of_forall_set_integral_eq := ae_eq_condExp_of_forall_set_integral_eq

theorem condExp_bot' [hμ : NeZero μ] (f : α → E) :
    μ[f|⊥] = fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  by_cases hμ_finite : IsFiniteMeasure μ
  swap
  · have h : ¬SigmaFinite (μ.trim bot_le) := by rwa [sigmaFinite_trim_bot_iff]
    rw [not_isFiniteMeasure_iff] at hμ_finite
    rw [condExp_of_not_sigmaFinite bot_le h]
    simp only [hμ_finite, ENNReal.top_toReal, inv_zero, zero_smul]
    rfl
  have h_meas : StronglyMeasurable[⊥] (μ[f|⊥]) := stronglyMeasurable_condExp
  obtain ⟨c, h_eq⟩ := stronglyMeasurable_bot_iff.mp h_meas
  rw [h_eq]
  have h_integral : ∫ x, (μ[f|⊥]) x ∂μ = ∫ x, f x ∂μ := integral_condExp bot_le
  simp_rw [h_eq, integral_const] at h_integral
  rw [← h_integral, ← smul_assoc, smul_eq_mul, inv_mul_cancel₀, one_smul]
  rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, measure_ne_top μ Set.univ⟩

@[deprecated (since := "2025-01-21")] alias condexp_bot' := condExp_bot'

theorem condExp_bot_ae_eq (f : α → E) :
    μ[f|⊥] =ᵐ[μ] fun _ => (μ Set.univ).toReal⁻¹ • ∫ x, f x ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · rw [ae_zero]; exact eventually_bot
  · exact Eventually.of_forall <| congr_fun (condExp_bot' f)

@[deprecated (since := "2025-01-21")] alias condexp_bot_ae_eq := condExp_bot_ae_eq

theorem condExp_bot [IsProbabilityMeasure μ] (f : α → E) : μ[f|⊥] = fun _ => ∫ x, f x ∂μ := by
  refine (condExp_bot' f).trans ?_; rw [measure_univ, ENNReal.one_toReal, inv_one, one_smul]

@[deprecated (since := "2025-01-21")] alias condexp_bot := condExp_bot

theorem condExp_add (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α) :
    μ[f + g|m] =ᵐ[μ] μ[f|m] + μ[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_add hf hg]
  exact (coeFn_add _ _).trans
    ((condExp_ae_eq_condExpL1 hm _).symm.add (condExp_ae_eq_condExpL1 hm _).symm)

@[deprecated (since := "2025-01-21")] alias condexp_add := condExp_add

theorem condExp_finset_sum {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hf : ∀ i ∈ s, Integrable (f i) μ) (m : MeasurableSpace α) :
    μ[∑ i ∈ s, f i|m] =ᵐ[μ] ∑ i ∈ s, μ[f i|m] := by
  induction' s using Finset.induction_on with i s his heq hf
  · rw [Finset.sum_empty, Finset.sum_empty, condExp_zero]
  · rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (condExp_add (hf i <| Finset.mem_insert_self i s)
      (integrable_finset_sum' _ <| Finset.forall_of_forall_insert hf) _).trans
        ((EventuallyEq.refl _ _).add <| heq <| Finset.forall_of_forall_insert hf)

@[deprecated (since := "2025-01-21")] alias condexp_finset_sum := condExp_finset_sum

theorem condExp_smul [NormedSpace 𝕜 E] (c : 𝕜) (f : α → E) (m : MeasurableSpace α) :
    μ[c • f|m] =ᵐ[μ] c • μ[f|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; simp
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; simp
  refine (condExp_ae_eq_condExpL1 hm _).trans ?_
  rw [condExpL1_smul c f]
  refine (condExp_ae_eq_condExpL1 hm f).mp ?_
  refine (coeFn_smul c (condExpL1 hm μ f)).mono fun x hx1 hx2 => ?_
  simp only [hx1, hx2, Pi.smul_apply]

@[deprecated (since := "2025-01-21")] alias condexp_smul := condExp_smul

theorem condExp_neg (f : α → E) (m : MeasurableSpace α) : μ[-f|m] =ᵐ[μ] -μ[f|m] := by
  calc
    μ[-f|m] = μ[(-1 : ℝ) • f|m] := by rw [neg_one_smul ℝ f]
    _ =ᵐ[μ] (-1 : ℝ) • μ[f|m] := condExp_smul ..
    _ = -μ[f|m] := neg_one_smul ℝ (μ[f|m])

@[deprecated (since := "2025-01-21")] alias condexp_neg := condExp_neg

theorem condExp_sub (hf : Integrable f μ) (hg : Integrable g μ) (m : MeasurableSpace α) :
    μ[f - g|m] =ᵐ[μ] μ[f|m] - μ[g|m] := by
  simp_rw [sub_eq_add_neg]
  exact (condExp_add hf hg.neg _).trans (EventuallyEq.rfl.add (condExp_neg ..))

@[deprecated (since := "2025-01-21")] alias condexp_sub := condExp_sub

/-- **Tower property of the conditional expectation**.

Taking the `m₂`-conditional expectation then the `m₁`-conditional expectation, where `m₁` is a
smaller σ-algebra, is the same as taking the `m₁`-conditional expectation directly. -/
theorem condExp_condExp_of_le {m₁ m₂ m₀ : MeasurableSpace α} {μ : Measure α} (hm₁₂ : m₁ ≤ m₂)
    (hm₂ : m₂ ≤ m₀) [SigmaFinite (μ.trim hm₂)] : μ[μ[f|m₂]|m₁] =ᵐ[μ] μ[f|m₁] := by
  by_cases hμm₁ : SigmaFinite (μ.trim (hm₁₂.trans hm₂))
  swap; · simp_rw [condExp_of_not_sigmaFinite (hm₁₂.trans hm₂) hμm₁]; rfl
  by_cases hf : Integrable f μ
  swap; · simp_rw [condExp_undef hf, condExp_zero]; rfl
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (hm₁₂.trans hm₂)
    (fun s _ _ => integrable_condExp.integrableOn) (fun s _ _ => integrable_condExp.integrableOn) ?_
    stronglyMeasurable_condExp.aeStronglyMeasurable'
    stronglyMeasurable_condExp.aeStronglyMeasurable'
  intro s hs _
  rw [setIntegral_condExp (hm₁₂.trans hm₂) integrable_condExp hs]
  rw [setIntegral_condExp (hm₁₂.trans hm₂) hf hs, setIntegral_condExp hm₂ hf (hm₁₂ s hs)]

@[deprecated (since := "2025-01-21")] alias condexp_condexp_of_le := condExp_condExp_of_le

section MemL2
variable [InnerProductSpace 𝕜 E]

lemma Memℒp.condExpL2_ae_eq_condExp' (hm : m ≤ m₀) (hf1 : Integrable f μ) (hf2 : Memℒp f 2 μ)
    [SigmaFinite (μ.trim hm)] : condExpL2 E 𝕜 hm hf2.toLp =ᵐ[μ] μ[f | m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf1
    (fun s hs htop ↦ integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop ↦ ?_)
    (aeStronglyMeasurable'_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf2.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm _ hs) ?_
  filter_upwards [hf2.coeFn_toLp] with ω hω _ using hω

lemma Memℒp.condExpL2_ae_eq_condExp (hm : m ≤ m₀) (hf : Memℒp f 2 μ) [IsFiniteMeasure μ] :
    condExpL2 E 𝕜 hm hf.toLp =ᵐ[μ] μ[f | m] :=
  hf.condExpL2_ae_eq_condExp' hm (memℒp_one_iff_integrable.1 <| hf.mono_exponent one_le_two)

-- TODO: Generalize via the conditional Jensen inequality
include 𝕜 in
lemma eLpNorm_condExp_le : eLpNorm (μ[f | m]) 2 μ ≤ eLpNorm f 2 μ := by
  by_cases hm : m ≤ m₀; swap
  · simp [condExp_of_not_le hm]
  by_cases hfμ : SigmaFinite (μ.trim hm); swap
  · rw [condExp_of_not_sigmaFinite hm hfμ]
    simp
  by_cases hfi : Integrable f μ; swap
  · rw [condExp_undef hfi]
    simp
  obtain hf | hf := eq_or_ne (eLpNorm f 2 μ) ∞
  · simp [hf]
  replace hf : Memℒp f 2 μ := ⟨hfi.1, Ne.lt_top' fun a ↦ hf (id (Eq.symm a))⟩
  rw [← eLpNorm_congr_ae (hf.condExpL2_ae_eq_condExp' (𝕜 := 𝕜) hm hfi)]
  refine le_trans (eLpNorm_condExpL2_le hm _) ?_
  rw [eLpNorm_congr_ae hf.coeFn_toLp]

include 𝕜 in
protected lemma Memℒp.condExp (hf : Memℒp f 2 μ) : Memℒp (μ[f | m]) 2 μ := by
  by_cases hm : m ≤ m₀
  · exact ⟨(stronglyMeasurable_condExp.mono hm).aestronglyMeasurable,
      eLpNorm_condExp_le (𝕜 := 𝕜).trans_lt hf.eLpNorm_lt_top⟩
  · simp [condExp_of_not_le hm]

end MemL2
end NormedAddCommGroup

section NormedLatticeAddCommGroup
variable [NormedLatticeAddCommGroup E] [CompleteSpace E] [NormedSpace ℝ E]

/-- **Lebesgue dominated convergence theorem**: sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `condExpL1`. -/
theorem tendsto_condExpL1_of_dominated_convergence (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {fs : ℕ → α → E} {f : α → E} (bound_fs : α → ℝ)
    (hfs_meas : ∀ n, AEStronglyMeasurable (fs n) μ) (h_int_bound_fs : Integrable bound_fs μ)
    (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => condExpL1 hm μ (fs n)) atTop (𝓝 (condExpL1 hm μ f)) :=
  tendsto_setToFun_of_dominated_convergence _ bound_fs hfs_meas h_int_bound_fs hfs_bound hfs

@[deprecated (since := "2025-01-21")]
alias tendsto_condexpL1_of_dominated_convergence := tendsto_condExpL1_of_dominated_convergence

/-- If two sequences of functions have a.e. equal conditional expectations at each step, converge
and verify dominated convergence hypotheses, then the conditional expectations of their limits are
a.e. equal. -/
theorem tendsto_condExp_unique (fs gs : ℕ → α → E) (f g : α → E)
    (hfs_int : ∀ n, Integrable (fs n) μ) (hgs_int : ∀ n, Integrable (gs n) μ)
    (hfs : ∀ᵐ x ∂μ, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hgs : ∀ᵐ x ∂μ, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) (bound_fs : α → ℝ)
    (h_int_bound_fs : Integrable bound_fs μ) (bound_gs : α → ℝ)
    (h_int_bound_gs : Integrable bound_gs μ) (hfs_bound : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ bound_fs x)
    (hgs_bound : ∀ n, ∀ᵐ x ∂μ, ‖gs n x‖ ≤ bound_gs x) (hfg : ∀ n, μ[fs n|m] =ᵐ[μ] μ[gs n|m]) :
    μ[f|m] =ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m₀; swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm); swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  refine (condExp_ae_eq_condExpL1 hm f).trans ((condExp_ae_eq_condExpL1 hm g).trans ?_).symm
  rw [← Lp.ext_iff]
  have hn_eq : ∀ n, condExpL1 hm μ (gs n) = condExpL1 hm μ (fs n) := by
    intro n
    ext1
    refine (condExp_ae_eq_condExpL1 hm (gs n)).symm.trans ((hfg n).symm.trans ?_)
    exact condExp_ae_eq_condExpL1 hm (fs n)
  have hcond_fs : Tendsto (fun n => condExpL1 hm μ (fs n)) atTop (𝓝 (condExpL1 hm μ f)) :=
    tendsto_condExpL1_of_dominated_convergence hm _ (fun n => (hfs_int n).1) h_int_bound_fs
      hfs_bound hfs
  have hcond_gs : Tendsto (fun n => condExpL1 hm μ (gs n)) atTop (𝓝 (condExpL1 hm μ g)) :=
    tendsto_condExpL1_of_dominated_convergence hm _ (fun n => (hgs_int n).1) h_int_bound_gs
      hgs_bound hgs
  exact tendsto_nhds_unique_of_eventuallyEq hcond_gs hcond_fs (Eventually.of_forall hn_eq)

@[deprecated (since := "2025-01-21")] alias tendsto_condexp_unique := tendsto_condExp_unique

variable [OrderedSMul ℝ E]

lemma condExp_mono (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    μ[f|m] ≤ᵐ[μ] μ[g|m] := by
  by_cases hm : m ≤ m₀
  swap; · simp_rw [condExp_of_not_le hm]; rfl
  by_cases hμm : SigmaFinite (μ.trim hm)
  swap; · simp_rw [condExp_of_not_sigmaFinite hm hμm]; rfl
  exact (condExp_ae_eq_condExpL1 hm _).trans_le
    ((condExpL1_mono hf hg hfg).trans_eq (condExp_ae_eq_condExpL1 hm _).symm)

lemma condExp_nonneg (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] μ[f|m] := by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condExp_mono (integrable_zero _ _ _) hfint hf
  · rw [condExp_undef hfint]

lemma condExp_nonpos (hf : f ≤ᵐ[μ] 0) : μ[f|m] ≤ᵐ[μ] 0 := by
  by_cases hfint : Integrable f μ
  · rw [(condExp_zero.symm : (0 : α → E) = μ[0|m])]
    exact condExp_mono hfint (integrable_zero _ _ _) hf
  · rw [condExp_undef hfint]

@[deprecated (since := "2025-01-21")] alias condexp_mono := condExp_mono
@[deprecated (since := "2025-01-21")] alias condexp_nonneg := condExp_nonneg
@[deprecated (since := "2025-01-21")] alias condexp_nonpos := condExp_nonpos

end NormedLatticeAddCommGroup
end MeasureTheory
