/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`: for functions which are
  `AEFinStronglyMeasurable`.
* `Lp.ae_eq_of_forall_setIntegral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `Integrable.ae_eq_of_forall_setIntegral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.

We also register the corresponding lemma for integrals of `ℝ≥0∞`-valued functions, in
`ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `fun x => inner c (f x) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the dual space,
  `fun x => c (f x) =ᵐ[μ] 0` then `f =ᵐ[μ] 0`.

-/


open Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

theorem ae_const_le_iff_forall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] (f : α → β) (c : β) :
    (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 := by
  rw [ae_iff]
  push_neg
  constructor
  · intro h b hb
    exact measure_mono_null (fun y hy => (lt_of_le_of_lt hy hb : _)) h
  intro hc
  by_cases h : ∀ b, c ≤ b
  · have : {a : α | f a < c} = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.2 fun x hx => ?_
      exact (lt_irrefl _ (lt_of_lt_of_le hx (h (f x)))).elim
    simp [this]
  by_cases H : ¬IsLUB (Set.Iio c) c
  · have : c ∈ upperBounds (Set.Iio c) := fun y hy => le_of_lt hy
    obtain ⟨b, b_up, bc⟩ : ∃ b : β, b ∈ upperBounds (Set.Iio c) ∧ b < c := by
      simpa [IsLUB, IsLeast, this, lowerBounds] using H
    exact measure_mono_null (fun x hx => b_up hx) (hc b bc)
  push_neg at H h
  obtain ⟨u, _, u_lt, u_lim, -⟩ :
    ∃ u : ℕ → β,
      StrictMono u ∧ (∀ n : ℕ, u n < c) ∧ Tendsto u atTop (𝓝 c) ∧ ∀ n : ℕ, u n ∈ Set.Iio c :=
    H.exists_seq_strictMono_tendsto_of_not_mem (lt_irrefl c) h
  have h_Union : {x | f x < c} = ⋃ n : ℕ, {x | f x ≤ u n} := by
    ext1 x
    simp_rw [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor <;> intro h
    · obtain ⟨n, hn⟩ := ((tendsto_order.1 u_lim).1 _ h).exists; exact ⟨n, hn.le⟩
    · obtain ⟨n, hn⟩ := h; exact hn.trans_lt (u_lt _)
  rw [h_Union, measure_iUnion_null_iff]
  intro n
  exact hc _ (u_lt n)

theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  have A : ∀ (ε N : ℝ≥0) (p : ℕ), 0 < ε →
      μ ({x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanningSets μ p) = 0 := by
    intro ε N p εpos
    let s := {x | g x + ε ≤ f x ∧ g x ≤ N} ∩ spanningSets μ p
    have s_lt_top : μ s < ∞ :=
      (measure_mono (Set.inter_subset_right)).trans_lt (measure_spanningSets_lt_top μ p)
    have A : (∫⁻ x in s, g x ∂μ) + ε * μ s ≤ (∫⁻ x in s, g x ∂μ) + 0 :=
      calc
        (∫⁻ x in s, g x ∂μ) + ε * μ s = (∫⁻ x in s, g x ∂μ) + ∫⁻ _ in s, ε ∂μ := by
          simp only [lintegral_const, Set.univ_inter, MeasurableSet.univ, Measure.restrict_apply]
        _ = ∫⁻ x in s, g x + ε ∂μ := (lintegral_add_right _ measurable_const).symm
        _ ≤ ∫⁻ x in s, f x ∂μ :=
          setLIntegral_mono_ae hf.restrict <| ae_of_all _ fun x hx => hx.1.1
        _ ≤ (∫⁻ x in s, g x ∂μ) + 0 := by
          rw [add_zero, ← Measure.restrict_toMeasurable s_lt_top.ne]
          refine h _ (measurableSet_toMeasurable ..) ?_
          rwa [measure_toMeasurable]
    have B : (∫⁻ x in s, g x ∂μ) ≠ ∞ :=
      (setLIntegral_lt_top_of_le_nnreal s_lt_top.ne ⟨N, fun _ h ↦ h.1.2⟩).ne
    have : (ε : ℝ≥0∞) * μ s ≤ 0 := ENNReal.le_of_add_le_add_left B A
    simpa only [ENNReal.coe_eq_zero, nonpos_iff_eq_zero, mul_eq_zero, εpos.ne', false_or]
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ≥0)
  let s := fun n : ℕ => {x | g x + u n ≤ f x ∧ g x ≤ (n : ℝ≥0)} ∩ spanningSets μ n
  have μs : ∀ n, μ (s n) = 0 := fun n => A _ _ _ (u_pos n)
  have B : {x | f x ≤ g x}ᶜ ⊆ ⋃ n, s n := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf, not_le] at hx
    have L1 : ∀ᶠ n in atTop, g x + u n ≤ f x := by
      have : Tendsto (fun n => g x + u n) atTop (𝓝 (g x + (0 : ℝ≥0))) :=
        tendsto_const_nhds.add (ENNReal.tendsto_coe.2 u_lim)
      simp only [ENNReal.coe_zero, add_zero] at this
      exact eventually_le_of_tendsto_lt hx this
    have L2 : ∀ᶠ n : ℕ in (atTop : Filter ℕ), g x ≤ (n : ℝ≥0) :=
      haveI : Tendsto (fun n : ℕ => ((n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 ∞) := by
        simp only [ENNReal.coe_natCast]
        exact ENNReal.tendsto_nat_nhds_top
      eventually_ge_of_tendsto_gt (hx.trans_le le_top) this
    apply Set.mem_iUnion.2
    exact ((L1.and L2).and (eventually_mem_spanningSets μ x)).exists
  refine le_antisymm ?_ bot_le
  calc
    μ {x : α | (fun x : α => f x ≤ g x) x}ᶜ ≤ μ (⋃ n, s n) := measure_mono B
    _ ≤ ∑' n, μ (s n) := measure_iUnion_le _
    _ = 0 := by simp only [μs, tsum_zero]

@[deprecated (since := "2024-06-29")]
alias ae_le_of_forall_set_lintegral_le_of_sigmaFinite₀ :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀

theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ) : f ≤ᵐ[μ] g :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf.aemeasurable h

@[deprecated (since := "2024-06-29")]
alias ae_le_of_forall_set_lintegral_le_of_sigmaFinite :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  have A : f ≤ᵐ[μ] g :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf fun s hs h's => le_of_eq (h s hs h's)
  have B : g ≤ᵐ[μ] f :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hg fun s hs h's => ge_of_eq (h s hs h's)
  filter_upwards [A, B] with x using le_antisymm

@[deprecated (since := "2024-06-29")]
alias ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite₀ :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.aemeasurable hg.aemeasurable h

@[deprecated (since := "2024-06-29")]
alias ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite

-- todo: duplicate. Move the other one from SimpleFuncDenseLp to SimpleFunc?
theorem SimpleFunc.measure_support_lt_top' {β : Type*} [Zero β] (f : SimpleFunc α β)
    (hf : ∀ y, y ≠ 0 → μ (f ⁻¹' {y}) < ∞) :
    μ (Function.support f) < ∞ := by
  rw [support_eq]
  refine (measure_biUnion_finset_le _ _).trans_lt (ENNReal.sum_lt_top.mpr fun y hy => ?_)
  classical
  rw [Finset.mem_filter] at hy
  exact hf y hy.2

lemma SimpleFunc.measure_support_lt_top_of_lintegral_ne_top {f : SimpleFunc α ℝ≥0∞}
    (hf : f.lintegral μ ≠ ∞) :
    μ (Function.support f) < ∞ := by
  refine SimpleFunc.measure_support_lt_top' f ?_
  rw [← SimpleFunc.finMeasSupp_iff]
  refine SimpleFunc.FinMeasSupp.of_lintegral_ne_top hf

lemma SimpleFunc.tendsto_eapprox {f : α → ℝ≥0∞} (hf_meas : Measurable f) (x : α) :
    Tendsto (fun n ↦ SimpleFunc.eapprox f n x) atTop (𝓝 (f x)) := by
  nth_rw 2 [← SimpleFunc.iSup_coe_eapprox hf_meas]
  rw [iSup_apply]
  exact tendsto_atTop_iSup fun _ _ hnm ↦ SimpleFunc.monotone_eapprox f hnm x

lemma SimpleFunc.lintegral_le_lintegral {f : α → ℝ≥0∞} (hf_meas : Measurable f) (n : ℕ) :
    (SimpleFunc.eapprox f n).lintegral μ ≤ ∫⁻ x, f x ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf_meas]
  exact le_iSup (fun n ↦ (SimpleFunc.eapprox f n).lintegral μ) n

lemma SimpleFunc.measure_support_eapprox_lt_top {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∫⁻ x, f x ∂μ ≠ ∞) (n : ℕ) :
    μ (Function.support (SimpleFunc.eapprox f n)) < ∞ := by
  refine SimpleFunc.measure_support_lt_top_of_lintegral_ne_top ?_
  exact ((SimpleFunc.lintegral_le_lintegral hf_meas n).trans_lt hf.lt_top).ne

theorem ENNReal.finStronglyMeasurable_of_measurable {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hf_meas : Measurable f) :
    FinStronglyMeasurable f μ := by
  exact ⟨SimpleFunc.eapprox f, SimpleFunc.measure_support_eapprox_lt_top hf_meas hf,
    SimpleFunc.tendsto_eapprox hf_meas⟩

theorem ENNReal.aefinStronglyMeasurable_of_aemeasurable {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hf_meas : AEMeasurable f μ) :
    AEFinStronglyMeasurable f μ := by
  have h := ENNReal.finStronglyMeasurable_of_measurable (μ := μ) (f := hf_meas.mk f) ?_
    hf_meas.measurable_mk
  · exact ⟨hf_meas.mk f, h, hf_meas.ae_eq_mk⟩
  · rwa [lintegral_congr_ae hf_meas.ae_eq_mk.symm]

theorem AEMeasurable.ae_eq_of_forall_setLIntegral_eq {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (hgi : ∫⁻ x, g x ∂μ ≠ ∞)
    (hfg : ∀ ⦃s⦄, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  have hf' : AEFinStronglyMeasurable f μ :=
    ENNReal.aefinStronglyMeasurable_of_aemeasurable hfi hf
  have hg' : AEFinStronglyMeasurable g μ :=
    ENNReal.aefinStronglyMeasurable_of_aemeasurable hgi hg
  let s := hf'.sigmaFiniteSet
  let t := hg'.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict (s ∪ t)] g by
    refine ae_of_ae_restrict_of_ae_restrict_compl _ this ?_
    simp only [Set.compl_union]
    have h1 : f =ᵐ[μ.restrict sᶜ] 0 := hf'.ae_eq_zero_compl
    have h2 : g =ᵐ[μ.restrict tᶜ] 0 := hg'.ae_eq_zero_compl
    rw [ae_restrict_iff' (hf'.measurableSet.compl.inter hg'.measurableSet.compl)]
    rw [EventuallyEq, ae_restrict_iff' hf'.measurableSet.compl] at h1
    rw [EventuallyEq, ae_restrict_iff' hg'.measurableSet.compl] at h2
    filter_upwards [h1, h2] with x h1 h2 hx
    rw [h1 (Set.inter_subset_left hx), h2 (Set.inter_subset_right hx)]
  have := hf'.sigmaFinite_restrict
  have := hg'.sigmaFinite_restrict
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.restrict hg.restrict
    fun u hu huμ ↦ ?_
  rw [Measure.restrict_restrict hu]
  rw [Measure.restrict_apply hu] at huμ
  exact hfg (hu.inter (hf'.measurableSet.union hg'.measurableSet)) huμ

@[deprecated (since := "2024-06-29")]
alias AEMeasurable.ae_eq_of_forall_set_lintegral_eq := AEMeasurable.ae_eq_of_forall_setLIntegral_eq

section WithDensity

variable {m : MeasurableSpace α} {μ : Measure α}

theorem withDensity_eq_iff_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf hg fun s hs _ ↦ ?_
    rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩

theorem withDensity_eq_iff {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg ↦ by
    refine AEMeasurable.ae_eq_of_forall_setLIntegral_eq hf hg hfi ?_ fun s hs _ ↦ ?_
    · rwa [← setLIntegral_univ, ← withDensity_apply g MeasurableSet.univ, ← hfg,
        withDensity_apply f MeasurableSet.univ, setLIntegral_univ]
    · rw [← withDensity_apply f hs, ← withDensity_apply g hs, ← hfg], withDensity_congr_ae⟩

end WithDensity

end MeasureTheory
