/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

This file is about Lebesgue integrals. See the file `AEEqOfIntegral` for Bochner integrals.

## Main statements

The results listed below apply to two functions `f, g`, under the hypothesis that
for all measurable sets `s` with finite measure, `∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ`.
The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEMeasurable.ae_eq_of_forall_setLIntegral_eq`: for functions which are `AEMeasurable` and
  have finite integral.

-/

public section


open Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

theorem ae_const_le_iff_forall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] (f : α → β) (c : β) :
    (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 := by
  rw [ae_iff]
  push Not
  constructor
  · intro h b hb
    exact measure_mono_null (fun y hy => (lt_of_le_of_lt hy hb : _)) h
  intro hc
  by_cases! h : ∀ b, c ≤ b
  · have : {a : α | f a < c} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      exact (lt_irrefl _ (lt_of_lt_of_le hx (h (f x)))).elim
    simp [this]
  by_cases! H : ¬IsLUB (Set.Iio c) c
  · have : c ∈ upperBounds (Set.Iio c) := fun y hy => le_of_lt hy
    obtain ⟨b, b_up, bc⟩ : ∃ b : β, b ∈ upperBounds (Set.Iio c) ∧ b < c := by
      simpa [IsLUB, IsLeast, this, lowerBounds] using H
    exact measure_mono_null (fun x hx => b_up hx) (hc b bc)
  obtain ⟨u, _, u_lt, u_lim, -⟩ :
    ∃ u : ℕ → β,
      StrictMono u ∧ (∀ n : ℕ, u n < c) ∧ Tendsto u atTop (𝓝 c) ∧ ∀ n : ℕ, u n ∈ Set.Iio c :=
    H.exists_seq_strictMono_tendsto_of_notMem (lt_irrefl c) h
  have h_Union : {x | f x < c} = ⋃ n : ℕ, {x | f x ≤ u n} := by
    ext1 x
    simp_rw [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor <;> intro h
    · obtain ⟨n, hn⟩ := ((tendsto_order.1 u_lim).1 _ h).exists; exact ⟨n, hn.le⟩
    · obtain ⟨n, hn⟩ := h; exact hn.trans_lt (u_lt _)
  rw [h_Union, measure_iUnion_null_iff]
  intro n
  exact hc _ (u_lt n)

lemma ae_le_const_iff_forall_gt_measure_zero {β} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [FirstCountableTopology β] {μ : Measure α} (f : α → β) (c : β) :
    (∀ᵐ x ∂μ, f x ≤ c) ↔ ∀ b, c < b → μ {x | b ≤ f x} = 0 :=
  ae_const_le_iff_forall_lt_measure_zero (β := βᵒᵈ) _ _

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
      exact this.eventually_le_const hx
    have L2 : ∀ᶠ n : ℕ in (atTop : Filter ℕ), g x ≤ (n : ℝ≥0) :=
      have : Tendsto (fun n : ℕ => ((n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 ∞) := by
        simp only [ENNReal.coe_natCast]
        exact ENNReal.tendsto_nat_nhds_top
      this.eventually_const_le (hx.trans_le le_top)
    apply Set.mem_iUnion.2
    exact ((L1.and L2).and (eventually_mem_spanningSets μ x)).exists
  refine le_antisymm ?_ bot_le
  calc
    μ {x : α | (fun x : α => f x ≤ g x) x}ᶜ ≤ μ (⋃ n, s n) := measure_mono B
    _ ≤ ∑' n, μ (s n) := measure_iUnion_le _
    _ = 0 := by simp only [μs, tsum_zero]

theorem ae_le_of_forall_setLIntegral_le_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → (∫⁻ x in s, f x ∂μ) ≤ ∫⁻ x in s, g x ∂μ) : f ≤ᵐ[μ] g :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf.aemeasurable h

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ [SigmaFinite μ]
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g := by
  have A : f ≤ᵐ[μ] g :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf fun s hs h's => le_of_eq (h s hs h's)
  have B : g ≤ᵐ[μ] f :=
    ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hg fun s hs h's => ge_of_eq (h s hs h's)
  filter_upwards [A, B] with x using le_antisymm

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) : f =ᵐ[μ] g :=
  ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.aemeasurable hg.aemeasurable h

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
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hf.restrict hg.restrict
    fun u hu huμ ↦ ?_
  rw [Measure.restrict_restrict hu]
  rw [Measure.restrict_apply hu] at huμ
  exact hfg (hu.inter (hf'.measurableSet.union hg'.measurableSet)) huμ

section PiSystem

variable {s : Set (Set α)} {f g : α → ℝ≥0∞}

theorem lintegral_eq_lintegral_of_isPiSystem
    (h_eq : m0 = MeasurableSpace.generateFrom s) (h_inter : IsPiSystem s)
    (basic : ∀ t ∈ s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ)
    (h_univ : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ) (hf_int : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ t (_ : MeasurableSet t), ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ := by
  refine MeasurableSpace.induction_on_inter h_eq h_inter ?_ basic ?_ ?_
  · simp
  · intro t ht h_eq
    rw [setLIntegral_compl ht, setLIntegral_compl ht, h_eq, h_univ]
    · refine ne_of_lt ?_
      calc ∫⁻ x in t, g x ∂μ
      _ ≤ ∫⁻ x, g x ∂μ := setLIntegral_le_lintegral t _
      _ < ∞ := by rw [← h_univ]; exact hf_int.lt_top
    · refine ne_of_lt ?_
      calc ∫⁻ x in t, f x ∂μ
      _ ≤ ∫⁻ x, f x ∂μ := setLIntegral_le_lintegral t _
      _ < ∞ := hf_int.lt_top
  · intro t htd htm h
    simp_rw [lintegral_iUnion htm htd, h]

lemma lintegral_eq_lintegral_of_isPiSystem_of_univ_mem
    (h_eq : m0 = MeasurableSpace.generateFrom s) (h_inter : IsPiSystem s) (h_univ : Set.univ ∈ s)
    (basic : ∀ t ∈ s, ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ)
    (hf_int : ∫⁻ x, f x ∂μ ≠ ∞) {t : Set α} (ht : MeasurableSet t) :
    ∫⁻ x in t, f x ∂μ = ∫⁻ x in t, g x ∂μ := by
  refine lintegral_eq_lintegral_of_isPiSystem h_eq h_inter basic ?_ hf_int t ht
  rw [← setLIntegral_univ, ← setLIntegral_univ g]
  exact basic _ h_univ

/-- If two a.e.-measurable functions `α × β → ℝ≥0∞` with finite integrals have the same integral
on every rectangle, then they are almost everywhere equal. -/
lemma ae_eq_of_setLIntegral_prod_eq {β : Type*} {mβ : MeasurableSpace β}
    {μ : Measure (α × β)} {f g : α × β → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hf_int : ∫⁻ x, f x ∂μ ≠ ∞)
    (h : ∀ ⦃s : Set α⦄ (_ : MeasurableSet s) ⦃t : Set β⦄ (_ : MeasurableSet t),
      ∫⁻ x in s ×ˢ t, f x ∂μ = ∫⁻ x in s ×ˢ t, g x ∂μ) :
    f =ᵐ[μ] g := by
  have hg_int : ∫⁻ x, g x ∂μ ≠ ∞ := by
    rwa [← setLIntegral_univ, ← Set.univ_prod_univ, ← h .univ .univ, Set.univ_prod_univ,
      setLIntegral_univ]
  refine AEMeasurable.ae_eq_of_forall_setLIntegral_eq hf hg hf_int hg_int fun s hs _ ↦ ?_
  refine lintegral_eq_lintegral_of_isPiSystem_of_univ_mem generateFrom_prod.symm isPiSystem_prod
    ?_ ?_ hf_int hs
  · exact ⟨Set.univ, .univ, Set.univ, .univ, Set.univ_prod_univ⟩
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact h hs ht

end PiSystem

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
