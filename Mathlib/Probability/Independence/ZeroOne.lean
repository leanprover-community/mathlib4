/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional

#align_import probability.independence.zero_one from "leanprover-community/mathlib"@"2f8347015b12b0864dfaf366ec4909eb70c78740"

/-!
# Kolmogorov's 0-1 law

Let `s : ι → MeasurableSpace Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s atTop` has probability 0 or 1.

## Main statements

* `measure_zero_or_one_of_measurableSet_limsup_atTop`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s atTop` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.
-/


open MeasureTheory MeasurableSpace

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {α Ω ι : Type _} {_mα : MeasurableSpace α} {m m0 : MeasurableSpace Ω}
  {κ : kernel α Ω} {μα : Measure α} {μ : Measure Ω}

theorem measure_eq_zero_or_one_or_top_of_indepSetₖ_self {t : Set Ω}
    (h_indep : IndepSetₖ t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 ∨ κ a t = ∞ := by
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (t ∩ t)), Set.inter_self, ENNReal.mul_eq_mul_right h0 h_top] at ha
  exact Or.inr (Or.inl ha.symm)

theorem measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using measure_eq_zero_or_one_or_top_of_indepSetₖ_self h_indep
#align probability_theory.measure_eq_zero_or_one_or_top_of_indep_set_self ProbabilityTheory.measure_eq_zero_or_one_or_top_of_indepSet_self

theorem measure_eq_zero_or_one_of_indepSetₖ_self [∀ a, IsFiniteMeasure (κ a)] {t : Set Ω}
    (h_indep : IndepSetₖ t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSetₖ_self h_indep] with a h_0_1_top
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top

theorem measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using measure_eq_zero_or_one_of_indepSetₖ_self h_indep
#align probability_theory.measure_eq_zero_or_one_of_indep_set_self ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self

theorem condexp_eq_zero_or_one_of_condIndepSet_self
    [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [hμ : IsFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t)
    (h_indep : CondIndepSet m hm t t μ) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  have h := ae_of_ae_trim hm (measure_eq_zero_or_one_of_indepSetₖ_self h_indep)
  filter_upwards [condexpKernel_ae_eq_condexp hm ht, h] with ω hω_eq hω
  rw [← hω_eq, ENNReal.toReal_eq_zero_iff, ENNReal.toReal_eq_one_iff]
  cases hω with
  | inl h => exact Or.inl (Or.inl h)
  | inr h => exact Or.inr h

variable [IsMarkovKernel κ] [IsProbabilityMeasure μ] {s : ι → MeasurableSpace Ω}

open Filter

theorem indepₖ_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα) (t : Set ι) :
    Indepₖ (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) κ μα :=
  indepₖ_iSup_of_disjoint h_le h_indep disjoint_compl_right

theorem indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
  indepₖ_biSup_compl h_le h_indep t
#align probability_theory.indep_bsupr_compl ProbabilityTheory.indep_biSup_compl

theorem condIndep_biSup_compl [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (t : Set ι) :
    CondIndep m (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) hm μ :=
  indepₖ_biSup_compl h_le h_indep t

section Abstract

variable {α : Type _} {p : Set ι → Prop} {f : Filter ι} {ns : α → Set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : Set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → Set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = Set.univ`.

For the example of `f = atTop`, we can take
`p = bddAbove` and `ns : ι → Set ι := fun i => Set.Iic i`.
-/

theorem indepₖ_biSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) {t : Set ι} (ht : p t) :
    Indepₖ (⨆ n ∈ t, s n) (limsup s f) κ μα := by
  refine' indepₖ_of_indepₖ_of_le_right (indepₖ_biSup_compl h_le h_indep t) _
  refine' limsSup_le_of_le (by isBoundedDefault) _
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

theorem indep_biSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) μ :=
  indepₖ_biSup_limsup h_le h_indep hf ht
#align probability_theory.indep_bsupr_limsup ProbabilityTheory.indep_biSup_limsup

theorem condIndep_biSup_limsup [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    CondIndep m (⨆ n ∈ t, s n) (limsup s f) hm μ :=
  indepₖ_biSup_limsup h_le h_indep hf ht

theorem indepₖ_iSup_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indepₖ (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) κ μα := by
  refine' indepₖ_iSup_of_directed_le _ _ _ _
  · exact fun a => indepₖ_biSup_limsup h_le h_indep hf (hnsp a)
  · exact fun a => iSup₂_le fun n _ => h_le n
  · exact limsup_le_iSup.trans (iSup_le h_le)
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine' ⟨c, _, _⟩ <;> refine' iSup_mono fun n => iSup_mono' fun hn => ⟨_, le_rfl⟩
    · exact hc.1 hn
    · exact hc.2 hn

theorem indep_iSup_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) μ :=
  indepₖ_iSup_directed_limsup h_le h_indep hf hns hnsp
#align probability_theory.indep_supr_directed_limsup ProbabilityTheory.indep_iSup_directed_limsup

theorem condIndep_iSup_directed_limsup [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω]
    [Nonempty Ω] (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    CondIndep m (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) hm μ :=
  indepₖ_iSup_directed_limsup h_le h_indep hf hns hnsp

theorem indepₖ_iSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indepₖ (⨆ n, s n) (limsup s f) κ μα := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indepₖ_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine' iSup_congr fun n => _
  have h : ⨆ (i : α) (_ : n ∈ ns i), s n = ⨆ _ : ∃ i, n ∈ ns i, s n := by rw [iSup_exists]
  haveI : Nonempty (∃ i : α, n ∈ ns i) := ⟨hns_univ n⟩
  rw [h, iSup_const]

theorem indep_iSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) μ :=
  indepₖ_iSup_limsup h_le h_indep hf hns hnsp hns_univ
#align probability_theory.indep_supr_limsup ProbabilityTheory.indep_iSup_limsup

theorem condIndep_iSup_limsup [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (⨆ n, s n) (limsup s f) hm μ :=
  indepₖ_iSup_limsup h_le h_indep hf hns hnsp hns_univ

theorem indepₖ_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indepₖ (limsup s f) (limsup s f) κ μα :=
  indepₖ_of_indepₖ_of_le_left (indepₖ_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup

theorem indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  indepₖ_limsup_self h_le h_indep hf hns hnsp hns_univ
#align probability_theory.indep_limsup_self ProbabilityTheory.indep_limsup_self

theorem condIndep_limsup_self [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (limsup s f) (limsup s f) hm μ :=
  indepₖ_limsup_self h_le h_indep hf hns hnsp hns_univ

theorem measure_zero_or_one_of_measurableSet_limsup' (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndepₖ s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  measure_eq_zero_or_one_of_indepSetₖ_self
    ((indepₖ_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSetₖ_of_measurableSet ht_tail
      ht_tail)

theorem measure_zero_or_one_of_measurableSet_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    μ t = 0 ∨ μ t = 1 :=
  by simpa only [ae_dirac_eq, Filter.eventually_pure]
    using measure_zero_or_one_of_measurableSet_limsup' h_le h_indep hf hns hnsp hns_univ ht_tail
#align probability_theory.measure_zero_or_one_of_measurable_set_limsup ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup

theorem condexp_zero_or_one_of_measurableSet_limsup [TopologicalSpace Ω] [BorelSpace Ω]
    [PolishSpace Ω] [Nonempty Ω] (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  have h := ae_of_ae_trim hm
    (measure_zero_or_one_of_measurableSet_limsup' h_le h_indep hf hns hnsp hns_univ ht_tail)
  have ht : MeasurableSet t := limsup_le_iSup.trans (iSup_le h_le) t ht_tail
  filter_upwards [condexpKernel_ae_eq_condexp hm ht, h] with ω hω_eq hω
  rw [← hω_eq, ENNReal.toReal_eq_zero_iff, ENNReal.toReal_eq_one_iff]
  cases hω with
  | inl h => exact Or.inl (Or.inl h)
  | inr h => exact Or.inr h

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

theorem indepₖ_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα) :
    Indepₖ (limsup s atTop) (limsup s atTop) κ μα := by
  let ns : ι → Set ι := Set.Iic
  have hnsp : ∀ i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine' indepₖ_limsup_self h_le h_indep _ _ hnsp _
  · simp only [mem_atTop_sets, ge_iff_le, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine' ⟨b, fun c hc hct => _⟩
    suffices : ∀ i ∈ t, i < c; exact lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
  · exact fun n => ⟨n, le_rfl⟩

theorem indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ :=
  indepₖ_limsup_atTop_self h_le h_indep
#align probability_theory.indep_limsup_at_top_self ProbabilityTheory.indep_limsup_atTop_self

theorem condIndep_limsup_atTop_self [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atTop) (limsup s atTop) hm μ :=
  indepₖ_limsup_atTop_self h_le h_indep

theorem measure_zero_or_one_of_measurableSet_limsup_atTop' (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndepₖ s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  measure_eq_zero_or_one_of_indepSetₖ_self
    ((indepₖ_limsup_atTop_self h_le h_indep).indepSetₖ_of_measurableSet ht_tail ht_tail)

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s atTop` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using measure_zero_or_one_of_measurableSet_limsup_atTop' h_le h_indep ht_tail
#align probability_theory.measure_zero_or_one_of_measurable_set_limsup_at_top ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop

theorem condexp_zero_or_one_of_measurableSet_limsup_atTop [TopologicalSpace Ω] [BorelSpace Ω]
    [PolishSpace Ω] [Nonempty Ω] (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condexp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atTop_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

theorem indepₖ_limsup_atBot_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndepₖ s κ μα) :
    Indepₖ (limsup s atBot) (limsup s atBot) κ μα := by
  let ns : ι → Set ι := Set.Ici
  have hnsp : ∀ i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine' indepₖ_limsup_self h_le h_indep _ _ hnsp _
  · simp only [mem_atBot_sets, ge_iff_le, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine' ⟨b, fun c hc hct => _⟩
    suffices : ∀ i ∈ t, c < i; exact lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
  · exact directed_of_inf fun i j hij k hki => hij.trans hki
  · exact fun n => ⟨n, le_rfl⟩

theorem indep_limsup_atBot_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ :=
  indepₖ_limsup_atBot_self h_le h_indep
#align probability_theory.indep_limsup_at_bot_self ProbabilityTheory.indep_limsup_atBot_self

theorem condIndep_limsup_atBot_self [TopologicalSpace Ω] [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atBot) (limsup s atBot) hm μ :=
  indepₖ_limsup_atBot_self h_le h_indep

theorem measure_zero_or_one_of_measurableSet_limsup_atBot' (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndepₖ s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  measure_eq_zero_or_one_of_indepSetₖ_self
    ((indepₖ_limsup_atBot_self h_le h_indep).indepSetₖ_of_measurableSet ht_tail ht_tail)

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using measure_zero_or_one_of_measurableSet_limsup_atBot' h_le h_indep ht_tail
#align probability_theory.measure_zero_or_one_of_measurable_set_limsup_at_bot ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atBot

theorem condexp_zero_or_one_of_measurableSet_limsup_atBot [TopologicalSpace Ω] [BorelSpace Ω]
    [PolishSpace Ω] [Nonempty Ω] (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condexp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atBot_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtBot

end ProbabilityTheory
