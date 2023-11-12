/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic

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

variable {Ω ι : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  rw [IndepSet_iff] at h_indep
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  by_cases h0 : μ t = 0
  · exact Or.inl h0
  by_cases h_top : μ t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (μ (t ∩ t)), Set.inter_self, ENNReal.mul_eq_mul_right h0 h_top] at h_indep
  exact Or.inr (Or.inl h_indep.symm)
#align probability_theory.measure_eq_zero_or_one_or_top_of_indep_set_self ProbabilityTheory.measure_eq_zero_or_one_or_top_of_indepSet_self

theorem measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 := by
  have h_0_1_top := measure_eq_zero_or_one_or_top_of_indepSet_self h_indep
  simpa [measure_ne_top μ] using h_0_1_top
#align probability_theory.measure_eq_zero_or_one_of_indep_set_self ProbabilityTheory.measure_eq_zero_or_one_of_indepSet_self

variable [IsProbabilityMeasure μ] {s : ι → MeasurableSpace Ω}

open Filter

theorem indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
  indep_iSup_of_disjoint h_le h_indep disjoint_compl_right
#align probability_theory.indep_bsupr_compl ProbabilityTheory.indep_biSup_compl

section Abstract

variable {α : Type*} {p : Set ι → Prop} {f : Filter ι} {ns : α → Set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : Set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → Set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = Set.univ`.

For the example of `f = atTop`, we can take
`p = bddAbove` and `ns : ι → Set ι := fun i => Set.Iic i`.
-/


theorem indep_biSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) : Indep (⨆ n ∈ t, s n) (limsup s f) μ := by
  refine' indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) _
  refine' limsSup_le_of_le (by isBoundedDefault) _
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂
#align probability_theory.indep_bsupr_limsup ProbabilityTheory.indep_biSup_limsup

theorem indep_iSup_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) μ := by
  refine' indep_iSup_of_directed_le _ _ _ _
  · exact fun a => indep_biSup_limsup h_le h_indep hf (hnsp a)
  · exact fun a => iSup₂_le fun n _ => h_le n
  · exact limsup_le_iSup.trans (iSup_le h_le)
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine' ⟨c, _, _⟩ <;> refine' iSup_mono fun n => iSup_mono' fun hn => ⟨_, le_rfl⟩
    · exact hc.1 hn
    · exact hc.2 hn
#align probability_theory.indep_supr_directed_limsup ProbabilityTheory.indep_iSup_directed_limsup

theorem indep_iSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) μ := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine' iSup_congr fun n => _
  have h : ⨆ (i : α) (_ : n ∈ ns i), s n = ⨆ _ : ∃ i, n ∈ ns i, s n := by rw [iSup_exists]
  haveI : Nonempty (∃ i : α, n ∈ ns i) := ⟨hns_univ n⟩
  rw [h, iSup_const]
#align probability_theory.indep_supr_limsup ProbabilityTheory.indep_iSup_limsup

theorem indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup
#align probability_theory.indep_limsup_self ProbabilityTheory.indep_limsup_self

theorem measure_zero_or_one_of_measurableSet_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    μ t = 0 ∨ μ t = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
#align probability_theory.measure_zero_or_one_of_measurable_set_limsup ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

theorem indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ := by
  let ns : ι → Set ι := Set.Iic
  have hnsp : ∀ i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine' indep_limsup_self h_le h_indep _ _ hnsp _
  · simp only [mem_atTop_sets, ge_iff_le, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine' ⟨b, fun c hc hct => _⟩
    suffices : ∀ i ∈ t, i < c; exact lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
  · exact fun n => ⟨n, le_rfl⟩
#align probability_theory.indep_limsup_at_top_self ProbabilityTheory.indep_limsup_atTop_self

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s atTop` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    μ t = 0 ∨ μ t = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
#align probability_theory.measure_zero_or_one_of_measurable_set_limsup_at_top ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

theorem indep_limsup_atBot_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ := by
  let ns : ι → Set ι := Set.Ici
  have hnsp : ∀ i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine' indep_limsup_self h_le h_indep _ _ hnsp _
  · simp only [mem_atBot_sets, ge_iff_le, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine' ⟨b, fun c hc hct => _⟩
    suffices : ∀ i ∈ t, c < i; exact lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
  · exact Antitone.directed_le fun _ _ ↦ Set.Ici_subset_Ici.2
  · exact fun n => ⟨n, le_rfl⟩
#align probability_theory.indep_limsup_at_bot_self ProbabilityTheory.indep_limsup_atBot_self

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    μ t = 0 ∨ μ t = 1 :=
  measure_eq_zero_or_one_of_indepSet_self
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
#align probability_theory.measure_zero_or_one_of_measurable_set_limsup_at_bot ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atBot

end AtBot

end ProbabilityTheory
