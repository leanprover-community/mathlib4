/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional

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

variable {α Ω ι : Type*} {_mα : MeasurableSpace α} {s : ι → MeasurableSpace Ω}
  {m m0 : MeasurableSpace Ω} {κ : Kernel α Ω} {μα : Measure α} {μ : Measure Ω}

theorem Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : Kernel.IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 ∨ κ a t = ∞ := by
  specialize h_indep t t (measurableSet_generateFrom (Set.mem_singleton t))
    (measurableSet_generateFrom (Set.mem_singleton t))
  filter_upwards [h_indep] with a ha
  by_cases h0 : κ a t = 0
  · exact Or.inl h0
  by_cases h_top : κ a t = ∞
  · exact Or.inr (Or.inr h_top)
  rw [← one_mul (κ a (t ∩ t)), Set.inter_self, ENNReal.mul_left_inj h0 h_top] at ha
  exact Or.inr (Or.inl ha.symm)

theorem measure_eq_zero_or_one_or_top_of_indepSet_self {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using Kernel.measure_eq_zero_or_one_or_top_of_indepSet_self h_indep

theorem Kernel.measure_eq_zero_or_one_of_indepSet_self' (h : ∀ᵐ a ∂μα, IsFiniteMeasure (κ a))
    {t : Set Ω} (h_indep : IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  filter_upwards [measure_eq_zero_or_one_or_top_of_indepSet_self h_indep, h] with a h_0_1_top h'
  simpa only [measure_ne_top (κ a), or_false] using h_0_1_top

theorem Kernel.measure_eq_zero_or_one_of_indepSet_self [h : ∀ a, IsFiniteMeasure (κ a)] {t : Set Ω}
    (h_indep : IndepSet t t κ μα) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 :=
  Kernel.measure_eq_zero_or_one_of_indepSet_self' (ae_of_all μα h) h_indep

theorem measure_eq_zero_or_one_of_indepSet_self [IsFiniteMeasure μ] {t : Set Ω}
    (h_indep : IndepSet t t μ) : μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep

theorem condExp_eq_zero_or_one_of_condIndepSet_self
    [StandardBorelSpace Ω]
    (hm : m ≤ m0) [hμ : IsFiniteMeasure μ] {t : Set Ω} (ht : MeasurableSet t)
    (h_indep : CondIndepSet m hm t t μ) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  -- TODO: Why is not inferred?
  have (a : _) : IsFiniteMeasure (condExpKernel μ m a) := inferInstance
  have h := ae_of_ae_trim hm (Kernel.measure_eq_zero_or_one_of_indepSet_self h_indep)
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero_iff, measureReal_def, ENNReal.toReal_eq_one_iff]

open Filter

theorem Kernel.indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) κ μα :=
  indep_iSup_of_disjoint h_le h_indep disjoint_compl_right

theorem indep_biSup_compl (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
  Kernel.indep_biSup_compl h_le h_indep t

theorem condIndep_biSup_compl [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (t : Set ι) :
    CondIndep m (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) hm μ :=
  Kernel.indep_biSup_compl h_le h_indep t

section Abstract

variable {β : Type*} {p : Set ι → Prop} {f : Filter ι} {ns : β → Set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : Set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → Set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = Set.univ`.

For the example of `f = atTop`, we can take
`p = bddAbove` and `ns : ι → Set ι := fun i => Set.Iic i`.
-/

theorem Kernel.indep_biSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) κ μα := by
  refine indep_of_indep_of_le_right (indep_biSup_compl h_le h_indep t) ?_
  refine limsSup_le_of_le (by isBoundedDefault) ?_
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_iSup₂

theorem indep_biSup_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    Indep (⨆ n ∈ t, s n) (limsup s f) μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht

theorem condIndep_biSup_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    {t : Set ι} (ht : p t) :
    CondIndep m (⨆ n ∈ t, s n) (limsup s f) hm μ :=
  Kernel.indep_biSup_limsup h_le h_indep hf ht

theorem Kernel.indep_iSup_directed_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) κ μα := by
  rcases eq_or_ne μα 0 with rfl | hμ
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[μα] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel h_indep.ae_isProbabilityMeasure hμ
  replace h_indep := h_indep.congr η_eq
  apply Indep.congr (Filter.EventuallyEq.symm η_eq)
  apply indep_iSup_of_directed_le
  · exact fun a => indep_biSup_limsup h_le h_indep hf (hnsp a)
  · exact fun a => iSup₂_le fun n _ => h_le n
  · exact limsup_le_iSup.trans (iSup_le h_le)
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine ⟨c, ?_, ?_⟩ <;> refine iSup_mono fun n => iSup_mono' fun hn => ⟨?_, le_rfl⟩
    · exact hc.1 hn
    · exact hc.2 hn

theorem indep_iSup_directed_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

theorem condIndep_iSup_directed_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) :
    CondIndep m (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) hm μ :=
  Kernel.indep_iSup_directed_limsup h_le h_indep hf hns hnsp

theorem Kernel.indep_iSup_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) κ μα := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_iSup_directed_limsup h_le h_indep hf hns hnsp
  rw [iSup_comm]
  refine iSup_congr fun n => ?_
  have h : ⨆ (i : β) (_ : n ∈ ns i), s n = ⨆ _ : ∃ i, n ∈ ns i, s n := by rw [iSup_exists]
  haveI : Nonempty (∃ i : β, n ∈ ns i) := ⟨hns_univ n⟩
  rw [h, iSup_const]

theorem indep_iSup_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

theorem condIndep_iSup_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (⨆ n, s n) (limsup s f) hm μ :=
  Kernel.indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ

theorem Kernel.indep_limsup_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) κ μα :=
  indep_of_indep_of_le_left (indep_iSup_limsup h_le h_indep hf hns hnsp hns_univ) limsup_le_iSup

theorem indep_limsup_self
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

theorem condIndep_limsup_self [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    CondIndep m (limsup s f) (limsup s f) hm μ :=
  Kernel.indep_limsup_self h_le h_indep hf hns hnsp hns_univ

theorem Kernel.measure_zero_or_one_of_measurableSet_limsup (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_self h_le h_indep hf hns hnsp hns_univ).indepSet_of_measurableSet ht_tail
      ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

theorem measure_zero_or_one_of_measurableSet_limsup
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ
      ht_tail

theorem condExp_zero_or_one_of_measurableSet_limsup [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a))
    (hns_univ : ∀ n, ∃ a, n ∈ ns a) {t : Set Ω} (ht_tail : MeasurableSet[limsup s f] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 := by
  have h := ae_of_ae_trim hm
    (Kernel.measure_zero_or_one_of_measurableSet_limsup h_le h_indep hf hns hnsp hns_univ ht_tail)
  have ht : MeasurableSet t := limsup_le_iSup.trans (iSup_le h_le) t ht_tail
  filter_upwards [condExpKernel_ae_eq_condExp hm ht, h] with ω hω_eq hω
  rwa [← hω_eq, measureReal_eq_zero_iff, measureReal_def, ENNReal.toReal_eq_one_iff]

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

theorem Kernel.indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atTop) (limsup s atTop) κ μα := by
  let ns : ι → Set ι := Set.Iic
  have hnsp : ∀ i, BddAbove (ns i) := fun i => bddAbove_Iic
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atTop_sets, Set.mem_compl_iff, BddAbove, upperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices ∀ i ∈ t, i < c from lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
  · exact fun n => ⟨n, le_rfl⟩

theorem indep_limsup_atTop_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep

theorem condIndep_limsup_atTop_self [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atTop) (limsup s atTop) hm μ :=
  Kernel.indep_limsup_atTop_self h_le h_indep

theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atTop_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s atTop` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atTop
    (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using Kernel.measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep ht_tail

theorem condExp_zero_or_one_of_measurableSet_limsup_atTop [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ] (h_le : ∀ n, s n ≤ m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atTop] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atTop_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

theorem Kernel.indep_limsup_atBot_self (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s κ μα) :
    Indep (limsup s atBot) (limsup s atBot) κ μα := by
  let ns : ι → Set ι := Set.Ici
  have hnsp : ∀ i, BddBelow (ns i) := fun i => bddBelow_Ici
  refine indep_limsup_self h_le h_indep ?_ ?_ hnsp ?_
  · simp only [mem_atBot_sets, Set.mem_compl_iff, BddBelow, lowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine ⟨b, fun c hc hct => ?_⟩
    suffices ∀ i ∈ t, c < i from lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
  · exact Antitone.directed_le fun _ _ ↦ Set.Ici_subset_Ici.2
  · exact fun n => ⟨n, le_rfl⟩

theorem indep_limsup_atBot_self
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep

theorem condIndep_limsup_atBot_self [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ]
    (h_le : ∀ n, s n ≤ m0) (h_indep : iCondIndep m hm s μ) :
    CondIndep m (limsup s atBot) (limsup s atBot) hm μ :=
  Kernel.indep_limsup_atBot_self h_le h_indep

/-- **Kolmogorov's 0-1 law**, kernel version: any event in the tail σ-algebra of an independent
sequence of sub-σ-algebras has probability 0 or 1 almost surely. -/
theorem Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot (h_le : ∀ n, s n ≤ m0)
    (h_indep : iIndep s κ μα) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    ∀ᵐ a ∂μα, κ a t = 0 ∨ κ a t = 1 := by
  apply measure_eq_zero_or_one_of_indepSet_self' ?_
    ((indep_limsup_atBot_self h_le h_indep).indepSet_of_measurableSet ht_tail ht_tail)
  filter_upwards [h_indep.ae_isProbabilityMeasure] with a ha using by infer_instance

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurableSet_limsup_atBot
    (h_le : ∀ n, s n ≤ m0) (h_indep : iIndep s μ) {t : Set Ω}
    (ht_tail : MeasurableSet[limsup s atBot] t) :
    μ t = 0 ∨ μ t = 1 := by
  simpa only [ae_dirac_eq, Filter.eventually_pure]
    using Kernel.measure_zero_or_one_of_measurableSet_limsup_atBot h_le h_indep ht_tail

/-- **Kolmogorov's 0-1 law**, conditional version: any event in the tail σ-algebra of a
conditionally independent sequence of sub-σ-algebras has conditional probability 0 or 1. -/
theorem condExp_zero_or_one_of_measurableSet_limsup_atBot [StandardBorelSpace Ω]
    (hm : m ≤ m0) [IsFiniteMeasure μ] (h_le : ∀ n, s n ≤ m0)
    (h_indep : iCondIndep m hm s μ) {t : Set Ω} (ht_tail : MeasurableSet[limsup s atBot] t) :
    ∀ᵐ ω ∂μ, (μ⟦t | m⟧) ω = 0 ∨ (μ⟦t | m⟧) ω = 1 :=
  condExp_eq_zero_or_one_of_condIndepSet_self hm (limsup_le_iSup.trans (iSup_le h_le) t ht_tail)
    ((condIndep_limsup_atBot_self hm h_le h_indep).condIndepSet_of_measurableSet ht_tail ht_tail)

end AtBot

end ProbabilityTheory
