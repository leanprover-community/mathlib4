/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic.AdaptationNote

/-!
# Hitting time

Given a stochastic process, the hitting time provides the first time the process "hits" some
subset of the state space. The hitting time is a stopping time in the case that the time index is
discrete and the process is adapted (this is true in a far more general setting however we have
only proved it for the discrete case so far).

## Main definition

* `MeasureTheory.hitting`: the hitting time of a stochastic process

## Main results

* `MeasureTheory.hitting_isStoppingTime`: a discrete hitting time of an adapted process is a
  stopping time

## Implementation notes

In the definition of the hitting time, we bound the hitting time by an upper and lower bound.
This is to ensure that our result is meaningful in the case we are taking the infimum of an
empty set or the infimum of a set which is unbounded from below. With this, we can talk about
hitting times indexed by the natural numbers or the reals. By taking the bounds to be
`⊤` and `⊥`, we obtain the standard definition in the case that the index is `ℕ∞` or `ℝ≥0∞`.

-/


open Filter Order TopologicalSpace

open scoped MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω β ι : Type*} {m : MeasurableSpace Ω}

open scoped Classical in
/-- Hitting time: given a stochastic process `u` and a set `s`, `hitting u s n m` is the first time
`u` is in `s` after time `n` and before time `m` (if `u` does not hit `s` after time `n` and
before `m` then the hitting time is simply `m`).

The hitting time is a stopping time if the process is adapted and discrete. -/
noncomputable def hitting [Preorder ι] [InfSet ι] (u : ι → Ω → β)
    (s : Set β) (n m : ι) : Ω → ι :=
  fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s
    then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m

open scoped Classical in
theorem hitting_def [Preorder ι] [InfSet ι] (u : ι → Ω → β) (s : Set β) (n m : ι) :
    hitting u s n m =
    fun x => if ∃ j ∈ Set.Icc n m, u j x ∈ s then sInf (Set.Icc n m ∩ {i : ι | u i x ∈ s}) else m :=
  rfl

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} {s : Set β} {n i : ι} {ω : Ω}

/-- This lemma is strictly weaker than `hitting_of_le`. -/
theorem hitting_of_lt {m : ι} (h : m < n) : hitting u s n m ω = m := by
  simp_rw [hitting]
  have h_not : ¬∃ (j : ι) (_ : j ∈ Set.Icc n m), u j ω ∈ s := by
    push_neg
    intro j
    rw [Set.Icc_eq_empty_of_lt h]
    simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff]
  simp only [exists_prop] at h_not
  simp only [h_not, if_false]

theorem hitting_le {m : ι} (ω : Ω) : hitting u s n m ω ≤ m := by
  simp only [hitting]
  split_ifs with h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    change j ∈ {i | u i ω ∈ s} at hj₂
    exact (csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter hj₁ hj₂)).trans hj₁.2
  · exact le_rfl

theorem notMem_of_lt_hitting {m k : ι} (hk₁ : k < hitting u s n m ω) (hk₂ : n ≤ k) :
    u k ω ∉ s := by
  classical
  intro h
  have hexists : ∃ j ∈ Set.Icc n m, u j ω ∈ s := ⟨k, ⟨hk₂, le_trans hk₁.le <| hitting_le _⟩, h⟩
  refine not_le.2 hk₁ ?_
  simp_rw [hitting, if_pos hexists]
  exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hk₂, le_trans hk₁.le <| hitting_le _⟩, h⟩

@[deprecated (since := "2025-05-23")] alias not_mem_of_lt_hitting := notMem_of_lt_hitting

theorem hitting_eq_end_iff {m : ι} : hitting u s n m ω = m ↔
    (∃ j ∈ Set.Icc n m, u j ω ∈ s) → sInf (Set.Icc n m ∩ {i : ι | u i ω ∈ s}) = m := by
  classical
  rw [hitting, ite_eq_right_iff]

theorem hitting_of_le {m : ι} (hmn : m ≤ n) : hitting u s n m ω = m := by
  obtain rfl | h := le_iff_eq_or_lt.1 hmn
  · classical
    rw [hitting, ite_eq_right_iff, forall_exists_index]
    conv => intro; rw [Set.mem_Icc, Set.Icc_self, and_imp, and_imp]
    intro i hi₁ hi₂ hi
    rw [Set.inter_eq_left.2, csInf_singleton]
    exact Set.singleton_subset_iff.2 (le_antisymm hi₂ hi₁ ▸ hi)
  · exact hitting_of_lt h

theorem le_hitting {m : ι} (hnm : n ≤ m) (ω : Ω) : n ≤ hitting u s n m ω := by
  simp only [hitting]
  split_ifs with h
  · refine le_csInf ?_ fun b hb => ?_
    · obtain ⟨k, hk_Icc, hk_s⟩ := h
      exact ⟨k, hk_Icc, hk_s⟩
    · rw [Set.mem_inter_iff] at hb
      exact hb.1.1
  · exact hnm

theorem le_hitting_of_exists {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    n ≤ hitting u s n m ω := by
  refine le_hitting ?_ ω
  by_contra h
  rw [Set.Icc_eq_empty_of_lt (not_le.mp h)] at h_exists
  simp at h_exists

theorem hitting_mem_Icc {m : ι} (hnm : n ≤ m) (ω : Ω) : hitting u s n m ω ∈ Set.Icc n m :=
  ⟨le_hitting hnm ω, hitting_le ω⟩

theorem hitting_mem_set [WellFoundedLT ι] {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    u (hitting u s n m ω) ω ∈ s := by
  simp_rw [hitting, if_pos h_exists]
  have h_nonempty : (Set.Icc n m ∩ {i : ι | u i ω ∈ s}).Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  have h_mem := csInf_mem h_nonempty
  rw [Set.mem_inter_iff] at h_mem
  exact h_mem.2

theorem hitting_mem_set_of_hitting_lt [WellFoundedLT ι] {m : ι} (hl : hitting u s n m ω < m) :
    u (hitting u s n m ω) ω ∈ s := by
  by_cases h : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · exact hitting_mem_set h
  · simp_rw [hitting, if_neg h] at hl
    exact False.elim (hl.ne rfl)

theorem hitting_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) :
    hitting u s n m ω ≤ i := by
  have h_exists : ∃ k ∈ Set.Icc n m, u k ω ∈ s := ⟨i, ⟨hin, him⟩, his⟩
  simp_rw [hitting, if_pos h_exists]
  exact csInf_le (BddBelow.inter_of_left bddBelow_Icc) (Set.mem_inter ⟨hin, him⟩ his)

theorem hitting_le_iff_of_exists [WellFoundedLT ι] {m : ι}
    (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    hitting u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  constructor <;> intro h'
  · exact ⟨hitting u s n m ω, ⟨le_hitting_of_exists h_exists, h'⟩, hitting_mem_set h_exists⟩
  · have h'' : ∃ k ∈ Set.Icc n (min m i), u k ω ∈ s := by
      obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h'
      refine ⟨min k₁ k₂, ⟨le_min hk₁_mem.1 hk₂_mem.1, min_le_min hk₁_mem.2 hk₂_mem.2⟩, ?_⟩
      exact min_rec' (fun j => u j ω ∈ s) hk₁_s hk₂_s
    obtain ⟨k, hk₁, hk₂⟩ := h''
    refine le_trans ?_ (hk₁.2.trans (min_le_right _ _))
    exact hitting_le_of_mem hk₁.1 (hk₁.2.trans (min_le_left _ _)) hk₂

theorem hitting_le_iff_of_lt [WellFoundedLT ι] {m : ι} (i : ι) (hi : i < m) :
    hitting u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  by_cases h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · rw [hitting_le_iff_of_exists h_exists]
  · simp_rw [hitting, if_neg h_exists]
    push_neg at h_exists
    simp only [not_le.mpr hi, Set.mem_Icc, false_iff, not_exists, not_and, and_imp]
    exact fun k hkn hki => h_exists k ⟨hkn, hki.trans hi.le⟩

theorem hitting_lt_iff [WellFoundedLT ι] {m : ι} (i : ι) (hi : i ≤ m) :
    hitting u s n m ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h : ∃ j ∈ Set.Icc n m, u j ω ∈ s := by
      by_contra h
      simp_rw [hitting, if_neg h, ← not_le] at h'
      exact h' hi
    exact ⟨hitting u s n m ω, ⟨le_hitting_of_exists h, h'⟩, hitting_mem_set h⟩
  · obtain ⟨k, hk₁, hk₂⟩ := h'
    refine lt_of_le_of_lt ?_ hk₁.2
    exact hitting_le_of_mem hk₁.1 (hk₁.2.le.trans hi) hk₂

theorem hitting_eq_hitting_of_exists {m₁ m₂ : ι} (h : m₁ ≤ m₂)
    (h' : ∃ j ∈ Set.Icc n m₁, u j ω ∈ s) : hitting u s n m₁ ω = hitting u s n m₂ ω := by
  simp only [hitting, if_pos h']
  obtain ⟨j, hj₁, hj₂⟩ := h'
  rw [if_pos]
  · refine le_antisymm ?_ (csInf_le_csInf bddBelow_Icc.inter_of_left ⟨j, hj₁, hj₂⟩
      (Set.inter_subset_inter_left _ (Set.Icc_subset_Icc_right h)))
    refine le_csInf ⟨j, Set.Icc_subset_Icc_right h hj₁, hj₂⟩ fun i hi => ?_
    by_cases hi' : i ≤ m₁
    · exact csInf_le bddBelow_Icc.inter_of_left ⟨⟨hi.1.1, hi'⟩, hi.2⟩
    · change j ∈ {i | u i ω ∈ s} at hj₂
      exact ((csInf_le bddBelow_Icc.inter_of_left ⟨hj₁, hj₂⟩).trans (hj₁.2.trans le_rfl)).trans
        (le_of_lt (not_le.1 hi'))
  exact ⟨j, ⟨hj₁.1, hj₁.2.trans h⟩, hj₂⟩

theorem hitting_mono {m₁ m₂ : ι} (hm : m₁ ≤ m₂) : hitting u s n m₁ ω ≤ hitting u s n m₂ ω := by
  by_cases h : ∃ j ∈ Set.Icc n m₁, u j ω ∈ s
  · exact (hitting_eq_hitting_of_exists hm h).le
  · simp_rw [hitting, if_neg h]
    split_ifs with h'
    · obtain ⟨j, hj₁, hj₂⟩ := h'
      refine le_csInf ⟨j, hj₁, hj₂⟩ ?_
      by_contra hneg; push_neg at hneg
      obtain ⟨i, hi₁, hi₂⟩ := hneg
      exact h ⟨i, ⟨hi₁.1.1, hi₂.le⟩, hi₁.2⟩
    · exact hm

end Inequalities

/-- A discrete hitting time is a stopping time. -/
theorem hitting_isStoppingTime [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    [Countable ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {f : Filtration ι m} {u : ι → Ω → β} {s : Set β} {n n' : ι} (hu : Adapted f u)
    (hs : MeasurableSet s) : IsStoppingTime f (hitting u s n n') := by
  intro i
  rcases le_or_gt n' i with hi | hi
  · have h_le : ∀ ω, hitting u s n n' ω ≤ i := fun x => (hitting_le x).trans hi
    simp [h_le]
  · have h_set_eq_Union : {ω | hitting u s n n' ω ≤ i} = ⋃ j ∈ Set.Icc n i, u j ⁻¹' s := by
      ext x
      rw [Set.mem_setOf_eq, hitting_le_iff_of_lt _ hi]
      simp only [Set.mem_Icc, exists_prop, Set.mem_iUnion, Set.mem_preimage]
    rw [h_set_eq_Union]
    exact MeasurableSet.iUnion fun j =>
      MeasurableSet.iUnion fun hj => f.mono hj.2 _ ((hu j).measurable hs)

theorem stoppedValue_hitting_mem [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι]
    {u : ι → Ω → β} {s : Set β} {n m : ι} {ω : Ω} (h : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    stoppedValue u (hitting u s n m) ω ∈ s := by
  simp only [stoppedValue, hitting, if_pos h]
  obtain ⟨j, hj₁, hj₂⟩ := h
  have : sInf (Set.Icc n m ∩ {i | u i ω ∈ s}) ∈ Set.Icc n m ∩ {i | u i ω ∈ s} :=
    csInf_mem (Set.nonempty_of_mem ⟨hj₁, hj₂⟩)
  exact this.2

/-- The hitting time of a discrete process with the starting time indexed by a stopping time
is a stopping time. -/
theorem isStoppingTime_hitting_isStoppingTime [ConditionallyCompleteLinearOrder ι]
    [WellFoundedLT ι] [Countable ι] [TopologicalSpace ι] [OrderTopology ι]
    [FirstCountableTopology ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : Filtration ι m} {u : ι → Ω → β} {τ : Ω → ι} (hτ : IsStoppingTime f τ)
    {N : ι} (hτbdd : ∀ x, τ x ≤ N) {s : Set β} (hs : MeasurableSet s) (hf : Adapted f u) :
    IsStoppingTime f fun x => hitting u s (τ x) N x := by
  intro n
  have h₁ : {x | hitting u s (τ x) N x ≤ n} =
    (⋃ i ≤ n, {x | τ x = i} ∩ {x | hitting u s i N x ≤ n}) ∪
      ⋃ i > n, {x | τ x = i} ∩ {x | hitting u s i N x ≤ n} := by
    ext x
    simp [← exists_or, ← or_and_right, le_or_gt]
  have h₂ : ⋃ i > n, {x | τ x = i} ∩ {x | hitting u s i N x ≤ n} = ∅ := by
    ext x
    simp only [gt_iff_lt, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop,
      Set.mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
    rintro m hm rfl
    exact lt_of_lt_of_le hm (le_hitting (hτbdd _) _)
  rw [h₁, h₂, Set.union_empty]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi =>
    (f.mono hi _ (hτ.measurableSet_eq i)).inter (hitting_isStoppingTime hf hs n)

section CompleteLattice

variable [CompleteLattice ι] {u : ι → Ω → β} {s : Set β}

theorem hitting_eq_sInf (ω : Ω) : hitting u s ⊥ ⊤ ω = sInf {i : ι | u i ω ∈ s} := by
  simp only [hitting, Set.mem_Icc, bot_le, le_top, and_self_iff, exists_true_left, Set.Icc_bot,
    Set.Iic_top, Set.univ_inter, ite_eq_left_iff, not_exists]
  intro h_notMem_s
  symm
  rw [sInf_eq_top]
  simp only [Set.mem_univ, true_and] at h_notMem_s
  exact fun i hi_mem_s => absurd hi_mem_s (h_notMem_s i)

end CompleteLattice

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι]
variable {u : ι → Ω → β} {s : Set β}

theorem hitting_bot_le_iff {i n : ι} {ω : Ω} (hx : ∃ j, j ≤ n ∧ u j ω ∈ s) :
    hitting u s ⊥ n ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s := by
  rcases lt_or_ge i n with hi | hi
  · rw [hitting_le_iff_of_lt _ hi]
    simp
  · simp only [(hitting_le ω).trans hi, true_iff]
    obtain ⟨j, hj₁, hj₂⟩ := hx
    exact ⟨j, hj₁.trans hi, hj₂⟩

end ConditionallyCompleteLinearOrderBot

end MeasureTheory
