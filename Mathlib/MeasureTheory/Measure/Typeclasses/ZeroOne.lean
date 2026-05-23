/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Dirac

/-!

We introduce the typeclass `IsZeroOneMeasure` for measures that only take the values `0` and `1`.

## Main definitions

* `IsZeroOneMeasure`: a measure is a zero-one measure if it only takes the values `0`
  or `1`.

## Main statements

* `exists_eq_dirac`: in a countably separated measurable space, a zero-one measure that is not
  the zero measure is a Dirac measure.

-/

@[expose] public section

open Set

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- A measure is a zero-one measure if it only takes the values `0` or `1`. -/
class IsZeroOneMeasure (μ : Measure α) : Prop where
  zero_one₀ : ∀ ⦃s⦄, MeasurableSet s → μ s = 0 ∨ μ s = 1

lemma Measure.zero_one (μ : Measure α) [IsZeroOneMeasure μ] :
    ∀ s, μ s = 0 ∨ μ s = 1 := by
  intro s
  by_cases hs : MeasurableSet s
  · exact IsZeroOneMeasure.zero_one₀ hs
  · obtain ⟨t, _, mt, ht⟩ := exists_measurable_superset μ s
    rw [← ht]
    exact IsZeroOneMeasure.zero_one₀ mt

variable {μ : Measure α} [IsZeroOneMeasure μ]

instance : IsZeroOrProbabilityMeasure μ where
  measure_univ := μ.zero_one univ

namespace IsZeroOneMeasure

lemma exists_measure_eq_one_iff_measure_univ_eq_one : (∃ s, μ s = 1) ↔ μ univ = 1 := by
  constructor
  · rintro ⟨s, h⟩
    rcases μ.zero_one univ with (h₀ | h₁)
    · have := measure_mono (μ := μ) <| subset_univ s
      rw [h] at this
      simp_all
    · exact h₁
  · intro h
    exact ⟨univ, h⟩

lemma measure_univ {s : Set α} (hμs : μ s = 1) : μ univ = 1 :=
  (exists_measure_eq_one_iff_measure_univ_eq_one).mp ⟨s, hμs⟩

lemma measure_inter_eq_one {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s = 1) (hμt : μ t = 1) : μ (s ∩ t) = 1 := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  rcases μ.zero_one s with (_ | hμs)
    <;> rcases μ.zero_one t with (_ | hμt)
    <;> rcases μ.zero_one (s ∩ t)
  all_goals try simp_all only [zero_le, zero_ne_one]
  suffices μ (s ∩ t)ᶜ ≤ 0 by
    rw [measure_compl (hs.inter ht) (by simp), measure_univ ‹_›] at this
    simp_all
  calc
  _ = μ (sᶜ ∪ tᶜ) := by simp [compl_inter]
  _ ≤ μ sᶜ + μ tᶜ := measure_union_le _ _
  _ ≤ 0 := by
    rw [measure_compl hs (by simp), measure_univ hμs, hμs, tsub_self,
      measure_compl ht (by simp), measure_univ hμt, hμt, tsub_self]
    simp

lemma measure_inter_eq_prod {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ∩ t) = μ s * μ t := by
  have : μ (s ∩ t) ≤ μ s := measure_mono inter_subset_left
  have : μ (s ∩ t) ≤ μ t := measure_mono inter_subset_right
  cases μ.zero_one s <;> cases μ.zero_one t <;> cases μ.zero_one (s ∩ t)
  all_goals try simp_all [measure_inter_eq_one]

lemma measure_singleton_eq_measure_measurableAtom {α : Type*} {mα : MeasurableSpace α}
    (μ : Measure α) (x : α) :
    μ {x} = μ (measurableAtom x) := by
  refine le_antisymm (measure_mono ?_) ?_
  · rintro y rfl
    exact mem_measurableAtom_self y
  · rw [← measure_toMeasurable {x}]
    refine measure_mono ?_
    refine measurableAtom_subset (measurableSet_toMeasurable μ {x}) ?_
    exact subset_toMeasurable _ _ (mem_singleton x)

open MeasurableSpace

-- the atoms in a countably generated measurable space
open Classical in
def todo (α : Type*) [MeasurableSpace α] [CountablyGenerated α] : (ℕ → Prop) → Set α :=
  fun p ↦ ⋂ n, if p n then natGeneratingSequence α n else (natGeneratingSequence α n)ᶜ

lemma measurableSet_todo [CountablyGenerated α] (p : ℕ → Prop) : MeasurableSet (todo α p) := by
  refine MeasurableSet.iInter fun n ↦ ?_
  convert MeasurableSet.ite' (fun _ ↦ measurableSet_natGeneratingSequence n)
    (fun _ ↦ (measurableSet_natGeneratingSequence n).compl)

lemma disjoint_todo [CountablyGenerated α] : Pairwise (Function.onFun Disjoint (todo α)) := by
  intro p q hpq s hsp hsq
  simp only [le_eq_subset, bot_eq_empty, subset_empty_iff] at hsp hsq ⊢
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hxs
  obtain ⟨n, hn⟩ : ∃ n, p n ≠ q n := by grind
  specialize hsp hxs
  specialize hsq hxs
  simp only [todo, mem_iInter] at hsp hsq
  grind

lemma iUnion_todo [CountablyGenerated α] : ⋃ p, todo α p = univ := by
  ext x
  simp only [todo, mem_iUnion, mem_iInter, mem_univ, iff_true]
  exact ⟨fun n ↦ x ∈ natGeneratingSequence α n, fun n ↦ by grind⟩

lemma mem_todo_natGeneratingSequence [CountablyGenerated α] (x : α) :
    x ∈ todo α (x ∈ natGeneratingSequence α ·) := by simp [todo]; grind

open Classical in
lemma exists_eq_iUnion_todo [CountablyGenerated α] {s : Set α} (hs : MeasurableSet s) :
    ∃ (q : (ℕ → Prop) → Prop), s = ⋃ p, if q p then todo α p else ∅ := by
  rw [← generateFrom_natGeneratingSequence α] at hs
  refine generateFrom_induction (range (natGeneratingSequence α)) _ ?_ ?_ ?_ ?_ s hs
  · simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    refine fun n _ ↦ ⟨fun p ↦ p n, ?_⟩
    ext x
    simp only [mem_iUnion, mem_ite_empty_right]
    refine ⟨fun hx ↦ ?_, ?_⟩
    · exact ⟨(x ∈ natGeneratingSequence α ·), by simp [todo]; grind⟩
    · rintro ⟨p, hpn, hpx⟩
      simp only [todo, mem_iInter] at hpx
      specialize hpx n
      simpa [hpn] using hpx
  · exact ⟨fun _ ↦ False, by simp⟩
  · simp only [forall_exists_index]
    intro t ht q htq
    refine ⟨fun p ↦ ¬ q p, ?_⟩
    ext x
    simp only [htq, compl_iUnion, mem_iInter, mem_compl_iff, mem_ite_empty_right, not_and,
      mem_iUnion]
    refine ⟨fun h ↦ ?_, ?_⟩
    · refine ⟨fun n ↦ x ∈ natGeneratingSequence α n, ?_, mem_todo_natGeneratingSequence x⟩
      contrapose! h
      refine ⟨fun n ↦ x ∈ natGeneratingSequence α n, h, mem_todo_natGeneratingSequence x⟩
    · rintro ⟨p, hpq, hpx⟩ p' hqp' hx_mem
      have hpp' : p ≠ p' := by grind
      have h_disj : Disjoint (todo α p) (todo α p') := disjoint_todo hpp'
      grind
  · intro t ht h
    choose q hq using h
    refine ⟨fun p ↦ ⨆ n, q n p, ?_⟩
    ext
    simp [hq]
    grind

lemma measurableAtom_eq_iInter_natGeneratingSequence [CountablyGenerated α] (x : α) :
    measurableAtom x = todo α (x ∈ natGeneratingSequence α ·) := by
  let A := natGeneratingSequence α
  have hA : ∀ n, MeasurableSet (A n) := measurableSet_natGeneratingSequence
  have hA_gen : generateFrom (range A) = mα := generateFrom_natGeneratingSequence α
  change measurableAtom x = todo α (x ∈ A ·)
  refine subset_antisymm (measurableAtom_subset ?_ ?_) ?_
  · exact measurableSet_todo _
  · exact mem_todo_natGeneratingSequence x
  classical
  unfold measurableAtom
  simp only [subset_iInter_iff]
  intro s hxs hs
  obtain ⟨q, hq⟩ : ∃ (q : (ℕ → Prop) → Prop), s = ⋃ p, if q p then todo α p else ∅ :=
    exists_eq_iUnion_todo hs
  suffices q (x ∈ A ·) by
    rw [hq]
    refine subset_trans (le_of_eq ?_) (subset_iUnion _ (x ∈ A ·))
    simp [this]
  simp only [hq, mem_iUnion, mem_ite_empty_right] at hxs
  obtain ⟨p, hpq, hpx⟩ := hxs
  suffices p = (x ∈ A ·) by rwa [← this]
  by_contra! hp
  have h_disj : Disjoint (todo α p) (todo α (x ∈ A ·)) := disjoint_todo hp
  have hx_mem : x ∈ todo α (x ∈ A ·) := mem_todo_natGeneratingSequence x
  grind

lemma measurableSet_measurableAtom [CountablyGenerated α] (x : α) :
    MeasurableSet (measurableAtom x) := by
  rw [measurableAtom_eq_iInter_natGeneratingSequence]
  exact measurableSet_todo _

open MeasurableSpace in
/-- In a countably separated measurable space, a zero-one measure that is not the zero measure is
a Dirac measure. -/
theorem exists_eq_dirac' [CountablyGenerated α] [NeZero μ] :
    ∃ x₀, μ = Measure.dirac x₀ := by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  let A := natGeneratingSequence α
  have hAm : ∀ n, MeasurableSet (A n) := measurableSet_natGeneratingSequence
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n ↦ ?_
    simp only [dite_eq_ite, B]
    convert MeasurableSet.ite' (fun _ ↦ hAm n) (fun _ ↦ (hAm n).compl)
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    have := μ.zero_one (A n)
    split_ifs with h <;> simp_all
  obtain ⟨x₀, hx₀⟩ : (⋂ n, B n).Nonempty := by by_contra! h; simp [h] at hBn
  classical
  have hBA n : B n = if x₀ ∈ A n then A n else (A n)ᶜ := by
    simp only [mem_iInter] at hx₀
    specialize hx₀ n
    revert hx₀
    simp [B]
    grind
  have hB_atom : ⋂ n, B n = measurableAtom x₀ := by
    classical
    rw [measurableAtom_eq_iInter_natGeneratingSequence]
    congr with n x
    rw [hBA n]
  use x₀
  ext s hs
  rw [Measure.dirac_apply' x₀ hs]
  by_cases h : x₀ ∈ s
  · simp only [h, indicator_of_mem, Pi.one_apply]
    refine le_antisymm prob_le_one ?_
    rw [← hBn, hB_atom]
    exact measure_mono (measurableAtom_subset hs h)
  · simp only [h, not_false_eq_true, indicator_of_notMem]
    refine measure_mono_null (t := (⋂ n, B n)ᶜ) ?_ ?_
    · rw [subset_compl_comm, hB_atom]
      exact measurableAtom_subset hs.compl (by grind)
    · rwa [prob_compl_eq_zero_iff mBn]

/-- In a countably separated measurable space, a zero-one measure that is not the zero measure is
a Dirac measure. -/
theorem exists_eq_dirac [MeasurableSpace.CountablySeparated α] [NeZero μ] :
    ∃ x₀, μ = Measure.dirac x₀ := by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n ↦ ?_
    simp only [dite_eq_ite, B]
    convert MeasurableSet.ite' (fun _ ↦ hAm n) (fun _ ↦ (hAm n).compl)
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    have := μ.zero_one (A n)
    split_ifs with h <;> simp_all
  obtain ⟨x₀, hx₀_mem⟩ : (⋂ n, B n).Nonempty := by by_contra! h; simp [h] at hBn
  have hx₀ : ⋂ n, B n = {x₀} := by
    simp_rw [eq_singleton_iff_unique_mem]
    have neBn : (⋂ n, B n).Nonempty := by
      by_contra! h
      rw [h] at hBn
      simp_all
    refine ⟨hx₀_mem, fun y hy ↦ ?_⟩
    refine hAsep y (by trivial) x₀ (by trivial) fun n ↦ ?_
    simp only [dite_eq_ite, mem_iInter, B] at hx₀_mem hy
    specialize hx₀_mem n
    specialize hy n
    constructor
    · intro h
      split_ifs at hy with hμAn
      · simpa [hμAn] using hx₀_mem
      · contradiction
    · intro h
      split_ifs at hx₀_mem with hμAn
      · simpa [hμAn] using hy
      · contradiction
  use x₀
  ext s hs
  rw [Measure.dirac_apply' x₀ hs]
  by_cases h : x₀ ∈ s
  · simp [h]
    have : μ {x₀} ≤ μ s := measure_mono (μ := μ) (by grind)
    rw [← hx₀, hBn] at this
    simp_all
  · simp [h]
    have : μ s ≤ μ {x₀}ᶜ := measure_mono (μ := μ) (by grind)
    rw [← hx₀, measure_compl mBn (by simp), MeasureTheory.measure_univ, hBn] at this
    simp_all

end IsZeroOneMeasure

end MeasureTheory
