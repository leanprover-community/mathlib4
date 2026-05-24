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

section CountablyGeneratedAtom

open MeasurableSpace
variable [CountablyGenerated α]

open Classical in
/-- The atoms in a countably generated measurable space.

Some of those sets may be empty, but the nonempty ones are the atoms of the measurable space.
See `measurableAtom_eq_countablyGeneratedAtom_natGeneratingSequence`. -/
def countablyGeneratedAtom (α : Type*) [MeasurableSpace α] [CountablyGenerated α] :
    (ℕ → Prop) → Set α :=
  fun p ↦ ⋂ n, if p n then natGeneratingSequence α n else (natGeneratingSequence α n)ᶜ

lemma measurableSet_countablyGeneratedAtom (p : ℕ → Prop) :
    MeasurableSet (countablyGeneratedAtom α p) := by
  refine MeasurableSet.iInter fun n ↦ ?_
  convert MeasurableSet.ite' (fun _ ↦ measurableSet_natGeneratingSequence n)
    (fun _ ↦ (measurableSet_natGeneratingSequence n).compl)

lemma disjoint_countablyGeneratedAtom :
    Pairwise (Function.onFun Disjoint (countablyGeneratedAtom α)) := by
  intro p q hpq s hsp hsq
  simp only [le_eq_subset, bot_eq_empty, subset_empty_iff] at hsp hsq ⊢
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hxs
  obtain ⟨n, hn⟩ : ∃ n, p n ≠ q n := by grind
  specialize hsp hxs
  specialize hsq hxs
  simp only [countablyGeneratedAtom, mem_iInter] at hsp hsq
  grind

lemma iUnion_countablyGeneratedAtom : ⋃ p, countablyGeneratedAtom α p = univ := by
  ext x
  simp only [countablyGeneratedAtom, mem_iUnion, mem_iInter, mem_univ, iff_true]
  exact ⟨fun n ↦ x ∈ natGeneratingSequence α n, fun n ↦ by grind⟩

lemma mem_countablyGeneratedAtom_natGeneratingSequence (x : α) :
    x ∈ countablyGeneratedAtom α (x ∈ natGeneratingSequence α ·) := by
  simp [countablyGeneratedAtom]; grind

open Classical in
lemma exists_eq_iUnion_countablyGeneratedAtom {s : Set α} (hs : MeasurableSet s) :
    ∃ (q : (ℕ → Prop) → Prop), s = ⋃ p, if q p then countablyGeneratedAtom α p else ∅ := by
  rw [← generateFrom_natGeneratingSequence α] at hs
  refine generateFrom_induction (range (natGeneratingSequence α)) _ ?_ ?_ ?_ ?_ s hs
  · simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    refine fun n _ ↦ ⟨fun p ↦ p n, ?_⟩
    ext x
    simp only [mem_iUnion, mem_ite_empty_right]
    refine ⟨fun hx ↦ ?_, ?_⟩
    · exact ⟨(x ∈ natGeneratingSequence α ·), by simp [countablyGeneratedAtom]; grind⟩
    · rintro ⟨p, hpn, hpx⟩
      simp only [countablyGeneratedAtom, mem_iInter] at hpx
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
    · refine ⟨fun n ↦ x ∈ natGeneratingSequence α n, ?_,
        mem_countablyGeneratedAtom_natGeneratingSequence x⟩
      contrapose! h
      refine ⟨fun n ↦ x ∈ natGeneratingSequence α n, h,
        mem_countablyGeneratedAtom_natGeneratingSequence x⟩
    · rintro ⟨p, hpq, hpx⟩ p' hqp' hx_mem
      have hpp' : p ≠ p' := by grind
      have h_disj : Disjoint (countablyGeneratedAtom α p) (countablyGeneratedAtom α p') :=
        disjoint_countablyGeneratedAtom hpp'
      grind
  · intro t ht h
    choose q hq using h
    refine ⟨fun p ↦ ⨆ n, q n p, ?_⟩
    ext
    simp [hq]
    grind

lemma measurableAtom_eq_countablyGeneratedAtom_natGeneratingSequence (x : α) :
    measurableAtom x = countablyGeneratedAtom α (x ∈ natGeneratingSequence α ·) := by
  let A := natGeneratingSequence α
  have hA : ∀ n, MeasurableSet (A n) := measurableSet_natGeneratingSequence
  have hA_gen : generateFrom (range A) = mα := generateFrom_natGeneratingSequence α
  change measurableAtom x = countablyGeneratedAtom α (x ∈ A ·)
  refine subset_antisymm (measurableAtom_subset ?_ ?_) ?_
  · exact measurableSet_countablyGeneratedAtom _
  · exact mem_countablyGeneratedAtom_natGeneratingSequence x
  classical
  unfold measurableAtom
  simp only [subset_iInter_iff]
  intro s hxs hs
  obtain ⟨q, hq⟩ : ∃ (q : (ℕ → Prop) → Prop), s =
      ⋃ p, if q p then countablyGeneratedAtom α p else ∅ :=
    exists_eq_iUnion_countablyGeneratedAtom hs
  suffices q (x ∈ A ·) by
    rw [hq]
    refine subset_trans (le_of_eq ?_) (subset_iUnion _ (x ∈ A ·))
    simp [this]
  simp only [hq, mem_iUnion, mem_ite_empty_right] at hxs
  obtain ⟨p, hpq, hpx⟩ := hxs
  suffices p = (x ∈ A ·) by rwa [← this]
  by_contra! hp
  have h_disj : Disjoint (countablyGeneratedAtom α p) (countablyGeneratedAtom α (x ∈ A ·)) :=
    disjoint_countablyGeneratedAtom hp
  have hx_mem : x ∈ countablyGeneratedAtom α (x ∈ A ·) :=
    mem_countablyGeneratedAtom_natGeneratingSequence x
  grind

lemma measurableSet_measurableAtom (x : α) : MeasurableSet (measurableAtom x) := by
  rw [measurableAtom_eq_countablyGeneratedAtom_natGeneratingSequence]
  exact measurableSet_countablyGeneratedAtom _

end CountablyGeneratedAtom

/-- If there is a countable family of sets that generates the atoms of the measurable space, then
a zero-one measure that is not the zero measure is a Dirac measure. -/
lemma exists_eq_dirac_of_measurableAtom_eq_iInter [NeZero μ] [∀ (A : Set α), DecidablePred (· ∈ A)]
    {A : ℕ → Set α} (hA : ∀ n, MeasurableSet (A n))
    (hA_atom : ∀ x, measurableAtom x = ⋂ n, if x ∈ A n then A n else (A n)ᶜ) :
    ∃ x₀, μ = Measure.dirac x₀ := by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n ↦ ?_
    simp only [dite_eq_ite, B]
    convert MeasurableSet.ite' (fun _ ↦ hA n) (fun _ ↦ (hA n).compl)
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    have := μ.zero_one (A n)
    split_ifs with h <;> simp_all
  obtain ⟨x₀, hx₀⟩ : (⋂ n, B n).Nonempty := by by_contra! h; simp [h] at hBn
  have hBA n : B n = if x₀ ∈ A n then A n else (A n)ᶜ := by
    simp only [mem_iInter] at hx₀
    specialize hx₀ n
    revert hx₀
    simp [B]
    grind
  have hB_atom : ⋂ n, B n = measurableAtom x₀ := by simp_rw [hA_atom, hBA]
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

open MeasurableSpace in
/-- In a countably separated measurable space, a zero-one measure that is not the zero measure is
a Dirac measure. -/
theorem exists_eq_dirac' [CountablyGenerated α] [NeZero μ] :
    ∃ x₀, μ = Measure.dirac x₀ := by
  let A := natGeneratingSequence α
  have hAm : ∀ n, MeasurableSet (A n) := measurableSet_natGeneratingSequence
  classical
  refine exists_eq_dirac_of_measurableAtom_eq_iInter hAm fun x ↦ ?_
  exact measurableAtom_eq_countablyGeneratedAtom_natGeneratingSequence x

lemma iInter_seq_separating [MeasurableSpace.CountablySeparated α]
    [∀ (A : Set α), DecidablePred (· ∈ A)] (x : α) :
    let A := (exists_seq_separating (α := α) MeasurableSet.univ univ).choose
    (⋂ n, if x ∈ A n then A n else (A n)ᶜ) = {x} := by
  simp only
  let A := (exists_seq_separating (α := α) MeasurableSet.univ univ).choose
  change (⋂ n, if x ∈ A n then A n else (A n)ᶜ) = {x}
  have hAsep : ∀ x ∈ univ, ∀ y ∈ univ, (∀ n, (x ∈ A n ↔ y ∈ A n)) → x = y :=
    (exists_seq_separating (α := α) MeasurableSet.univ univ).choose_spec.2
  ext y
  simp only [mem_iInter, mem_singleton_iff]
  specialize hAsep x (mem_univ x) y (mem_univ y)
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]; grind⟩
  symm
  refine hAsep fun n ↦ ?_
  specialize h n
  grind

-- todo: is this a dangerous instance?
instance [MeasurableSpace.CountablySeparated α] : MeasurableSingletonClass α := by
  let A := (exists_seq_separating (α := α) MeasurableSet.univ univ).choose
  have hAm : ∀ n, MeasurableSet (A n) :=
    (exists_seq_separating (α := α) MeasurableSet.univ univ).choose_spec.1
  classical
  refine ⟨fun x ↦ ?_⟩
  rw [← iInter_seq_separating x]
  refine MeasurableSet.iInter fun n ↦ ?_
  exact MeasurableSet.ite' (fun _ ↦ hAm n) (fun _ ↦ (hAm n).compl)

/-- In a countably separated measurable space, a zero-one measure that is not the zero measure is
a Dirac measure. -/
theorem exists_eq_dirac [MeasurableSpace.CountablySeparated α] [NeZero μ] :
    ∃ x₀, μ = Measure.dirac x₀ := by
  let A := (exists_seq_separating (α := α) MeasurableSet.univ univ).choose
  have hAm : ∀ n, MeasurableSet (A n) :=
    (exists_seq_separating (α := α) MeasurableSet.univ univ).choose_spec.1
  classical
  refine exists_eq_dirac_of_measurableAtom_eq_iInter hAm fun x ↦ ?_
  rw [measurableAtom_of_measurableSingletonClass, iInter_seq_separating x]

end IsZeroOneMeasure

end MeasureTheory
