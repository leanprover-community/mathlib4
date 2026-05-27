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
* `exists_eq_dirac'`: same result in a countably generated measurable space.

The common property of the two types of spaces in those results is that there exists a
countable family of sets that generates the atoms of the measurable space.

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
    split_ifs <;> simp_all
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

/-- In a countably generated measurable space, a zero-one measure that is not the zero measure is
a Dirac measure. -/
theorem exists_eq_dirac' [MeasurableSpace.CountablyGenerated α] [NeZero μ] :
    ∃ x₀, μ = Measure.dirac x₀ := by
  let A := MeasurableSpace.natGeneratingSequence α
  have hAm : ∀ n, MeasurableSet (A n) := MeasurableSpace.measurableSet_natGeneratingSequence
  classical
  refine exists_eq_dirac_of_measurableAtom_eq_iInter hAm fun x ↦ ?_
  exact MeasurableSpace.measurableAtom_eq_countablyGeneratedAtom_natGeneratingSequence x

/-- In a countably separated measurable space, a zero-one measure that is not the zero measure is
a Dirac measure. -/
theorem exists_eq_dirac [MeasurableSpace.CountablySeparated α] [NeZero μ] :
    ∃ x₀, μ = Measure.dirac x₀ := by
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  classical
  refine exists_eq_dirac_of_measurableAtom_eq_iInter hAm fun x ↦ ?_
  have := MeasurableSpace.measurableSingletonClass_of_countablySeparated (α := α)
  rw [measurableAtom_of_measurableSingletonClass]
  ext y
  simp only [mem_iInter, mem_singleton_iff]
  specialize hAsep x (mem_univ x) y (mem_univ y)
refine ⟨fun h ↦ by simp [h]; grind, fun h ↦ symm <| hAsep fun n ↦ ?_⟩
  grind

end IsZeroOneMeasure

end MeasureTheory
