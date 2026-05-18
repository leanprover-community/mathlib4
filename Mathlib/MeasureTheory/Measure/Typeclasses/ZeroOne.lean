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

* `exists_eq_dirac`: in a standard Borel space, a zero-one measure that is not the zero measure is
  a Dirac measure.

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

/-- In a standard Borel space, a zero-one measure that is not the zero measure is a Dirac
measure. -/
theorem exists_eq_dirac [StandardBorelSpace α] [NeZero μ] : ∃ x₀, μ = Measure.dirac x₀ := by
  have : IsProbabilityMeasure μ := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with (h | h)
    · simp_all
    · exact ⟨h⟩
  obtain ⟨A, hAm, hAsep⟩ := exists_seq_separating (α := α) MeasurableSet.univ univ
  let B := fun n => if h : μ (A n) = 1 then A n else (A n)ᶜ
  have mBn : MeasurableSet (⋂ n, B n) := by
    refine MeasurableSet.iInter fun n ↦ ?_
    simp only [dite_eq_ite, B]
    split_ifs
    · exact hAm n
    · exact (hAm n).compl
  have hBn : μ (⋂ n, B n) = 1 := by
    refine (prob_compl_eq_zero_iff mBn).mp ?_
    simp only [dite_eq_ite, compl_iInter, measure_iUnion_null_iff, B]
    intro n
    split_ifs with h
    · simp_all
    · rw [compl_compl]
      rcases μ.zero_one (A n) with (h₀ | h₁)
      · exact h₀
      · simp_all
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ⋂ n, B n = {x₀} := by
    simp_rw [eq_singleton_iff_unique_mem]
    have neBn : (⋂ n, B n).Nonempty := by
      by_contra! h
      rw [h] at hBn
      simp_all
    refine ⟨neBn.some, neBn.some_mem, fun y hy ↦ ?_⟩
    refine hAsep y (by trivial) neBn.some (by trivial) fun n ↦ ?_
    have hsome := neBn.some_mem
    simp only [dite_eq_ite, mem_iInter, B] at hsome hy
    specialize hsome n
    specialize hy n
    constructor
    · intro h
      split_ifs at hy with hμAn
      · simpa [hμAn] using hsome
      · contradiction
    · intro h
      split_ifs at hsome with hμAn
      · simpa [hμAn] using hy
      · contradiction
  use x₀
  ext s hs
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
