/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

/-!
# Dieudonné measure

Let `α` be a well-ordered type, of uncountable cofinality. We can define a measurable space on `α`,
consisting of sets that either contain or entirely omit an `IsClub` set. On this measurable space,
the indicator function of stationary sets is a zero-one measure with empty support.

In the specific case `α = Iio ω₁`, this is known as the Dieudonné measure. We use this name for the
general case, for lack of a better term.

## Implementation notes

The Dieudonné measurable space and measure on a well-order are scoped to the
`MeasureTheory.Dieudonne` namespace.
-/

@[expose] public section

namespace MeasureTheory.Dieudonne

open Cardinal Order Set

variable {α : Type*} {s : Set α} [LinearOrder α] [WellFoundedLT α] [h₀ : Fact (cof α ≠ ℵ₀)]
include h₀

/-- Measurable sets in Dieudonné space either contain or entirely omit some club set. -/
scoped instance : MeasurableSpace α where
  MeasurableSet' s := ∃ t, IsClub t ∧ (t ⊆ s ∨ t ⊆ sᶜ)
  measurableSet_empty := ⟨_, .univ, by simp⟩
  measurableSet_compl _ := by simp [or_comm]
  measurableSet_iUnion f hf := by
    by_cases! H : ∃ i t, IsClub t ∧ t ⊆ f i
    · obtain ⟨i, t, ht, htf⟩ := H
      exact ⟨t, ht, .inl (htf.trans (subset_iUnion f i))⟩
    choose g hg hgf using hf
    refine ⟨⋂ i, g i, ?_, .inr ?_⟩
    · apply IsClub.iInter_of_countable _ hg
      simpa using h₀.out
    · rw [subset_compl_iff_disjoint_left, disjoint_iUnion_left]
      refine fun i ↦ .mono_right (Set.iInter_subset g i) ?_
      rw [← subset_compl_iff_disjoint_left]
      exact (hgf i).resolve_left <| H _ _ (hg i)

theorem measurableSet_def : MeasurableSet s ↔ ∃ t, IsClub t ∧ (t ⊆ s ∨ t ⊆ sᶜ) :=
  .rfl

theorem measurableSet_of_isClub (hs : IsClub s) : MeasurableSet s :=
  ⟨s, hs, .inl subset_rfl⟩

theorem measurableSet_of_not_isStationary (hs : ¬ IsStationary s) : MeasurableSet s := by
  obtain ⟨t, ht, ht'⟩ := not_isStationary_iff.1 hs
  exact ⟨t, ht, .inr <| ht'.subset_compl_left⟩

theorem measurableSet_of_orderTop [OrderTop α] : MeasurableSet s := by
  use {⊤}
  simp [em]

theorem exists_isClub_subset (hs : IsStationary s) (hs' : MeasurableSet s) : ∃ t ⊆ s, IsClub t := by
  obtain ⟨t, ht, hts | hts⟩ := hs'
  · exact ⟨t, hts, ht⟩
  · rw [subset_compl_iff_disjoint_left, disjoint_iff_inter_eq_empty] at hts
    simpa [hts] using hs ht

instance : MeasurableSingletonClass α where
  measurableSet_singleton x := by
    cases topOrderOrNoTopOrder α with
    | inl =>
      use {⊤}
      simp [eq_comm, em]
    | inr h =>
      rw [noTopOrder_iff_noMaxOrder] at h
      use Ioi x
      simp

open Classical in
/-- The measure on Dieudonné space is defined as the indicator function for stationary sets. -/
noncomputable def measure : Measure α where
  measureOf s := if IsStationary s then 1 else 0
  empty := by simp
  mono {s t} hst := by
    by_cases H : IsStationary s ∧ ¬ IsStationary t
    · cases H.2 <| H.1.mono hst
    · split_ifs <;> simp_all
  iUnion_nat f _ := by
    rw [isStationary_iUnion_iff_of_countable (by simpa using h₀.out)]
    split_ifs with hf
    · obtain ⟨i, hi⟩ := hf
      apply (ENNReal.le_tsum i).trans'
      rw [if_pos hi]
    · rw [ENNReal.tsum_eq_zero.2]
      simpa using hf
  m_iUnion f hf hf' := by
    dsimp
    rw [isStationary_iUnion_iff_of_countable (by simpa using h₀.out)]
    split_ifs with hf
    · obtain ⟨i, hi⟩ := hf
      rw [tsum_eq_single i]
      · simpa
      · refine fun j hji ↦ if_neg fun hj ↦ ?_
        obtain ⟨s, hsi, hs⟩ := exists_isClub_subset hi (hf i)
        obtain ⟨t, htj, ht⟩ := exists_isClub_subset hj (hf j)
        have : Nonempty α := hi.nonempty.to_type
        obtain ⟨a, ha⟩ := (hs.inter h₀.out ht).nonempty
        exact ((hf' hji.symm).inter_eq ▸ notMem_empty a) ⟨hsi ha.1, htj ha.2⟩
    · rw [ENNReal.tsum_eq_zero.2]
      simpa using hf
  trim_le s := by
    rw [OuterMeasure.trim_eq_iInf']
    dsimp
    split_ifs with hs
    · refine iInf_le_of_le ⟨univ, ?_⟩ ?_
      · simp
      · split_ifs <;> simp
    · refine iInf_le_of_le ⟨s, ?_⟩ ?_
      · simpa using measurableSet_of_not_isStationary hs
      · simp [hs]

instance : IsZeroOneMeasure (α := α) measure where
  zero_one₀ s _ := by rw [or_comm]; classical exact ite_eq_or_eq ..

theorem measure_eq_one_iff : measure s = 1 ↔ IsStationary s := by
  classical change ite .. = 1 ↔ _
  simp

theorem measure_eq_zero_iff : measure s = 0 ↔ ¬ IsStationary s := by
  classical change ite .. = 0 ↔ _
  simp

alias ⟨_, measure_of_isStationary⟩ := measure_eq_one_iff
alias ⟨_, measure_of_not_isStationary⟩ := measure_eq_zero_iff

theorem measure_of_isClub [Nonempty α] (hs : IsClub s) : measure s = 1 :=
  measure_of_isStationary (hs.isStationary h₀.out)

theorem measure_of_not_isCofinal (hs : ¬ IsCofinal s) : measure s = 0 :=
  measure_of_not_isStationary (mt IsStationary.isCofinal hs)

instance [Nonempty α] : IsProbabilityMeasure (α := α) measure where
  measure_univ := measure_of_isStationary .univ

theorem measure_eq_dirac [OrderTop α] : measure (α := α) = Measure.dirac ⊤ := by
  ext s
  rw [Measure.dirac_apply]
  by_cases hs : IsStationary s
  · rw [measure_of_isStationary hs, indicator_of_mem]
    · rfl
    · rwa [← isStationary_iff_top_mem]
  · rw [measure_of_not_isStationary hs, indicator_of_notMem]
    rwa [← isStationary_iff_top_mem]

instance [NoMaxOrder α] : NoAtoms (α := α) measure where
  measure_singleton x := measure_of_not_isStationary (by simp)

@[simp]
theorem support_measure [NoMaxOrder α] [TopologicalSpace α] [ClosedIciTopology α] :
    (measure (α := α)).support = ∅ := by
  ext x
  rw [mem_empty_iff_false, iff_false, Measure.mem_support_iff,
    Filter.not_frequently, Filter.eventually_smallSets]
  obtain ⟨y, hy⟩ := exists_gt x
  refine ⟨_, Iio_mem_nhds hy, fun s hs ↦ ?_⟩
  apply ((measure_mono hs).trans _).not_gt
  rw [measure_of_not_isCofinal (not_isCofinal_Iio y)]

end MeasureTheory.Dieudonne
