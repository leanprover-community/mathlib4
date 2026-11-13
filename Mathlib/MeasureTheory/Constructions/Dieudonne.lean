/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Dieudonné measure

Let `α` be a well-ordered type, of uncountable cofinality. We can define a measurable space on `α`,
consisting of sets that either contain or entirely omit some `IsClub` set. On this measurable space,
the indicator function of stationary sets is a zero-one measure with empty support.

In the specific case `α = Iio ω₁`, this is known as the Dieudonné measure. We use this name for the
general case, for lack of a better term.

## Implementation notes

The Dieudonné measurable space and measure on a well-order are scoped to the
`MeasureTheory.Dieudonne` namespace.
-/

public section

namespace MeasureTheory.Dieudonne

open Cardinal Order Set

variable {α : Type*} {s : Set α} [LinearOrder α] [WellFoundedLT α] [h₀ : Fact (cof α ≠ ℵ₀)]
include h₀

open Ordinal in
scoped instance cof_Iio_omega_one_ne_aleph0 : Fact (cof (Iio ω₁) ≠ ℵ₀) where
  out := by simp

/-- Measurable sets in Dieudonné space either contain or entirely omit some club set. -/
scoped instance : MeasurableSpace α where
  MeasurableSet' s := ∃ t, IsClub t ∧ (t ⊆ s ∨ t ⊆ sᶜ)
  measurableSet_empty := ⟨_, .univ, by simp⟩
  measurableSet_compl _ := by simp [or_comm]
  measurableSet_iUnion f hf := by
    choose g hg hgf using hf
    by_cases! H : ∃ i, g i ⊆ f i
    · obtain ⟨i, hi⟩ := H
      exact ⟨g i, hg i, .inl (hi.trans (subset_iUnion f i))⟩
    refine ⟨⋂ i, g i, .iInter_of_countable h₀.out hg, .inr ?_⟩
    simp_rw [compl_iUnion, subset_iInter_iff]
    exact fun i ↦ (iInter_subset g i).trans <| (hgf i).resolve_left (H i)

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
    by_cases hx : IsMax x
    · exact measurableSet_of_isClub hx.isClub_singleton
    · exact measurableSet_of_not_isStationary (mt isStationary_singleton_iff.1 hx)

open Classical in
/-- The measure on Dieudonné space is defined as the indicator function for stationary sets. -/
noncomputable def measure : Measure α where
  measureOf s := if IsStationary s then 1 else 0
  empty := by simp
  mono {s t} hst := by grind [IsStationary.mono, zero_le]
  iUnion_nat f _ := by
    rw [isStationary_iUnion_iff_of_countable (by simpa using h₀.out)]
    split_ifs with hf
    · obtain ⟨i, hi⟩ := hf
      apply (le_tsum _ i).trans'
      rw [ite_eq_left hi]
    · rw [tsum_eq_zero_iff.2]
      simpa using hf
  m_iUnion f hf hf' := by
    dsimp
    rw [isStationary_iUnion_iff_of_countable h₀.out]
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      obtain ⟨s, hsi, hs⟩ := exists_isClub_subset hi (hf i)
      rw [tsum_eq_single i fun j hji ↦ ite_eq_right fun hj ↦ ?_, ite_eq_left hi]
      obtain ⟨a, haj, has⟩ := hj hs
      exact disjoint_left.1 (hf' hji) haj (hsi has)
    · simp_all
  trim_le s := by
    rw [OuterMeasure.trim_eq_iInf']
    by_cases hs : IsStationary s
    · exact iInf_le_of_le ⟨univ, subset_univ s, .univ⟩ (by dsimp; split_ifs <;> simp)
    · exact iInf_le_of_le ⟨s, subset_rfl, measurableSet_of_not_isStationary hs⟩ le_rfl

instance : IsZeroOneMeasure (α := α) measure where
  zero_one₀ s _ := by rw [or_comm]; classical exact ite_eq_or_eq ..

theorem measure_eq_one_iff : measure s = 1 ↔ IsStationary s := by
  classical change ite .. = 1 ↔ _
  simp

theorem measure_eq_zero_iff : measure s = 0 ↔ ¬ IsStationary s := by
  classical change ite .. = 0 ↔ _
  simp

theorem measure_ne_one_iff : measure s ≠ 1 ↔ ¬ IsStationary s := by
  rw [← measure_eq_one_iff]

theorem measure_ne_zero_iff : measure s ≠ 0 ↔ IsStationary s := by
  rw [ne_eq, measure_eq_zero_iff, not_not]

alias ⟨_, measure_of_isStationary⟩ := measure_eq_one_iff
alias ⟨_, measure_of_not_isStationary⟩ := measure_eq_zero_iff

instance [Nonempty α] : NeZero (measure (α := α)) where
  out := by
    rw [← Measure.measure_univ_ne_zero, measure_ne_zero_iff]
    exact .univ

theorem measure_of_isClub [Nonempty α] (hs : IsClub s) : measure s = 1 :=
  measure_of_isStationary (hs.isStationary h₀.out)

theorem measure_of_not_isCofinal (hs : ¬ IsCofinal s) : measure s = 0 :=
  measure_of_not_isStationary (mt IsStationary.isCofinal hs)

@[simp]
theorem measure_eq_dirac [OrderTop α] : measure (α := α) = Measure.dirac ⊤ := by
  ext s
  classical
  rw [Measure.dirac_apply, indicator_apply, ← isStationary_iff_top_mem]
  split_ifs with hs
  exacts [measure_of_isStationary hs, measure_of_not_isStationary hs]

instance [NoMaxOrder α] : NullSingletonClass (α := α) measure where
  measure_singleton x := measure_of_not_isStationary (by simp)

@[simp]
theorem support_measure [NoMaxOrder α] [TopologicalSpace α] [ClosedIciTopology α] :
    (measure (α := α)).support = ∅ := by
  simp_rw [eq_empty_iff_forall_notMem, Measure.mem_support_iff,
    Filter.not_frequently, Filter.eventually_smallSets, not_lt]
  intro x
  obtain ⟨y, hy⟩ := exists_gt x
  refine ⟨_, Iio_mem_nhds hy, fun s hs ↦ ?_⟩
  grw [hs, measure_of_not_isCofinal (not_isCofinal_Iio y)]

end MeasureTheory.Dieudonne
