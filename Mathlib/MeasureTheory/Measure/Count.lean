/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Counting measure

In this file we define the counting measure `MeasurTheory.Measure.count`
as `MeasureTheory.Measure.sum MeasureTheory.Measure.dirac`
and prove basic properties of this measure.
-/

open Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α}

noncomputable section

namespace MeasureTheory.Measure

/-- Counting measure on any measurable space. -/
def count : Measure α :=
  sum dirac

@[simp] lemma count_ne_zero'' [Nonempty α] : (count : Measure α) ≠ 0 := by simp [count]

theorem le_count_apply : ∑' _ : s, (1 : ℝ≥0∞) ≤ count s :=
  calc
    (∑' _ : s, 1 : ℝ≥0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ ≤ ∑' i, dirac i s := ENNReal.tsum_le_tsum fun _ => le_dirac_apply
    _ ≤ count s := le_sum_apply _ _

theorem count_apply (hs : MeasurableSet s) : count s = ∑' i : s, 1 := by
  simp only [count, sum_apply, hs, dirac_apply', ← tsum_subtype s (1 : α → ℝ≥0∞), Pi.one_apply]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem count_empty : count (∅ : Set α) = 0 := by rw [count_apply MeasurableSet.empty, tsum_empty]

@[simp]
theorem count_apply_finset' {s : Finset α} (s_mble : MeasurableSet (s : Set α)) :
    count (↑s : Set α) = s.card :=
  calc
    count (↑s : Set α) = ∑' i : (↑s : Set α), 1 := count_apply s_mble
    _ = ∑ i ∈ s, 1 := s.tsum_subtype 1
    _ = s.card := by simp

@[simp]
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
    count (↑s : Set α) = s.card :=
  count_apply_finset' s.measurableSet

theorem count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s) :
    count s = s_fin.toFinset.card := by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]

theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite) :
    count s = hs.toFinset.card := by rw [← count_apply_finset, Finite.coe_toFinset]

/-- `count` measure evaluates to infinity at infinite sets. -/
theorem count_apply_infinite (hs : s.Infinite) : count s = ∞ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (t.card : ℝ≥0∞) = ∑ i ∈ t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ ≤ count (t : Set α) := le_count_apply
    _ ≤ count s := measure_mono ht

@[simp]
theorem count_apply_eq_top' (s_mble : MeasurableSet s) : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]
theorem count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  · exact count_apply_eq_top' hs.measurableSet
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]
theorem count_apply_lt_top' (s_mble : MeasurableSet s) : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr (count_apply_eq_top' s_mble)
    _ ↔ s.Finite := Classical.not_not

@[simp]
theorem count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr count_apply_eq_top
    _ ↔ s.Finite := Classical.not_not

theorem empty_of_count_eq_zero' (s_mble : MeasurableSet s) (hsc : count s = 0) : s = ∅ := by
  have hs : s.Finite := by
    rw [← count_apply_lt_top' s_mble, hsc]
    exact WithTop.zero_lt_top
  simpa [count_apply_finite' hs s_mble] using hsc

theorem empty_of_count_eq_zero [MeasurableSingletonClass α] (hsc : count s = 0) : s = ∅ := by
  have hs : s.Finite := by
    rw [← count_apply_lt_top, hsc]
    exact WithTop.zero_lt_top
  simpa [count_apply_finite _ hs] using hsc

@[simp]
theorem count_eq_zero_iff' (s_mble : MeasurableSet s) : count s = 0 ↔ s = ∅ :=
  ⟨empty_of_count_eq_zero' s_mble, fun h => h.symm ▸ count_empty⟩

@[simp]
theorem count_eq_zero_iff [MeasurableSingletonClass α] : count s = 0 ↔ s = ∅ :=
  ⟨empty_of_count_eq_zero, fun h => h.symm ▸ count_empty⟩

theorem count_ne_zero' (hs' : s.Nonempty) (s_mble : MeasurableSet s) : count s ≠ 0 := by
  rw [Ne, count_eq_zero_iff' s_mble]
  exact hs'.ne_empty

theorem count_ne_zero [MeasurableSingletonClass α] (hs' : s.Nonempty) : count s ≠ 0 := by
  rw [Ne, count_eq_zero_iff]
  exact hs'.ne_empty

@[simp]
theorem count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} : Set α) = 1 := by
  rw [count_apply_finite' (Set.finite_singleton a) ha, Set.Finite.toFinset]
  simp [@toFinset_card _ _ (Set.finite_singleton a).fintype,
    @Fintype.card_unique _ _ (Set.finite_singleton a).fintype]

-- @[simp] -- Porting note (#10618): simp can prove this
theorem count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α) = 1 :=
  count_singleton' (measurableSet_singleton a)

theorem count_injective_image' {f : β → α} (hf : Function.Injective f) {s : Set β}
    (s_mble : MeasurableSet s) (fs_mble : MeasurableSet (f '' s)) : count (f '' s) = count s := by
  classical
  by_cases hs : s.Finite
  · lift s to Finset β using hs
    rw [← Finset.coe_image, count_apply_finset' _, count_apply_finset' s_mble,
      s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
  · rw [count_apply_infinite hs]
    rw [← finite_image_iff hf.injOn] at hs
    rw [count_apply_infinite hs]

theorem count_injective_image [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : β → α}
    (hf : Function.Injective f) (s : Set β) : count (f '' s) = count s := by
  by_cases hs : s.Finite
  · exact count_injective_image' hf hs.measurableSet (Finite.image f hs).measurableSet
  rw [count_apply_infinite hs]
  rw [← finite_image_iff hf.injOn] at hs
  rw [count_apply_infinite hs]

instance count.isFiniteMeasure [Finite α] :
    IsFiniteMeasure (Measure.count : Measure α) :=
  ⟨by cases nonempty_fintype α; simp [Measure.count_apply, tsum_fintype]⟩

@[simp] lemma count_univ [Fintype α] : count (univ : Set α) = Fintype.card α := by
  rw [count_apply .univ]; exact (tsum_univ 1).trans (by simp [tsum_fintype])

end Measure

end MeasureTheory
