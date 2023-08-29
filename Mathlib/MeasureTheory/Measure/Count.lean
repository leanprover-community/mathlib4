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

set_option autoImplicit true

open Set
open scoped ENNReal BigOperators Classical

variable [MeasurableSpace α] [MeasurableSpace β] {s : Set α}

noncomputable section

namespace MeasureTheory.Measure

/-- Counting measure on any measurable space. -/
def count : Measure α :=
  sum dirac
#align measure_theory.measure.count MeasureTheory.Measure.count

theorem le_count_apply : ∑' _ : s, (1 : ℝ≥0∞) ≤ count s :=
  calc
    (∑' _ : s, 1 : ℝ≥0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ ≤ ∑' i, dirac i s := (ENNReal.tsum_le_tsum fun _ => le_dirac_apply)
    _ ≤ count s := le_sum_apply _ _
#align measure_theory.measure.le_count_apply MeasureTheory.Measure.le_count_apply

theorem count_apply (hs : MeasurableSet s) : count s = ∑' i : s, 1 := by
  simp only [count, sum_apply, hs, dirac_apply', ← tsum_subtype s (1 : α → ℝ≥0∞), Pi.one_apply]
  -- 🎉 no goals
#align measure_theory.measure.count_apply MeasureTheory.Measure.count_apply

-- @[simp] -- Porting note: simp can prove this
theorem count_empty : count (∅ : Set α) = 0 := by rw [count_apply MeasurableSet.empty, tsum_empty]
                                                  -- 🎉 no goals
#align measure_theory.measure.count_empty MeasureTheory.Measure.count_empty

@[simp]
theorem count_apply_finset' {s : Finset α} (s_mble : MeasurableSet (s : Set α)) :
    count (↑s : Set α) = s.card :=
  calc
    count (↑s : Set α) = ∑' i : (↑s : Set α), 1 := count_apply s_mble
    _ = ∑ i in s, 1 := (s.tsum_subtype 1)
    _ = s.card := by simp
                     -- 🎉 no goals

#align measure_theory.measure.count_apply_finset' MeasureTheory.Measure.count_apply_finset'

@[simp]
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
    count (↑s : Set α) = s.card :=
  count_apply_finset' s.measurableSet
#align measure_theory.measure.count_apply_finset MeasureTheory.Measure.count_apply_finset

theorem count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s) :
    count s = s_fin.toFinset.card := by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]
#align measure_theory.measure.count_apply_finite' MeasureTheory.Measure.count_apply_finite'

theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite) :
    count s = hs.toFinset.card := by rw [← count_apply_finset, Finite.coe_toFinset]
                                     -- 🎉 no goals
#align measure_theory.measure.count_apply_finite MeasureTheory.Measure.count_apply_finite

/-- `count` measure evaluates to infinity at infinite sets. -/
theorem count_apply_infinite (hs : s.Infinite) : count s = ∞ := by
  refine' top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => _)
  -- ⊢ ↑n ≤ ↑↑count s
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  -- ⊢ ↑(Finset.card t) ≤ ↑↑count s
  calc
    (t.card : ℝ≥0∞) = ∑ i in t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ ≤ count (t : Set α) := le_count_apply
    _ ≤ count s := measure_mono ht

#align measure_theory.measure.count_apply_infinite MeasureTheory.Measure.count_apply_infinite

@[simp]
theorem count_apply_eq_top' (s_mble : MeasurableSet s) : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  -- ⊢ ↑↑count s = ⊤ ↔ Set.Infinite s
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
    -- 🎉 no goals
  · change s.Infinite at hs
    -- ⊢ ↑↑count s = ⊤ ↔ Set.Infinite s
    simp [hs, count_apply_infinite]
    -- 🎉 no goals
#align measure_theory.measure.count_apply_eq_top' MeasureTheory.Measure.count_apply_eq_top'

@[simp]
theorem count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  -- ⊢ ↑↑count s = ⊤ ↔ Set.Infinite s
  · exact count_apply_eq_top' hs.measurableSet
    -- 🎉 no goals
  · change s.Infinite at hs
    -- ⊢ ↑↑count s = ⊤ ↔ Set.Infinite s
    simp [hs, count_apply_infinite]
    -- 🎉 no goals
#align measure_theory.measure.count_apply_eq_top MeasureTheory.Measure.count_apply_eq_top

@[simp]
theorem count_apply_lt_top' (s_mble : MeasurableSet s) : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := (not_congr (count_apply_eq_top' s_mble))
    _ ↔ s.Finite := Classical.not_not

#align measure_theory.measure.count_apply_lt_top' MeasureTheory.Measure.count_apply_lt_top'

@[simp]
theorem count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := (not_congr count_apply_eq_top)
    _ ↔ s.Finite := Classical.not_not

#align measure_theory.measure.count_apply_lt_top MeasureTheory.Measure.count_apply_lt_top

theorem empty_of_count_eq_zero' (s_mble : MeasurableSet s) (hsc : count s = 0) : s = ∅ := by
  have hs : s.Finite := by
    rw [← count_apply_lt_top' s_mble, hsc]
    exact WithTop.zero_lt_top
  simpa [count_apply_finite' hs s_mble] using hsc
  -- 🎉 no goals
#align measure_theory.measure.empty_of_count_eq_zero' MeasureTheory.Measure.empty_of_count_eq_zero'

theorem empty_of_count_eq_zero [MeasurableSingletonClass α] (hsc : count s = 0) : s = ∅ := by
  have hs : s.Finite := by
    rw [← count_apply_lt_top, hsc]
    exact WithTop.zero_lt_top
  simpa [count_apply_finite _ hs] using hsc
  -- 🎉 no goals
#align measure_theory.measure.empty_of_count_eq_zero MeasureTheory.Measure.empty_of_count_eq_zero

@[simp]
theorem count_eq_zero_iff' (s_mble : MeasurableSet s) : count s = 0 ↔ s = ∅ :=
  ⟨empty_of_count_eq_zero' s_mble, fun h => h.symm ▸ count_empty⟩
#align measure_theory.measure.count_eq_zero_iff' MeasureTheory.Measure.count_eq_zero_iff'

@[simp]
theorem count_eq_zero_iff [MeasurableSingletonClass α] : count s = 0 ↔ s = ∅ :=
  ⟨empty_of_count_eq_zero, fun h => h.symm ▸ count_empty⟩
#align measure_theory.measure.count_eq_zero_iff MeasureTheory.Measure.count_eq_zero_iff

theorem count_ne_zero' (hs' : s.Nonempty) (s_mble : MeasurableSet s) : count s ≠ 0 := by
  rw [Ne.def, count_eq_zero_iff' s_mble]
  -- ⊢ ¬s = ∅
  exact hs'.ne_empty
  -- 🎉 no goals
#align measure_theory.measure.count_ne_zero' MeasureTheory.Measure.count_ne_zero'

theorem count_ne_zero [MeasurableSingletonClass α] (hs' : s.Nonempty) : count s ≠ 0 := by
  rw [Ne.def, count_eq_zero_iff]
  -- ⊢ ¬s = ∅
  exact hs'.ne_empty
  -- 🎉 no goals
#align measure_theory.measure.count_ne_zero MeasureTheory.Measure.count_ne_zero

@[simp]
theorem count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} : Set α) = 1 := by
  rw [count_apply_finite' (Set.finite_singleton a) ha, Set.Finite.toFinset]
  -- ⊢ ↑(Finset.card (toFinset {a})) = 1
  simp [@toFinset_card _ _ (Set.finite_singleton a).fintype,
    @Fintype.card_unique _ _ (Set.finite_singleton a).fintype]
#align measure_theory.measure.count_singleton' MeasureTheory.Measure.count_singleton'

-- @[simp] -- Porting note: simp can prove this
theorem count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α) = 1 :=
  count_singleton' (measurableSet_singleton a)
#align measure_theory.measure.count_singleton MeasureTheory.Measure.count_singleton

theorem count_injective_image' {f : β → α} (hf : Function.Injective f) {s : Set β}
    (s_mble : MeasurableSet s) (fs_mble : MeasurableSet (f '' s)) : count (f '' s) = count s := by
  by_cases hs : s.Finite
  -- ⊢ ↑↑count (f '' s) = ↑↑count s
  · lift s to Finset β using hs
    -- ⊢ ↑↑count (f '' ↑s) = ↑↑count ↑s
    rw [← Finset.coe_image, count_apply_finset' _, count_apply_finset' s_mble,
      s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
    -- 🎉 no goals
  · rw [count_apply_infinite hs]
    -- ⊢ ↑↑count (f '' s) = ⊤
    rw [← finite_image_iff <| hf.injOn _] at hs
    -- ⊢ ↑↑count (f '' s) = ⊤
    rw [count_apply_infinite hs]
    -- 🎉 no goals
#align measure_theory.measure.count_injective_image' MeasureTheory.Measure.count_injective_image'

theorem count_injective_image [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : β → α}
    (hf : Function.Injective f) (s : Set β) : count (f '' s) = count s := by
  by_cases hs : s.Finite
  -- ⊢ ↑↑count (f '' s) = ↑↑count s
  · exact count_injective_image' hf hs.measurableSet (Finite.image f hs).measurableSet
    -- 🎉 no goals
  rw [count_apply_infinite hs]
  -- ⊢ ↑↑count (f '' s) = ⊤
  rw [← finite_image_iff <| hf.injOn _] at hs
  -- ⊢ ↑↑count (f '' s) = ⊤
  rw [count_apply_infinite hs]
  -- 🎉 no goals
#align measure_theory.measure.count_injective_image MeasureTheory.Measure.count_injective_image

instance count.isFiniteMeasure [Finite α] [MeasurableSpace α] :
    IsFiniteMeasure (Measure.count : Measure α) :=
  ⟨by
    cases nonempty_fintype α
    -- ⊢ ↑↑count univ < ⊤
    simpa [Measure.count_apply, tsum_fintype] using (ENNReal.nat_ne_top _).lt_top⟩
    -- 🎉 no goals
#align measure_theory.measure.count.is_finite_measure MeasureTheory.Measure.count.isFiniteMeasure
