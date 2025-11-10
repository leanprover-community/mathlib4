/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Counting measure

In this file we define the counting measure `MeasureTheory.Measure.count`
as `MeasureTheory.Measure.sum MeasureTheory.Measure.dirac`
and prove basic properties of this measure.
-/

open Set
open scoped ENNReal Finset

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

theorem count_apply (hs : MeasurableSet s) : count s = s.encard := by
  simp [count, hs, ← tsum_subtype]

@[simp]
theorem count_apply_finset' {s : Finset α} (hs : MeasurableSet (s : Set α)) :
    count (↑s : Set α) = #s := by simp [count_apply hs]

@[simp]
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
    count (↑s : Set α) = #s :=
  count_apply_finset' s.measurableSet

theorem count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s) :
    count s = #s_fin.toFinset := by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]

theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite) :
    count s = #hs.toFinset := by rw [← count_apply_finset, Finite.coe_toFinset]

/-- `count` measure evaluates to infinity at infinite sets. -/
theorem count_apply_infinite (hs : s.Infinite) : count s = ∞ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (#t : ℝ≥0∞) = ∑ i ∈ t, 1 := by simp
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

@[simp]
theorem count_eq_zero_iff : count s = 0 ↔ s = ∅ where
  mp h := eq_empty_of_forall_notMem fun x hx ↦ by
    simpa [hx] using ((ENNReal.le_tsum x).trans <| le_sum_apply _ _).trans_eq h
  mpr := by rintro rfl; exact measure_empty

lemma count_ne_zero_iff : count s ≠ 0 ↔ s.Nonempty :=
  count_eq_zero_iff.not.trans nonempty_iff_ne_empty.symm

alias ⟨_, count_ne_zero⟩ := count_ne_zero_iff

@[simp]
lemma ae_count_iff {p : α → Prop} : (∀ᵐ x ∂count, p x) ↔ ∀ x, p x := by
  refine ⟨fun h x ↦ ?_, ae_of_all _⟩
  rw [ae_iff, count_eq_zero_iff] at h
  by_contra hx
  rwa [← mem_empty_iff_false x, ← h]

@[simp]
theorem count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} : Set α) = 1 := by
  rw [count_apply_finite' (Set.finite_singleton a) ha, Set.Finite.toFinset]
  simp [
    ]

theorem count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α) = 1 :=
  count_singleton' (measurableSet_singleton a)

@[simp]
theorem _root_.MeasureTheory.count_real_singleton'
    {a : α} (ha : MeasurableSet ({a} : Set α)) :
    count.real ({a} : Set α) = 1 := by
  rw [measureReal_def, count_singleton' ha, ENNReal.toReal_one]

theorem _root_.MeasureTheory.count_real_singleton [MeasurableSingletonClass α] (a : α) :
    count.real ({a} : Set α) = 1 :=
  count_real_singleton' (measurableSet_singleton a)

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

instance count.instSigmaFinite [MeasurableSingletonClass α] [Countable α] :
    SigmaFinite (count : Measure α) := by simp [sigmaFinite_iff_measure_singleton_lt_top]

instance count.isFiniteMeasure [Finite α] :
    IsFiniteMeasure (Measure.count : Measure α) :=
  ⟨by simp [Measure.count_apply]⟩

@[simp]
lemma count_univ : count (univ : Set α) = ENat.card α := by simp [count_apply .univ, encard_univ]

end Measure

end MeasureTheory
