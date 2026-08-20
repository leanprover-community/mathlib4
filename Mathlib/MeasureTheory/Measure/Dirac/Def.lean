/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Measure.Module

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

@[expose] public section

open Function Set
open scoped ENNReal NNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

namespace MeasureTheory.Measure

/-- The dirac measure. -/
def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)

instance : MeasureSpace PUnit :=
  ⟨dirac PUnit.unit⟩

theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _

@[simp]
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  toMeasure_apply _ _ hs

theorem dirac_apply_eq_zero_or_one :
    dirac a s = 0 ∨ dirac a s = 1 := by
  rw [← measure_toMeasurable s, dirac_apply' a (measurableSet_toMeasurable ..), indicator]
  simp only [Pi.one_apply, ite_eq_right_iff, one_ne_zero, imp_false, ite_eq_left_iff, zero_ne_one,
    not_not]
  tauto

@[simp]
theorem dirac_apply_ne_zero_iff_eq_one :
    dirac a s ≠ 0 ↔ dirac a s = 1 where
  mp := dirac_apply_eq_zero_or_one.resolve_left
  mpr := ne_zero_of_eq_one

@[simp]
theorem dirac_apply_ne_one_iff_eq_zero :
    dirac a s ≠ 1 ↔ dirac a s = 0 where
  mp := dirac_apply_eq_zero_or_one.resolve_right
  mpr h := h ▸ zero_ne_one

@[simp]
theorem dirac_apply_of_mem {a : α} (h : a ∈ s) : dirac a s = 1 := by
  have : ∀ t : Set α, a ∈ t → t.indicator (1 : α → ℝ≥0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine le_antisymm (this univ trivial ▸ ?_) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)

@[simp]
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a ∈ s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_notMem h, ← nonpos_iff_eq_zero]
  calc
    dirac a s ≤ dirac a {a}ᶜ := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurableSet_singleton _).compl]

@[simp] lemma dirac_ne_zero : dirac a ≠ 0 :=
  fun h ↦ by simpa [h] using dirac_apply_of_mem (mem_univ a)

end MeasureTheory.Measure
