/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Measures without atoms

An *atom* of a measure `μ` is a measurable set `s` of positive measure such that every measurable
subset of `s` has measure either `0` or `μ s`. A measure *has no atoms* if it has no atoms in this
sense, or equivalently if every measurable set `s` with `0 < μ s` contains a measurable subset `t`
with `0 < μ t < μ s`.

## Main definitions

* `MeasureTheory.Measure.IsAtom μ s`: the set `s` is an atom of the measure `μ`.
* `MeasureTheory.NoAtoms μ`: the measure `μ` has no atoms.

## Main statements

* `MeasureTheory.noAtoms_iff_forall_exists`: `μ` has no atoms if and only if every measurable set
  of positive measure contains a measurable subset of strictly smaller positive measure.

## Implementation notes

Under mild assumptions, `NoAtoms μ` implies `NullSingletonClass μ`, but the converse fails in
general: on an uncountable type with the countable-cocountable σ-algebra, the measure which is
`0` on countable sets and `1` on cocountable sets vanishes on singletons, but `univ` is an atom.
-/

public section

namespace MeasureTheory

open Set Measure

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

namespace Measure

/-- An *atom* of a measure `μ` is a measurable set `s` of positive measure for which all
measurable subsets have measure either `0` or `μ s`. -/
@[mk_iff]
structure IsAtom (μ : Measure α) (s : Set α) : Prop where
  measurableSet : MeasurableSet s
  pos : 0 < μ s
  measure_eq_zero_or_eq' : ∀ t ⊆ s, MeasurableSet t → μ t = 0 ∨ μ t = μ s

theorem isAtom_singleton_iff [MeasurableSingletonClass α] {x : α} :
    μ.IsAtom {x} ↔ 0 < μ {x} := by
  refine ⟨IsAtom.pos, fun h ↦ ⟨measurableSet_singleton x, h, fun t hts _ ↦ ?_⟩⟩
  rcases subset_singleton_iff_eq.1 hts with rfl | rfl <;> simp

namespace IsAtom

/-- A version of `IsAtom.measure_eq_zero_or_eq` for subsets `t` which need not be measurable. -/
theorem measure_eq_zero_or_eq (h : μ.IsAtom s) {t : Set α} (hts : t ⊆ s) :
    μ t = 0 ∨ μ t = μ s := by
  obtain ⟨u, -, hus, hu, hut⟩ := exists_measurable_superset_of_subset μ hts h.measurableSet
  exact hut ▸ h.measure_eq_zero_or_eq' u hus hu

theorem not_isAtom_of_exists (h : ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s) : ¬ IsAtom μ s := by
  intro ha
  obtain ⟨t, hts, ht₀, hts'⟩ := h
  exact (ha.measure_eq_zero_or_eq hts).elim ht₀.ne' hts'.ne

theorem not_isAtom_iff_exists (hs : MeasurableSet s) (hμs : 0 < μ s) :
    ¬ IsAtom μ s ↔ ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := by
  refine ⟨fun h ↦ ?_, fun ⟨t, hts, _, ht⟩ ↦ not_isAtom_of_exists ⟨t, hts, ht⟩⟩
  simp only [isAtom_iff, hs, hμs, true_and, not_forall, not_or] at h
  obtain ⟨t, hts, ht, ht₀, hts'⟩ := h
  exact ⟨t, hts, ht, pos_iff_ne_zero.2 ht₀, (measure_mono hts).lt_of_ne hts'⟩

theorem measure_ne_zero (h : μ.IsAtom s) : μ s ≠ 0 :=
  h.pos.ne'

theorem nonempty (h : μ.IsAtom s) : s.Nonempty :=
  nonempty_of_measure_ne_zero h.measure_ne_zero

end IsAtom

end Measure

/-- A measure `μ` *has no atoms* if there is no measurable set `s` of positive measure such that
every measurable subset of `s` has measure `0` or `μ s`. Equivalently (see
`noAtoms_iff_forall_exists`), every measurable set `s` with `0 < μ s` contains a measurable `t`
with `0 < μ t < μ s`. -/
@[mk_iff]
class NoAtoms (μ : Measure α) : Prop where
  not_isAtom : ∀ s, ¬μ.IsAtom s

theorem noAtoms_iff_forall_exists :
    NoAtoms μ ↔
      ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s :=
  ⟨fun h s hs hμs ↦ (IsAtom.not_isAtom_iff_exists hs hμs).1 (h.not_isAtom s),
    fun h ↦ ⟨fun s ha ↦ (IsAtom.not_isAtom_iff_exists ha.measurableSet ha.pos).2
      (h s ha.measurableSet ha.pos) ha⟩⟩

namespace NoAtoms

/-- A constructor for `NoAtoms` in which the subset `t` need not be measurable. -/
theorem mk' (h : ∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s) :
    NoAtoms μ :=
  ⟨fun s ha ↦ IsAtom.not_isAtom_of_exists (h s ha.measurableSet ha.pos) ha⟩

variable [NoAtoms μ]

theorem exists_measurable_subset_lt (hs : MeasurableSet s) (hμs : 0 < μ s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s :=
  noAtoms_iff_forall_exists.1 ‹_› s hs hμs

theorem exists_measurable_subset_lt₀ (hs : NullMeasurableSet s μ) (hμs : 0 < μ s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s := by
  obtain ⟨r, hrs, hr, hrs'⟩ := hs.exists_measurable_subset_ae_eq
  rw [← hrs'.measure_eq] at hμs ⊢
  obtain ⟨t, htr, ht⟩ := exists_measurable_subset_lt hr hμs
  exact ⟨t, htr.trans hrs, ht⟩

end NoAtoms

end MeasureTheory
