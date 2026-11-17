/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

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
* `MeasureTheory.NoAtoms.instNullSingletonClass`,
  `MeasureTheory.NoAtoms.instNullSingletonClass_of_sfinite`: a measure without atoms vanishes on
  singletons, provided singletons are null measurable or the measure is s-finite.
* `MeasureTheory.Measure.restrict.instNoAtoms`: restrictions of s-finite measures without atoms
  have no atoms.
* `MeasurableEquiv.noAtoms_map_iff`: having no atoms is invariant under measurable equivalences.

## Implementation notes

Under mild assumptions, `NoAtoms μ` implies `NullSingletonClass μ`, but the converse fails in
general: on an uncountable type with the countable-cocountable σ-algebra, the measure which is
`0` on countable sets and `1` on cocountable sets vanishes on singletons, but `univ` is an atom.
-/

public section

namespace MeasureTheory

open Set Measure

variable {α β : Type*} {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {s t : Set α}

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

/-- A version of `IsAtom.measure_eq_zero_or_eq'` for subsets `t` which need not be measurable. -/
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

theorem _root_.MeasurableEquiv.isAtom_map_iff (e : α ≃ᵐ β) {s : Set β} :
    (μ.map e).IsAtom s ↔ μ.IsAtom (e ⁻¹' s) := by
  simp only [isAtom_iff, e.map_apply, e.measurableSet_preimage]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun h t hts ht ↦ ?_, fun h t hts ht ↦ ?_⟩
  · simpa [e.preimage_image] using h (e '' t) (image_subset_iff.2 hts) (e.measurableSet_image.2 ht)
  · exact h (e ⁻¹' t) (preimage_mono hts) (e.measurableSet_preimage.2 ht)

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

theorem exists_measurable_between (hs : MeasurableSet s) (ht : NullMeasurableSet t μ)
    (hst : s ⊆ t) (hμst : μ s < μ t) :
    ∃ u, MeasurableSet u ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t := by
  have h := measure_sdiff hst hs.nullMeasurableSet hμst.ne_top
  obtain ⟨v, hv, hv_meas, hv_pos, hv_lt⟩ :=
    exists_measurable_subset_lt₀ (ht.diff hs.nullMeasurableSet) (h ▸ tsub_pos_of_lt hμst)
  have hsv : Disjoint s v := disjoint_of_subset_right hv disjoint_sdiff_right
  refine ⟨s ∪ v, hs.union hv_meas, subset_union_left, union_subset hst (hv.trans sdiff_subset),
    ?_, ?_⟩ <;> rw [measure_union hsv hv_meas]
  · exact ENNReal.lt_add_right hμst.ne_top hv_pos.ne'
  · exact lt_tsub_iff_left.1 (h ▸ hv_lt)

theorem exists_nullMeasurable_between (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (hst : s ⊆ t) (hμst : μ s < μ t) :
    ∃ u, NullMeasurableSet u μ ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t := by
  obtain ⟨r, hrs, hr, hrs'⟩ := hs.exists_measurable_subset_ae_eq
  rw [← hrs'.measure_eq] at hμst ⊢
  obtain ⟨u, hu, hru, hut, hru', hut'⟩ := exists_measurable_between hr ht (hrs.trans hst) hμst
  have : μ (u ∪ s) = μ u := by
    rw [measure_congr (ae_eq_set_union Filter.EventuallyEqSet.rfl hrs'.symm), union_eq_left.2 hru]
  exact ⟨u ∪ s, hu.nullMeasurableSet.union hs, subset_union_right, union_subset hut hst,
    this ▸ hru', this ▸ hut'⟩

/- The assumptions `MeasurableSingletonClass (NullMeasurableSpace α μ)` resp. `SFinite μ` in
the following two instances cannot both be dropped.
Sketch of such a counterexample: let `Ω` be uncountable, `ω₀ ∈ Ω`, `X := Ω × [0, 1]`, and call
`B ⊆ X` measurable if all sections `B_ω` are Borel, `B_ω₀ = ∅` or `B_ω₀ = [0, 1]`, and
`B_ω = B_ω₀` for all but countably many `ω`. This is a σ-algebra; put `μ B := ∑ ω, volume B_ω`.
* `μ` has no atoms: let `B` be measurable with `μ B > 0`. If `B_ω₀ = ∅`, then `B` is the countable
  union of the `{ω} × B_ω` with `ω ≠ ω₀`, so `volume B_ω > 0` for some `ω ≠ ω₀`. As `volume` has no
  atoms, there is a Borel `A ⊆ B_ω` with `0 < volume A < volume B_ω`, and `t := {ω} × A ⊆ B` is
  measurable with `0 < μ t < volume B_ω ≤ μ B` (whether or not `μ B` is finite). If
  `B_ω₀ = [0, 1]`, then `μ B = ∞` and `B` contains some `{ω} × [0, 1]` of measure `1`.
* For `x := (ω₀, 0)`, every measurable `B ∋ x` contains `{ω} × [0, 1]` for all but countably
  many `ω`, so `μ {x} = ∞`.
-/

/-- A measure without atoms vanishes on singletons if singletons are null measurable. See also
`instNullSingletonClass_of_sfinite`. -/
instance instNullSingletonClass [MeasurableSingletonClass (NullMeasurableSpace α μ)] :
    NullSingletonClass μ where
  measure_singleton x := by
    by_contra! hx
    obtain ⟨t, htx, -, ht, ht'⟩ :=
      exists_measurable_subset_lt₀ (nullMeasurableSet_singleton x) (pos_iff_ne_zero.2 hx)
    rcases subset_singleton_iff_eq.1 htx with rfl | rfl <;> simp_all

/-- An s-finite measure without atoms vanishes on singletons. See also `instNullSingletonClass`. -/
instance instNullSingletonClass_of_sfinite [SFinite μ] : NullSingletonClass μ where
  measure_singleton x := by
    by_contra! hx
    refine not_isAtom (μ := μ) (toMeasurable μ {x}) ⟨measurableSet_toMeasurable _ _,
      by rwa [measure_toMeasurable, pos_iff_ne_zero], fun t hty ht ↦ ?_⟩
    rw [← inter_eq_right.2 hty, measure_toMeasurable_inter_of_sfinite ht, measure_toMeasurable]
    by_cases hxt : x ∈ t <;> simp [hxt]

/-- The restriction of a measure without atoms to a null measurable set has no atoms. For
s-finite measures, see the instance `Measure.restrict.instNoAtoms` for arbitrary sets. -/
theorem restrict (hs : NullMeasurableSet s μ) : NoAtoms (μ.restrict s) := by
  refine mk' fun t ht hμt ↦ ?_
  rw [restrict_apply ht] at hμt
  obtain ⟨r, hrts, -, hr₀, hrts'⟩ :=
    exists_measurable_subset_lt₀ (ht.nullMeasurableSet.inter hs) hμt
  refine ⟨r, hrts.trans inter_subset_left, ?_⟩
  rw [restrict_apply ht, restrict_apply₀' hs, inter_eq_left.2 (hrts.trans inter_subset_right)]
  exact ⟨hr₀, hrts'⟩

end NoAtoms

instance Measure.restrict.instNoAtoms [NoAtoms μ] [SFinite μ] (s : Set α) :
    NoAtoms (μ.restrict s) := by
  rw [← restrict_toMeasurable_of_sfinite]
  exact NoAtoms.restrict (measurableSet_toMeasurable μ s).nullMeasurableSet

instance _root_.MeasurableEquiv.instNoAtomsMap [NoAtoms μ] (e : α ≃ᵐ β) : NoAtoms (μ.map e) :=
  ⟨fun _ hs ↦ NoAtoms.not_isAtom _ (e.isAtom_map_iff.1 hs)⟩

theorem _root_.MeasurableEquiv.noAtoms_map_iff (e : α ≃ᵐ β) : NoAtoms (μ.map e) ↔ NoAtoms μ :=
  ⟨fun _ ↦ e.map_symm_map (μ := μ) ▸ inferInstance, fun _ ↦ inferInstance⟩

end MeasureTheory
