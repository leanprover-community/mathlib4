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
* `MeasurableEmbedding.noAtoms_map_iff`: having no atoms is invariant under pushforwards along
  measurable embeddings.

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

/-- For an s-finite measure, a singleton of positive measure is contained in an atom of the same
measure, namely its measurable hull. -/
theorem isAtom_toMeasurable_singleton_iff [SFinite μ] {x : α} :
    μ.IsAtom (toMeasurable μ {x}) ↔ 0 < μ {x} := by
  refine ⟨fun h ↦ measure_toMeasurable (μ := μ) {x} ▸ h.pos, fun hx ↦
    ⟨measurableSet_toMeasurable _ _, by rwa [measure_toMeasurable], fun t hty ht ↦ ?_⟩⟩
  rw [← inter_eq_right.2 hty, measure_toMeasurable_inter_of_sfinite ht, measure_toMeasurable]
  by_cases hxt : x ∈ t <;> simp [hxt]

namespace IsAtom

/-- A version of `IsAtom.measure_eq_zero_or_eq'` for subsets `t` which need not be measurable. -/
theorem measure_eq_zero_or_eq (h : μ.IsAtom s) {t : Set α} (hts : t ⊆ s) :
    μ t = 0 ∨ μ t = μ s := by
  obtain ⟨u, -, hus, hu, hut⟩ := exists_measurable_superset_of_subset μ hts h.measurableSet
  exact hut ▸ h.measure_eq_zero_or_eq' u hus hu

/-- A subset of an atom which is not a null set has the same measure as the atom. -/
theorem measure_eq_of_ne_zero (h : μ.IsAtom s) {t : Set α} (hts : t ⊆ s) (ht : μ t ≠ 0) :
    μ t = μ s :=
  (h.measure_eq_zero_or_eq hts).resolve_left ht

/-- A measurable subset of an atom which is not a null set is an atom. -/
theorem of_subset (h : μ.IsAtom s) (hts : t ⊆ s) (ht : MeasurableSet t) (hμt : μ t ≠ 0) :
    μ.IsAtom t := by
  refine ⟨ht, pos_iff_ne_zero.2 hμt, fun u hut hu ↦ ?_⟩
  rw [h.measure_eq_of_ne_zero hts hμt]
  exact h.measure_eq_zero_or_eq' u (hut.trans hts) hu

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

theorem _root_.MeasurableEmbedding.isAtom_map_iff {e : α → β} (he : MeasurableEmbedding e)
    {s : Set β} (hs : MeasurableSet s) : (μ.map e).IsAtom s ↔ μ.IsAtom (e ⁻¹' s) := by
  simp only [isAtom_iff, he.map_apply, hs, he.measurable hs, true_and]
  refine and_congr_right fun _ ↦ ⟨fun h t hts ht ↦ ?_, fun h t hts ht ↦ ?_⟩
  · simpa [he.injective.preimage_image] using
      h (e '' t) (image_subset_iff.2 hts) (he.measurableSet_image.2 ht)
  · exact h (e ⁻¹' t) (preimage_mono hts) (he.measurable ht)

theorem _root_.MeasurableEmbedding.isAtom_preimage {e : α → β} (he : MeasurableEmbedding e)
    {s : Set β} (h : (μ.map e).IsAtom s) : μ.IsAtom (e ⁻¹' s) :=
  (he.isAtom_map_iff h.measurableSet).1 h

theorem _root_.MeasurableEmbedding.isAtom_map_image {e : α → β} (he : MeasurableEmbedding e)
    (h : μ.IsAtom s) : (μ.map e).IsAtom (e '' s) := by
  rwa [he.isAtom_map_iff (he.measurableSet_image.2 h.measurableSet), he.injective.preimage_image]

theorem _root_.MeasurableEquiv.isAtom_map_iff (e : α ≃ᵐ β) {s : Set β} :
    (μ.map e).IsAtom s ↔ μ.IsAtom (e ⁻¹' s) := by
  by_cases hs : MeasurableSet s
  · exact e.measurableEmbedding.isAtom_map_iff hs
  · simp [isAtom_iff, hs]

theorem IsAtom.of_restrict (hs : MeasurableSet s) (h : (μ.restrict s).IsAtom t) :
    μ.IsAtom (t ∩ s) := by
  refine ⟨h.measurableSet.inter hs, restrict_apply h.measurableSet ▸ h.pos, fun u hut hu ↦ ?_⟩
  have := h.measure_eq_zero_or_eq' u (hut.trans inter_subset_left) hu
  rwa [restrict_apply hu, restrict_apply h.measurableSet,
    inter_eq_left.2 (hut.trans inter_subset_right)] at this

theorem IsAtom.restrict_of_inter (h : μ.IsAtom (t ∩ s)) (ht : MeasurableSet t) :
    (μ.restrict s).IsAtom t := by
  refine ⟨ht, (restrict_apply ht).symm ▸ h.pos, fun u hut hu ↦ ?_⟩
  rw [restrict_apply hu, restrict_apply ht]
  exact h.measure_eq_zero_or_eq (inter_subset_inter_left s hut)

theorem IsAtom.restrict (h : μ.IsAtom t) (hts : t ⊆ s) : (μ.restrict s).IsAtom t :=
  IsAtom.restrict_of_inter (by rwa [inter_eq_left.2 hts]) h.measurableSet

theorem isAtom_restrict_iff (hs : MeasurableSet s) :
    (μ.restrict s).IsAtom t ↔ MeasurableSet t ∧ μ.IsAtom (t ∩ s) :=
  ⟨fun h ↦ ⟨h.measurableSet, h.of_restrict hs⟩, fun ⟨ht, h⟩ ↦ h.restrict_of_inter ht⟩

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

/-- The completion of a measure without atoms has no atoms. -/
instance instCompletion : NoAtoms μ.completion :=
  mk' fun _ hs hμs ↦ by
    obtain ⟨t, hts, -, ht⟩ := exists_measurable_subset_lt₀ (μ := μ) hs hμs
    exact ⟨t, hts, ht⟩

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
    ∃ u, NullMeasurableSet u μ ∧ s ⊆ u ∧ u ⊆ t ∧ μ s < μ u ∧ μ u < μ t :=
  exists_measurable_between (μ := μ.completion) hs (MeasurableSet.nullMeasurableSet ht) hst hμst

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
  measure_singleton _ := by_contra fun hx ↦
    not_isAtom _ (isAtom_toMeasurable_singleton_iff.2 (pos_iff_ne_zero.2 hx))

/-- The restriction of a measure without atoms to a null measurable set has no atoms. For
s-finite measures, see the instance `Measure.restrict.instNoAtoms` for arbitrary sets. -/
theorem restrict (hs : NullMeasurableSet s μ) : NoAtoms (μ.restrict s) := by
  obtain ⟨r, -, hr, hrs⟩ := hs.exists_measurable_subset_ae_eq
  rw [← restrict_congr_set hrs]
  exact ⟨fun t ht ↦ not_isAtom _ (ht.of_restrict hr)⟩

end NoAtoms

instance Measure.restrict.instNoAtoms [NoAtoms μ] [SFinite μ] (s : Set α) :
    NoAtoms (μ.restrict s) := by
  rw [← restrict_toMeasurable_of_sfinite]
  exact NoAtoms.restrict (measurableSet_toMeasurable μ s).nullMeasurableSet

theorem _root_.MeasurableEmbedding.noAtoms_map [NoAtoms μ] {e : α → β}
    (he : MeasurableEmbedding e) : NoAtoms (μ.map e) :=
  ⟨fun _ hs ↦ NoAtoms.not_isAtom _ (he.isAtom_preimage hs)⟩

theorem _root_.MeasurableEmbedding.noAtoms_map_iff {e : α → β} (he : MeasurableEmbedding e) :
    NoAtoms (μ.map e) ↔ NoAtoms μ :=
  ⟨fun h ↦ ⟨fun _ hs ↦ h.not_isAtom _ (he.isAtom_map_image hs)⟩, fun _ ↦ he.noAtoms_map⟩

instance _root_.MeasurableEquiv.instNoAtomsMap [NoAtoms μ] (e : α ≃ᵐ β) : NoAtoms (μ.map e) :=
  e.measurableEmbedding.noAtoms_map

end MeasureTheory
