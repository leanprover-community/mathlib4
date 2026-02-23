/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Trim

/-!
# Classes for semifinite measures

We introduce the following typeclass for measures:

* `SemiFinite μ`: any measurable set with positive measure has a subset with
  finite positive measure.

-/

@[expose] public section

namespace MeasureTheory

open MeasureTheory Set

variable {α : Type*} {m mα : MeasurableSpace α} {μ : Measure α}

/-- A measure is called semifinite if any measurable set with positive measure has a subset with
finite positive measure. -/
class SemiFinite (μ : Measure α) : Prop where
  exists_lt_top ⦃s : Set α⦄ (hms : MeasurableSet s) (hs : 0 < μ s) : ∃ t, t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤

/-- It is sufficient to prove that the condition holds for any sets of infinite measure. -/
theorem SemiFinite.iff_finite :
    SemiFinite μ ↔ ∀ s, MeasurableSet s → μ s = ⊤ → ∃ t, t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤ where
  mp h s hms hs := h.exists_lt_top hms (by simp [hs])
  mpr h := by
    constructor
    intro s hms hs
    by_cases! hμs : μ s = ⊤
    · exact h s hms hμs
    · exact ⟨s, refl s, hs, by simp [lt_top_iff_ne_top, hμs]⟩

/-- A measure is semifinite iff any null measurable set with positive measure has a subset with
finite positive measure. -/
theorem Semifinite.iff_nullMeasurable :
    SemiFinite μ ↔ ∀ s, NullMeasurableSet s μ → 0 < μ s → ∃ t, t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤ where
  mp h s hms hs := by
    obtain ⟨t, ht⟩ := h.exists_lt_top (measurableSet_toMeasurable μ s) (by simp [hs])
    have : μ (t ∩ s) = μ t :=
      measure_inter_conull' (μ.mono_null (by grind) (ae_eq_set.1 hms.toMeasurable_ae_eq).1)
    exact ⟨t ∩ s, inter_subset_right, this ▸ ht.2⟩
  mpr h := by
    constructor
    exact fun s hs hs' => h s hs.nullMeasurableSet hs'

/-- A measure is semifinite iff any measurable set with positive measure has a measurable subset
with finite positive measure. -/
theorem SemiFinite.iff :
    SemiFinite μ ↔ ∀ s, MeasurableSet s → 0 < μ s →
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < ⊤ where
  mp h s hms hs := by
    obtain ⟨t, ht⟩ := h.exists_lt_top hms hs
    refine ⟨s ∩ toMeasurable μ t, hms.inter ?_, inter_subset_left, ?_, ?_⟩
    · exact measurableSet_toMeasurable μ t
    · exact ht.2.1.trans_le (measure_mono (subset_inter ht.1 (subset_toMeasurable μ t)))
    · exact ((measure_toMeasurable t) ▸ ht.2.2).trans_le' (measure_mono inter_subset_right)
  mpr h := by
    constructor
    intro s hms hs
    obtain ⟨t, ht⟩ := h s hms hs
    exact ⟨t, ht.2⟩

instance [SigmaFinite μ] : SemiFinite μ where
  exists_lt_top s _ hs := by
    obtain ⟨n, hn⟩ := (μ.exists_measure_inter_spanningSets_pos s).2 hs
    refine ⟨s ∩ spanningSets μ n, inter_subset_left, hn, ?_⟩
    exact (measure_spanningSets_lt_top μ n).trans_le' (measure_mono inter_subset_right)

instance {s : Set α} (hms : MeasurableSet s) [SemiFinite μ] : SemiFinite (μ.restrict s) where
  exists_lt_top t ht ht' := by
    have : 0 < μ (s ∩ t) := by rw [inter_comm, ← μ.restrict_apply ht]; exact ht'
    obtain ⟨a, ha⟩ := SemiFinite.exists_lt_top (μ := μ) (hms.inter ht) this
    have : μ.restrict s a = μ a := by
      rw [μ.restrict_apply' hms, inter_eq_self_of_subset_left (ha.1.trans inter_subset_left)]
    exact ⟨a, ha.1.trans inter_subset_right, this ▸ ha.2⟩

/-- Let `s` be a measurable set such that its intersection with any set of finite measure is null.
Then `s` is null. -/
theorem measure_eq_zero_of_measure_inter_finite_eq_zero [h : SemiFinite μ]
    {s : Set α} (hms : MeasurableSet s) (hs : ∀ t, MeasurableSet t → μ t < ⊤ → μ (s ∩ t) = 0) :
    μ s = 0 := by
  by_contra! hne
  obtain ⟨t, ht⟩ := SemiFinite.iff.1 h s hms (by positivity)
  have := Set.inter_eq_self_of_subset_right ht.2.1 ▸ hs t ht.1
  grind

/-- If a proposition `p` is true almost everywhere in any measurable set with finite measure, then
it is true almost everywhere. -/
theorem ae_iff_ae_restrict [SemiFinite μ] {p : α → Prop} (hmp : MeasurableSet {a | ¬ p a})
    (hp : ∀ t, MeasurableSet t → μ t < ⊤ → ∀ᵐ a ∂(μ.restrict t), p a) :
    ∀ᵐ a ∂μ, p a := by
  simp_all only [ae_iff]
  refine measure_eq_zero_of_measure_inter_finite_eq_zero hmp fun t ht => ?_
  simpa [← μ.restrict_apply' ht] using hp t ht

end MeasureTheory
