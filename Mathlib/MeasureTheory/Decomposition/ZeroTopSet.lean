/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# ZeroTopSet

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-! ### IsZeroTopSet -/

def IsZeroTopSet (s : Set α) (μ : Measure α) : Prop :=
  ∀ t, MeasurableSet t → t ⊆ s → μ t = 0 ∨ μ t = ∞

lemma isZeroTopSet_of_null (hs_zero : μ s = 0) : IsZeroTopSet s μ :=
  fun _ _ ht_subset ↦ Or.inl <| measure_mono_null ht_subset hs_zero

lemma measure_isZeroTopSet (hs0 : IsZeroTopSet s μ) (hs : MeasurableSet s) : μ s = 0 ∨ μ s = ⊤ :=
  hs0 s hs subset_rfl

lemma isZeroTopSet_iff_null [SigmaFinite μ] (hs : MeasurableSet s) :
    IsZeroTopSet s μ ↔ μ s = 0 := by
  refine ⟨fun h ↦ ?_, isZeroTopSet_of_null⟩
  rw [← Measure.iSup_restrict_spanningSets]
  simp only [ENNReal.iSup_eq_zero]
  intro n
  rw [Measure.restrict_apply' (measurable_spanningSets μ n)]
  refine (h (s ∩ spanningSets μ n) (hs.inter (measurable_spanningSets μ n))
    (Set.inter_subset_left _ _)).resolve_right (ne_of_lt ?_)
  exact (measure_mono (Set.inter_subset_right _ _)).trans_lt (measure_spanningSets_lt_top _ _)

lemma isZeroTopSet_compl_sigmaFiniteSet (μ : Measure α) [SFinite μ] :
    IsZeroTopSet μ.sigmaFiniteSetᶜ μ :=
  fun _ ht ht_subset ↦ measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet ht ht_subset

end MeasureTheory
