/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Decomposition.Exhaustion
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# ZeroTopSet

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open scoped NNReal ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

namespace Measure

lemma ae_lt_top_of_sigmaFinite [SigmaFinite μ] {f : α → ℝ≥0∞} (hf : Measurable f)
    (h2f : ∀ s, MeasurableSet s → μ s < ∞ → ∫⁻ x in s, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  ae_of_forall_measure_lt_top_ae_restrict _ (fun s hs hμs ↦ ae_lt_top hf (h2f s hs hμs))

lemma measure_eq_iSup_measure_subset [SigmaFinite μ] (hs : MeasurableSet s) :
    μ s = ⨆ (t : Set α) (_ht : MeasurableSet t) (_hμt : μ t ≠ ∞) (_hts : t ⊆ s), μ t := by
  refine le_antisymm ?_ ?_
  · rw [← iSup_restrict_spanningSets]
    simp only [ne_eq, iSup_le_iff]
    intro i
    rw [restrict_apply' (measurable_spanningSets _ _)]
    refine le_trans ?_ (le_iSup _ (s ∩ spanningSets μ i))
    simp only [hs.inter (measurable_spanningSets _ _),
      ((measure_mono (Set.inter_subset_right s _)).trans_lt (measure_spanningSets_lt_top μ _)).ne,
      not_false_eq_true, Set.inter_subset_left, iSup_pos, le_refl]
  · simp only [ne_eq, iSup_le_iff]
    exact fun _ _ _ hts ↦ measure_mono hts

/-- Auxiliary lemma for `sFinite_of_absolutelyContinuous`. -/
lemma sFinite_of_absolutelyContinuous_aux [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h : ∀ s, MeasurableSet s → ν s ≠ 0 → μ s = ∞) :
    SFinite μ := by
  suffices μ = ν.withDensity (fun _ ↦ ∞) by
    rw [this]
    exact sFinite_withDensity_of_measurable _ measurable_const
  ext s hs
  simp only [withDensity_const, Measure.smul_apply, smul_eq_mul]
  by_cases hνs : ν s = 0
  · simp [hνs, hμν hνs]
  · simp [h s hs hνs, hνs]

/-- Auxiliary lemma for `sFinite_of_absolutelyContinuous`. -/
lemma sFinite_of_absolutelyContinuous_of_isFiniteMeasure [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    SFinite μ := by
  let s := sigmaFiniteSetWRT μ ν
  have hs : MeasurableSet s := measurableSet_sigmaFiniteSetWRT μ ν
  rw [← restrict_add_restrict_compl (μ := μ) hs]
  have : SFinite (μ.restrict sᶜ) := by
    refine sFinite_of_absolutelyContinuous_aux (hμν.restrict sᶜ) (fun t ht hνt ↦ ?_)
    rw [restrict_apply ht] at hνt ⊢
    refine measure_eq_top_of_subset_compl_sigmaFiniteSetWRT (ht.inter hs.compl) ?_ hνt
    exact Set.inter_subset_right _ _
  infer_instance

/-- If `μ ≪ ν` and `ν` is s-finite, then `μ` is s-finite. -/
theorem sFinite_of_absolutelyContinuous [SFinite ν] (hμν : μ ≪ ν) : SFinite μ :=
  sFinite_of_absolutelyContinuous_of_isFiniteMeasure (hμν.trans (absolutelyContinuous_toFinite ν))

instance [SFinite μ] (f : α → ENNReal) : SFinite (μ.withDensity f) :=
  sFinite_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)

/-! ### IsZeroTopSet -/

def IsZeroTopSet (s : Set α) (μ : Measure α) : Prop :=
  ∀ t, MeasurableSet t → t ⊆ s → μ t = 0 ∨ μ t = ∞

lemma isZeroTopSet_of_null (hs_zero : μ s = 0) : IsZeroTopSet s μ :=
  fun _ _ ht_subset ↦ Or.inl <| measure_mono_null ht_subset hs_zero

lemma measure_isZeroTopSet (hs0 : IsZeroTopSet s μ) (hs : MeasurableSet s) : μ s = 0 ∨ μ s = ⊤ :=
  hs0 s hs subset_rfl

lemma iSup_measure_subset_eq_zero_of_isZeroTopSet (hs : IsZeroTopSet s μ) :
    ⨆ (t : Set α) (_ : MeasurableSet t) (_ : μ t ≠ ∞) (_ : t ⊆ s), μ t = 0 := by
  simp only [ne_eq, ENNReal.iSup_eq_zero]
  exact fun t ht hμt hts ↦ (hs t ht hts).resolve_right hμt

lemma isZeroTopSet_iff_null [SigmaFinite μ] (hs : MeasurableSet s) :
    IsZeroTopSet s μ ↔ μ s = 0 := by
  refine ⟨fun h ↦ ?_, isZeroTopSet_of_null⟩
  rw [measure_eq_iSup_measure_subset hs, iSup_measure_subset_eq_zero_of_isZeroTopSet h]

def maxZeroTopSet (μ : Measure α) [SFinite μ] : Set α :=
  {x | densityToSigmaFinite μ x = ∞}

lemma measurableSet_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    MeasurableSet (maxZeroTopSet μ) :=
  measurable_densityToSigmaFinite μ (measurableSet_singleton ∞)

lemma isZeroTopSet_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    IsZeroTopSet (maxZeroTopSet μ) μ := by
  intro t ht ht_subset
  rw [← withDensity_densityToSigmaFinite μ, withDensity_apply _ ht]
  have h_int_eq : ∫⁻ a in t, densityToSigmaFinite μ a ∂μ.toSigmaFinite = ∞ * μ.toSigmaFinite t := by
    calc ∫⁻ a in t, densityToSigmaFinite μ a ∂μ.toSigmaFinite
    _ = ∫⁻ _ in t, ∞ ∂μ.toSigmaFinite :=
        set_lintegral_congr_fun ht (ae_of_all _ (fun x hx ↦ ht_subset hx))
    _ = ∞ * μ.toSigmaFinite t := by simp
  rw [h_int_eq]
  by_cases h0 : μ.toSigmaFinite t = 0 <;> simp [h0]

lemma restrict_compl_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    μ.restrict (maxZeroTopSet μ)ᶜ = (μ.toSigmaFinite).restrict (maxZeroTopSet μ)ᶜ := by
  have hμ := withDensity_densityToSigmaFinite μ
  nth_rewrite 1 [← hμ]
  ext s hs
  rw [restrict_apply hs, withDensity_apply _ (hs.inter (measurableSet_maxZeroTopSet μ).compl),
    restrict_apply hs, ← set_lintegral_one]
  refine set_lintegral_congr_fun (hs.inter (measurableSet_maxZeroTopSet μ).compl)
    (ae_of_all _ (fun x hx ↦ ?_))
  simp only [maxZeroTopSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
    densityToSigmaFinite_eq_top_iff] at hx
  rw [densityToSigmaFinite_eq_one_iff]
  exact hx.2

lemma toSigmaFinite_add_restrict_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    (μ.toSigmaFinite).restrict (maxZeroTopSet μ)ᶜ + μ.restrict (maxZeroTopSet μ) = μ := by
  rw [← restrict_compl_maxZeroTopSet, restrict_compl_add_restrict (measurableSet_maxZeroTopSet μ)]

lemma restrict_maxZeroTopSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (hs : MeasurableSet s) :
    μ.restrict (maxZeroTopSet μ) s = 0 ∨ μ.restrict (maxZeroTopSet μ) s = ∞ := by
  rw [restrict_apply' (measurableSet_maxZeroTopSet μ)]
  exact isZeroTopSet_maxZeroTopSet μ (s ∩ maxZeroTopSet μ)
    (hs.inter (measurableSet_maxZeroTopSet μ)) (Set.inter_subset_right _ _)

lemma sigmaFinite_iff_measure_maxZeroTopSet (μ : Measure α) [SFinite μ] :
    SigmaFinite μ ↔ μ (maxZeroTopSet μ) = 0 := by
  refine ⟨fun h ↦ (isZeroTopSet_iff_null (measurableSet_maxZeroTopSet μ)).mp
    (isZeroTopSet_maxZeroTopSet μ), fun h ↦ ?_⟩
  rw [← toSigmaFinite_add_restrict_maxZeroTopSet μ, restrict_eq_zero.mpr h, add_zero]
  infer_instance

lemma measure_eq_iSup_measure_subset_toMeasurable [SigmaFinite μ] (s : Set α) :
    μ s = ⨆ (t : Set α) (_ht : MeasurableSet t) (_hμt : μ t ≠ ∞) (_hts : t ⊆ toMeasurable μ s),
      μ t := by
  rw [← measure_toMeasurable s,measure_eq_iSup_measure_subset (measurableSet_toMeasurable _ _)]

lemma isZeroTopSet_iff_ne_iSup_of_eq_top (hμs : μ s = ∞) :
    IsZeroTopSet s μ
      ↔ μ s ≠ ⨆ (t : Set α) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (hts : t ⊆ s), μ t := by
  refine ⟨fun hs ↦ ?_, fun h ↦ ?_⟩
  · simp [iSup_measure_subset_eq_zero_of_isZeroTopSet hs, hμs]
  · sorry

end Measure

end MeasureTheory
