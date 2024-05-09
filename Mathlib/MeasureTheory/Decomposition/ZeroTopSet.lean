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

def Measure.sigmaFiniteSet (μ : Measure α) [SFinite μ] : Set α := {x | μ.densityToSigmaFinite x ≠ ∞}

lemma measurableSet_sigmaFiniteSet (μ : Measure α) [SFinite μ] :
    MeasurableSet μ.sigmaFiniteSet :=
  (measurable_densityToSigmaFinite μ (measurableSet_singleton ∞)).compl

lemma isZeroTopSet_compl_sigmaFiniteSet (μ : Measure α) [SFinite μ] :
    IsZeroTopSet μ.sigmaFiniteSetᶜ μ := by
  intros t ht ht_subset
  rw [← withDensity_densityToSigmaFinite μ, withDensity_apply _ ht]
  have h_int_eq : ∫⁻ a in t, μ.densityToSigmaFinite a ∂μ.toSigmaFinite = ∞ * μ.toSigmaFinite t := by
    calc ∫⁻ a in t, μ.densityToSigmaFinite a ∂μ.toSigmaFinite
    _ = ∫⁻ _ in t, ∞ ∂μ.toSigmaFinite := by
        refine set_lintegral_congr_fun ht (ae_of_all _ (fun x hx ↦ ?_))
        simpa [Measure.sigmaFiniteSet] using (ht_subset hx)
    _ = ∞ * μ.toSigmaFinite t := by simp
  rw [h_int_eq]
  by_cases h0 : μ.toSigmaFinite t = 0 <;> simp [h0]

lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ]
    (hs : MeasurableSet s) :
    μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s = ∞ := by
  rw [Measure.restrict_apply' (measurableSet_sigmaFiniteSet μ).compl]
  exact isZeroTopSet_compl_sigmaFiniteSet μ (s ∩ μ.sigmaFiniteSetᶜ)
    (hs.inter (measurableSet_sigmaFiniteSet μ).compl) (Set.inter_subset_right _ _)

lemma toSigmaFinite_restrict_sigmaFiniteSet (μ : Measure α) [SFinite μ] :
    μ.toSigmaFinite.restrict μ.sigmaFiniteSet = μ.restrict μ.sigmaFiniteSet := by
  have hμ := withDensity_densityToSigmaFinite μ
  nth_rewrite 3 [← hμ]
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    withDensity_apply _ (hs.inter (measurableSet_sigmaFiniteSet μ)), ← set_lintegral_one]
  refine set_lintegral_congr_fun (hs.inter (measurableSet_sigmaFiniteSet μ))
    (ae_of_all _ (fun x hx ↦ Eq.symm ?_))
  simp only [Measure.sigmaFiniteSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq,
    ne_eq, densityToSigmaFinite_eq_top_iff] at hx
  rw [densityToSigmaFinite_eq_one_iff]
  exact hx.2

instance (μ : Measure α) [SFinite μ] : SigmaFinite (μ.restrict μ.sigmaFiniteSet) := by
  rw [← toSigmaFinite_restrict_sigmaFiniteSet]
  infer_instance

lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero [SFinite μ]
    (h : μ μ.sigmaFiniteSetᶜ = 0) :
    SigmaFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet μ),
    Measure.restrict_eq_zero.mpr h, add_zero]
  infer_instance

@[simp]
lemma measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0 :=
  (isZeroTopSet_iff_null (measurableSet_sigmaFiniteSet μ).compl).mp
    (isZeroTopSet_compl_sigmaFiniteSet μ)

lemma sigmaFinite_iff_measure_compl_sigmaFiniteSet_eq_zero (μ : Measure α) [SFinite μ] :
    SigmaFinite μ ↔ μ μ.sigmaFiniteSetᶜ = 0 :=
  ⟨fun _ ↦ measure_compl_sigmaFiniteSet μ, sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero⟩

end MeasureTheory
