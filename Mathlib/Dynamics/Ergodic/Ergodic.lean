/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Ergodic maps and measures

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only measurable sets `s` such that
`f⁻¹' s = s` are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi measure preserving.

# Main definitions:

* `PreErgodic`: the ergodicity condition without the measure preserving condition. This exists
  to share code between the `Ergodic` and `QuasiErgodic` definitions.
* `Ergodic`: the definition of ergodic maps / measures.
* `QuasiErgodic`: the definition of quasi ergodic maps / measures.
* `Ergodic.quasiErgodic`: an ergodic map / measure is quasi ergodic.
* `QuasiErgodic.ae_empty_or_univ'`: when the map is quasi measure preserving, one may relax the
  strict invariance condition to almost invariance in the ergodicity condition.

-/


open Set Function Filter MeasureTheory MeasureTheory.Measure

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {s : Set α}

/-- A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any measurable
strictly invariant set is either almost empty or full. -/
structure PreErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop where
  aeconst_set ⦃s : Set α⦄ : MeasurableSet s → f ⁻¹' s = s → EventuallyConst s (ae μ)

/-- A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is measure
preserving and pre-ergodic. -/
structure Ergodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  MeasurePreserving f μ μ, PreErgodic f μ

/-- A map `f : α → α` is said to be quasi ergodic with respect to a measure `μ` if it is quasi
measure preserving and pre-ergodic. -/
structure QuasiErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ

variable {f : α → α} {μ : Measure α}

namespace PreErgodic

theorem ae_empty_or_univ (hf : PreErgodic f μ) (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  simpa only [eventuallyConst_set'] using hf.aeconst_set hs hfs

theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ sᶜ = 0 := by
  simpa using hf.ae_empty_or_univ hs hs'

theorem ae_mem_or_ae_notMem (hf : PreErgodic f μ) (hsm : MeasurableSet s) (hs : f ⁻¹' s = s) :
    (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  eventuallyConst_set.1 <| hf.aeconst_set hsm hs

@[deprecated (since := "2025-05-24")] alias ae_mem_or_ae_nmem := ae_mem_or_ae_notMem

/-- On a probability space, the (pre)ergodicity condition is a zero one law. -/
theorem prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ) (hs : MeasurableSet s)
    (hs' : f ⁻¹' s = s) : μ s = 0 ∨ μ s = 1 := by
  simpa [hs] using hf.measure_self_or_compl_eq_zero hs hs'

theorem of_iterate (n : ℕ) (hf : PreErgodic f^[n] μ) : PreErgodic f μ :=
  ⟨fun _ hs hs' => hf.aeconst_set hs <| IsFixedPt.preimage_iterate hs' n⟩

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : PreErgodic f μ) (c : R) : PreErgodic f (c • μ) where
  aeconst_set _s hs hfs := (hf.aeconst_set hs hfs).anti <| ae_smul_measure_le _

theorem zero_measure (f : α → α) : @PreErgodic α m f 0 where
  aeconst_set _ _ _ := by simp

end PreErgodic

namespace MeasureTheory.MeasurePreserving

variable {β : Type*} {m' : MeasurableSpace β} {μ' : Measure β} {g : α → β}

theorem preErgodic_of_preErgodic_conjugate (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
    {f' : β → β} (h_comm : Semiconj g f f') : PreErgodic f' μ' where
  aeconst_set s hs₀ hs₁ := by
    rw [← hg.aeconst_preimage hs₀.nullMeasurableSet]
    apply hf.aeconst_set (hg.measurable hs₀)
    rw [← preimage_comp, h_comm.comp_eq, preimage_comp, hs₁]

theorem preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := by
  refine ⟨fun hf => preErgodic_of_preErgodic_conjugate (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_conjugate h hf ?_⟩
  · simp [Semiconj]
  · simp [Semiconj]

theorem ergodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    Ergodic (e ∘ f ∘ e.symm) μ' ↔ Ergodic f μ := by
  have : MeasurePreserving (e ∘ f ∘ e.symm) μ' μ' ↔ MeasurePreserving f μ μ := by
    rw [h.comp_left_iff, (MeasurePreserving.symm e h).comp_right_iff]
  replace h : PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := h.preErgodic_conjugate_iff
  exact ⟨fun hf => { this.mp hf.toMeasurePreserving, h.mp hf.toPreErgodic with },
    fun hf => { this.mpr hf.toMeasurePreserving, h.mpr hf.toPreErgodic with }⟩

end MeasureTheory.MeasurePreserving

namespace QuasiErgodic

theorem aeconst_set₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  let ⟨_t, h₀, h₁, h₂⟩ := hf.toQuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hsm hs
  (hf.aeconst_set h₀ h₂).congr h₁

/-- For a quasi ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
theorem ae_empty_or_univ₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  eventuallyConst_set'.mp <| hf.aeconst_set₀ hsm hs

/-- For a quasi ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
theorem ae_mem_or_ae_notMem₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  eventuallyConst_set.mp <| hf.aeconst_set₀ hsm hs

@[deprecated (since := "2025-05-24")] alias ae_mem_or_ae_nmem₀ := ae_mem_or_ae_notMem₀

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : QuasiErgodic f μ) (c : R) : QuasiErgodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

theorem zero_measure {f : α → α} (hf : Measurable f) : @QuasiErgodic α m f 0 where
  measurable := hf
  absolutelyContinuous := by simp
  toPreErgodic := .zero_measure f

end QuasiErgodic

namespace Ergodic

/-- An ergodic map is quasi ergodic. -/
theorem quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ :=
  { hf.toPreErgodic, hf.toMeasurePreserving.quasiMeasurePreserving with }

/-- See also `Ergodic.ae_empty_or_univ_of_preimage_ae_le`. -/
theorem ae_empty_or_univ_of_preimage_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).ge ?_ h_fin
  exact hs.preimage hf.quasiMeasurePreserving

/-- See also `Ergodic.ae_empty_or_univ_of_ae_le_preimage`. -/
theorem ae_empty_or_univ_of_ae_le_preimage' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  replace h_fin : μ (f ⁻¹' s) ≠ ∞ := by rwa [hf.measure_preimage hs]
  refine hf.quasiErgodic.ae_empty_or_univ₀ hs ?_
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm

/-- See also `Ergodic.ae_empty_or_univ_of_image_ae_le`. -/
theorem ae_empty_or_univ_of_image_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ := by
  replace hs' : s ≤ᵐ[μ] f ⁻¹' s :=
    (HasSubset.Subset.eventuallyLE (subset_preimage_image f s)).trans
      (hf.quasiMeasurePreserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin

/-- If a measurable equivalence is ergodic, then so is the inverse map. -/
theorem symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ where
  toMeasurePreserving := he.toMeasurePreserving.symm
  aeconst_set s hsm hs := he.aeconst_set hsm <| by
    conv_lhs => rw [← hs, ← e.image_eq_preimage, e.preimage_image]

@[simp] theorem symm_iff {e : α ≃ᵐ α} : Ergodic e.symm μ ↔ Ergodic e μ := ⟨.symm, .symm⟩

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : Ergodic f μ) (c : R) : Ergodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

theorem zero_measure {f : α → α} (hf : Measurable f) : @Ergodic α m f 0 where
  measurable := hf
  map_eq := by simp
  toPreErgodic := .zero_measure f

section IsFiniteMeasure

variable [IsFiniteMeasure μ]

theorem ae_empty_or_univ_of_preimage_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_preimage_ae_le' hf hs hs' <| measure_ne_top μ s

theorem ae_empty_or_univ_of_ae_le_preimage (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_ae_le_preimage' hf hs hs' <| measure_ne_top μ s

theorem ae_empty_or_univ_of_image_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s ≤ᵐ[μ] s) : s =ᵐ[μ] (∅ : Set α) ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_image_ae_le' hf hs hs' <| measure_ne_top μ s

end IsFiniteMeasure

end Ergodic
