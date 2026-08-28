/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Ergodic maps and measures

Let `f : α → α` be measure preserving with respect to a measure `μ`. We say `f` is ergodic with
respect to `μ` (or `μ` is ergodic with respect to `f`) if the only null-measurable sets `s` that
are almost invariant (i.e. `f ⁻¹' s =ᵐ[μ] s`) are either almost empty or full.

In this file we define ergodic maps / measures together with quasi-ergodic maps / measures and
provide some basic API. Quasi-ergodicity is a weaker condition than ergodicity for which the measure
preserving condition is relaxed to quasi-measure-preserving.

## Main definitions

* `PreErgodic`: the ergodicity condition without the measure-preserving condition. This exists
  to share code between the `Ergodic` and `QuasiErgodic` definitions.
* `Ergodic`: the definition of ergodic maps / measures.
* `QuasiErgodic`: the definition of quasi-ergodic maps / measures.
* `Ergodic.quasiErgodic`: an ergodic map / measure is quasi-ergodic.
* `PreErgodic.of_preimage_eq`: to prove pre-ergodicity of a quasi-measure-preserving map, it
  suffices to check the ergodicity condition on strictly invariant measurable sets.

-/

public section

open Set Function Filter MeasureTheory MeasureTheory.Measure

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {s : Set α}

/-- A map `f : α → α` is said to be pre-ergodic with respect to a measure `μ` if any
null-measurable almost invariant set is either almost empty or full. -/
structure PreErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop where
  aeconst_set ⦃s : Set α⦄ : NullMeasurableSet s μ → f ⁻¹' s =ᵐ[μ] s → EventuallyEmptyOrUniv s (ae μ)

/-- A map `f : α → α` is said to be ergodic with respect to a measure `μ` if it is measure
preserving and pre-ergodic. -/
structure Ergodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  MeasurePreserving f μ μ, PreErgodic f μ

/-- A map `f : α → α` is said to be quasi-ergodic with respect to a measure `μ` if it is
quasi-measure-preserving and pre-ergodic. -/
structure QuasiErgodic (f : α → α) (μ : Measure α := by volume_tac) : Prop extends
  QuasiMeasurePreserving f μ μ, PreErgodic f μ

variable {f : α → α} {μ : Measure α}

/-- To prove that a measurable quasi-measure-preserving `f` is pre-ergodic, it suffices to check the
ergodicity condition on strictly invariant measurable sets. -/
theorem PreErgodic.of_preimage_eq (hfm : Measurable f) (hf : QuasiMeasurePreserving f μ μ)
    (h : ∀ ⦃s : Set α⦄, MeasurableSet s → f ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) :
    PreErgodic f μ where
  aeconst_set _s hsm hs :=
    let ⟨_t, htm, hts, htf⟩ := hf.exists_preimage_eq_of_preimage_ae hfm hsm hs
    (h htm htf).congr hts

theorem PreErgodic.of_preimage_eq_of_isComplete [μ.IsComplete] (hf : QuasiMeasurePreserving f μ μ)
    (h : ∀ ⦃s : Set α⦄, MeasurableSet s → f ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) :
    PreErgodic f μ :=
  .of_preimage_eq (aemeasurable_iff_measurable.1 hf.aemeasurable) hf h

/-- To prove that a quasi-measure-preserving `f` is ergodic, it suffices to check the ergodicity
condition on strictly invariant measurable sets. -/
theorem Ergodic.of_preimage_eq (hf : MeasurePreserving f μ μ)
    (h : ∀ ⦃s : Set α⦄, MeasurableSet s → f ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) :
    Ergodic f μ :=
  ⟨hf, .of_preimage_eq hf.measurable hf.quasiMeasurePreserving h⟩

/-- To prove that a measurable quasi-measure-preserving `f` is quasi-ergodic, it suffices to check
the ergodicity condition on strictly invariant measurable sets. -/
theorem QuasiErgodic.of_preimage_eq (hfm : Measurable f) (hf : QuasiMeasurePreserving f μ μ)
    (h : ∀ ⦃s : Set α⦄, MeasurableSet s → f ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) :
    QuasiErgodic f μ :=
  ⟨hf, .of_preimage_eq hfm hf h⟩

theorem QuasiErgodic.of_preimage_eq_of_isComplete [μ.IsComplete] (hf : QuasiMeasurePreserving f μ μ)
    (h : ∀ ⦃s : Set α⦄, MeasurableSet s → f ⁻¹' s = s → EventuallyEmptyOrUniv s (ae μ)) :
    QuasiErgodic f μ :=
  ⟨hf, .of_preimage_eq_of_isComplete hf h⟩

namespace PreErgodic

theorem ae_empty_or_univ (hf : PreErgodic f μ) (hs : NullMeasurableSet s μ)
    (hfs : f ⁻¹' s =ᵐ[μ] s) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ := by
  simpa only [eventuallyEmptyOrUniv_iff'] using hf.aeconst_set hs hfs

theorem measure_self_or_compl_eq_zero (hf : PreErgodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s =ᵐ[μ] s) : μ s = 0 ∨ μ sᶜ = 0 := by
  simpa using hf.ae_empty_or_univ hs hs'

theorem ae_mem_or_ae_notMem (hf : PreErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  eventuallyEmptyOrUniv_iff.1 <| hf.aeconst_set hsm hs

/-- On a probability space, the (pre)ergodicity condition is a zero-one law. -/
theorem prob_eq_zero_or_one [IsProbabilityMeasure μ] (hf : PreErgodic f μ)
    (hs : NullMeasurableSet s μ) (hs' : f ⁻¹' s =ᵐ[μ] s) : μ s = 0 ∨ μ s = 1 := by
  simpa [prob_compl_eq_zero_iff₀ hs] using hf.measure_self_or_compl_eq_zero hs hs'

theorem of_iterate (n : ℕ) (hqmp : QuasiMeasurePreserving f μ μ) (hf : PreErgodic f^[n] μ) :
    PreErgodic f μ where
  aeconst_set _s hs hs' := hf.aeconst_set hs (hqmp.preimage_iterate_ae_eq n hs')

theorem zero_measure (f : α → α) : @PreErgodic α m f 0 where
  aeconst_set _ _ _ := EventuallyEmptyOrUniv.bot.anti ae_zero.le

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : PreErgodic f μ) (c : R) : PreErgodic f (c • μ) := by
  rw [← smul_one_smul ℝ≥0∞ c μ]
  by_cases hc : c • (1 : ℝ≥0∞) = 0
  · rw [hc, zero_smul]
    exact zero_measure f
  · exact ⟨fun _s hs hfs ↦ by
      rw [ae_ennreal_smul_measure_eq hc] at hfs ⊢
      exact hf.aeconst_set (hs.mono_ac (absolutelyContinuous_smul hc)) hfs⟩

end PreErgodic

namespace MeasureTheory.MeasurePreserving

variable {β : Type*} {m' : MeasurableSpace β} {μ' : Measure β} {g : α → β}

theorem preErgodic_of_preErgodic_semiconj (hg : MeasurePreserving g μ μ') (hf : PreErgodic f μ)
    {f' : β → β} (h_comm : Semiconj g f f') : PreErgodic f' μ' where
  aeconst_set s hs₀ hs₁ := by
    rw [← hg.aeconst_preimage hs₀]
    refine hf.aeconst_set (hs₀.preimage hg.quasiMeasurePreserving) ?_
    rw [← preimage_comp, h_comm.comp_eq, preimage_comp]
    exact hg.quasiMeasurePreserving.preimage_ae_eq hs₁

theorem ergodic_of_ergodic_semiconj (hg : MeasurePreserving g μ μ') (hf : Ergodic f μ)
    {f' : β → β} (hf' : Measurable f') (h_comm : Semiconj g f f') : Ergodic f' μ' :=
  ⟨hg.of_semiconj hf.toMeasurePreserving h_comm hf',
   hg.preErgodic_of_preErgodic_semiconj hf.toPreErgodic h_comm⟩

theorem preErgodic_conjugate_iff {e : α ≃ᵐ β} (h : MeasurePreserving e μ μ') :
    PreErgodic (e ∘ f ∘ e.symm) μ' ↔ PreErgodic f μ := by
  refine ⟨fun hf => preErgodic_of_preErgodic_semiconj (h.symm e) hf ?_,
      fun hf => preErgodic_of_preErgodic_semiconj h hf ?_⟩
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

@[deprecated PreErgodic.aeconst_set (since := "2026-09-06")]
theorem aeconst_set₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ) (hs : f ⁻¹' s =ᵐ[μ] s) :
    EventuallyEmptyOrUniv s (ae μ) :=
  hf.aeconst_set hsm hs

/-- For a quasi-ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
@[deprecated PreErgodic.ae_empty_or_univ (since := "2026-09-06")]
theorem ae_empty_or_univ₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ :=
  hf.ae_empty_or_univ hsm hs

/-- For a quasi-ergodic map, sets that are almost invariant (rather than strictly invariant) are
still either almost empty or full. -/
@[deprecated PreErgodic.ae_mem_or_ae_notMem (since := "2026-09-06")]
theorem ae_mem_or_ae_notMem₀ (hf : QuasiErgodic f μ) (hsm : NullMeasurableSet s μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :
    (∀ᵐ x ∂μ, x ∈ s) ∨ ∀ᵐ x ∂μ, x ∉ s :=
  hf.ae_mem_or_ae_notMem hsm hs

theorem smul_measure {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (hf : QuasiErgodic f μ) (c : R) : QuasiErgodic f (c • μ) :=
  ⟨hf.1.smul_measure _, hf.2.smul_measure _⟩

theorem zero_measure {f : α → α} : @QuasiErgodic α m f 0 where
  aemeasurable := aemeasurable_zero_measure
  absolutelyContinuous := by simp
  toPreErgodic := .zero_measure f

end QuasiErgodic

namespace Ergodic

/-- An ergodic map is quasi-ergodic. -/
theorem quasiErgodic (hf : Ergodic f μ) : QuasiErgodic f μ :=
  { hf.toPreErgodic, hf.toMeasurePreserving.quasiMeasurePreserving with }

/-- See also `Ergodic.ae_empty_or_univ_of_preimage_ae_le`. -/
theorem ae_empty_or_univ_of_preimage_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ := by
  refine hf.ae_empty_or_univ hs ?_
  refine ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).ge ?_ h_fin
  exact hs.preimage hf.quasiMeasurePreserving

/-- See also `Ergodic.ae_empty_or_univ_of_ae_le_preimage`. -/
theorem ae_empty_or_univ_of_ae_le_preimage' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ := by
  replace h_fin : μ (f ⁻¹' s) ≠ ∞ := by rwa [hf.measure_preimage hs]
  refine hf.ae_empty_or_univ hs ?_
  exact (ae_eq_of_ae_subset_of_measure_ge hs' (hf.measure_preimage hs).le hs h_fin).symm

/-- See also `Ergodic.ae_empty_or_univ_of_image_ae_le`. -/
theorem ae_empty_or_univ_of_image_ae_le' (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s ≤ᵐ[μ] s) (h_fin : μ s ≠ ∞) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ := by
  replace hs' : s ≤ᵐ[μ] f ⁻¹' s :=
    (subset_preimage_image f s).eventuallySubset.trans
      (hf.quasiMeasurePreserving.preimage_mono_ae hs')
  exact ae_empty_or_univ_of_ae_le_preimage' hf hs hs' h_fin

/-- If a measurable equivalence is ergodic, then so is the inverse map. -/
theorem symm {e : α ≃ᵐ α} (he : Ergodic e μ) : Ergodic e.symm μ :=
  .of_preimage_eq he.toMeasurePreserving.symm fun s hsm hs ↦
    he.aeconst_set hsm.nullMeasurableSet <| by
      conv_lhs => rw [← hs, ← e.image_eq_preimage_symm, e.preimage_image]

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
    (hs' : f ⁻¹' s ≤ᵐ[μ] s) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_preimage_ae_le' hf hs hs' <| measure_ne_top μ s

theorem ae_empty_or_univ_of_ae_le_preimage (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : s ≤ᵐ[μ] f ⁻¹' s) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_ae_le_preimage' hf hs hs' <| measure_ne_top μ s

theorem ae_empty_or_univ_of_image_ae_le (hf : Ergodic f μ) (hs : NullMeasurableSet s μ)
    (hs' : f '' s ≤ᵐ[μ] s) : s =ᵐ[μ] ∅ ∨ s =ᵐ[μ] univ :=
  ae_empty_or_univ_of_image_ae_le' hf hs hs' <| measure_ne_top μ s

end IsFiniteMeasure

end Ergodic
