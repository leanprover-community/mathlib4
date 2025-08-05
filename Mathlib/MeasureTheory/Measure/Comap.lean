/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Pullback of a measure

In this file we define the pullback `MeasureTheory.Measure.comap f μ`
of a measure `μ` along an injective map `f`
such that the image of any measurable set under `f` is a null-measurable set.
If `f` does not have these properties, then we define `comap f μ` to be zero.

In the future, we may decide to redefine `comap f μ` so that it gives meaningful results, e.g.,
for covering maps like `(↑) : ℝ → AddCircle (1 : ℝ)`.
-/

open Function Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureTheory

namespace Measure

variable {α β γ : Type*} {s : Set α}

open Classical in
/-- Pullback of a `Measure` as a linear map. If `f` sends each measurable set to a measurable
set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

Note that if `f` is not injective, this definition assigns `Set.univ` measure zero.

If the linearity is not needed, please use `comap` instead, which works for a larger class of
functions. `comapₗ` is an auxiliary definition and most lemmas deal with comap. -/
def comapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0

theorem comapₗ_apply {_ : MeasurableSpace α} {_ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ, dif_pos, liftLinear_apply _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]
  exact ⟨hfi, hf⟩

open Classical in
/-- Pullback of a `Measure`. If `f` sends each measurable set to a null-measurable set,
then for each measurable set `s` we have `comap f μ s = μ (f '' s)`.

Note that if `f` is not injective, this definition assigns `Set.univ` measure zero. -/
def comap [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      exact (measure_inter_add_diff₀ _ (hf.2 s hs)).symm
  else 0

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : α → β} {g : β → γ}

theorem comap_apply₀ (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap, dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]

lemma comap_undef {μ : Measure β}
    (h : ¬ (Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)) :
    comap f μ = 0 := dif_neg h

theorem le_comap_apply (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) ≤ comap f μ s := by
  rw [comap, dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _

theorem comap_apply (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet

theorem comapₗ_eq_comap (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm

theorem measure_image_eq_zero_of_comap_eq_zero (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 :=
  le_antisymm ((le_comap_apply f μ hfi hf s).trans hs.le) (zero_le _)

theorem ae_eq_image_of_ae_eq_comap (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [EventuallyEq, ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t ∪ t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_setOf_eq, mem_union, mem_diff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t ∪ f '' t \ f '' s := by
    ext1 x
    simp only [eq_iff_iff, mem_setOf_eq, mem_union, mem_diff]
    tauto
  rw [← Set.image_diff hfi, ← Set.image_diff hfi, ← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst

theorem NullMeasurableSet.image (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ := by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMeasurableSet.toMeasurable_ae_eq hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm

theorem comap_preimage (f : α → β) (μ : Measure β) (hf : Injective f) (hf' : Measurable f)
    (h : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ) {s : Set β} (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet, image_preimage_eq_inter_range]

@[simp] lemma comap_zero (f : α → β) : (0 : Measure β).comap f = 0 := by
  by_cases hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) (0 : Measure β)
  · simp [comap, hf]
  · simp [comap, hf]

@[simp]
lemma comap_id (μ : Measure β) : comap (fun x ↦ x) μ = μ := by
  ext s hs
  rw [comap_apply, image_id']
  · exact injective_id
  all_goals simp [*]

lemma comap_comap (hf' : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (hg : Injective g)
    (hg' : ∀ s, MeasurableSet s → MeasurableSet (g '' s)) (μ : Measure γ) :
    comap f (comap g μ) = comap (g ∘ f) μ := by
  by_cases hf : Injective f
  · ext s hs
    rw [comap_apply _ hf hf' _ hs, comap_apply _ hg hg' _ (hf' _ hs),
      comap_apply _ (hg.comp hf) (fun t ht ↦ image_comp g f _ ▸ hg' _ <| hf' _ ht) _ hs, image_comp]
  · rw [comap, dif_neg <| mt And.left hf, comap, dif_neg fun h ↦ hf h.1.of_comp]

lemma comap_smul {μ : Measure β} (c : ℝ≥0∞) : comap f (c • μ) = c • comap f μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  by_cases h : Function.Injective f ∧ ∀ s : Set α, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [comap_apply₀ f _ h.1 _ hs.nullMeasurableSet, smul_apply, smul_apply,
      comap_apply₀ f μ h.1 h.2 hs.nullMeasurableSet]
    simpa [nullMeasurableSet_smul_measure_iff hc] using h.2
  · have h' : ¬ (Function.Injective f ∧
        ∀ (s : Set α), MeasurableSet s → NullMeasurableSet (f '' s) (c • μ)) := by
      simpa [nullMeasurableSet_smul_measure_iff hc] using h
    simp [comap_undef, h, h']

end Measure

end MeasureTheory

open MeasureTheory Measure

variable {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β}

lemma MeasurableEmbedding.comap_add {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure β) :
    (μ + ν).comap f = μ.comap f + ν.comap f := by
  ext s hs
  simp only [← comapₗ_eq_comap _ hf.injective (fun _ ↦ hf.measurableSet_image.mpr) _ hs,
    map_add, add_apply]

namespace MeasurableEquiv

lemma comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.comap e.symm = μ.map e := by
  ext s hs
  rw [e.map_apply, Measure.comap_apply _ e.symm.injective _ _ hs, image_symm]
  exact fun t ht ↦ e.symm.measurableSet_image.mpr ht

lemma map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e := by
  rw [← comap_symm, symm_symm]

end MeasurableEquiv

lemma MeasureTheory.Measure.comap_swap (μ : Measure (α × β)) : μ.comap .swap = μ.map .swap :=
  (MeasurableEquiv.prodComm ..).comap_symm
