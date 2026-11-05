/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Map

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Pullback of a measure

In this file we define the pullback `MeasureTheory.Measure.comap f μ` of a measure `μ` along a map
`f` such that every measurable set is the preimage of a set that is Carathéodory-measurable
for `μ`. Then `comap f μ s = μ (f '' s)` for every measurable set `s`.
If `f` does not have this property, then we define `comap f μ` to be zero.

In the future, we may decide to redefine `comap f μ` so that it gives meaningful results, e.g.,
for covering maps like `(↑) : ℝ → AddCircle (1 : ℝ)`.
-/

@[expose] public section

open Function Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureTheory

namespace Measure

variable {α β γ : Type*} {s : Set α}

open scoped Classical in
/-- Pullback of a `Measure` as a linear map. If every measurable set is the preimage of a
measurable set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

If the linearity is not needed, please use `comap` instead, which works for a larger class of
functions. `comapₗ` is an auxiliary definition and most lemmas deal with comap. -/
def comapₗ [mα : MeasurableSpace α] [mβ : MeasurableSpace β] (f : α → β) :
    Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : mα ≤ mβ.comap f then
    liftLinear (OuterMeasure.comap f) fun μ ↦ hf.trans <|
      (MeasurableSpace.comap_mono (le_toOuterMeasure_caratheodory μ)).trans
        (OuterMeasure.le_comap_caratheodory f _)
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem comapₗ_apply {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β}
    (hf : mα ≤ mβ.comap f) (μ : Measure β) (hs : MeasurableSet s) :
    comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ, dite_eq_left hf, liftLinear_apply _ hs, OuterMeasure.comap_apply,
    coe_toOuterMeasure]

open scoped Classical in
/-- Pullback of a `Measure`. If every measurable set is the preimage of a set that is
Carathéodory-measurable for `μ`, then for each measurable set `s` we have
`comap f μ s = μ (f '' s)`. Otherwise, `comap f μ` is zero.

The condition holds if `f` is injective and sends measurable sets to null-measurable sets
(`le_comap_caratheodory_of_injective`), or if every measurable set is the preimage of a
measurable set (`le_comap_caratheodory_of_le_comap`). -/
def comap [mα : MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : mα ≤ μ.caratheodory.comap f then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure
      (hf.trans (OuterMeasure.le_comap_caratheodory f _))
  else 0

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : α → β} {g : β → γ}

/-- If every measurable set is the preimage of a measurable set, then `f` satisfies the
hypothesis of `comap_apply`. -/
theorem le_comap_caratheodory_of_le_comap (hf : mα ≤ mβ.comap f) (μ : Measure β) :
    mα ≤ μ.caratheodory.comap f :=
  hf.trans (MeasurableSpace.comap_mono (le_toOuterMeasure_caratheodory μ))

/-- If `f` is injective and sends measurable sets to null-measurable sets, then `f`
satisfies the hypothesis of `comap_apply`. -/
theorem le_comap_caratheodory_of_injective {μ : Measure β} (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) : mα ≤ μ.caratheodory.comap f :=
  fun s hs ↦ ⟨f '' s, fun t ↦ (measure_inter_add_sdiff₀ t (hf s hs)).symm, hfi.preimage_image s⟩

/-- If `f` is a measurable embedding, then `f` satisfies the hypothesis of `comap_apply`. -/
theorem _root_.MeasurableEmbedding.le_comap_caratheodory (hf : MeasurableEmbedding f)
    (μ : Measure β) : mα ≤ μ.caratheodory.comap f :=
  le_comap_caratheodory_of_le_comap hf.comap_eq.ge μ

theorem comap_apply₀ {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap, dite_eq_left hf] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]

lemma comap_undef {μ : Measure β} (h : ¬ mα ≤ μ.caratheodory.comap f) : comap f μ = 0 :=
  dite_eq_right h

theorem le_comap_apply {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f) (s : Set α) :
    μ (f '' s) ≤ comap f μ s := by
  grw [comap, dite_eq_left hf, ← le_toMeasure_apply]; rfl

theorem comap_apply {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ hf hs.nullMeasurableSet

theorem comap_apply_le (f : α → β) (μ : Measure β) (hs : NullMeasurableSet s (μ.comap f)) :
    μ.comap f s ≤ μ (f '' s) := by
  by_cases hf : mα ≤ μ.caratheodory.comap f
  · rw [comap_apply₀ hf hs]
  · simp [comap_undef hf]

/-- If `f` is measurable, then `comap f μ s = μ (f '' s)` holds for every set `s`. -/
theorem comap_apply_of_measurable {μ : Measure β} (hfm : Measurable f)
    (hf : mα ≤ μ.caratheodory.comap f) (s : Set α) : comap f μ s = μ (f '' s) := by
  refine le_antisymm ?_ (le_comap_apply hf s)
  grw [image_subset_iff.mp (subset_toMeasurable μ (f '' s)),
    comap_apply hf (hfm (measurableSet_toMeasurable ..)), image_preimage_subset,
    measure_toMeasurable]

theorem comapₗ_eq_comap (hf : mα ≤ mβ.comap f) (μ : Measure β) : comapₗ f μ = comap f μ :=
  ext fun _ hs ↦ (comapₗ_apply hf μ hs).trans
    (comap_apply (le_comap_caratheodory_of_le_comap hf μ) hs).symm

theorem measure_image_eq_zero_of_comap_eq_zero {μ : Measure β}
    (hf : mα ≤ μ.caratheodory.comap f) {s : Set α} (hs : comap f μ s = 0) : μ (f '' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_comap_apply hf s).trans hs.le

theorem ae_eq_image_of_ae_eq_comap {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [ae_eq_set] at hst ⊢
  obtain ⟨hst, hts⟩ := hst
  exact ⟨measure_mono_null (subset_image_sdiff f s t)
      (measure_image_eq_zero_of_comap_eq_zero hf hst),
    measure_mono_null (subset_image_sdiff f t s) (measure_image_eq_zero_of_comap_eq_zero hf hts)⟩

theorem NullMeasurableSet.image {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f)
    (hf' : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ :=
  (hf' _ (measurableSet_toMeasurable _ s)).congr
    (ae_eq_image_of_ae_eq_comap hf hs.toMeasurable_ae_eq)

theorem comap_preimage {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f) (hf' : Measurable f)
    (s : Set β) : μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply_of_measurable hf' hf, image_preimage_eq_inter_range]

@[simp] lemma comap_zero (f : α → β) : (0 : Measure β).comap f = 0 := by
  by_cases hf : mα ≤ (0 : Measure β).caratheodory.comap f
  · ext s hs
    simp [comap_apply hf hs]
  · exact comap_undef hf

@[simp]
lemma comap_id (μ : Measure β) : comap (fun x ↦ x) μ = μ :=
  ext fun s hs ↦ by
    rw [comap_apply (f := fun x ↦ x) (MeasurableEmbedding.id.le_comap_caratheodory μ) hs,
      image_id']

lemma comap_comap {μ : Measure γ} (hg : Measurable g) (hgμ : mβ ≤ μ.caratheodory.comap g)
    (hgf : mα ≤ μ.caratheodory.comap (g ∘ f)) : comap f (comap g μ) = comap (g ∘ f) μ := by
  have hf : mα ≤ (comap g μ).caratheodory.comap f := by
    have : (comap g μ).toOuterMeasure = OuterMeasure.comap g μ.toOuterMeasure :=
      OuterMeasure.ext (comap_apply_of_measurable hg hgμ)
    rw [this]
    grw [hgf, ← MeasurableSpace.comap_comp, OuterMeasure.le_comap_caratheodory]
  ext s hs
  rw [comap_apply hf hs, comap_apply_of_measurable hg hgμ, comap_apply hgf hs, image_comp]

lemma comap_smul_of_le {μ : Measure β} (hf : mα ≤ μ.caratheodory.comap f) (c : ℝ≥0∞) :
    comap f (c • μ) = c • comap f μ := by
  have hcf : mα ≤ (c • μ).caratheodory.comap f := by
    rw [smul_toOuterMeasure]
    exact hf.trans (MeasurableSpace.comap_mono (OuterMeasure.le_smul_caratheodory c _))
  ext s hs
  rw [comap_apply hcf hs, smul_apply, smul_apply, comap_apply hf hs]

/-- See `comap_smul_of_le` for `c = ⊤`. Every set is Carathéodory-measurable for `⊤ • μ`, so
`comap f (⊤ • μ)` can be nonzero while `comap f μ = 0`. -/
lemma comap_smul {μ : Measure β} {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    comap f (c • μ) = c • comap f μ := by
  obtain rfl | hc₀ := eq_or_ne c 0
  · simp
  by_cases hf : mα ≤ μ.caratheodory.comap f
  · exact comap_smul_of_le hf c
  have hcf : ¬ mα ≤ (c • μ).caratheodory.comap f := by
    refine fun h ↦ hf (h.trans (MeasurableSpace.comap_mono ?_))
    have := OuterMeasure.le_smul_caratheodory c⁻¹ (c • μ).toOuterMeasure
    rwa [smul_toOuterMeasure, smul_smul, ENNReal.inv_mul_cancel hc₀ hc, one_smul] at this
  rw [comap_undef hf, comap_undef hcf, smul_zero]

lemma comap_add (hf : mα ≤ mβ.comap f) (μ ν : Measure β) :
    (μ + ν).comap f = μ.comap f + ν.comap f := by
  simp only [← comapₗ_eq_comap hf, map_add]

end Measure

end MeasureTheory

open MeasureTheory Measure

variable {α β : Type*} {ma : MeasurableSpace α} {mb : MeasurableSpace β}

lemma MeasurableEmbedding.comap_add {f : α → β} (hf : MeasurableEmbedding f) (μ ν : Measure β) :
    (μ + ν).comap f = μ.comap f + ν.comap f :=
  Measure.comap_add hf.comap_eq.ge μ ν

namespace MeasurableEquiv

lemma comap_symm {μ : Measure α} (e : α ≃ᵐ β) : μ.comap e.symm = μ.map e := by
  ext s hs
  rw [e.map_apply, comap_apply (e.symm.measurableEmbedding.le_comap_caratheodory μ) hs,
    image_symm]

lemma map_symm {μ : Measure α} (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e := by
  rw [← comap_symm, symm_symm]

end MeasurableEquiv

lemma MeasureTheory.Measure.comap_swap (μ : Measure (α × β)) : μ.comap .swap = μ.map .swap :=
  (MeasurableEquiv.prodComm ..).comap_symm
