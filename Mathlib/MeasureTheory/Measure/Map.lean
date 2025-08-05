/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Pushforward of a measure

In this file we define the pushforward `MeasureTheory.Measure.map f μ`
of a measure `μ` along an almost everywhere measurable map `f`.
If `f` is not a.e. measurable, then we define `map f μ` to be zero.

## Main definitions

* `MeasureTheory.Measure.map f μ`: map of the measure `μ` along the map `f`.

## Main statements

* `map_apply`: for `s` a measurable set, `μ.map f s = μ (f ⁻¹' s)`
* `map_map`: `(μ.map f).map g = μ.map (g ∘ f)`

-/

variable {α β γ : Type*}

open Set Function ENNReal NNReal
open Filter hiding map

namespace MeasureTheory

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {s : Set α}

namespace Measure

/-- Lift a linear map between `OuterMeasure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `Measure` spaces. -/
noncomputable
def liftLinear [MeasurableSpace β] (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) :
    Measure α →ₗ[ℝ≥0∞] Measure β where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      OuterMeasure.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [LinearMap.map_smulₛₗ, Pi.smul_apply,
      toMeasure_apply, smul_toOuterMeasure (R := ℝ≥0∞), OuterMeasure.coe_smul (R := ℝ≥0∞),
      smul_apply, hs]

lemma liftLinear_apply₀ {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : NullMeasurableSet s (liftLinear f hf μ)) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply₀ _ (hf μ) hs

@[simp]
theorem liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ (hf μ) hs

theorem le_liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s ≤ liftLinear f hf μ s :=
  le_toMeasure_apply _ (hf μ) s

open Classical in
/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
noncomputable
def mapₗ [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0

theorem mapₗ_congr {f g : α → β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using measure_congr (h.preimage s)

open Classical in
/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
noncomputable
irreducible_def map [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (μ : Measure α) :
    Measure β :=
  if hf : AEMeasurable f μ then mapₗ (hf.mk f) μ else 0

theorem mapₗ_mk_apply_of_aemeasurable {f : α → β} (hf : AEMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]

theorem mapₗ_apply_of_measurable {f : α → β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ := by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk

@[simp]
protected theorem map_add (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]

@[simp]
protected theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]

@[simp]
theorem map_of_not_aemeasurable {f : α → β} {μ : Measure α} (hf : ¬AEMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]

theorem _root_.AEMeasurable.of_map_ne_zero {f : α → β} {μ : Measure α} (hf : μ.map f ≠ 0) :
    AEMeasurable f μ := not_imp_comm.1 map_of_not_aemeasurable hf

theorem map_congr {f g : α → β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ := by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasurable g μ := by simpa [← aemeasurable_congr h] using hf
    simp [map_of_not_aemeasurable, hf, hg]

@[simp]
protected theorem map_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) (μ : Measure α) (f : α → β) : (c • μ).map f = c • μ.map f := by
  suffices ∀ c : ℝ≥0∞, (c • μ).map f = c • μ.map f by simpa using this (c • 1)
  clear c; intro c
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hfc,
      LinearMap.map_smulₛₗ, RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact EventuallyEq.trans ((ae_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AEMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_aemeasurable hf, map_of_not_aemeasurable hfc]

variable {f : α → β}

lemma map_apply₀ {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹' s) := by
  rw [map, dif_pos hf, mapₗ, dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs, measure_congr (hf.ae_eq_mk.preimage s)]
  rfl

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `MeasureTheory.Measure.le_map_apply` and `MeasurableEquiv.map_apply`. -/
@[simp]
theorem map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) := map_apply₀ hf hs.nullMeasurableSet

@[simp]
theorem map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aemeasurable hf.aemeasurable hs

theorem map_toOuterMeasure (hf : AEMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim := by
  rw [← trimmed, OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]

@[simp] lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]

@[simp] lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  rw [mapₗ_apply_of_measurable hf, map_eq_zero_iff hf.aemeasurable]

/-- If `map f μ = μ`, then the measure of the preimage of any null measurable set `s`
is equal to the measure of `s`.
Note that this lemma does not assume (a.e.) measurability of `f`. -/
lemma measure_preimage_of_map_eq_self {f : α → α} (hf : map f μ = μ)
    {s : Set α} (hs : NullMeasurableSet s μ) : μ (f ⁻¹' s) = μ s := by
  if hfm : AEMeasurable f μ then
    rw [← map_apply₀ hfm, hf]
    rwa [hf]
  else
    rw [map_of_not_aemeasurable hfm] at hf
    simp [← hf]

lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).not
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 :=
  (mapₗ_eq_zero_iff hf).not

@[simp]
theorem map_id : map id μ = μ :=
  ext fun _ => map_apply measurable_id

@[simp]
theorem map_id' : map (fun x => x) μ = μ :=
  map_id

/-- Mapping a measure twice is the same as mapping the measure with the composition. This version is
for measurable functions. See `map_map_of_aemeasurable` when they are just ae measurable. -/
theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]

@[mono]
theorem map_mono {f : α → β} (h : μ ≤ ν) (hf : Measurable f) : μ.map f ≤ ν.map f :=
  le_iff.2 fun s hs ↦ by simp [hf.aemeasurable, hs, h _]

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `MeasurableEquiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : AEMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
  calc
    μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _

theorem le_map_apply_image {f : α → β} (hf : AEMeasurable f μ) (s : Set α) :
    μ s ≤ μ.map f (f '' s) :=
  (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
theorem preimage_null_of_map_null {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_map_apply hf s).trans_eq hs

theorem tendsto_ae_map {f : α → β} (hf : AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f)) :=
  fun _ hs => preimage_null_of_map_null hf hs

end Measure

open Measure

theorem mem_ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    s ∈ ae (μ.map f) ↔ f ⁻¹' s ∈ ae μ := by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]

theorem mem_ae_of_mem_ae_map {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : s ∈ ae (μ.map f)) : f ⁻¹' s ∈ ae μ :=
  (tendsto_ae_map hf).eventually hs

theorem ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) : (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_map_iff hf hp

theorem ae_of_ae_map {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop} (h : ∀ᵐ y ∂μ.map f, p y) :
    ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h

theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α → β) (hf : MeasurableSet (range f))
    (μ : Measure α) : ∀ᵐ x ∂μ.map f, x ∈ range f := by
  by_cases h : AEMeasurable f μ
  · change range f ∈ ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} {μ ν : Measure α}

nonrec theorem map_apply (hf : MeasurableEmbedding f) (μ : Measure α) (s : Set β) :
    μ.map f s = μ (f ⁻¹' s) := by
  refine le_antisymm ?_ (le_map_apply hf.measurable.aemeasurable s)
  set t := f '' toMeasurable μ (f ⁻¹' s) ∪ (range f)ᶜ
  have htm : MeasurableSet t :=
    (hf.measurableSet_image.2 <| measurableSet_toMeasurable _ _).union
      hf.measurableSet_range.compl
  have hst : s ⊆ t := by
    rw [subset_union_compl_iff_inter_subset, ← image_preimage_eq_inter_range]
    exact image_mono (subset_toMeasurable _ _)
  have hft : f ⁻¹' t = toMeasurable μ (f ⁻¹' s) := by
    rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      hf.injective.preimage_image]
  calc
    μ.map f s ≤ μ.map f t := by gcongr
    _ = μ (f ⁻¹' s) := by rw [map_apply hf.measurable htm, hft, measure_toMeasurable]

end MeasurableEmbedding

namespace MeasurableEquiv

/-! Interactions of measurable equivalences and measures -/

open Equiv MeasureTheory MeasureTheory.Measure

variable {_ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  f.measurableEmbedding.map_apply _ _

@[simp]
theorem map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ := by
  simp [map_map e.symm.measurable e.measurable]

@[simp]
theorem map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν := by
  simp [map_map e.measurable e.symm.measurable]

theorem map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (Measure.map e) := by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ

theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ μ = ν.map e.symm := by
  rw [← (map_measurableEquiv_injective e).eq_iff, map_map_symm]

theorem map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f (ae μ) = ae (map f μ) := by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]

end MeasurableEquiv
