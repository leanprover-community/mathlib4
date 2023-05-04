/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measure.measure_space
! leanprover-community/mathlib commit 88fcb83fe7996142dfcfe7368d31304a9adc874a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.p4

/-!
# Measure spaces

The definition of a measure and a measure space are in `measure_theory.measure_space_def`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `measure_space_def`, and to
be available in `measure_space` (through `measurable_space`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

We introduce the following typeclasses for measures:

* `is_probability_measure μ`: `μ univ = 1`;
* `is_finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `is_locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/


noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace

open TopologicalSpace (SecondCountableTopology)

open Classical Topology BigOperators Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type _}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]

variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

@[simp]
theorem top_add : ⊤ + μ = ⊤ :=
  top_unique <| Measure.le_add_right le_rfl
#align measure_theory.measure.top_add MeasureTheory.Measure.top_add

@[simp]
theorem add_top : μ + ⊤ = ⊤ :=
  top_unique <| Measure.le_add_left le_rfl
#align measure_theory.measure.add_top MeasureTheory.Measure.add_top

protected theorem zero_le {m0 : MeasurableSpace α} (μ : Measure α) : 0 ≤ μ :=
  bot_le
#align measure_theory.measure.zero_le MeasureTheory.Measure.zero_le

theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.le_iff_eq
#align measure_theory.measure.nonpos_iff_eq_zero' MeasureTheory.Measure.nonpos_iff_eq_zero'

@[simp]
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s hs => trans_rel_left (· ≤ ·) (measure_mono (subset_univ s)) h, fun h =>
    h.symm ▸ rfl⟩
#align measure_theory.measure.measure_univ_eq_zero MeasureTheory.Measure.measure_univ_eq_zero

theorem measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 :=
  measure_univ_eq_zero.not
#align measure_theory.measure.measure_univ_ne_zero MeasureTheory.Measure.measure_univ_ne_zero

@[simp]
theorem measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero
#align measure_theory.measure.measure_univ_pos MeasureTheory.Measure.measure_univ_pos

/-! ### Pushforward and pullback -/


/-- Lift a linear map between `outer_measure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `measure` spaces. -/
def liftLinear {m0 : MeasurableSpace α} (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) : Measure α →ₗ[ℝ≥0∞] Measure β
    where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, eq_self_iff_true,
      toMeasure_apply, add_toOuterMeasure, coe_add, hs]
    --by simp [hs]
  map_smul' c μ := ext fun s hs => by simp [hs]
#align measure_theory.measure.lift_linear MeasureTheory.Measure.liftLinear

@[simp]
theorem liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.lift_linear_apply MeasureTheory.Measure.liftLinear_apply

theorem le_liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s ≤ liftLinear f hf μ s :=
  le_toMeasure_apply _ _ s
#align measure_theory.measure.le_lift_linear_apply MeasureTheory.Measure.le_liftLinear_apply

/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
def mapₗ [MeasurableSpace α] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0
#align measure_theory.measure.mapₗ MeasureTheory.Measure.mapₗ

theorem mapₗ_congr {f g : α → β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, lift_linear_apply, outer_measure.map_apply,
    coe_to_outer_measure] using measure_congr (h.preimage s)
#align measure_theory.measure.mapₗ_congr MeasureTheory.Measure.mapₗ_congr

/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
irreducible_def map [MeasurableSpace α] (f : α → β) (μ : Measure α) : Measure β :=
  if hf : AeMeasurable f μ then mapₗ (hf.mk f) μ else 0
#align measure_theory.measure.map MeasureTheory.Measure.map

include m0

theorem mapₗ_mk_apply_of_aeMeasurable {f : α → β} (hf : AeMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]
#align measure_theory.measure.mapₗ_mk_apply_of_ae_measurable MeasureTheory.Measure.mapₗ_mk_apply_of_aeMeasurable

theorem mapₗ_apply_of_measurable {f : α → β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ := by
  simp only [← mapₗ_mk_apply_of_ae_measurable hf.ae_measurable]
  exact mapₗ_congr hf hf.ae_measurable.measurable_mk hf.ae_measurable.ae_eq_mk
#align measure_theory.measure.mapₗ_apply_of_measurable MeasureTheory.Measure.mapₗ_apply_of_measurable

@[simp]
theorem map_add (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]
#align measure_theory.measure.map_add MeasureTheory.Measure.map_add

@[simp]
theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AeMeasurable f (0 : Measure α) <;> simp [map, hf]
#align measure_theory.measure.map_zero MeasureTheory.Measure.map_zero

theorem map_of_not_aeMeasurable {f : α → β} {μ : Measure α} (hf : ¬AeMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]
#align measure_theory.measure.map_of_not_ae_measurable MeasureTheory.Measure.map_of_not_aeMeasurable

theorem map_congr {f g : α → β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ := by
  by_cases hf : AeMeasurable f μ
  · have hg : AeMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_ae_measurable hf, ← mapₗ_mk_apply_of_ae_measurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AeMeasurable g μ := by simpa [← aeMeasurable_congr h] using hf
    simp [map_of_not_ae_measurable, hf, hg]
#align measure_theory.measure.map_congr MeasureTheory.Measure.map_congr

@[simp]
protected theorem map_smul (c : ℝ≥0∞) (μ : Measure α) (f : α → β) : (c • μ).map f = c • μ.map f :=
  by
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AeMeasurable f μ
  · have hfc : AeMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_ae_measurable hf, ← mapₗ_mk_apply_of_ae_measurable hfc,
      LinearMap.map_smulₛₗ, RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact eventually_eq.trans ((ae_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AeMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_ae_measurable hf, map_of_not_ae_measurable hfc]
#align measure_theory.measure.map_smul MeasureTheory.Measure.map_smul

@[simp]
protected theorem map_smul_nNReal (c : ℝ≥0) (μ : Measure α) (f : α → β) :
    (c • μ).map f = c • μ.map f :=
  μ.map_smul (c : ℝ≥0∞) f
#align measure_theory.measure.map_smul_nnreal MeasureTheory.Measure.map_smul_nNReal

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `measure_theory.measure.le_map_apply` and `measurable_equiv.map_apply`. -/
@[simp]
theorem map_apply_of_aeMeasurable {f : α → β} (hf : AeMeasurable f μ) {s : Set β}
    (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s) := by
  simpa only [mapₗ, hf.measurable_mk, hs, dif_pos, lift_linear_apply, outer_measure.map_apply,
    coe_to_outer_measure, ← mapₗ_mk_apply_of_ae_measurable hf] using
    measure_congr (hf.ae_eq_mk.symm.preimage s)
#align measure_theory.measure.map_apply_of_ae_measurable MeasureTheory.Measure.map_apply_of_aeMeasurable

@[simp]
theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aeMeasurable hf.AeMeasurable hs
#align measure_theory.measure.map_apply MeasureTheory.Measure.map_apply

theorem map_toOuterMeasure {f : α → β} (hf : AeMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim := by
  rw [← trimmed, outer_measure.trim_eq_trim_iff]
  intro s hs
  rw [coe_to_outer_measure, map_apply_of_ae_measurable hf hs, outer_measure.map_apply,
    coe_to_outer_measure]
#align measure_theory.measure.map_to_outer_measure MeasureTheory.Measure.map_toOuterMeasure

@[simp]
theorem map_id : map id μ = μ :=
  ext fun s => map_apply measurable_id
#align measure_theory.measure.map_id MeasureTheory.Measure.map_id

@[simp]
theorem map_id' : map (fun x => x) μ = μ :=
  map_id
#align measure_theory.measure.map_id' MeasureTheory.Measure.map_id'

theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]
#align measure_theory.measure.map_map MeasureTheory.Measure.map_map

@[mono]
theorem map_mono {f : α → β} (h : μ ≤ ν) (hf : Measurable f) : μ.map f ≤ ν.map f := fun s hs => by
  simp [hf.ae_measurable, hs, h _ (hf hs)]
#align measure_theory.measure.map_mono MeasureTheory.Measure.map_mono

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `measurable_equiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : AeMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
  calc
    μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable (μ.map f) s) :=
      measure_mono <| preimage_mono <| subset_toMeasurable _ _
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aeMeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _

#align measure_theory.measure.le_map_apply MeasureTheory.Measure.le_map_apply

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
theorem preimage_null_of_map_null {f : α → β} (hf : AeMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_map_apply hf s).trans_eq hs
#align measure_theory.measure.preimage_null_of_map_null MeasureTheory.Measure.preimage_null_of_map_null

theorem tendsto_ae_map {f : α → β} (hf : AeMeasurable f μ) : Tendsto f μ.ae (μ.map f).ae :=
  fun s hs => preimage_null_of_map_null hf hs
#align measure_theory.measure.tendsto_ae_map MeasureTheory.Measure.tendsto_ae_map

omit m0

/-- Pullback of a `measure` as a linear map. If `f` sends each measurable set to a measurable
set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

If the linearity is not needed, please use `comap` instead, which works for a larger class of
functions. -/
def comapₗ [MeasurableSpace α] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [coe_to_outer_measure, outer_measure.comap_apply, image_inter hf.1, image_diff hf.1]
      apply le_to_outer_measure_caratheodory
      exact hf.2 s hs
  else 0
#align measure_theory.measure.comapₗ MeasureTheory.Measure.comapₗ

theorem comapₗ_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ, dif_pos, lift_linear_apply _ hs, outer_measure.comap_apply, coe_to_outer_measure]
  exact ⟨hfi, hf⟩
#align measure_theory.measure.comapₗ_apply MeasureTheory.Measure.comapₗ_apply

/-- Pullback of a `measure`. If `f` sends each measurable set to a null-measurable set,
then for each measurable set `s` we have `comap f μ s = μ (f '' s)`. -/
def comap [MeasurableSpace α] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [coe_to_outer_measure, outer_measure.comap_apply, image_inter hf.1, image_diff hf.1]
      exact (measure_inter_add_diff₀ _ (hf.2 s hs)).symm
  else 0
#align measure_theory.measure.comap MeasureTheory.Measure.comap

theorem comap_apply₀ [MeasurableSpace α] (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap, dif_pos (And.intro hfi hf)] at hs⊢
  rw [to_measure_apply₀ _ _ hs, outer_measure.comap_apply, coe_to_outer_measure]
#align measure_theory.measure.comap_apply₀ MeasureTheory.Measure.comap_apply₀

theorem le_comap_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (μ : Measure β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) ≤ comap f μ s := by
  rw [comap, dif_pos (And.intro hfi hf)]
  exact le_to_measure_apply _ _ _
#align measure_theory.measure.le_comap_apply MeasureTheory.Measure.le_comap_apply

theorem comap_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).NullMeasurableSet) hs.NullMeasurableSet
#align measure_theory.measure.comap_apply MeasureTheory.Measure.comap_apply

theorem comapₗ_eq_comap {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm
#align measure_theory.measure.comapₗ_eq_comap MeasureTheory.Measure.comapₗ_eq_comap

theorem measure_image_eq_zero_of_comap_eq_zero {β} [MeasurableSpace α] {mβ : MeasurableSpace β}
    (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 :=
  le_antisymm ((le_comap_apply f μ hfi hf s).trans hs.le) (zero_le _)
#align measure_theory.measure.measure_image_eq_zero_of_comap_eq_zero MeasureTheory.Measure.measure_image_eq_zero_of_comap_eq_zero

theorem ae_eq_image_of_ae_eq_comap {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (μ : Measure β) (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [eventually_eq, ae_iff] at hst⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t ∪ t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_set_of_eq, mem_union, mem_diff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t ∪ f '' t \ f '' s := by
    ext1 x
    simp only [eq_iff_iff, mem_set_of_eq, mem_union, mem_diff]
    tauto
  rw [← Set.image_diff hfi, ← Set.image_diff hfi, ← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst
#align measure_theory.measure.ae_eq_image_of_ae_eq_comap MeasureTheory.Measure.ae_eq_image_of_ae_eq_comap

theorem NullMeasurableSet.image {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (μ : Measure β) (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s : Set α} (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ := by
  refine' ⟨to_measurable μ (f '' to_measurable (μ.comap f) s), measurable_set_to_measurable _ _, _⟩
  refine' eventually_eq.trans _ (null_measurable_set.to_measurable_ae_eq _).symm
  swap
  · exact hf _ (measurable_set_to_measurable _ _)
  have h : to_measurable (comap f μ) s =ᵐ[comap f μ] s :=
    @null_measurable_set.to_measurable_ae_eq _ _ (μ.comap f : Measure α) s hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm
#align measure_theory.measure.null_measurable_set.image MeasureTheory.Measure.NullMeasurableSet.image

theorem comap_preimage {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (μ : Measure β)
    {s : Set β} (hf : Injective f) (hf' : Measurable f)
    (h : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ) (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).NullMeasurableSet, image_preimage_eq_inter_range]
#align measure_theory.measure.comap_preimage MeasureTheory.Measure.comap_preimage

