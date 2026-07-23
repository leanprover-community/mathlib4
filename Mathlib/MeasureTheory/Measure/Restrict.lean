/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Comap

/-!
# Restricting a measure to a subset or a subtype

Given a measure `μ` on a type `α` and a subset `s` of `α`, we define a measure `μ.restrict s` as
the restriction of `μ` to `s` (still as a measure on `α`).

We investigate how this notion interacts with usual operations on measures (sum, pushforward,
pullback), and on sets (inclusion, union, Union).

We also study the relationship between the restriction of a measure to a subtype (given by the
pullback under `Subtype.val`) and the restriction to a set as above.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open Set MeasureTheory Measure Filter MeasurableSpace ENNReal Function

variable {R α β δ γ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

/-! ### Restricting a measure -/

/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
@[irreducible]
noncomputable def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measure α →ₗ[ℝ≥0∞] Measure α :=
  liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s ∩ t) = μ (s ∩ t ∩ s') + μ ((s ∩ t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_sdiff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _

/-- Restrict a measure `μ` to a set `s`. -/
noncomputable def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ

@[simp]
theorem restrictₗ_apply {_m0 : MeasurableSpace α} (s : Set α) (μ : Measure α) :
    restrictₗ s μ = μ.restrict s :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- This lemma shows that `restrict` and `toOuterMeasure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) :
    (μ.restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuterMeasure := by
  simp_rw [restrict, restrictₗ, liftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    toMeasure_toOuterMeasure, OuterMeasure.restrict_trim h, μ.trimmed]

theorem restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) : μ.restrict s t = μ (t ∩ s) := by
  rw [restrict, restrictₗ] at ht
  rw [← restrictₗ_apply, restrictₗ, liftLinear_apply₀ _ ht, OuterMeasure.restrict_apply,
    coe_toOuterMeasure]

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `Measure.restrict_apply'`. -/
@[simp]
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s) :=
  restrict_apply₀ ht.nullMeasurableSet

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
theorem restrict_mono' {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s ≤ᵐ[μ] s')
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' :=
  Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ (t ∩ s') := (measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ ≤ ν (t ∩ s') := le_iff'.1 hμν (t ∩ s')
    _ = ν.restrict s' t := (restrict_apply ht).symm

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono, gcongr]
theorem restrict_mono {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s ⊆ s') ⦃μ ν : Measure α⦄
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' :=
  restrict_mono' (ae_of_all _ hs) hμν

theorem restrict_mono_measure {_ : MeasurableSpace α} {μ ν : Measure α} (h : μ ≤ ν) (s : Set α) :
    μ.restrict s ≤ ν.restrict s :=
  restrict_mono subset_rfl h

theorem restrict_mono_set {_ : MeasurableSpace α} (μ : Measure α) {s t : Set α} (h : s ⊆ t) :
    μ.restrict s ≤ μ.restrict t :=
  restrict_mono h le_rfl

theorem restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
  restrict_mono' h (le_refl μ)

theorem restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
  le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`Measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp]
theorem restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t ∩ s) := by
  rw [← toOuterMeasure_apply,
    Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hs,
    OuterMeasure.restrict_apply s t _, toOuterMeasure_apply]

theorem _root_.IsCountablySpanning.null_of_forall_inter_null {C : Set (Set α)}
    (hC : IsCountablySpanning C) (ht : ∀ t ∈ C, μ (s ∩ t) = 0) :
    μ s = 0 := by
  obtain ⟨t, ht1, ht2⟩ := hC
  rw [show s = ⋃ n, s ∩ t n by rw [← inter_iUnion, ht2, inter_univ], measure_iUnion_null_iff]
  exact fun i => ht (t i) (ht1 i)

theorem forall_measure_inter_isCountablySpanning_eq_zero {C : Set (Set α)}
    (hC : IsCountablySpanning C) : (∀ t ∈ C, μ (s ∩ t) = 0) ↔ μ s = 0 where
  mp := hC.null_of_forall_inter_null
  mpr h t _ := measure_inter_null_of_null_left t h

theorem _root_.IsCountablySpanning.null_of_forall_restrict_null {C : Set (Set α)}
    (hC : IsCountablySpanning C) (hm : C ⊆ MeasurableSet) (ht : ∀ t ∈ C, μ.restrict t s = 0) :
    μ s = 0 := by
  rw [← forall_measure_inter_isCountablySpanning_eq_zero hC]
  intro t htc
  simpa [← μ.restrict_apply' (hm htc)] using ht t htc

theorem restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  rw [← restrict_congr_set hs.toMeasurable_ae_eq,
    restrict_apply' (measurableSet_toMeasurable _ _),
    measure_congr ((ae_eq_refl t).inter hs.toMeasurable_ae_eq)]

theorem restrict_le_self : μ.restrict s ≤ μ :=
  Measure.le_iff.2 fun t ht => calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ t := measure_mono inter_subset_left

theorem absolutelyContinuous_restrict : μ.restrict s ≪ μ :=
  Measure.absolutelyContinuous_of_le Measure.restrict_le_self

theorem restrict_absolutelyContinuous_restrict' {s s' : Set α} {μ ν : Measure α}
    (hs : (· ∈ s) ≤ᵐ[μ] (· ∈ s')) (hμν : μ ≪ ν) :
    μ.restrict s ≪ ν.restrict s' := by
  refine .mk fun t ht h ↦ ?_
  rw [restrict_apply ht] at ⊢ h
  have hv : μ (t ∩ s) ≤ μ (t ∩ s') :=
    measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩
  simpa [nonpos_iff_eq_zero, hμν.null_mono, h] using hv

theorem restrict_absolutelyContinuous_restrict {s s' : Set α} {μ ν : Measure α}
    (hs : s ⊆ s') (hμν : μ ≪ ν) : μ.restrict s ≪ ν.restrict s' :=
  restrict_absolutelyContinuous_restrict' (ae_of_all _ hs) hμν

variable (μ)

theorem restrict_eq_self (h : s ⊆ t) : μ.restrict t s = μ s :=
  (le_iff'.1 restrict_le_self s).antisymm <|
    calc
      μ s ≤ μ (toMeasurable (μ.restrict t) s ∩ t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurableSet_toMeasurable _ _), measure_toMeasurable]

@[simp]
theorem restrict_apply_self (s : Set α) : (μ.restrict s) s = μ s :=
  restrict_eq_self μ Subset.rfl

variable {μ}

theorem restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s := by
  rw [restrict_apply MeasurableSet.univ, Set.univ_inter]

theorem le_restrict_apply (s t : Set α) : μ (t ∩ s) ≤ μ.restrict s t :=
  calc
    μ (t ∩ s) = μ.restrict s (t ∩ s) := (restrict_eq_self μ inter_subset_right).symm
    _ ≤ μ.restrict s t := measure_mono inter_subset_left

theorem restrict_apply_le (s t : Set α) : μ.restrict s t ≤ μ t :=
  Measure.le_iff'.1 restrict_le_self _

theorem restrict_apply_superset (h : s ⊆ t) : μ.restrict s t = μ s :=
  ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)

@[simp]
theorem restrict_add {_m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α) :
    (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
  (restrictₗ s).map_add μ ν

@[simp]
theorem restrict_zero {_m0 : MeasurableSpace α} (s : Set α) : (0 : Measure α).restrict s = 0 :=
  (restrictₗ s).map_zero

@[simp]
theorem restrict_smul {_m0 : MeasurableSpace α} {R : Type*} [SMul R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (μ : Measure α) (s : Set α) :
    (c • μ).restrict s = c • μ.restrict s := by
  simpa only [smul_one_smul] using! (restrictₗ s).map_smul (c • 1) μ

theorem restrict_restrict₀ (hs : NullMeasurableSet s (μ.restrict t)) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.nullMeasurableSet.inter hs)]

@[simp]
theorem restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀ hs.nullMeasurableSet

@[simp]
theorem restrict_restrict_of_subset (h : s ⊆ t) : (μ.restrict t).restrict s = μ.restrict s := by
  ext1 u hu
  rw [restrict_apply hu, restrict_apply hu, restrict_eq_self]
  exact inter_subset_right.trans h

theorem restrict_restrict₀' (ht : NullMeasurableSet t μ) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]

theorem restrict_restrict' (ht : MeasurableSet t) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀' ht.nullMeasurableSet

theorem restrict_comm (hs : MeasurableSet s) :
    (μ.restrict t).restrict s = (μ.restrict s).restrict t := by
  rw [restrict_restrict hs, restrict_restrict' hs, inter_comm]

theorem restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply ht]

theorem measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t ∩ s) = 0 :=
  nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)

theorem restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply' hs]

@[simp]
theorem restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 := by
  rw [← measure_univ_eq_zero, restrict_apply_univ]

/-- If `μ s ≠ 0`, then `μ.restrict s ≠ 0`, in terms of `NeZero` instances. -/
instance restrict.neZero [NeZero (μ s)] : NeZero (μ.restrict s) :=
  ⟨mt restrict_eq_zero.mp <| NeZero.ne _⟩

theorem restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0 :=
  restrict_eq_zero.2 h

@[simp]
theorem restrict_empty : μ.restrict ∅ = 0 :=
  restrict_zero_set measure_empty

@[simp]
theorem restrict_univ : μ.restrict univ = μ :=
  ext fun s hs => by simp [hs]

theorem restrict_inter_add_sdiff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s := by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, sdiff_eq]
  exact measure_inter_add_sdiff₀ (u ∩ s) ht

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff₀ := restrict_inter_add_sdiff₀

theorem restrict_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s :=
  restrict_inter_add_sdiff₀ s ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

theorem restrict_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  rw [← restrict_inter_add_sdiff₀ (s ∪ t) ht, union_inter_cancel_right, union_sdiff_right, ←
    restrict_inter_add_sdiff₀ s ht, add_comm, ← add_assoc, add_right_comm]

theorem restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
  restrict_union_add_inter₀ s ht.nullMeasurableSet

theorem restrict_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs

theorem restrict_union₀ (h : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]

theorem restrict_union (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
  restrict_union₀ h.aedisjoint ht.nullMeasurableSet

theorem restrict_union' (h : Disjoint s t) (hs : MeasurableSet s) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  rw [union_comm, restrict_union h.symm hs, add_comm]

@[simp]
theorem restrict_add_restrict_compl (hs : MeasurableSet s) :
    μ.restrict s + μ.restrict sᶜ = μ := by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl, union_compl_self,
    restrict_univ]

@[simp]
theorem restrict_compl_add_restrict (hs : MeasurableSet s) : μ.restrict sᶜ + μ.restrict s = μ := by
  rw [add_comm, restrict_add_restrict_compl hs]

theorem restrict_union_le (s s' : Set α) : μ.restrict (s ∪ s') ≤ μ.restrict s + μ.restrict s' :=
  le_iff.2 fun t ht ↦ by
    simpa [ht, inter_union_distrib_left] using measure_union_le (t ∩ s) (t ∩ s')

theorem restrict_iUnion_apply_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t := by
  simp only [restrict_apply, ht, inter_iUnion]
  exact
    measure_iUnion₀ (hd.mono fun i j h => h.mono inter_subset_right inter_subset_right)
      fun i => ht.nullMeasurableSet.inter (hm i)

theorem restrict_iUnion_apply [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
  restrict_iUnion_apply_ae hd.aedisjoint (fun i => (hm i).nullMeasurableSet) ht

theorem restrict_iUnion_apply_eq_iSup [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s)
    {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t := by
  simp only [restrict_apply ht, inter_iUnion]
  rw [Directed.measure_iUnion]
  exacts [hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]

/-- The restriction of the pushforward measure is the pushforward of the restriction. For a version
assuming only `AEMeasurable`, see `restrict_map_of_aemeasurable`. -/
theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  ext fun t ht => by simp [*, hf ht]

theorem restrict_inter_toMeasurable (h : μ s ≠ ∞) (ht : MeasurableSet t) (hst : s ⊆ t) :
    μ.restrict (t ∩ toMeasurable μ s) = μ.restrict s := by
  ext u hu
  rw [restrict_apply hu, restrict_apply hu, inter_comm t, inter_comm, inter_assoc,
    measure_toMeasurable_inter (ht.inter hu) h]
  congr 1
  grind

theorem restrict_toMeasurable (h : μ s ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s := by
  simpa using restrict_inter_toMeasurable h MeasurableSet.univ (subset_univ _)

theorem restrict_eq_self_of_ae_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄
    (hs : ∀ᵐ x ∂μ, x ∈ s) : μ.restrict s = μ :=
  calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ

theorem restrict_congr_meas (hs : MeasurableSet s) :
    μ.restrict s = ν.restrict s ↔ ∀ t ⊆ s, MeasurableSet t → μ t = ν t :=
  ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts, ← restrict_apply ht, H, restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht, restrict_apply ht, H _ inter_subset_right (ht.inter hs)]⟩

theorem restrict_congr_mono (hs : s ⊆ t) (h : μ.restrict t = ν.restrict t) :
    μ.restrict s = ν.restrict s := by
  rw [← restrict_restrict_of_subset hs, h, restrict_restrict_of_subset hs]

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
theorem restrict_union_congr :
    μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔
      μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t := by
  refine ⟨fun h ↦ ⟨restrict_congr_mono subset_union_left h,
    restrict_congr_mono subset_union_right h⟩, ?_⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u ∩ s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u ∩ s ∪ u ∩ t) = μ (US ∪ u ∩ t) :=
      measure_union_congr_of_subset hsub hμ.le Subset.rfl le_rfl
    _ = μ US + μ ((u ∩ t) \ US) := (measure_add_sdiff hm.nullMeasurableSet _).symm
    _ = restrict μ s u + restrict μ t (u \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hμ, ← inter_comm t, inter_sdiff_assoc]
    _ = restrict ν s u + restrict ν t (u \ US) := by rw [hs, ht]
    _ = ν US + ν ((u ∩ t) \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hν, ← inter_comm t, inter_sdiff_assoc]
    _ = ν (US ∪ u ∩ t) := measure_add_sdiff hm.nullMeasurableSet _
    _ = ν (u ∩ s ∪ u ∩ t) := .symm <| measure_union_congr_of_subset hsub hν.le Subset.rfl le_rfl

theorem restrict_biUnion_finset_congr {s : Finset ι} {t : ι → Set α} :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs =>
    simp only [forall_eq_or_imp, iUnion_iUnion_eq_or_left, Finset.mem_insert]
    rw [restrict_union_congr, ← hs]

theorem restrict_iUnion_congr [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  refine ⟨fun h i => restrict_congr_mono (subset_iUnion _ _) h, fun h => ?_⟩
  ext1 t ht
  have D : Directed (· ⊆ ·) fun t : Finset ι => ⋃ i ∈ t, s i :=
    Monotone.directed_le fun t₁ t₂ ht => biUnion_subset_biUnion_left ht
  rw [iUnion_eq_iUnion_finset]
  simp only [restrict_iUnion_apply_eq_iSup D ht, restrict_biUnion_finset_congr.2 fun i _ => h i]

theorem restrict_biUnion_congr {s : Set ι} {t : ι → Set α} (hc : s.Countable) :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) := by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, SetCoe.forall', restrict_iUnion_congr]

theorem restrict_sUnion_congr {S : Set (Set α)} (hc : S.Countable) :
    μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s := by
  rw [sUnion_eq_biUnion, restrict_biUnion_congr hc]

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
theorem restrict_sInf_eq_sInf_restrict {m0 : MeasurableSpace α} {m : Set (Measure α)}
    (hm : m.Nonempty) (ht : MeasurableSet t) :
    (sInf m).restrict t = sInf ((fun μ : Measure α => μ.restrict t) '' m) := by
  ext1 s hs
  simp_rw [sInf_apply hs, restrict_apply hs, sInf_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_toOuterMeasure_eq_toOuterMeasure_restrict ht, ←
    Set.image_image _ toOuterMeasure, ← OuterMeasure.restrict_sInf_eq_sInf_restrict _ (hm.image _),
    OuterMeasure.restrict_apply]

theorem exists_mem_of_measure_ne_zero_of_ae (hs : μ s ≠ 0) {p : α → Prop}
    (hp : ∀ᵐ x ∂μ.restrict s, p x) : ∃ x, x ∈ s ∧ p x := by
  rw [← μ.restrict_apply_self, ← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists

/-- If a quasi-measure-preserving map `f` maps a set `s` to a set `t`,
then it is quasi-measure-preserving with respect to the restrictions of the measures. -/
theorem QuasiMeasurePreserving.restrict {ν : Measure β} {f : α → β}
    (hf : QuasiMeasurePreserving f μ ν) {t : Set β} (hmaps : MapsTo f s t) :
    QuasiMeasurePreserving f (μ.restrict s) (ν.restrict t) where
  measurable := hf.measurable
  absolutelyContinuous := by
    refine AbsolutelyContinuous.mk fun u hum ↦ ?_
    suffices ν (u ∩ t) = 0 → μ (f ⁻¹' u ∩ s) = 0 by simpa [hum, hf.measurable, hf.measurable hum]
    refine fun hu ↦ measure_mono_null ?_ (hf.preimage_null hu)
    rw [preimage_inter]
    gcongr
    assumption

/-! ### Extensionality results -/

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
theorem ext_iff_of_iUnion_eq_univ [Countable ι] {s : ι → Set α} (hs : ⋃ i, s i = univ) :
    μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_iUnion_congr, hs, restrict_univ, restrict_univ]

alias ⟨_, ext_of_iUnion_eq_univ⟩ := ext_iff_of_iUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `biUnion`). -/
theorem ext_iff_of_biUnion_eq_univ {S : Set ι} {s : ι → Set α} (hc : S.Countable)
    (hs : ⋃ i ∈ S, s i = univ) : μ = ν ↔ ∀ i ∈ S, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_biUnion_congr hc, hs, restrict_univ, restrict_univ]

alias ⟨_, ext_of_biUnion_eq_univ⟩ := ext_iff_of_biUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
theorem ext_iff_of_sUnion_eq_univ {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S = univ) :
    μ = ν ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
  ext_iff_of_biUnion_eq_univ hc <| by rwa [← sUnion_eq_biUnion]

alias ⟨_, ext_of_sUnion_eq_univ⟩ := ext_iff_of_sUnion_eq_univ

theorem ext_of_generateFrom_of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (hc : T.Countable) (h_inter : IsPiSystem S) (hU : ⋃₀ T = univ) (htop : ∀ t ∈ T, μ t ≠ ∞)
    (ST_eq : ∀ t ∈ T, ∀ s ∈ S, μ (s ∩ t) = ν (s ∩ t)) (T_eq : ∀ t ∈ T, μ t = ν t) : μ = ν := by
  refine ext_of_sUnion_eq_univ hc hU fun t ht => ?_
  ext1 u hu
  simp only [restrict_apply hu]
  induction u, hu using induction_on_inter h_gen h_inter with
  | empty => simp only [Set.empty_inter, measure_empty]
  | basic u hu => exact ST_eq _ ht _ hu
  | compl u hu ihu =>
    have := T_eq t ht
    rw [Set.inter_comm] at ihu ⊢
    rwa [← measure_inter_add_sdiff t hu, ← measure_inter_add_sdiff t hu, ← ihu,
      ENNReal.add_right_inj] at this
    exact ne_top_of_le_ne_top (htop t ht) (measure_mono Set.inter_subset_left)
  | iUnion f hfd hfm ihf =>
    simp only [← restrict_apply (hfm _), ← restrict_apply (MeasurableSet.iUnion hfm)] at ihf ⊢
    simp only [measure_iUnion hfd hfm, ihf]

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on an increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
theorem ext_of_generateFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (h_inter : IsPiSystem S) (h_sub : T ⊆ S) (hc : T.Countable) (hU : ⋃₀ T = univ)
    (htop : ∀ s ∈ T, μ s ≠ ∞) (h_eq : ∀ s ∈ S, μ s = ν s) : μ = ν := by
  refine ext_of_generateFrom_of_cover h_gen hc h_inter hU htop ?_ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; rcases (s ∩ t).eq_empty_or_nonempty with H | H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on an increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `iUnion`.
  `FiniteSpanningSetsIn.ext` is a reformulation of this lemma. -/
theorem ext_of_generateFrom_of_iUnion (C : Set (Set α)) (B : ℕ → Set α) (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h1B : ⋃ i, B i = univ) (h2B : ∀ i, B i ∈ C) (hμB : ∀ i, μ (B i) ≠ ∞)
    (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν := by
  refine ext_of_generateFrom_of_cover_subset hA hC ?_ (countable_range B) h1B ?_ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB

@[simp]
theorem restrict_sum (μ : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s :=
  ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp]
theorem restrict_sum_of_countable [Countable ι] (μ : ι → Measure α) (s : Set α) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s := by
  ext t ht
  simp_rw [sum_apply _ ht, restrict_apply ht, sum_apply_of_countable]

lemma AbsolutelyContinuous.restrict (h : μ ≪ ν) (s : Set α) : μ.restrict s ≪ ν.restrict s := by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν ↦ ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν

lemma AbsolutelyContinuous.restrict_of_subset {s s' : Set α} {μ ν : Measure α}
    (hμν : μ.restrict s' ≪ ν.restrict s') (hs : s ⊆ s') :
    μ.restrict s ≪ ν.restrict s := by
  simpa [hs] using hμν.restrict s

theorem restrict_iUnion_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  ext fun t ht => by simp only [sum_apply _ ht, restrict_iUnion_apply_ae hd hm ht]

theorem restrict_iUnion [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  restrict_iUnion_ae hd.aedisjoint fun i => (hm i).nullMeasurableSet

theorem restrict_biUnion {s : ι → Set α} {T : Set ι} (hT : Countable T)
    (hd : T.Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
    μ.restrict (⋃ i ∈ T, s i) = sum fun (i : T) => μ.restrict (s i) := by
  rw [Set.biUnion_eq_iUnion]
  exact restrict_iUnion (fun i j hij ↦ hd i.coe_prop j.coe_prop (Subtype.coe_ne_coe.mpr hij)) (hm ·)

theorem restrict_biUnion_finset {s : ι → Set α} {T : Finset ι}
    (hd : (T : Set ι).Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
    μ.restrict (⋃ i ∈ T, s i) = sum fun (i : T) => μ.restrict (s i) :=
  restrict_biUnion (T := (T : Set ι)) Finite.to_countable hd hm

theorem restrict_iUnion_le [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) ≤ sum fun i => μ.restrict (s i) :=
  le_iff.2 fun t ht ↦ by simpa [ht, inter_iUnion] using measure_iUnion_le (t ∩ s ·)

theorem restrict_biUnion_le {s : ι → Set α} {T : Set ι} (hT : Countable T) :
    μ.restrict (⋃ i ∈ T, s i) ≤ sum fun (i : T) => μ.restrict (s i) :=
  le_iff.2 fun t ht ↦ by simpa [ht, inter_iUnion] using measure_biUnion_le μ hT (t ∩ s ·)

end Measure

@[simp]
theorem ae_restrict_iUnion_eq [Countable ι] (s : ι → Set α) :
    ae (μ.restrict (⋃ i, s i)) = ⨆ i, ae (μ.restrict (s i)) :=
  le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_iUnion_le) <|
    iSup_le fun i => ae_mono <| restrict_mono (subset_iUnion s i) le_rfl

@[simp]
theorem ae_restrict_union_eq (s t : Set α) :
    ae (μ.restrict (s ∪ t)) = ae (μ.restrict s) ⊔ ae (μ.restrict t) := by
  simp [union_eq_iUnion, iSup_bool_eq]

theorem ae_restrict_biUnion_eq (s : ι → Set α) {t : Set ι} (ht : t.Countable) :
    ae (μ.restrict (⋃ i ∈ t, s i)) = ⨆ i ∈ t, ae (μ.restrict (s i)) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion, ae_restrict_iUnion_eq, ← iSup_subtype'']

theorem ae_restrict_biUnion_finset_eq (s : ι → Set α) (t : Finset ι) :
    ae (μ.restrict (⋃ i ∈ t, s i)) = ⨆ i ∈ t, ae (μ.restrict (s i)) :=
  ae_restrict_biUnion_eq s t.countable_toSet

theorem ae_restrict_iUnion_iff [Countable ι] (s : ι → Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ ∀ i, ∀ᵐ x ∂μ.restrict (s i), p x := by simp

theorem ae_restrict_union_iff (s t : Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (s ∪ t), p x) ↔ (∀ᵐ x ∂μ.restrict s, p x) ∧ ∀ᵐ x ∂μ.restrict t, p x := by simp

theorem ae_restrict_biUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_eq s ht, mem_iSup]

@[simp]
theorem ae_restrict_biUnion_finset_iff (s : ι → Set α) (t : Finset ι) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_finset_eq s, mem_iSup]

theorem ae_eq_restrict_iUnion_iff [Countable ι] (s : ι → Set α) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ ∀ i, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup]

theorem ae_eq_restrict_biUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [ae_restrict_biUnion_eq s ht, EventuallyEq, eventually_iSup]

theorem ae_eq_restrict_biUnion_finset_iff (s : ι → Set α) (t : Finset ι) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g :=
  ae_eq_restrict_biUnion_iff s t.countable_toSet f g

open scoped Interval in
theorem ae_restrict_uIoc_eq [LinearOrder α] (a b : α) :
    ae (μ.restrict (Ι a b)) = ae (μ.restrict (Ioc a b)) ⊔ ae (μ.restrict (Ioc b a)) := by
  simp only [uIoc_eq_union, ae_restrict_union_eq]

open scoped Interval in
/-- See also `MeasureTheory.ae_uIoc_iff`. -/
theorem ae_restrict_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ.restrict (Ι a b), P x) ↔
      (∀ᵐ x ∂μ.restrict (Ioc a b), P x) ∧ ∀ᵐ x ∂μ.restrict (Ioc b a), P x := by
  rw [ae_restrict_uIoc_eq, eventually_sup]

theorem ae_restrict_iff₀ {p : α → Prop} (hp : NullMeasurableSet { x | p x } (μ.restrict s)) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff, ← compl_ofPred, Measure.restrict_apply₀ hp.compl]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

theorem ae_restrict_iff {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  ae_restrict_iff₀ hp.nullMeasurableSet

theorem ae_imp_of_ae_restrict {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ.restrict s, p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff] at h ⊢
  simpa [ofPred_and, inter_comm] using measure_inter_eq_zero_of_restrict h

theorem ae_restrict_iff'₀ {p : α → Prop} (hs : NullMeasurableSet s μ) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff, ← compl_ofPred, restrict_apply₀' hs]
  rw [iff_iff_eq]; congr with x; simp [and_comm]

theorem ae_restrict_iff' {p : α → Prop} (hs : MeasurableSet s) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  ae_restrict_iff'₀ hs.nullMeasurableSet

theorem _root_.Filter.EventuallyEq.restrict {f g : α → δ} {s : Set α} (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.restrict s] g := by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine hfg.filter_mono ?_
  rw [Measure.ae_le_iff_absolutelyContinuous]
  exact absolutelyContinuous_restrict

theorem ae_restrict_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  (ae_restrict_iff'₀ hs).2 (Filter.Eventually.of_forall fun _ => id)

theorem ae_restrict_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  ae_restrict_mem₀ hs.nullMeasurableSet

theorem ae_restrict_of_forall_mem {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} (h : ∀ x ∈ s, p x) : ∀ᵐ (x : α) ∂μ.restrict s, p x :=
  (ae_restrict_mem hs).mono h

lemma _root_.Set.EqOn.aeEq_restrict {α β : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → β} (h : s.EqOn f g) (hs : MeasurableSet s) : f =ᵐ[μ.restrict s] g :=
  ae_restrict_of_forall_mem hs h

theorem ae_restrict_of_ae {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono Measure.restrict_le_self)

theorem ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α → Prop} (hst : s ⊆ t)
    (h : ∀ᵐ x ∂μ.restrict t, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))

theorem ae_of_ae_restrict_of_ae_restrict_compl (t : Set α) {p : α → Prop}
    (ht : ∀ᵐ x ∂μ.restrict t, p x) (htc : ∀ᵐ x ∂μ.restrict tᶜ, p x) : ∀ᵐ x ∂μ, p x :=
  nonpos_iff_eq_zero.1 <|
    calc
      μ { x | ¬p x } ≤ μ ({ x | ¬p x } ∩ t) + μ ({ x | ¬p x } ∩ tᶜ) :=
        measure_le_inter_add_sdiff _ _ _
      _ ≤ μ.restrict t { x | ¬p x } + μ.restrict tᶜ { x | ¬p x } :=
        add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
      _ = 0 := by rw [ae_iff.1 ht, ae_iff.1 htc, zero_add]

theorem mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α → β} (hs : MeasurableSet s) :
    t ∈ Filter.map f (ae (μ.restrict s)) ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0 := by
  rw [mem_map, mem_ae_iff, Measure.restrict_apply' hs]

@[simp] theorem ae_add_measure_iff {p : α → Prop} {ν} :
    (∀ᵐ x ∂μ + ν, p x) ↔ (∀ᵐ x ∂μ, p x) ∧ ∀ᵐ x ∂ν, p x :=
  add_eq_zero

/-- See also `Measure.ae_sum_iff`. -/
@[simp] lemma ae_finsetSum_measure_iff {p : α → Prop} {s : Finset ι} {μ : ι → Measure α} :
    (∀ᵐ x ∂∑ i ∈ s, μ i, p x) ↔ ∀ i ∈ s, ∀ᵐ x ∂μ i, p x := by
  induction s using Finset.cons_induction <;> simp [*]

theorem ae_eq_comp' {ν : Measure β} {f : α → β} {g g' : β → δ} (hf : AEMeasurable f μ)
    (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
  (tendsto_ae_map hf).mono_right h2.ae_le h

theorem Measure.QuasiMeasurePreserving.ae_eq_comp {ν : Measure β} {f : α → β} {g g' : β → δ}
    (hf : QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf.aemeasurable h hf.absolutelyContinuous

theorem ae_eq_comp {f : α → β} {g g' : β → δ} (hf : AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') :
    g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf h AbsolutelyContinuous.rfl

@[to_additive]
theorem div_ae_eq_one {β} [Group β] (f g : α → β) : f / g =ᵐ[μ] 1 ↔ f =ᵐ[μ] g := by
  refine ⟨fun h ↦ h.mono fun x hx ↦ ?_, fun h ↦ h.mono fun x hx ↦ ?_⟩
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one] at hx
  · rwa [Pi.div_apply, Pi.one_apply, div_eq_one]

@[to_additive sub_nonneg_ae]
lemma one_le_div_ae {β : Type*} [Group β] [LE β] [MulRightMono β] (f g : α → β) :
    1 ≤ᵐ[μ] g / f ↔ f ≤ᵐ[μ] g := by
  refine ⟨fun h ↦ h.mono fun a ha ↦ ?_, fun h ↦ h.mono fun a ha ↦ ?_⟩
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div'] at ha
  · rwa [Pi.one_apply, Pi.div_apply, one_le_div']

theorem le_ae_restrict : ae μ ⊓ 𝓟 s ≤ ae (μ.restrict s) := fun _s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp]
theorem ae_restrict_eq (hs : MeasurableSet s) : ae (μ.restrict s) = ae μ ⊓ 𝓟 s := by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_ofPred,
    Classical.not_imp, fun a => and_comm (a := a ∈ s) (b := a ∉ t)]
  rfl

lemma ae_restrict_le : ae (μ.restrict s) ≤ ae μ :=
  ae_mono restrict_le_self

theorem ae_restrict_eq_bot {s} : ae (μ.restrict s) = ⊥ ↔ μ s = 0 :=
  ae_eq_bot.trans restrict_eq_zero

theorem ae_restrict_neBot {s} : (ae <| μ.restrict s).NeBot ↔ μ s ≠ 0 :=
  neBot_iff.trans ae_restrict_eq_bot.not

theorem self_mem_ae_restrict {s} (hs : MeasurableSet s) : s ∈ ae (μ.restrict s) := by
  simp only [ae_restrict_eq hs, mem_principal, mem_inf_iff]
  exact ⟨_, univ_mem, s, Subset.rfl, (univ_inter s).symm⟩

/-- If two measurable sets are `ae_eq` then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
theorem ae_restrict_of_ae_eq_of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) → ∀ᵐ x ∂μ.restrict t, p x := by simp [Measure.restrict_congr_set hst]

/-- If two measurable sets are `ae_eq` then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
theorem ae_restrict_congr_set {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ.restrict t, p x :=
  ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩

lemma NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const
    {β : Type*} [MeasurableSpace β] {b : β} {f : α → β} {s : Set α}
    (f_mble : NullMeasurable f (μ.restrict s)) (hs : f =ᵐ[Measure.restrict μ sᶜ] (fun _ ↦ b))
    {t : Set β} (t_mble : MeasurableSet t) (ht : b ∉ t) :
    μ (f ⁻¹' t) = μ.restrict s (f ⁻¹' t) := by
  rw [Measure.restrict_apply₀ (f_mble t_mble)]
  rw [EventuallyEq, ae_iff, Measure.restrict_apply₀] at hs
  · apply le_antisymm _ (measure_mono inter_subset_left)
    apply (measure_mono (Eq.symm (inter_union_compl (f ⁻¹' t) s)).le).trans
    apply (measure_union_le _ _).trans
    suffices μ ((f ⁻¹' t) ∩ sᶜ) = 0 by simp [this]
    rw [← nonpos_iff_eq_zero, ← hs]
    gcongr
    exact fun x hx hfx ↦ ht (hfx ▸ hx)
  · exact NullMeasurableSet.of_null hs

lemma nullMeasurableSet_restrict (hs : NullMeasurableSet s μ) {t : Set α} :
    NullMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet (t ∩ s) μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨t', -, ht', t't⟩ : ∃ t' ⊇ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
      h.exists_measurable_superset_ae_eq
    have A : (t' ∩ s : Set α) =ᵐ[μ] (t ∩ s : Set α) := by
      have : ∀ᵐ x ∂μ, x ∈ s → (x ∈ t') = (x ∈ t) :=
        (ae_restrict_iff'₀ hs).1 t't
      filter_upwards [this] with y hy
      change (y ∈ t' ∩ s) = (y ∈ t ∩ s)
      simpa only [eq_iff_iff, mem_inter_iff, and_congr_left_iff] using hy
    obtain ⟨s', -, hs', s's⟩ : ∃ s' ⊇ s, MeasurableSet s' ∧ s' =ᵐ[μ] s :=
      hs.exists_measurable_superset_ae_eq
    have B : (t' ∩ s' : Set α) =ᵐ[μ] (t' ∩ s : Set α) :=
      ae_eq_set_inter (EventuallyEq.refl _ _) s's
    exact (ht'.inter hs').nullMeasurableSet.congr (B.trans A)
  · have A : NullMeasurableSet (t \ s) (μ.restrict s) := by
      apply NullMeasurableSet.of_null
      rw [Measure.restrict_apply₀' hs]
      simp
    have B : NullMeasurableSet (t ∩ s) (μ.restrict s) :=
      h.mono_ac absolutelyContinuous_restrict
    simpa using A.union B

lemma nullMeasurableSet_restrict_of_subset {t : Set α} (ht : t ⊆ s) :
    NullMeasurableSet t (μ.restrict s) ↔ NullMeasurableSet t μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono_ac absolutelyContinuous_restrict⟩
  obtain ⟨t', t'_subs, ht', t't⟩ : ∃ t' ⊆ t, MeasurableSet t' ∧ t' =ᵐ[μ.restrict s] t :=
    h.exists_measurable_subset_ae_eq
  have : ∀ᵐ x ∂μ, x ∈ s → (x ∈ t' ↔ x ∈ t) := by
    apply ae_imp_of_ae_restrict
    filter_upwards [t't] with x hx using by simpa using! hx
  have : t' =ᵐ[μ] t := by
    filter_upwards [this] with x hx
    change (x ∈ t') = (x ∈ t)
    simp only [eq_iff_iff]
    tauto
  exact ht'.nullMeasurableSet.congr this

namespace Measure

section Subtype

/-! ### Subtype of a measure space -/

section ComapAnyMeasure

theorem MeasurableSet.nullMeasurableSet_subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : MeasurableSet t) : NullMeasurableSet ((↑) '' t) μ := by
  rw [Subtype.instMeasurableSpace, comap_eq_generateFrom] at ht
  induction t, ht using generateFrom_induction with
  | hC t' ht' =>
    obtain ⟨s', hs', rfl⟩ := ht'
    rw [Subtype.image_preimage_coe]
    exact hs.inter (hs'.nullMeasurableSet)
  | empty => simp only [image_empty, nullMeasurableSet_empty]
  | compl t' _ ht' =>
    simp only [← range_sdiff_image Subtype.coe_injective, Subtype.range_coe_subtype, ofPred_mem_eq]
    exact hs.diff ht'
  | iUnion f _ hf =>
    rw [image_iUnion]
    exact .iUnion hf

theorem NullMeasurableSet.subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t (μ.comap Subtype.val)) : NullMeasurableSet (((↑) : s → α) '' t) μ :=
  NullMeasurableSet.image _ μ Subtype.coe_injective
    (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs) ht

theorem measure_subtype_coe_le_comap (hs : NullMeasurableSet s μ) (t : Set s) :
    μ (((↑) : s → α) '' t) ≤ μ.comap Subtype.val t :=
  le_comap_apply _ _ Subtype.coe_injective (fun _ =>
    MeasurableSet.nullMeasurableSet_subtype_coe hs) _

theorem measure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) {t : Set s}
    (ht : μ.comap Subtype.val t = 0) : μ (((↑) : s → α) '' t) = 0 :=
  eq_bot_iff.mpr <| (measure_subtype_coe_le_comap hs t).trans ht.le

end ComapAnyMeasure

section MeasureSpace

variable {u : Set δ} [MeasureSpace δ] {p : δ → Prop}

/-- In a measure space, one can restrict the measure to a subtype to get a new measure space.
Not registered as an instance, as there are other natural choices such as the normalized restriction
for a probability measure, or the subspace measure when restricting to a vector subspace. Enable
locally if needed with `attribute [local instance] Measure.Subtype.measureSpace`. -/
@[instance_reducible]
noncomputable def Subtype.measureSpace : MeasureSpace (Subtype p) where
  volume := Measure.comap Subtype.val volume

attribute [local instance] Subtype.measureSpace

theorem Subtype.volume_def : (volume : Measure u) = volume.comap Subtype.val :=
  rfl

theorem Subtype.volume_univ (hu : NullMeasurableSet u) : volume (univ : Set u) = volume u := by
  rw [Subtype.volume_def, comap_apply₀ _ _ _ _ MeasurableSet.univ.nullMeasurableSet]
  · simp only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => MeasurableSet.nullMeasurableSet_subtype_coe hu

theorem volume_subtype_coe_le_volume (hu : NullMeasurableSet u) (t : Set u) :
    volume (((↑) : u → δ) '' t) ≤ volume t :=
  measure_subtype_coe_le_comap hu t

theorem volume_subtype_coe_eq_zero_of_volume_eq_zero (hu : NullMeasurableSet u) {t : Set u}
    (ht : volume t = 0) : volume (((↑) : u → δ) '' t) = 0 :=
  measure_subtype_coe_eq_zero_of_comap_eq_zero hu ht

end MeasureSpace

end Subtype

end Measure

end MeasureTheory

open MeasureTheory Measure

namespace MeasurableEmbedding

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β}

section
variable (hf : MeasurableEmbedding f)
include hf

theorem map_comap (μ : Measure β) : (comap f μ).map f = μ.restrict (range f) := by
  ext1 t ht
  rw [hf.map_apply, comap_apply f hf.injective hf.measurableSet_image' _ (hf.measurable ht),
    image_preimage_eq_inter_range, Measure.restrict_apply ht]

theorem comap_apply (μ : Measure β) (s : Set α) : comap f μ s = μ (f '' s) :=
  calc
    comap f μ s = comap f μ (f ⁻¹' f '' s) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap, restrict_apply' hf.measurableSet_range,
        inter_eq_self_of_subset_left (image_subset_range _ _)]

theorem comap_map (μ : Measure α) : (map f μ).comap f = μ := by
  ext t _
  rw [hf.comap_apply, hf.map_apply, preimage_image_eq _ hf.injective]

theorem ae_map_iff {p : β → Prop} {μ : Measure α} : (∀ᵐ x ∂μ.map f, p x) ↔ ∀ᵐ x ∂μ, p (f x) := by
  simp only [ae_iff, hf.map_apply, preimage_ofPred_eq]

theorem restrict_map (μ : Measure α) (s : Set β) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]

protected theorem comap_preimage (μ : Measure β) (s : Set β) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [← hf.map_apply, hf.map_comap, restrict_apply' hf.measurableSet_range]

lemma comap_restrict (μ : Measure β) (s : Set β) :
    (μ.restrict s).comap f = (μ.comap f).restrict (f ⁻¹' s) := by
  ext t ht
  rw [Measure.restrict_apply ht, comap_apply hf, comap_apply hf,
    Measure.restrict_apply (hf.measurableSet_image.2 ht), image_inter_preimage]

lemma restrict_comap (μ : Measure β) (s : Set α) :
    (μ.comap f).restrict s = (μ.restrict (f '' s)).comap f := by
  rw [comap_restrict hf, preimage_image_eq _ hf.injective]

end

theorem _root_.MeasurableEquiv.restrict_map (e : α ≃ᵐ β) (μ : Measure α) (s : Set β) :
    (μ.map e).restrict s = (μ.restrict <| e ⁻¹' s).map e :=
  e.measurableEmbedding.restrict_map _ _

lemma _root_.MeasurableEquiv.comap_apply (e : α ≃ᵐ β) (μ : Measure β) (s : Set α) :
    comap e μ s = μ (e.symm ⁻¹' s) := by
  rw [e.measurableEmbedding.comap_apply, e.image_eq_preimage_symm]

end MeasurableEmbedding

lemma MeasureTheory.Measure.map_eq_comap {_ : MeasurableSpace α} {_ : MeasurableSpace β} {f : α → β}
    {g : β → α} {μ : Measure α} (hf : Measurable f) (hg : MeasurableEmbedding g)
    (hμg : ∀ᵐ a ∂μ, a ∈ Set.range g) (hfg : ∀ a, f (g a) = a) : μ.map f = μ.comap g := by
  ext s hs
  rw [map_apply hf hs, hg.comap_apply, ← measure_sdiff_null hμg]
  congr
  simp
  grind

section Subtype

theorem comap_subtype_coe_apply {_m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (t : Set s) : comap (↑) μ t = μ ((↑) '' t) :=
  (MeasurableEmbedding.subtype_coe hs).comap_apply _ _

theorem map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) : (comap (↑) μ).map ((↑) : s → α) = μ.restrict s := by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap, Subtype.range_coe]

theorem ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ (x : s) ∂comap ((↑) : s → α) μ, p x := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_map_iff]

variable [MeasureSpace α] {s t : Set α}

/-!
### Volume on `s : Set α`

Note the instance is provided earlier as `Subtype.measureSpace`.
-/
attribute [local instance] Subtype.measureSpace

theorem volume_set_coe_def (s : Set α) : (volume : Measure s) = comap ((↑) : s → α) volume :=
  rfl

theorem MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) :
    volume.map ((↑) : s → α) = restrict volume s := by
  rw [volume_set_coe_def, (MeasurableEmbedding.subtype_coe hs).map_comap volume, Subtype.range_coe]

theorem volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) :
    volume ((↑) '' t : Set α) = volume t :=
  (comap_subtype_coe_apply hs volume t).symm

@[simp]
theorem volume_preimage_coe (hs : NullMeasurableSet s) (ht : MeasurableSet t) :
    volume (((↑) : s → α) ⁻¹' t) = volume (t ∩ s) := by
  rw [volume_set_coe_def,
    comap_apply₀ _ _ Subtype.coe_injective
      (fun h => MeasurableSet.nullMeasurableSet_subtype_coe hs)
      (measurable_subtype_coe ht).nullMeasurableSet,
    image_preimage_eq_inter_range, Subtype.range_coe]

end Subtype

section Piecewise

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f g : α → β}

theorem piecewise_ae_eq_restrict [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict s] f := by
  rw [ae_restrict_eq hs]
  exact (piecewise_eqOn s f g).eventuallyEq.filter_mono inf_le_right

theorem piecewise_ae_eq_restrict_compl [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict sᶜ] g := by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eqOn_compl s f g).eventuallyEq.filter_mono inf_le_right

theorem piecewise_ae_eq_of_ae_eq_set [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g :=
  hst.mem_iff.mono fun x hx => by simp [piecewise, hx]

end Piecewise

section IndicatorFunction

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f : α → β}

theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set β}
    (ht : (0 : β) ∈ t) (hs : MeasurableSet s) :
    t ∈ Filter.map (s.indicator f) (ae μ) ↔ t ∈ Filter.map f (ae <| μ.restrict s) := by
  classical
  simp_rw [mem_map, mem_ae_iff]
  rw [Measure.restrict_apply' hs, Set.indicator_preimage, Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0
  simp only [ht, ← Set.compl_eq_univ_sdiff, compl_compl, if_true,
    Set.preimage_const]
  simp_rw [Set.union_inter_distrib_right, Set.compl_inter_self s, Set.union_empty]

theorem mem_map_indicator_ae_iff_of_zero_notMem [Zero β] {t : Set β} (ht : (0 : β) ∉ t) :
    t ∈ Filter.map (s.indicator f) (ae μ) ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0 := by
  classical
  rw [mem_map, mem_ae_iff, Set.indicator_preimage, Set.ite, Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_sdiff, Set.inter_univ, Set.preimage_const]

theorem map_restrict_ae_le_map_indicator_ae [Zero β] (hs : MeasurableSet s) :
    Filter.map f (ae <| μ.restrict s) ≤ Filter.map (s.indicator f) (ae μ) := by
  intro t
  by_cases ht : (0 : β) ∈ t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_notMem ht, mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null (Set.inter_subset_left.trans Set.subset_union_left) h

variable [Zero β]

theorem indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict s] f := by
  classical exact piecewise_ae_eq_restrict hs

theorem indicator_ae_eq_restrict_compl (hs : MeasurableSet s) :
    indicator s f =ᵐ[μ.restrict sᶜ] 0 := by
  classical exact piecewise_ae_eq_restrict_compl hs

theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict sᶜ] 0) : s.indicator f =ᵐ[μ] f := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, imp_true_iff]

theorem indicator_ae_eq_zero_of_restrict_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict s] 0) : s.indicator f =ᵐ[μ] 0 := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hxs]

theorem indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f := by
  classical exact piecewise_ae_eq_of_ae_eq_set hst

theorem indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0 :=
  indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)

theorem ae_eq_restrict_iff_indicator_ae_eq {g : α → β} (hs : MeasurableSet s) :
    f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x ∈ s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx

end IndicatorFunction

section Sum

open Finset in
/-- An upper bound on a sum of restrictions of a measure `μ`. This can be used to compare
`∫ x ∈ X, f x ∂μ` with `∑ i, ∫ x ∈ (s i), f x ∂μ`, where `s` is a cover of `X`. -/
lemma MeasureTheory.Measure.sum_restrict_le {_ : MeasurableSpace α}
    {μ : Measure α} {s : ι → Set α} {M : ℕ} (hs_meas : ∀ i, MeasurableSet (s i))
    (hs : ∀ y, {i | y ∈ s i}.encard ≤ M) :
    Measure.sum (fun i ↦ μ.restrict (s i)) ≤ M • μ.restrict (⋃ i, s i) := by
  classical
  refine le_iff.mpr (fun t ht ↦ le_of_eq_of_le (sum_apply _ ht) ?_)
  refine ENNReal.summable.tsum_le_of_sum_le (fun F ↦ ?_)
  -- `P` is a partition of `⋃ i ∈ F, s i` indexed by `C ∈ Cs` (nonempty subsets of `F`).
  -- `P` is a partition of `s i` when restricted to `C ∈ G i` (subsets of `F` containing `i`).
  let P (C : Finset ι) := (⋂ i ∈ C, s i) ∩ (⋂ i ∈ (F \ C), (s i)ᶜ)
  let Cs := F.powerset \ {∅}
  let G (i : ι) := { C | C ∈ F.powerset ∧ i ∈ C }
  have P_meas C : MeasurableSet (P C) :=
    measurableSet_biInter C (fun i _ ↦ hs_meas i) |>.inter <|
      measurableSet_biInter _ (fun i _ ↦ (hs_meas i).compl)
  have P_cover {i : ι} (hi : i ∈ F) : s i ⊆ ⋃ C ∈ G i, P C := by
    refine fun x hx ↦ Set.mem_biUnion (x := F.filter (x ∈ s ·)) ?_ ?_
    · exact ⟨Finset.mem_powerset.mpr (filter_subset _ F), mem_filter.mpr ⟨hi, hx⟩⟩
    · simp_rw [P, mem_inter_iff, mem_iInter, Finset.mem_sdiff, mem_filter]; tauto
  have iUnion_P : ⋃ C ∈ Cs, P C ⊆ ⋃ i, s i := by
    intro x hx
    simp_rw [Cs, Finset.mem_sdiff, mem_iUnion] at hx
    have ⟨C, ⟨_, C_nonempty⟩, hxC⟩ := hx
    have ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr <| Finset.notMem_singleton.mp C_nonempty
    exact ⟨s i, ⟨i, rfl⟩, hxC.1 (s i) ⟨i, by simp [hi]⟩⟩
  have P_subset_s {i : ι} {C : Finset ι} (hiC : i ∈ C) : P C ⊆ s i := by
    intro x hx
    simp only [P, mem_inter_iff, mem_iInter] at hx
    exact hx.1 i hiC
  have mem_C {i} (hi : i ∈ F) {C : Finset ι} {x : α} (hx : x ∈ P C) (hxs : x ∈ s i) : i ∈ C := by
    rw [mem_inter_iff, mem_iInter₂, mem_iInter₂] at hx
    exact of_not_not fun h ↦ hx.2 i (mem_sdiff.mpr ⟨hi, h⟩) hxs
  have C_subset_C {C₁ C₂} (hC₁ : C₁ ∈ Cs) {x : α} (hx : x ∈ P C₁ ∩ P C₂) : C₁ ⊆ C₂ :=
    fun i hi ↦ mem_C (mem_powerset.mp (sdiff_subset hC₁) hi) hx.2 <| P_subset_s hi hx.1
  calc ∑ i ∈ F, (μ.restrict (s i)) t
    _ ≤ ∑ i ∈ F, Measure.sum (fun (C : G i) ↦ μ.restrict (P C)) t :=
      F.sum_le_sum fun i hi ↦ (restrict_mono_set μ (P_cover hi) t).trans <|
        restrict_biUnion_le ((finite_toSet F.powerset).subset (sep_subset _ _)).countable t
    _ = ∑ i ∈ F, ∑' (C : G i), μ.restrict (P C) t := by simp_rw [Measure.sum_apply _ ht]
    _ = ∑' C, ∑ i ∈ F, (G i).indicator (fun C ↦ μ.restrict (P C) t) C := by
      rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
      congr with i
      rw [tsum_subtype (G i) (fun C ↦ (μ.restrict (P C)) t)]
    _ = ∑ C ∈ Cs, ∑ i ∈ F, (C : Set ι).indicator (fun _ ↦ (μ.restrict (P C)) t) i := by
      rw [sum_eq_tsum_indicator]
      congr with C
      by_cases hC : C ∈ F.powerset <;> by_cases hC' : C = ∅ <;>
        simp [hC, hC', Cs, G, indicator, -Finset.mem_powerset, -coe_powerset]
    _ = ∑ C ∈ Cs, {a ∈ F | a ∈ C}.card • μ.restrict (P C) t := by simp [indicator]; rfl
    _ ≤ ∑ C ∈ Cs, M • μ.restrict (P C) t := by
      refine sum_le_sum fun C hC ↦ ?_
      by_cases hPC : P C = ∅
      · simp [hPC]
      have hCM : (C : Set ι).encard ≤ M :=
        have ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hPC
        (encard_mono (mem_iInter₂.mp hx.1)).trans (hs x)
      exact nsmul_le_nsmul_left zero_le <| calc {a ∈ F | a ∈ C}.card
        _ ≤ C.card := card_mono <| fun i hi ↦ (F.mem_filter.mp hi).2
        _ = (C : Set ι).ncard := (ncard_coe_finset C).symm
        _ ≤ M := ENat.toNat_le_of_le_natCast hCM
    _ = M • (μ.restrict (⋃ C ∈ Cs, (P C)) t) := by
      rw [← smul_sum, ← Cs.tsum_subtype, μ.restrict_biUnion_finset _ P_meas, Measure.sum_apply _ ht]
      refine fun C₁ hC₁ C₂ hC₂ hC ↦ Set.disjoint_iff.mpr fun x hx ↦ hC <| ?_
      exact subset_antisymm (C_subset_C hC₁ hx) (C_subset_C hC₂ (Set.inter_comm _ _ ▸ hx))
    _ ≤ (M • μ.restrict (⋃ i, s i)) t := by
      rw [Measure.smul_apply]
      exact nsmul_le_nsmul_right (μ.restrict_mono_set iUnion_P t) M

end Sum
