/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Restricting a measure to a subset or a subtype

Given a measure `μ` on a type `α` and a subset `s` of `α`, we define a measure `μ.restrict s` as
the restriction of `μ` to `s` (still as a measure on `α`).

We investigate how this notion interacts with usual operations on measures (sum, pushforward,
pullback), and on sets (inclusion, union, Union).

We also study the relationship between the restriction of a measure to a subtype (given by the
pullback under `Subtype.val`) and the restriction to a set as above.
-/

open scoped ENNReal NNReal Topology BigOperators
open Set MeasureTheory Measure Filter MeasurableSpace ENNReal Function

variable {R α β δ γ ι : Type*}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]

variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

/-! ### Restricting a measure -/

/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
noncomputable def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measure α →ₗ[ℝ≥0∞] Measure α :=
  liftLinear (OuterMeasure.restrict s) fun μ s' hs' t => by
    suffices μ (s ∩ t) = μ (s ∩ t ∩ s') + μ ((s ∩ t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_diff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _
#align measure_theory.measure.restrictₗ MeasureTheory.Measure.restrictₗ

/-- Restrict a measure `μ` to a set `s`. -/
noncomputable def restrict {_m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ
#align measure_theory.measure.restrict MeasureTheory.Measure.restrict

@[simp]
theorem restrictₗ_apply {_m0 : MeasurableSpace α} (s : Set α) (μ : Measure α) :
    restrictₗ s μ = μ.restrict s :=
  rfl
#align measure_theory.measure.restrictₗ_apply MeasureTheory.Measure.restrictₗ_apply

/-- This lemma shows that `restrict` and `toOuterMeasure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) :
    (μ.restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuterMeasure := by
  simp_rw [restrict, restrictₗ, liftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    toMeasure_toOuterMeasure, OuterMeasure.restrict_trim h, μ.trimmed]
#align measure_theory.measure.restrict_to_outer_measure_eq_to_outer_measure_restrict MeasureTheory.Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict

theorem restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) : μ.restrict s t = μ (t ∩ s) :=
  (toMeasure_apply₀ _ (fun s' hs' t => by
    suffices μ (s ∩ t) = μ (s ∩ t ∩ s') + μ ((s ∩ t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_diff_assoc]
    exact le_toOuterMeasure_caratheodory _ _ hs' _) ht).trans <| by
    simp only [OuterMeasure.restrict_apply]
#align measure_theory.measure.restrict_apply₀ MeasureTheory.Measure.restrict_apply₀

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `Measure.restrict_apply'`. -/
@[simp]
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s) :=
  restrict_apply₀ ht.nullMeasurableSet
#align measure_theory.measure.restrict_apply MeasureTheory.Measure.restrict_apply

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
theorem restrict_mono' {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s ≤ᵐ[μ] s')
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' := fun t ht =>
  calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ (t ∩ s') := (measure_mono_ae <| hs.mono fun _x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ ≤ ν (t ∩ s') := (le_iff'.1 hμν (t ∩ s'))
    _ = ν.restrict s' t := (restrict_apply ht).symm

#align measure_theory.measure.restrict_mono' MeasureTheory.Measure.restrict_mono'

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono]
theorem restrict_mono {_m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s ⊆ s') ⦃μ ν : Measure α⦄
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' :=
  restrict_mono' (ae_of_all _ hs) hμν
#align measure_theory.measure.restrict_mono MeasureTheory.Measure.restrict_mono

theorem restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
  restrict_mono' h (le_refl μ)
#align measure_theory.measure.restrict_mono_ae MeasureTheory.Measure.restrict_mono_ae

theorem restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
  le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)
#align measure_theory.measure.restrict_congr_set MeasureTheory.Measure.restrict_congr_set

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`Measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp]
theorem restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t ∩ s) := by
  rw [Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict hs,
    OuterMeasure.restrict_apply s t _]
#align measure_theory.measure.restrict_apply' MeasureTheory.Measure.restrict_apply'

theorem restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  rw [← restrict_congr_set hs.toMeasurable_ae_eq,
    restrict_apply' (measurableSet_toMeasurable _ _),
    measure_congr ((ae_eq_refl t).inter hs.toMeasurable_ae_eq)]
#align measure_theory.measure.restrict_apply₀' MeasureTheory.Measure.restrict_apply₀'

theorem restrict_le_self : μ.restrict s ≤ μ := fun t ht =>
  calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ t := measure_mono <| inter_subset_left t s
#align measure_theory.measure.restrict_le_self MeasureTheory.Measure.restrict_le_self

variable (μ)

theorem restrict_eq_self (h : s ⊆ t) : μ.restrict t s = μ s :=
  (le_iff'.1 restrict_le_self s).antisymm <|
    calc
      μ s ≤ μ (toMeasurable (μ.restrict t) s ∩ t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurableSet_toMeasurable _ _), measure_toMeasurable]
#align measure_theory.measure.restrict_eq_self MeasureTheory.Measure.restrict_eq_self

@[simp]
theorem restrict_apply_self (s : Set α) : (μ.restrict s) s = μ s :=
  restrict_eq_self μ Subset.rfl
#align measure_theory.measure.restrict_apply_self MeasureTheory.Measure.restrict_apply_self

variable {μ}

theorem restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s := by
  rw [restrict_apply MeasurableSet.univ, Set.univ_inter]
#align measure_theory.measure.restrict_apply_univ MeasureTheory.Measure.restrict_apply_univ

theorem le_restrict_apply (s t : Set α) : μ (t ∩ s) ≤ μ.restrict s t :=
  calc
    μ (t ∩ s) = μ.restrict s (t ∩ s) := (restrict_eq_self μ (inter_subset_right _ _)).symm
    _ ≤ μ.restrict s t := measure_mono (inter_subset_left _ _)
#align measure_theory.measure.le_restrict_apply MeasureTheory.Measure.le_restrict_apply

theorem restrict_apply_le (s t : Set α) : μ.restrict s t ≤ μ t :=
  Measure.le_iff'.1 restrict_le_self _

theorem restrict_apply_superset (h : s ⊆ t) : μ.restrict s t = μ s :=
  ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)
#align measure_theory.measure.restrict_apply_superset MeasureTheory.Measure.restrict_apply_superset

@[simp]
theorem restrict_add {_m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α) :
    (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
  (restrictₗ s).map_add μ ν
#align measure_theory.measure.restrict_add MeasureTheory.Measure.restrict_add

@[simp]
theorem restrict_zero {_m0 : MeasurableSpace α} (s : Set α) : (0 : Measure α).restrict s = 0 :=
  (restrictₗ s).map_zero
#align measure_theory.measure.restrict_zero MeasureTheory.Measure.restrict_zero

@[simp]
theorem restrict_smul {_m0 : MeasurableSpace α} (c : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    (c • μ).restrict s = c • μ.restrict s :=
  (restrictₗ s).map_smul c μ
#align measure_theory.measure.restrict_smul MeasureTheory.Measure.restrict_smul

theorem restrict_restrict₀ (hs : NullMeasurableSet s (μ.restrict t)) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.nullMeasurableSet.inter hs)]
#align measure_theory.measure.restrict_restrict₀ MeasureTheory.Measure.restrict_restrict₀

@[simp]
theorem restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀ hs.nullMeasurableSet
#align measure_theory.measure.restrict_restrict MeasureTheory.Measure.restrict_restrict

theorem restrict_restrict_of_subset (h : s ⊆ t) : (μ.restrict t).restrict s = μ.restrict s := by
  ext1 u hu
  rw [restrict_apply hu, restrict_apply hu, restrict_eq_self]
  exact (inter_subset_right _ _).trans h
#align measure_theory.measure.restrict_restrict_of_subset MeasureTheory.Measure.restrict_restrict_of_subset

theorem restrict_restrict₀' (ht : NullMeasurableSet t μ) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]
#align measure_theory.measure.restrict_restrict₀' MeasureTheory.Measure.restrict_restrict₀'

theorem restrict_restrict' (ht : MeasurableSet t) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀' ht.nullMeasurableSet
#align measure_theory.measure.restrict_restrict' MeasureTheory.Measure.restrict_restrict'

theorem restrict_comm (hs : MeasurableSet s) :
    (μ.restrict t).restrict s = (μ.restrict s).restrict t := by
  rw [restrict_restrict hs, restrict_restrict' hs, inter_comm]
#align measure_theory.measure.restrict_comm MeasureTheory.Measure.restrict_comm

theorem restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply ht]
#align measure_theory.measure.restrict_apply_eq_zero MeasureTheory.Measure.restrict_apply_eq_zero

theorem measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t ∩ s) = 0 :=
  nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)
#align measure_theory.measure.measure_inter_eq_zero_of_restrict MeasureTheory.Measure.measure_inter_eq_zero_of_restrict

theorem restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply' hs]
#align measure_theory.measure.restrict_apply_eq_zero' MeasureTheory.Measure.restrict_apply_eq_zero'

@[simp]
theorem restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 := by
  rw [← measure_univ_eq_zero, restrict_apply_univ]
#align measure_theory.measure.restrict_eq_zero MeasureTheory.Measure.restrict_eq_zero

/-- If `μ s ≠ 0`, then `μ.restrict s ≠ 0`, in terms of `NeZero` instances. -/
instance restrict.neZero [NeZero (μ s)] : NeZero (μ.restrict s) :=
  ⟨mt restrict_eq_zero.mp <| NeZero.ne _⟩

theorem restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0 :=
  restrict_eq_zero.2 h
#align measure_theory.measure.restrict_zero_set MeasureTheory.Measure.restrict_zero_set

@[simp]
theorem restrict_empty : μ.restrict ∅ = 0 :=
  restrict_zero_set measure_empty
#align measure_theory.measure.restrict_empty MeasureTheory.Measure.restrict_empty

@[simp]
theorem restrict_univ : μ.restrict univ = μ :=
  ext fun s hs => by simp [hs]
#align measure_theory.measure.restrict_univ MeasureTheory.Measure.restrict_univ

theorem restrict_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s := by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, diff_eq]
  exact measure_inter_add_diff₀ (u ∩ s) ht
#align measure_theory.measure.restrict_inter_add_diff₀ MeasureTheory.Measure.restrict_inter_add_diff₀

theorem restrict_inter_add_diff (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s :=
  restrict_inter_add_diff₀ s ht.nullMeasurableSet
#align measure_theory.measure.restrict_inter_add_diff MeasureTheory.Measure.restrict_inter_add_diff

theorem restrict_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  rw [← restrict_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right, ←
    restrict_inter_add_diff₀ s ht, add_comm, ← add_assoc, add_right_comm]
#align measure_theory.measure.restrict_union_add_inter₀ MeasureTheory.Measure.restrict_union_add_inter₀

theorem restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
  restrict_union_add_inter₀ s ht.nullMeasurableSet
#align measure_theory.measure.restrict_union_add_inter MeasureTheory.Measure.restrict_union_add_inter

theorem restrict_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs
#align measure_theory.measure.restrict_union_add_inter' MeasureTheory.Measure.restrict_union_add_inter'

theorem restrict_union₀ (h : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]
#align measure_theory.measure.restrict_union₀ MeasureTheory.Measure.restrict_union₀

theorem restrict_union (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
  restrict_union₀ h.aedisjoint ht.nullMeasurableSet
#align measure_theory.measure.restrict_union MeasureTheory.Measure.restrict_union

theorem restrict_union' (h : Disjoint s t) (hs : MeasurableSet s) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  rw [union_comm, restrict_union h.symm hs, add_comm]
#align measure_theory.measure.restrict_union' MeasureTheory.Measure.restrict_union'

@[simp]
theorem restrict_add_restrict_compl (hs : MeasurableSet s) :
    μ.restrict s + μ.restrict sᶜ = μ := by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl, union_compl_self,
    restrict_univ]
#align measure_theory.measure.restrict_add_restrict_compl MeasureTheory.Measure.restrict_add_restrict_compl

@[simp]
theorem restrict_compl_add_restrict (hs : MeasurableSet s) : μ.restrict sᶜ + μ.restrict s = μ :=
  by rw [add_comm, restrict_add_restrict_compl hs]
#align measure_theory.measure.restrict_compl_add_restrict MeasureTheory.Measure.restrict_compl_add_restrict

theorem restrict_union_le (s s' : Set α) : μ.restrict (s ∪ s') ≤ μ.restrict s + μ.restrict s' := by
  intro t ht
  suffices μ (t ∩ s ∪ t ∩ s') ≤ μ (t ∩ s) + μ (t ∩ s') by simpa [ht, inter_union_distrib_left]
  apply measure_union_le
#align measure_theory.measure.restrict_union_le MeasureTheory.Measure.restrict_union_le

theorem restrict_iUnion_apply_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t := by
  simp only [restrict_apply, ht, inter_iUnion]
  exact
    measure_iUnion₀ (hd.mono fun i j h => h.mono (inter_subset_right _ _) (inter_subset_right _ _))
      fun i => ht.nullMeasurableSet.inter (hm i)
#align measure_theory.measure.restrict_Union_apply_ae MeasureTheory.Measure.restrict_iUnion_apply_ae

theorem restrict_iUnion_apply [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
  restrict_iUnion_apply_ae hd.aedisjoint (fun i => (hm i).nullMeasurableSet) ht
#align measure_theory.measure.restrict_Union_apply MeasureTheory.Measure.restrict_iUnion_apply

theorem restrict_iUnion_apply_eq_iSup [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s)
    {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t := by
  simp only [restrict_apply ht, inter_iUnion]
  rw [measure_iUnion_eq_iSup]
  exacts [hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]
#align measure_theory.measure.restrict_Union_apply_eq_supr MeasureTheory.Measure.restrict_iUnion_apply_eq_iSup

/-- The restriction of the pushforward measure is the pushforward of the restriction. For a version
assuming only `AEMeasurable`, see `restrict_map_of_aemeasurable`. -/
theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  ext fun t ht => by simp [*, hf ht]
#align measure_theory.measure.restrict_map MeasureTheory.Measure.restrict_map

theorem restrict_toMeasurable (h : μ s ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    rw [restrict_apply ht, restrict_apply ht, inter_comm, measure_toMeasurable_inter ht h,
      inter_comm]
#align measure_theory.measure.restrict_to_measurable MeasureTheory.Measure.restrict_toMeasurable

theorem restrict_eq_self_of_ae_mem {_m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄
    (hs : ∀ᵐ x ∂μ, x ∈ s) : μ.restrict s = μ :=
  calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ
#align measure_theory.measure.restrict_eq_self_of_ae_mem MeasureTheory.Measure.restrict_eq_self_of_ae_mem

theorem restrict_congr_meas (hs : MeasurableSet s) :
    μ.restrict s = ν.restrict s ↔ ∀ (t) (_ : t ⊆ s), MeasurableSet t → μ t = ν t :=
  ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts, ← restrict_apply ht, H, restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht, restrict_apply ht, H _ (inter_subset_right _ _) (ht.inter hs)]⟩
#align measure_theory.measure.restrict_congr_meas MeasureTheory.Measure.restrict_congr_meas

theorem restrict_congr_mono (hs : s ⊆ t) (h : μ.restrict t = ν.restrict t) :
    μ.restrict s = ν.restrict s := by
  rw [← restrict_restrict_of_subset hs, h, restrict_restrict_of_subset hs]
#align measure_theory.measure.restrict_congr_mono MeasureTheory.Measure.restrict_congr_mono

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
theorem restrict_union_congr :
    μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔
      μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t := by
  refine'
    ⟨fun h =>
      ⟨restrict_congr_mono (subset_union_left _ _) h,
        restrict_congr_mono (subset_union_right _ _) h⟩,
      _⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u ∩ s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u ∩ s ∪ u ∩ t) = μ (US ∪ u ∩ t) :=
      measure_union_congr_of_subset hsub hμ.le Subset.rfl le_rfl
    _ = μ US + μ ((u ∩ t) \ US) := (measure_add_diff hm _).symm
    _ = restrict μ s u + restrict μ t (u \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hμ, ← inter_comm t, inter_diff_assoc]
    _ = restrict ν s u + restrict ν t (u \ US) := by rw [hs, ht]
    _ = ν US + ν ((u ∩ t) \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hν, ← inter_comm t, inter_diff_assoc]
    _ = ν (US ∪ u ∩ t) := (measure_add_diff hm _)
    _ = ν (u ∩ s ∪ u ∩ t) := Eq.symm <| measure_union_congr_of_subset hsub hν.le Subset.rfl le_rfl

#align measure_theory.measure.restrict_union_congr MeasureTheory.Measure.restrict_union_congr

theorem restrict_finset_biUnion_congr {s : Finset ι} {t : ι → Set α} :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) := by
  classical
  induction' s using Finset.induction_on with i s _ hs; · simp
  simp only [forall_eq_or_imp, iUnion_iUnion_eq_or_left, Finset.mem_insert]
  rw [restrict_union_congr, ← hs]
#align measure_theory.measure.restrict_finset_bUnion_congr MeasureTheory.Measure.restrict_finset_biUnion_congr

theorem restrict_iUnion_congr [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  refine' ⟨fun h i => restrict_congr_mono (subset_iUnion _ _) h, fun h => _⟩
  ext1 t ht
  have D : Directed (· ⊆ ·) fun t : Finset ι => ⋃ i ∈ t, s i :=
    Monotone.directed_le fun t₁ t₂ ht => biUnion_subset_biUnion_left ht
  rw [iUnion_eq_iUnion_finset]
  simp only [restrict_iUnion_apply_eq_iSup D ht, restrict_finset_biUnion_congr.2 fun i _ => h i]
#align measure_theory.measure.restrict_Union_congr MeasureTheory.Measure.restrict_iUnion_congr

theorem restrict_biUnion_congr {s : Set ι} {t : ι → Set α} (hc : s.Countable) :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) := by
  haveI := hc.toEncodable
  simp only [biUnion_eq_iUnion, SetCoe.forall', restrict_iUnion_congr]
#align measure_theory.measure.restrict_bUnion_congr MeasureTheory.Measure.restrict_biUnion_congr

theorem restrict_sUnion_congr {S : Set (Set α)} (hc : S.Countable) :
    μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s := by
  rw [sUnion_eq_biUnion, restrict_biUnion_congr hc]
#align measure_theory.measure.restrict_sUnion_congr MeasureTheory.Measure.restrict_sUnion_congr

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
theorem restrict_sInf_eq_sInf_restrict {m0 : MeasurableSpace α} {m : Set (Measure α)}
    (hm : m.Nonempty) (ht : MeasurableSet t) :
    (sInf m).restrict t = sInf ((fun μ : Measure α => μ.restrict t) '' m) := by
  ext1 s hs
  simp_rw [sInf_apply hs, restrict_apply hs, sInf_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_toOuterMeasure_eq_toOuterMeasure_restrict ht, ←
    Set.image_image _ toOuterMeasure, ← OuterMeasure.restrict_sInf_eq_sInf_restrict _ (hm.image _),
    OuterMeasure.restrict_apply]
#align measure_theory.measure.restrict_Inf_eq_Inf_restrict MeasureTheory.Measure.restrict_sInf_eq_sInf_restrict

theorem exists_mem_of_measure_ne_zero_of_ae (hs : μ s ≠ 0) {p : α → Prop}
    (hp : ∀ᵐ x ∂μ.restrict s, p x) : ∃ x, x ∈ s ∧ p x := by
  rw [← μ.restrict_apply_self, ← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists
#align measure_theory.measure.exists_mem_of_measure_ne_zero_of_ae MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae

/-! ### Extensionality results -/

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
theorem ext_iff_of_iUnion_eq_univ [Countable ι] {s : ι → Set α} (hs : ⋃ i, s i = univ) :
    μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_iUnion_congr, hs, restrict_univ, restrict_univ]
#align measure_theory.measure.ext_iff_of_Union_eq_univ MeasureTheory.Measure.ext_iff_of_iUnion_eq_univ

alias ⟨_, ext_of_iUnion_eq_univ⟩ := ext_iff_of_iUnion_eq_univ
#align measure_theory.measure.ext_of_Union_eq_univ MeasureTheory.Measure.ext_of_iUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `biUnion`). -/
theorem ext_iff_of_biUnion_eq_univ {S : Set ι} {s : ι → Set α} (hc : S.Countable)
    (hs : ⋃ i ∈ S, s i = univ) : μ = ν ↔ ∀ i ∈ S, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_biUnion_congr hc, hs, restrict_univ, restrict_univ]
#align measure_theory.measure.ext_iff_of_bUnion_eq_univ MeasureTheory.Measure.ext_iff_of_biUnion_eq_univ

alias ⟨_, ext_of_biUnion_eq_univ⟩ := ext_iff_of_biUnion_eq_univ
#align measure_theory.measure.ext_of_bUnion_eq_univ MeasureTheory.Measure.ext_of_biUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
theorem ext_iff_of_sUnion_eq_univ {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S = univ) :
    μ = ν ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
  ext_iff_of_biUnion_eq_univ hc <| by rwa [← sUnion_eq_biUnion]
#align measure_theory.measure.ext_iff_of_sUnion_eq_univ MeasureTheory.Measure.ext_iff_of_sUnion_eq_univ

alias ⟨_, ext_of_sUnion_eq_univ⟩ := ext_iff_of_sUnion_eq_univ
#align measure_theory.measure.ext_of_sUnion_eq_univ MeasureTheory.Measure.ext_of_sUnion_eq_univ

theorem ext_of_generateFrom_of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (hc : T.Countable) (h_inter : IsPiSystem S) (hU : ⋃₀ T = univ) (htop : ∀ t ∈ T, μ t ≠ ∞)
    (ST_eq : ∀ t ∈ T, ∀ s ∈ S, μ (s ∩ t) = ν (s ∩ t)) (T_eq : ∀ t ∈ T, μ t = ν t) : μ = ν := by
  refine' ext_of_sUnion_eq_univ hc hU fun t ht => _
  ext1 u hu
  simp only [restrict_apply hu]
  refine' induction_on_inter h_gen h_inter _ (ST_eq t ht) _ _ hu
  · simp only [Set.empty_inter, measure_empty]
  · intro v hv hvt
    have := T_eq t ht
    rw [Set.inter_comm] at hvt ⊢
    rwa [← measure_inter_add_diff t hv, ← measure_inter_add_diff t hv, ← hvt,
      ENNReal.add_right_inj] at this
    exact ne_top_of_le_ne_top (htop t ht) (measure_mono <| Set.inter_subset_left _ _)
  · intro f hfd hfm h_eq
    simp only [← restrict_apply (hfm _), ← restrict_apply (MeasurableSet.iUnion hfm)] at h_eq ⊢
    simp only [measure_iUnion hfd hfm, h_eq]
#align measure_theory.measure.ext_of_generate_from_of_cover MeasureTheory.Measure.ext_of_generateFrom_of_cover

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on an increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
theorem ext_of_generateFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (h_inter : IsPiSystem S) (h_sub : T ⊆ S) (hc : T.Countable) (hU : ⋃₀ T = univ)
    (htop : ∀ s ∈ T, μ s ≠ ∞) (h_eq : ∀ s ∈ S, μ s = ν s) : μ = ν := by
  refine' ext_of_generateFrom_of_cover h_gen hc h_inter hU htop _ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; cases' (s ∩ t).eq_empty_or_nonempty with H H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)
#align measure_theory.measure.ext_of_generate_from_of_cover_subset MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on an increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `iUnion`.
  `FiniteSpanningSetsIn.ext` is a reformulation of this lemma. -/
theorem ext_of_generateFrom_of_iUnion (C : Set (Set α)) (B : ℕ → Set α) (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h1B : ⋃ i, B i = univ) (h2B : ∀ i, B i ∈ C) (hμB : ∀ i, μ (B i) ≠ ∞)
    (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν := by
  refine' ext_of_generateFrom_of_cover_subset hA hC _ (countable_range B) h1B _ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB
#align measure_theory.measure.ext_of_generate_from_of_Union MeasureTheory.Measure.ext_of_generateFrom_of_iUnion

@[simp]
theorem restrict_sum (μ : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s :=
  ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]
#align measure_theory.measure.restrict_sum MeasureTheory.Measure.restrict_sum

lemma AbsolutelyContinuous.restrict (h : μ ≪ ν) (s : Set α) : μ.restrict s ≪ ν.restrict s := by
  refine Measure.AbsolutelyContinuous.mk (fun t ht htν ↦ ?_)
  rw [restrict_apply ht] at htν ⊢
  exact h htν

theorem restrict_iUnion_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AEDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  ext fun t ht => by simp only [sum_apply _ ht, restrict_iUnion_apply_ae hd hm ht]
#align measure_theory.measure.restrict_Union_ae MeasureTheory.Measure.restrict_iUnion_ae

theorem restrict_iUnion [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  restrict_iUnion_ae hd.aedisjoint fun i => (hm i).nullMeasurableSet
#align measure_theory.measure.restrict_Union MeasureTheory.Measure.restrict_iUnion

theorem restrict_iUnion_le [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) ≤ sum fun i => μ.restrict (s i) := by
  intro t ht
  suffices μ (⋃ i, t ∩ s i) ≤ ∑' i, μ (t ∩ s i) by simpa [ht, inter_iUnion]
  apply measure_iUnion_le
#align measure_theory.measure.restrict_Union_le MeasureTheory.Measure.restrict_iUnion_le

end Measure

@[simp]
theorem ae_restrict_iUnion_eq [Countable ι] (s : ι → Set α) :
    (μ.restrict (⋃ i, s i)).ae = ⨆ i, (μ.restrict (s i)).ae :=
  le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_iUnion_le) <|
    iSup_le fun i => ae_mono <| restrict_mono (subset_iUnion s i) le_rfl
#align measure_theory.ae_restrict_Union_eq MeasureTheory.ae_restrict_iUnion_eq

@[simp]
theorem ae_restrict_union_eq (s t : Set α) :
    (μ.restrict (s ∪ t)).ae = (μ.restrict s).ae ⊔ (μ.restrict t).ae := by
  simp [union_eq_iUnion, iSup_bool_eq]
#align measure_theory.ae_restrict_union_eq MeasureTheory.ae_restrict_union_eq

theorem ae_restrict_biUnion_eq (s : ι → Set α) {t : Set ι} (ht : t.Countable) :
    (μ.restrict (⋃ i ∈ t, s i)).ae = ⨆ i ∈ t, (μ.restrict (s i)).ae := by
  haveI := ht.to_subtype
  rw [biUnion_eq_iUnion, ae_restrict_iUnion_eq, ← iSup_subtype'']
#align measure_theory.ae_restrict_bUnion_eq MeasureTheory.ae_restrict_biUnion_eq

theorem ae_restrict_biUnion_finset_eq (s : ι → Set α) (t : Finset ι) :
    (μ.restrict (⋃ i ∈ t, s i)).ae = ⨆ i ∈ t, (μ.restrict (s i)).ae :=
  ae_restrict_biUnion_eq s t.countable_toSet
#align measure_theory.ae_restrict_bUnion_finset_eq MeasureTheory.ae_restrict_biUnion_finset_eq

theorem ae_restrict_iUnion_iff [Countable ι] (s : ι → Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ ∀ i, ∀ᵐ x ∂μ.restrict (s i), p x := by simp
#align measure_theory.ae_restrict_Union_iff MeasureTheory.ae_restrict_iUnion_iff

theorem ae_restrict_union_iff (s t : Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (s ∪ t), p x) ↔ (∀ᵐ x ∂μ.restrict s, p x) ∧ ∀ᵐ x ∂μ.restrict t, p x := by simp
#align measure_theory.ae_restrict_union_iff MeasureTheory.ae_restrict_union_iff

theorem ae_restrict_biUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_eq s ht, mem_iSup]
#align measure_theory.ae_restrict_bUnion_iff MeasureTheory.ae_restrict_biUnion_iff

@[simp]
theorem ae_restrict_biUnion_finset_iff (s : ι → Set α) (t : Finset ι) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_biUnion_finset_eq s, mem_iSup]
#align measure_theory.ae_restrict_bUnion_finset_iff MeasureTheory.ae_restrict_biUnion_finset_iff

theorem ae_eq_restrict_iUnion_iff [Countable ι] (s : ι → Set α) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ ∀ i, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [EventuallyEq, ae_restrict_iUnion_eq, eventually_iSup]
#align measure_theory.ae_eq_restrict_Union_iff MeasureTheory.ae_eq_restrict_iUnion_iff

theorem ae_eq_restrict_biUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [ae_restrict_biUnion_eq s ht, EventuallyEq, eventually_iSup]
#align measure_theory.ae_eq_restrict_bUnion_iff MeasureTheory.ae_eq_restrict_biUnion_iff

theorem ae_eq_restrict_biUnion_finset_iff (s : ι → Set α) (t : Finset ι) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g :=
  ae_eq_restrict_biUnion_iff s t.countable_toSet f g
#align measure_theory.ae_eq_restrict_bUnion_finset_iff MeasureTheory.ae_eq_restrict_biUnion_finset_iff

theorem ae_restrict_uIoc_eq [LinearOrder α] (a b : α) :
    (μ.restrict (Ι a b)).ae = (μ.restrict (Ioc a b)).ae ⊔ (μ.restrict (Ioc b a)).ae := by
  simp only [uIoc_eq_union, ae_restrict_union_eq]
#align measure_theory.ae_restrict_uIoc_eq MeasureTheory.ae_restrict_uIoc_eq

/-- See also `MeasureTheory.ae_uIoc_iff`. -/
theorem ae_restrict_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ.restrict (Ι a b), P x) ↔
      (∀ᵐ x ∂μ.restrict (Ioc a b), P x) ∧ ∀ᵐ x ∂μ.restrict (Ioc b a), P x :=
  by rw [ae_restrict_uIoc_eq, eventually_sup]
#align measure_theory.ae_restrict_uIoc_iff MeasureTheory.ae_restrict_uIoc_iff

theorem ae_restrict_iff {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff, ← compl_setOf, Measure.restrict_apply hp.compl]
  rw [iff_iff_eq]; congr with x; simp [and_comm]
#align measure_theory.ae_restrict_iff MeasureTheory.ae_restrict_iff

theorem ae_imp_of_ae_restrict {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ.restrict s, p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff] at h ⊢
  simpa [setOf_and, inter_comm] using measure_inter_eq_zero_of_restrict h
#align measure_theory.ae_imp_of_ae_restrict MeasureTheory.ae_imp_of_ae_restrict

theorem ae_restrict_iff' {p : α → Prop} (hs : MeasurableSet s) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff, ← compl_setOf, restrict_apply_eq_zero' hs]
  rw [iff_iff_eq]; congr with x; simp [and_comm]
#align measure_theory.ae_restrict_iff' MeasureTheory.ae_restrict_iff'

theorem _root_.Filter.EventuallyEq.restrict {f g : α → δ} {s : Set α} (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.restrict s] g := by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine' hfg.filter_mono _
  rw [Measure.ae_le_iff_absolutelyContinuous]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
#align filter.eventually_eq.restrict Filter.EventuallyEq.restrict

theorem ae_restrict_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  (ae_restrict_iff' hs).2 (Filter.eventually_of_forall fun _ => id)
#align measure_theory.ae_restrict_mem MeasureTheory.ae_restrict_mem

theorem ae_restrict_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ.restrict s, x ∈ s := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, ht_eq⟩
  rw [← restrict_congr_set ht_eq]
  exact (ae_restrict_mem htm).mono hts
#align measure_theory.ae_restrict_mem₀ MeasureTheory.ae_restrict_mem₀

theorem ae_restrict_of_ae {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  Eventually.filter_mono (ae_mono Measure.restrict_le_self) h
#align measure_theory.ae_restrict_of_ae MeasureTheory.ae_restrict_of_ae

theorem ae_restrict_iff'₀ {p : α → Prop} (hs : NullMeasurableSet s μ) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x := by
  refine' ⟨fun h => ae_imp_of_ae_restrict h, fun h => _⟩
  filter_upwards [ae_restrict_mem₀ hs, ae_restrict_of_ae h] with x hx h'x using h'x hx
#align measure_theory.ae_restrict_iff'₀ MeasureTheory.ae_restrict_iff'₀

theorem ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α → Prop} (hst : s ⊆ t)
    (h : ∀ᵐ x ∂μ.restrict t, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))
#align measure_theory.ae_restrict_of_ae_restrict_of_subset MeasureTheory.ae_restrict_of_ae_restrict_of_subset

theorem ae_of_ae_restrict_of_ae_restrict_compl (t : Set α) {p : α → Prop}
    (ht : ∀ᵐ x ∂μ.restrict t, p x) (htc : ∀ᵐ x ∂μ.restrict tᶜ, p x) : ∀ᵐ x ∂μ, p x :=
  nonpos_iff_eq_zero.1 <|
    calc
      μ { x | ¬p x } = μ ({ x | ¬p x } ∩ t ∪ { x | ¬p x } ∩ tᶜ) := by
        rw [← inter_union_distrib_left, union_compl_self, inter_univ]
      _ ≤ μ ({ x | ¬p x } ∩ t) + μ ({ x | ¬p x } ∩ tᶜ) := (measure_union_le _ _)
      _ ≤ μ.restrict t { x | ¬p x } + μ.restrict tᶜ { x | ¬p x } :=
        (add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _))
      _ = 0 := by rw [ae_iff.1 ht, ae_iff.1 htc, zero_add]

#align measure_theory.ae_of_ae_restrict_of_ae_restrict_compl MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl

theorem mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α → β} (hs : MeasurableSet s) :
    t ∈ Filter.map f (μ.restrict s).ae ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0 := by
  rw [mem_map, mem_ae_iff, Measure.restrict_apply' hs]
#align measure_theory.mem_map_restrict_ae_iff MeasureTheory.mem_map_restrict_ae_iff

theorem ae_smul_measure {p : α → Prop} [Monoid R] [DistribMulAction R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : ∀ᵐ x ∂μ, p x) (c : R) : ∀ᵐ x ∂c • μ, p x :=
  ae_iff.2 <| by rw [smul_apply, ae_iff.1 h, smul_zero]
#align measure_theory.ae_smul_measure MeasureTheory.ae_smul_measure

theorem ae_add_measure_iff {p : α → Prop} {ν} :
    (∀ᵐ x ∂μ + ν, p x) ↔ (∀ᵐ x ∂μ, p x) ∧ ∀ᵐ x ∂ν, p x :=
  add_eq_zero_iff
#align measure_theory.ae_add_measure_iff MeasureTheory.ae_add_measure_iff

theorem ae_eq_comp' {ν : Measure β} {f : α → β} {g g' : β → δ} (hf : AEMeasurable f μ)
    (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
  (tendsto_ae_map hf).mono_right h2.ae_le h
#align measure_theory.ae_eq_comp' MeasureTheory.ae_eq_comp'

theorem Measure.QuasiMeasurePreserving.ae_eq_comp {ν : Measure β} {f : α → β} {g g' : β → δ}
    (hf : QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf.aemeasurable h hf.absolutelyContinuous
#align measure_theory.measure.quasi_measure_preserving.ae_eq_comp MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp

theorem ae_eq_comp {f : α → β} {g g' : β → δ} (hf : AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') :
    g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf h AbsolutelyContinuous.rfl
#align measure_theory.ae_eq_comp MeasureTheory.ae_eq_comp

theorem sub_ae_eq_zero {β} [AddGroup β] (f g : α → β) : f - g =ᵐ[μ] 0 ↔ f =ᵐ[μ] g := by
  refine' ⟨fun h => h.mono fun x hx => _, fun h => h.mono fun x hx => _⟩
  · rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
  · rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
#align measure_theory.sub_ae_eq_zero MeasureTheory.sub_ae_eq_zero

theorem le_ae_restrict : μ.ae ⊓ 𝓟 s ≤ (μ.restrict s).ae := fun _s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)
#align measure_theory.le_ae_restrict MeasureTheory.le_ae_restrict

@[simp]
theorem ae_restrict_eq (hs : MeasurableSet s) : (μ.restrict s).ae = μ.ae ⊓ 𝓟 s := by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_setOf, not_imp,
    fun a => and_comm (a := a ∈ s) (b := ¬a ∈ t)]
  rfl
#align measure_theory.ae_restrict_eq MeasureTheory.ae_restrict_eq

-- @[simp] -- Porting note: simp can prove this
theorem ae_restrict_eq_bot {s} : (μ.restrict s).ae = ⊥ ↔ μ s = 0 :=
  ae_eq_bot.trans restrict_eq_zero
#align measure_theory.ae_restrict_eq_bot MeasureTheory.ae_restrict_eq_bot

theorem ae_restrict_neBot {s} : (μ.restrict s).ae.NeBot ↔ μ s ≠ 0 :=
  neBot_iff.trans ae_restrict_eq_bot.not
#align measure_theory.ae_restrict_ne_bot MeasureTheory.ae_restrict_neBot

theorem self_mem_ae_restrict {s} (hs : MeasurableSet s) : s ∈ (μ.restrict s).ae := by
  simp only [ae_restrict_eq hs, exists_prop, mem_principal, mem_inf_iff]
  exact ⟨_, univ_mem, s, Subset.rfl, (univ_inter s).symm⟩
#align measure_theory.self_mem_ae_restrict MeasureTheory.self_mem_ae_restrict

/-- If two measurable sets are ae_eq then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
theorem ae_restrict_of_ae_eq_of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) → ∀ᵐ x ∂μ.restrict t, p x := by simp [Measure.restrict_congr_set hst]
#align measure_theory.ae_restrict_of_ae_eq_of_ae_restrict MeasureTheory.ae_restrict_of_ae_eq_of_ae_restrict

/-- If two measurable sets are ae_eq then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
theorem ae_restrict_congr_set {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ.restrict t, p x :=
  ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩
#align measure_theory.ae_restrict_congr_set MeasureTheory.ae_restrict_congr_set

/-- A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates such that
`∑ μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds frequently as `i → ∞` (or
equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero. -/
theorem measure_setOf_frequently_eq_zero {p : ℕ → α → Prop} (hp : ∑' i, μ { x | p i x } ≠ ∞) :
    μ { x | ∃ᶠ n in atTop, p n x } = 0 := by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, setOf_forall,
    setOf_exists] using measure_limsup_eq_zero hp
#align measure_theory.measure_set_of_frequently_eq_zero MeasureTheory.measure_setOf_frequently_eq_zero

/-- A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such that
`∑ μ sᵢ` exists, then for almost all `x`, `x` does not belong to almost all `sᵢ`. -/
theorem ae_eventually_not_mem {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n :=
  measure_setOf_frequently_eq_zero hs
#align measure_theory.ae_eventually_not_mem MeasureTheory.ae_eventually_not_mem

lemma NullMeasurable.measure_preimage_eq_measure_restrict_preimage_of_ae_compl_eq_const
    {β : Type*} [MeasurableSpace β] {b : β} {f : α → β} {s : Set α}
    (f_mble : NullMeasurable f (μ.restrict s)) (hs : f =ᵐ[Measure.restrict μ sᶜ] (fun _ ↦ b))
    {t : Set β} (t_mble : MeasurableSet t) (ht : b ∉ t) :
    μ (f ⁻¹' t) = μ.restrict s (f ⁻¹' t) := by
  rw [Measure.restrict_apply₀ (f_mble t_mble)]
  simp only [EventuallyEq, Filter.Eventually, Pi.zero_apply, Measure.ae,
             MeasurableSet.compl_iff, Filter.mem_mk, mem_setOf_eq] at hs
  rw [Measure.restrict_apply₀] at hs
  · apply le_antisymm _ (measure_mono (inter_subset_left _ _))
    apply (measure_mono (Eq.symm (inter_union_compl (f ⁻¹' t) s)).le).trans
    apply (measure_union_le _ _).trans
    have obs : μ ((f ⁻¹' t) ∩ sᶜ) = 0 := by
      apply le_antisymm _ (zero_le _)
      rw [← hs]
      apply measure_mono (inter_subset_inter_left _ _)
      intro x hx hfx
      simp only [mem_preimage, mem_setOf_eq] at hx hfx
      exact ht (hfx ▸ hx)
    simp only [obs, add_zero, le_refl]
  · exact NullMeasurableSet.of_null hs

namespace Measure

section Subtype

/-! ### Subtype of a measure space -/

section ComapAnyMeasure

theorem MeasurableSet.nullMeasurableSet_subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : MeasurableSet t) : NullMeasurableSet ((↑) '' t) μ := by
  rw [Subtype.instMeasurableSpace, comap_eq_generateFrom] at ht
  refine'
    generateFrom_induction (p := fun t : Set s => NullMeasurableSet ((↑) '' t) μ)
      { t : Set s | ∃ s' : Set α, MeasurableSet s' ∧ (↑) ⁻¹' s' = t } _ _ _ _ ht
  · rintro t' ⟨s', hs', rfl⟩
    rw [Subtype.image_preimage_coe]
    exact hs'.nullMeasurableSet.inter hs
  · simp only [image_empty, nullMeasurableSet_empty]
  · intro t'
    simp only [← range_diff_image Subtype.coe_injective, Subtype.range_coe_subtype, setOf_mem_eq]
    exact hs.diff
  · intro f
    dsimp only []
    rw [image_iUnion]
    exact NullMeasurableSet.iUnion
#align measure_theory.measure.measurable_set.null_measurable_set_subtype_coe MeasureTheory.Measure.MeasurableSet.nullMeasurableSet_subtype_coe

theorem NullMeasurableSet.subtype_coe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t (μ.comap Subtype.val)) : NullMeasurableSet (((↑) : s → α) '' t) μ :=
  NullMeasurableSet.image (↑) μ Subtype.coe_injective
    (fun _ => MeasurableSet.nullMeasurableSet_subtype_coe hs) ht
#align measure_theory.measure.null_measurable_set.subtype_coe MeasureTheory.Measure.NullMeasurableSet.subtype_coe

theorem measure_subtype_coe_le_comap (hs : NullMeasurableSet s μ) (t : Set s) :
    μ (((↑) : s → α) '' t) ≤ μ.comap Subtype.val t :=
  le_comap_apply _ _ Subtype.coe_injective (fun _ =>
    MeasurableSet.nullMeasurableSet_subtype_coe hs) _
#align measure_theory.measure.measure_subtype_coe_le_comap MeasureTheory.Measure.measure_subtype_coe_le_comap

theorem measure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) {t : Set s}
    (ht : μ.comap Subtype.val t = 0) : μ (((↑) : s → α) '' t) = 0 :=
  eq_bot_iff.mpr <| (measure_subtype_coe_le_comap hs t).trans ht.le
#align measure_theory.measure.measure_subtype_coe_eq_zero_of_comap_eq_zero MeasureTheory.Measure.measure_subtype_coe_eq_zero_of_comap_eq_zero

end ComapAnyMeasure

section MeasureSpace

variable {u : Set δ} [MeasureSpace δ] {p : δ → Prop}

/-- In a measure space, one can restrict the measure to a subtype to get a new measure space.
Not registered as an instance, as there are other natural choices such as the normalized restriction
for a probability measure, or the subspace measure when restricting to a vector subspace. Enable
locally if needed with `attribute [local instance] Measure.Subtype.measureSpace`. -/
noncomputable def Subtype.measureSpace : MeasureSpace (Subtype p) where
  volume := Measure.comap Subtype.val volume
#align measure_theory.measure.subtype.measure_space MeasureTheory.Measure.Subtype.measureSpace

attribute [local instance] Subtype.measureSpace

theorem Subtype.volume_def : (volume : Measure u) = volume.comap Subtype.val :=
  rfl
#align measure_theory.measure.subtype.volume_def MeasureTheory.Measure.Subtype.volume_def

theorem Subtype.volume_univ (hu : NullMeasurableSet u) : volume (univ : Set u) = volume u := by
  rw [Subtype.volume_def, comap_apply₀ _ _ _ _ MeasurableSet.univ.nullMeasurableSet]
  · congr
    simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => MeasurableSet.nullMeasurableSet_subtype_coe hu
#align measure_theory.measure.subtype.volume_univ MeasureTheory.Measure.Subtype.volume_univ

theorem volume_subtype_coe_le_volume (hu : NullMeasurableSet u) (t : Set u) :
    volume (((↑) : u → δ) '' t) ≤ volume t :=
  measure_subtype_coe_le_comap hu t
#align measure_theory.measure.volume_subtype_coe_le_volume MeasureTheory.Measure.volume_subtype_coe_le_volume

theorem volume_subtype_coe_eq_zero_of_volume_eq_zero (hu : NullMeasurableSet u) {t : Set u}
    (ht : volume t = 0) : volume (((↑) : u → δ) '' t) = 0 :=
  measure_subtype_coe_eq_zero_of_comap_eq_zero hu ht
#align measure_theory.measure.volume_subtype_coe_eq_zero_of_volume_eq_zero MeasureTheory.Measure.volume_subtype_coe_eq_zero_of_volume_eq_zero

end MeasureSpace

end Subtype

end Measure

end MeasureTheory

open MeasureTheory Measure

namespace MeasurableEmbedding

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} (hf : MeasurableEmbedding f)

theorem map_comap (μ : Measure β) : (comap f μ).map f = μ.restrict (range f) := by
  ext1 t ht
  rw [hf.map_apply, comap_apply f hf.injective hf.measurableSet_image' _ (hf.measurable ht),
    image_preimage_eq_inter_range, Measure.restrict_apply ht]
#align measurable_embedding.map_comap MeasurableEmbedding.map_comap

theorem comap_apply (μ : Measure β) (s : Set α) : comap f μ s = μ (f '' s) :=
  calc
    comap f μ s = comap f μ (f ⁻¹' (f '' s)) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap, restrict_apply' hf.measurableSet_range,
        inter_eq_self_of_subset_left (image_subset_range _ _)]
#align measurable_embedding.comap_apply MeasurableEmbedding.comap_apply

theorem comap_map (μ : Measure α) : (map f μ).comap f = μ := by
  ext t _
  rw [hf.comap_apply, hf.map_apply, preimage_image_eq _ hf.injective]

theorem ae_map_iff {p : β → Prop} {μ : Measure α} : (∀ᵐ x ∂μ.map f, p x) ↔ ∀ᵐ x ∂μ, p (f x) := by
  simp only [ae_iff, hf.map_apply, preimage_setOf_eq]
#align measurable_embedding.ae_map_iff MeasurableEmbedding.ae_map_iff

theorem restrict_map (μ : Measure α) (s : Set β) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]
#align measurable_embedding.restrict_map MeasurableEmbedding.restrict_map

protected theorem comap_preimage (μ : Measure β) (s : Set β) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [← hf.map_apply, hf.map_comap, restrict_apply' hf.measurableSet_range]
#align measurable_embedding.comap_preimage MeasurableEmbedding.comap_preimage

lemma comap_restrict (μ : Measure β) (s : Set β) :
    (μ.restrict s).comap f = (μ.comap f).restrict (f ⁻¹' s) := by
  ext t ht
  rw [Measure.restrict_apply ht, comap_apply hf, comap_apply hf,
    Measure.restrict_apply (hf.measurableSet_image.2 ht), image_inter_preimage]

lemma restrict_comap (μ : Measure β) (s : Set α) :
    (μ.comap f).restrict s = (μ.restrict (f '' s)).comap f := by
  rw [comap_restrict hf, preimage_image_eq _ hf.injective]

theorem _root_.MeasurableEquiv.restrict_map (e : α ≃ᵐ β) (μ : Measure α) (s : Set β) :
    (μ.map e).restrict s = (μ.restrict <| e ⁻¹' s).map e :=
  e.measurableEmbedding.restrict_map _ _
#align measurable_equiv.restrict_map MeasurableEquiv.restrict_map

end MeasurableEmbedding

section Subtype

theorem comap_subtype_coe_apply {_m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (t : Set s) : comap (↑) μ t = μ ((↑) '' t) :=
  (MeasurableEmbedding.subtype_coe hs).comap_apply _ _
#align comap_subtype_coe_apply comap_subtype_coe_apply

theorem map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) : (comap (↑) μ).map ((↑) : s → α) = μ.restrict s := by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap, Subtype.range_coe]
#align map_comap_subtype_coe map_comap_subtype_coe

theorem ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ (x : s) ∂comap ((↑) : s → α) μ, p x := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_map_iff]
#align ae_restrict_iff_subtype ae_restrict_iff_subtype

variable [MeasureSpace α] {s t : Set α}

/-!
### Volume on `s : Set α`

Note the instance is provided earlier as `Subtype.measureSpace`.
-/
attribute [local instance] Subtype.measureSpace

#align set_coe.measure_space MeasureTheory.Measure.Subtype.measureSpace

theorem volume_set_coe_def (s : Set α) : (volume : Measure s) = comap ((↑) : s → α) volume :=
  rfl
#align volume_set_coe_def volume_set_coe_def

theorem MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) :
    volume.map ((↑) : s → α) = restrict volume s := by
  rw [volume_set_coe_def, (MeasurableEmbedding.subtype_coe hs).map_comap volume, Subtype.range_coe]
#align measurable_set.map_coe_volume MeasurableSet.map_coe_volume

theorem volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) :
    volume ((↑) '' t : Set α) = volume t :=
  (comap_subtype_coe_apply hs volume t).symm
#align volume_image_subtype_coe volume_image_subtype_coe

@[simp]
theorem volume_preimage_coe (hs : NullMeasurableSet s) (ht : MeasurableSet t) :
    volume (((↑) : s → α) ⁻¹' t) = volume (t ∩ s) := by
  rw [volume_set_coe_def,
    comap_apply₀ _ _ Subtype.coe_injective
      (fun h => MeasurableSet.nullMeasurableSet_subtype_coe hs)
      (measurable_subtype_coe ht).nullMeasurableSet,
    image_preimage_eq_inter_range, Subtype.range_coe]
#align volume_preimage_coe volume_preimage_coe

end Subtype

section Piecewise

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f g : α → β}

theorem piecewise_ae_eq_restrict [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict s] f := by
  rw [ae_restrict_eq hs]
  exact (piecewise_eqOn s f g).eventuallyEq.filter_mono inf_le_right
#align piecewise_ae_eq_restrict piecewise_ae_eq_restrict

theorem piecewise_ae_eq_restrict_compl [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict sᶜ] g := by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eqOn_compl s f g).eventuallyEq.filter_mono inf_le_right
#align piecewise_ae_eq_restrict_compl piecewise_ae_eq_restrict_compl

theorem piecewise_ae_eq_of_ae_eq_set [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g :=
  hst.mem_iff.mono fun x hx => by simp [piecewise, hx]
#align piecewise_ae_eq_of_ae_eq_set piecewise_ae_eq_of_ae_eq_set

end Piecewise

section IndicatorFunction

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f : α → β}

theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set β}
    (ht : (0 : β) ∈ t) (hs : MeasurableSet s) :
    t ∈ Filter.map (s.indicator f) μ.ae ↔ t ∈ Filter.map f (μ.restrict s).ae := by
  classical
  simp_rw [mem_map, mem_ae_iff]
  rw [Measure.restrict_apply' hs, Set.indicator_preimage, Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0
  simp only [ht, ← Set.compl_eq_univ_diff, compl_compl, Set.compl_union, if_true,
    Set.preimage_const]
  simp_rw [Set.union_inter_distrib_right, Set.compl_inter_self s, Set.union_empty]
#align mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem

theorem mem_map_indicator_ae_iff_of_zero_nmem [Zero β] {t : Set β} (ht : (0 : β) ∉ t) :
    t ∈ Filter.map (s.indicator f) μ.ae ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0 := by
  classical
  rw [mem_map, mem_ae_iff, Set.indicator_preimage, Set.ite, Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun _ => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_diff, Set.inter_univ, Set.preimage_const]
#align mem_map_indicator_ae_iff_of_zero_nmem mem_map_indicator_ae_iff_of_zero_nmem

theorem map_restrict_ae_le_map_indicator_ae [Zero β] (hs : MeasurableSet s) :
    Filter.map f (μ.restrict s).ae ≤ Filter.map (s.indicator f) μ.ae := by
  intro t
  by_cases ht : (0 : β) ∈ t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_nmem ht, mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null ((Set.inter_subset_left _ _).trans (Set.subset_union_left _ _)) h
#align map_restrict_ae_le_map_indicator_ae map_restrict_ae_le_map_indicator_ae

variable [Zero β]

theorem indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict s] f := by
  classical exact piecewise_ae_eq_restrict hs
#align indicator_ae_eq_restrict indicator_ae_eq_restrict

theorem indicator_ae_eq_restrict_compl (hs : MeasurableSet s) :
    indicator s f =ᵐ[μ.restrict sᶜ] 0 := by
  classical exact piecewise_ae_eq_restrict_compl hs
#align indicator_ae_eq_restrict_compl indicator_ae_eq_restrict_compl

theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict sᶜ] 0) : s.indicator f =ᵐ[μ] f := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, eq_self_iff_true, imp_true_iff]
#align indicator_ae_eq_of_restrict_compl_ae_eq_zero indicator_ae_eq_of_restrict_compl_ae_eq_zero

theorem indicator_ae_eq_zero_of_restrict_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict s] 0) : s.indicator f =ᵐ[μ] 0 := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at hf
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hx, hxs]
#align indicator_ae_eq_zero_of_restrict_ae_eq_zero indicator_ae_eq_zero_of_restrict_ae_eq_zero

theorem indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f := by
  classical exact piecewise_ae_eq_of_ae_eq_set hst
#align indicator_ae_eq_of_ae_eq_set indicator_ae_eq_of_ae_eq_set

theorem indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0 :=
  indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)
#align indicator_meas_zero indicator_meas_zero

theorem ae_eq_restrict_iff_indicator_ae_eq {g : α → β} (hs : MeasurableSet s) :
    f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g := by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  refine' ⟨fun h => _, fun h => _⟩ <;> filter_upwards [h] with x hx
  · by_cases hxs : x ∈ s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx
#align ae_eq_restrict_iff_indicator_ae_eq ae_eq_restrict_iff_indicator_ae_eq

end IndicatorFunction
