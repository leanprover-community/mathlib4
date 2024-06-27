/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance

#align_import topology.metric_space.hausdorff_distance from "leanprover-community/mathlib"@"bc91ed7093bf098d253401e69df601fc33dde156"

/-!
# Thickenings in pseudo-metric spaces

## Main definitions
* `Metric.thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
* `Metric.cthickening δ s`, the closed thickening by radius `δ` of a set `s` in a pseudo emetric
  space.

## Main results
* `Disjoint.exists_thickenings`: two disjoint sets admit disjoint thickenings
* `Disjoint.exists_cthickenings`: two disjoint sets admit disjoint closed thickenings
* `IsCompact.exists_cthickening_subset_open`: if `s` is compact, `t` is open and `s ⊆ t`,
  some `cthickening` of `s` is contained in `t`.

* `Metric.hasBasis_nhdsSet_cthickening`: the `cthickening`s of a compact set `K` form a basis
  of the neighbourhoods of `K`
* `Metric.closure_eq_iInter_cthickening'`: the closure of a set equals the intersection
  of its closed thickenings of positive radii accumulating at zero.
  The same holds for open thickenings.
* `IsCompact.cthickening_eq_biUnion_closedBall`: if `s` is compact, `cthickening δ s` is the union
  of `closedBall`s of radius `δ` around `x : E`.

-/

noncomputable section
open NNReal ENNReal Topology Set Filter Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

namespace Metric

section Thickening

variable [PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α}

open EMetric

/-- The (open) `δ`-thickening `Metric.thickening δ E` of a subset `E` in a pseudo emetric space
consists of those points that are at distance less than `δ` from some point of `E`. -/
def thickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E < ENNReal.ofReal δ }
#align metric.thickening Metric.thickening

theorem mem_thickening_iff_infEdist_lt : x ∈ thickening δ s ↔ infEdist x s < ENNReal.ofReal δ :=
  Iff.rfl
#align metric.mem_thickening_iff_inf_edist_lt Metric.mem_thickening_iff_infEdist_lt

/-- An exterior point of a subset `E` (i.e., a point outside the closure of `E`) is not in the
(open) `δ`-thickening of `E` for small enough positive `δ`. -/
lemma eventually_not_mem_thickening_of_infEdist_pos {E : Set α} {x : α} (h : x ∉ closure E) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), x ∉ Metric.thickening δ E := by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEdist_of_not_mem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [thickening, mem_setOf_eq, not_lt]
  exact (ENNReal.ofReal_le_ofReal hδ.le).trans ε_lt.le

/-- The (open) thickening equals the preimage of an open interval under `EMetric.infEdist`. -/
theorem thickening_eq_preimage_infEdist (δ : ℝ) (E : Set α) :
    thickening δ E = (infEdist · E) ⁻¹' Iio (ENNReal.ofReal δ) :=
  rfl
#align metric.thickening_eq_preimage_inf_edist Metric.thickening_eq_preimage_infEdist

/-- The (open) thickening is an open set. -/
theorem isOpen_thickening {δ : ℝ} {E : Set α} : IsOpen (thickening δ E) :=
  Continuous.isOpen_preimage continuous_infEdist _ isOpen_Iio
#align metric.is_open_thickening Metric.isOpen_thickening

/-- The (open) thickening of the empty set is empty. -/
@[simp]
theorem thickening_empty (δ : ℝ) : thickening δ (∅ : Set α) = ∅ := by
  simp only [thickening, setOf_false, infEdist_empty, not_top_lt]
#align metric.thickening_empty Metric.thickening_empty

theorem thickening_of_nonpos (hδ : δ ≤ 0) (s : Set α) : thickening δ s = ∅ :=
  eq_empty_of_forall_not_mem fun _ => ((ENNReal.ofReal_of_nonpos hδ).trans_le bot_le).not_lt
#align metric.thickening_of_nonpos Metric.thickening_of_nonpos

/-- The (open) thickening `Metric.thickening δ E` of a fixed subset `E` is an increasing function of
the thickening radius `δ`. -/
theorem thickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickening δ₁ E ⊆ thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))
#align metric.thickening_mono Metric.thickening_mono

/-- The (open) thickening `Metric.thickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem thickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) :
    thickening δ E₁ ⊆ thickening δ E₂ := fun _ hx => lt_of_le_of_lt (infEdist_anti h) hx
#align metric.thickening_subset_of_subset Metric.thickening_subset_of_subset

theorem mem_thickening_iff_exists_edist_lt {δ : ℝ} (E : Set α) (x : α) :
    x ∈ thickening δ E ↔ ∃ z ∈ E, edist x z < ENNReal.ofReal δ :=
  infEdist_lt_iff
#align metric.mem_thickening_iff_exists_edist_lt Metric.mem_thickening_iff_exists_edist_lt

/-- The frontier of the (open) thickening of a set is contained in an `EMetric.infEdist` level
set. -/
theorem frontier_thickening_subset (E : Set α) {δ : ℝ} :
    frontier (thickening δ E) ⊆ { x : α | infEdist x E = ENNReal.ofReal δ } :=
  frontier_lt_subset_eq continuous_infEdist continuous_const
#align metric.frontier_thickening_subset Metric.frontier_thickening_subset

theorem frontier_thickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : ℝ => frontier (thickening r A)) := by
  refine (pairwise_disjoint_on _).2 fun r₁ r₂ hr => ?_
  rcases le_total r₁ 0 with h₁ | h₁
  · simp [thickening_of_nonpos h₁]
  refine ((disjoint_singleton.2 fun h => hr.ne ?_).preimage _).mono (frontier_thickening_subset _)
    (frontier_thickening_subset _)
  apply_fun ENNReal.toReal at h
  rwa [ENNReal.toReal_ofReal h₁, ENNReal.toReal_ofReal (h₁.trans hr.le)] at h
#align metric.frontier_thickening_disjoint Metric.frontier_thickening_disjoint

/-- Any set is contained in the complement of the δ-thickening of the complement of its
δ-thickening. -/
lemma subset_compl_thickening_compl_thickening_self (δ : ℝ) (E : Set α) :
    E ⊆ (thickening δ (thickening δ E)ᶜ)ᶜ := by
  intro x x_in_E
  simp only [thickening, mem_compl_iff, mem_setOf_eq, not_lt]
  apply EMetric.le_infEdist.mpr fun y hy ↦ ?_
  simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hy
  simpa only [edist_comm] using le_trans hy <| EMetric.infEdist_le_edist_of_mem x_in_E

/-- The δ-thickening of the complement of the δ-thickening of a set is contained in the complement
of the set. -/
lemma thickening_compl_thickening_self_subset_compl (δ : ℝ) (E : Set α) :
    thickening δ (thickening δ E)ᶜ ⊆ Eᶜ := by
  apply compl_subset_compl.mp
  simpa only [compl_compl] using subset_compl_thickening_compl_thickening_self δ E

variable {X : Type u} [PseudoMetricSpace X]

theorem mem_thickening_iff_infDist_lt {E : Set X} {x : X} (h : E.Nonempty) :
    x ∈ thickening δ E ↔ infDist x E < δ :=
  lt_ofReal_iff_toReal_lt (infEdist_ne_top h)

/-- A point in a metric space belongs to the (open) `δ`-thickening of a subset `E` if and only if
it is at distance less than `δ` from some point of `E`. -/
theorem mem_thickening_iff {E : Set X} {x : X} : x ∈ thickening δ E ↔ ∃ z ∈ E, dist x z < δ := by
  have key_iff : ∀ z : X, edist x z < ENNReal.ofReal δ ↔ dist x z < δ := fun z ↦ by
    rw [dist_edist, lt_ofReal_iff_toReal_lt (edist_ne_top _ _)]
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]
#align metric.mem_thickening_iff Metric.mem_thickening_iff

@[simp]
theorem thickening_singleton (δ : ℝ) (x : X) : thickening δ ({x} : Set X) = ball x δ := by
  ext
  simp [mem_thickening_iff]
#align metric.thickening_singleton Metric.thickening_singleton

theorem ball_subset_thickening {x : X} {E : Set X} (hx : x ∈ E) (δ : ℝ) :
    ball x δ ⊆ thickening δ E :=
  Subset.trans (by simp [Subset.rfl]) (thickening_subset_of_subset δ <| singleton_subset_iff.mpr hx)
#align metric.ball_subset_thickening Metric.ball_subset_thickening

/-- The (open) `δ`-thickening `Metric.thickening δ E` of a subset `E` in a metric space equals the
union of balls of radius `δ` centered at points of `E`. -/
theorem thickening_eq_biUnion_ball {δ : ℝ} {E : Set X} : thickening δ E = ⋃ x ∈ E, ball x δ := by
  ext x
  simp only [mem_iUnion₂, exists_prop]
  exact mem_thickening_iff
#align metric.thickening_eq_bUnion_ball Metric.thickening_eq_biUnion_ball

protected theorem _root_.Bornology.IsBounded.thickening {δ : ℝ} {E : Set X} (h : IsBounded E) :
    IsBounded (thickening δ E) := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · refine (isBounded_iff_subset_closedBall x).2 ⟨δ + diam E, fun y hy ↦ ?_⟩
    calc
      dist y x ≤ infDist y E + diam E := dist_le_infDist_add_diam (x := y) h hx
      _ ≤ δ + diam E := add_le_add_right ((mem_thickening_iff_infDist_lt ⟨x, hx⟩).1 hy).le _
#align metric.bounded.thickening Bornology.IsBounded.thickening

end Thickening

section Cthickening

variable [PseudoEMetricSpace α] {δ ε : ℝ} {s t : Set α} {x : α}

open EMetric

/-- The closed `δ`-thickening `Metric.cthickening δ E` of a subset `E` in a pseudo emetric space
consists of those points that are at infimum distance at most `δ` from `E`. -/
def cthickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEdist x E ≤ ENNReal.ofReal δ }
#align metric.cthickening Metric.cthickening

@[simp]
theorem mem_cthickening_iff : x ∈ cthickening δ s ↔ infEdist x s ≤ ENNReal.ofReal δ :=
  Iff.rfl
#align metric.mem_cthickening_iff Metric.mem_cthickening_iff

/-- An exterior point of a subset `E` (i.e., a point outside the closure of `E`) is not in the
closed `δ`-thickening of `E` for small enough positive `δ`. -/
lemma eventually_not_mem_cthickening_of_infEdist_pos {E : Set α} {x : α} (h : x ∉ closure E) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), x ∉ Metric.cthickening δ E := by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEdist_of_not_mem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [cthickening, mem_setOf_eq, not_le]
  exact ((ofReal_lt_ofReal_iff ε_pos).mpr hδ).trans ε_lt

theorem mem_cthickening_of_edist_le (x y : α) (δ : ℝ) (E : Set α) (h : y ∈ E)
    (h' : edist x y ≤ ENNReal.ofReal δ) : x ∈ cthickening δ E :=
  (infEdist_le_edist_of_mem h).trans h'
#align metric.mem_cthickening_of_edist_le Metric.mem_cthickening_of_edist_le

theorem mem_cthickening_of_dist_le {α : Type*} [PseudoMetricSpace α] (x y : α) (δ : ℝ) (E : Set α)
    (h : y ∈ E) (h' : dist x y ≤ δ) : x ∈ cthickening δ E := by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h'
#align metric.mem_cthickening_of_dist_le Metric.mem_cthickening_of_dist_le

theorem cthickening_eq_preimage_infEdist (δ : ℝ) (E : Set α) :
    cthickening δ E = (fun x => infEdist x E) ⁻¹' Iic (ENNReal.ofReal δ) :=
  rfl
#align metric.cthickening_eq_preimage_inf_edist Metric.cthickening_eq_preimage_infEdist

/-- The closed thickening is a closed set. -/
theorem isClosed_cthickening {δ : ℝ} {E : Set α} : IsClosed (cthickening δ E) :=
  IsClosed.preimage continuous_infEdist isClosed_Iic
#align metric.is_closed_cthickening Metric.isClosed_cthickening

/-- The closed thickening of the empty set is empty. -/
@[simp]
theorem cthickening_empty (δ : ℝ) : cthickening δ (∅ : Set α) = ∅ := by
  simp only [cthickening, ENNReal.ofReal_ne_top, setOf_false, infEdist_empty, top_le_iff]
#align metric.cthickening_empty Metric.cthickening_empty

theorem cthickening_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) (E : Set α) : cthickening δ E = closure E := by
  ext x
  simp [mem_closure_iff_infEdist_zero, cthickening, ENNReal.ofReal_eq_zero.2 hδ]
#align metric.cthickening_of_nonpos Metric.cthickening_of_nonpos

/-- The closed thickening with radius zero is the closure of the set. -/
@[simp]
theorem cthickening_zero (E : Set α) : cthickening 0 E = closure E :=
  cthickening_of_nonpos le_rfl E
#align metric.cthickening_zero Metric.cthickening_zero

theorem cthickening_max_zero (δ : ℝ) (E : Set α) : cthickening (max 0 δ) E = cthickening δ E := by
  cases le_total δ 0 <;> simp [cthickening_of_nonpos, *]
#align metric.cthickening_max_zero Metric.cthickening_max_zero

/-- The closed thickening `Metric.cthickening δ E` of a fixed subset `E` is an increasing function
of the thickening radius `δ`. -/
theorem cthickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ cthickening δ₂ E :=
  preimage_mono (Iic_subset_Iic.mpr (ENNReal.ofReal_le_ofReal hle))
#align metric.cthickening_mono Metric.cthickening_mono

@[simp]
theorem cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) {δ : ℝ} (hδ : 0 ≤ δ) :
    cthickening δ ({x} : Set α) = closedBall x δ := by
  ext y
  simp [cthickening, edist_dist, ENNReal.ofReal_le_ofReal_iff hδ]
#align metric.cthickening_singleton Metric.cthickening_singleton

theorem closedBall_subset_cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) (δ : ℝ) :
    closedBall x δ ⊆ cthickening δ ({x} : Set α) := by
  rcases lt_or_le δ 0 with (hδ | hδ)
  · simp only [closedBall_eq_empty.mpr hδ, empty_subset]
  · simp only [cthickening_singleton x hδ, Subset.rfl]
#align metric.closed_ball_subset_cthickening_singleton Metric.closedBall_subset_cthickening_singleton

/-- The closed thickening `Metric.cthickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
theorem cthickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) :
    cthickening δ E₁ ⊆ cthickening δ E₂ := fun _ hx => le_trans (infEdist_anti h) hx
#align metric.cthickening_subset_of_subset Metric.cthickening_subset_of_subset

theorem cthickening_subset_thickening {δ₁ : ℝ≥0} {δ₂ : ℝ} (hlt : (δ₁ : ℝ) < δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ thickening δ₂ E := fun _ hx =>
  hx.out.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt δ₁.prop hlt)).mpr hlt)
#align metric.cthickening_subset_thickening Metric.cthickening_subset_thickening

/-- The closed thickening `Metric.cthickening δ₁ E` is contained in the open thickening
`Metric.thickening δ₂ E` if the radius of the latter is positive and larger. -/
theorem cthickening_subset_thickening' {δ₁ δ₂ : ℝ} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ thickening δ₂ E := fun _ hx =>
  lt_of_le_of_lt hx.out ((ENNReal.ofReal_lt_ofReal_iff δ₂_pos).mpr hlt)
#align metric.cthickening_subset_thickening' Metric.cthickening_subset_thickening'

/-- The open thickening `Metric.thickening δ E` is contained in the closed thickening
`Metric.cthickening δ E` with the same radius. -/
theorem thickening_subset_cthickening (δ : ℝ) (E : Set α) : thickening δ E ⊆ cthickening δ E := by
  intro x hx
  rw [thickening, mem_setOf_eq] at hx
  exact hx.le
#align metric.thickening_subset_cthickening Metric.thickening_subset_cthickening

theorem thickening_subset_cthickening_of_le {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickening δ₁ E ⊆ cthickening δ₂ E :=
  (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)
#align metric.thickening_subset_cthickening_of_le Metric.thickening_subset_cthickening_of_le

theorem _root_.Bornology.IsBounded.cthickening {α : Type*} [PseudoMetricSpace α] {δ : ℝ} {E : Set α}
    (h : IsBounded E) : IsBounded (cthickening δ E) := by
  have : IsBounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply this.subset
  exact cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_right _ _))
    ((lt_add_one _).trans_le (le_max_left _ _)) _
#align metric.bounded.cthickening Bornology.IsBounded.cthickening

protected theorem _root_.IsCompact.cthickening
    {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {s : Set α}
    (hs : IsCompact s) {r : ℝ} : IsCompact (cthickening r s) :=
  isCompact_of_isClosed_isBounded isClosed_cthickening hs.isBounded.cthickening

theorem thickening_subset_interior_cthickening (δ : ℝ) (E : Set α) :
    thickening δ E ⊆ interior (cthickening δ E) :=
  (subset_interior_iff_isOpen.mpr isOpen_thickening).trans
    (interior_mono (thickening_subset_cthickening δ E))
#align metric.thickening_subset_interior_cthickening Metric.thickening_subset_interior_cthickening

theorem closure_thickening_subset_cthickening (δ : ℝ) (E : Set α) :
    closure (thickening δ E) ⊆ cthickening δ E :=
  (closure_mono (thickening_subset_cthickening δ E)).trans isClosed_cthickening.closure_subset
#align metric.closure_thickening_subset_cthickening Metric.closure_thickening_subset_cthickening

/-- The closed thickening of a set contains the closure of the set. -/
theorem closure_subset_cthickening (δ : ℝ) (E : Set α) : closure E ⊆ cthickening δ E := by
  rw [← cthickening_of_nonpos (min_le_right δ 0)]
  exact cthickening_mono (min_le_left δ 0) E
#align metric.closure_subset_cthickening Metric.closure_subset_cthickening

/-- The (open) thickening of a set contains the closure of the set. -/
theorem closure_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    closure E ⊆ thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E
#align metric.closure_subset_thickening Metric.closure_subset_thickening

/-- A set is contained in its own (open) thickening. -/
theorem self_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : E ⊆ thickening δ E :=
  (@subset_closure _ E).trans (closure_subset_thickening δ_pos E)
#align metric.self_subset_thickening Metric.self_subset_thickening

/-- A set is contained in its own closed thickening. -/
theorem self_subset_cthickening {δ : ℝ} (E : Set α) : E ⊆ cthickening δ E :=
  subset_closure.trans (closure_subset_cthickening δ E)
#align metric.self_subset_cthickening Metric.self_subset_cthickening

theorem thickening_mem_nhdsSet (E : Set α) {δ : ℝ} (hδ : 0 < δ) : thickening δ E ∈ 𝓝ˢ E :=
  isOpen_thickening.mem_nhdsSet.2 <| self_subset_thickening hδ E
#align metric.thickening_mem_nhds_set Metric.thickening_mem_nhdsSet

theorem cthickening_mem_nhdsSet (E : Set α) {δ : ℝ} (hδ : 0 < δ) : cthickening δ E ∈ 𝓝ˢ E :=
  mem_of_superset (thickening_mem_nhdsSet E hδ) (thickening_subset_cthickening _ _)
#align metric.cthickening_mem_nhds_set Metric.cthickening_mem_nhdsSet

@[simp]
theorem thickening_union (δ : ℝ) (s t : Set α) :
    thickening δ (s ∪ t) = thickening δ s ∪ thickening δ t := by
  simp_rw [thickening, infEdist_union, inf_eq_min, min_lt_iff, setOf_or]
#align metric.thickening_union Metric.thickening_union

@[simp]
theorem cthickening_union (δ : ℝ) (s t : Set α) :
    cthickening δ (s ∪ t) = cthickening δ s ∪ cthickening δ t := by
  simp_rw [cthickening, infEdist_union, inf_eq_min, min_le_iff, setOf_or]
#align metric.cthickening_union Metric.cthickening_union

@[simp]
theorem thickening_iUnion (δ : ℝ) (f : ι → Set α) :
    thickening δ (⋃ i, f i) = ⋃ i, thickening δ (f i) := by
  simp_rw [thickening, infEdist_iUnion, iInf_lt_iff, setOf_exists]
#align metric.thickening_Union Metric.thickening_iUnion

lemma thickening_biUnion {ι : Type*} (δ : ℝ) (f : ι → Set α) (I : Set ι) :
    thickening δ (⋃ i ∈ I, f i) = ⋃ i ∈ I, thickening δ (f i) := by simp only [thickening_iUnion]

theorem ediam_cthickening_le (ε : ℝ≥0) :
    EMetric.diam (cthickening ε s) ≤ EMetric.diam s + 2 * ε := by
  refine diam_le fun x hx y hy => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rw [mem_cthickening_iff, ENNReal.ofReal_coe_nnreal] at hx hy
  have hε : (ε : ℝ≥0∞) < ε + δ := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ hδ)
  replace hx := hx.trans_lt hε
  obtain ⟨x', hx', hxx'⟩ := infEdist_lt_iff.mp hx
  calc
    edist x y ≤ edist x x' + edist y x' := edist_triangle_right _ _ _
    _ ≤ ε + δ + (infEdist y s + EMetric.diam s) :=
      add_le_add hxx'.le (edist_le_infEdist_add_ediam hx')
    _ ≤ ε + δ + (ε + EMetric.diam s) := add_le_add_left (add_le_add_right hy _) _
    _ = _ := by rw [two_mul]; ac_rfl
#align metric.ediam_cthickening_le Metric.ediam_cthickening_le

theorem ediam_thickening_le (ε : ℝ≥0) : EMetric.diam (thickening ε s) ≤ EMetric.diam s + 2 * ε :=
  (EMetric.diam_mono <| thickening_subset_cthickening _ _).trans <| ediam_cthickening_le _
#align metric.ediam_thickening_le Metric.ediam_thickening_le

theorem diam_cthickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 ≤ ε) :
    diam (cthickening ε s) ≤ diam s + 2 * ε := by
  lift ε to ℝ≥0 using hε
  refine (toReal_le_add' (ediam_cthickening_le _) ?_ ?_).trans_eq ?_
  · exact fun h ↦ top_unique <| h ▸ EMetric.diam_mono (self_subset_cthickening _)
  · simp [mul_eq_top]
  · simp [diam]
#align metric.diam_cthickening_le Metric.diam_cthickening_le

theorem diam_thickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 ≤ ε) :
    diam (thickening ε s) ≤ diam s + 2 * ε := by
  by_cases hs : IsBounded s
  · exact (diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans
      (diam_cthickening_le _ hε)
  obtain rfl | hε := hε.eq_or_lt
  · simp [thickening_of_nonpos, diam_nonneg]
  · rw [diam_eq_zero_of_unbounded (mt (IsBounded.subset · <| self_subset_thickening hε _) hs)]
    positivity
#align metric.diam_thickening_le Metric.diam_thickening_le

@[simp]
theorem thickening_closure : thickening δ (closure s) = thickening δ s := by
  simp_rw [thickening, infEdist_closure]
#align metric.thickening_closure Metric.thickening_closure

@[simp]
theorem cthickening_closure : cthickening δ (closure s) = cthickening δ s := by
  simp_rw [cthickening, infEdist_closure]
#align metric.cthickening_closure Metric.cthickening_closure

open ENNReal

theorem _root_.Disjoint.exists_thickenings (hst : Disjoint s t) (hs : IsCompact s)
    (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (thickening δ s) (thickening δ t) := by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs ht hst
  refine ⟨r / 2, half_pos (NNReal.coe_pos.2 hr), ?_⟩
  rw [disjoint_iff_inf_le]
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  rw [← NNReal.coe_two, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal] at hzs hzt
  obtain ⟨x, hx, hzx⟩ := hzs
  obtain ⟨y, hy, hzy⟩ := hzt
  refine (h x hx y hy).not_le ?_
  calc
    edist x y ≤ edist z x + edist z y := edist_triangle_left _ _ _
    _ ≤ ↑(r / 2) + ↑(r / 2) := add_le_add hzx.le hzy.le
    _ = r := by rw [← ENNReal.coe_add, add_halves]
#align disjoint.exists_thickenings Disjoint.exists_thickenings

theorem _root_.Disjoint.exists_cthickenings (hst : Disjoint s t) (hs : IsCompact s)
    (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (cthickening δ s) (cthickening δ t) := by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine ⟨δ / 2, half_pos hδ, h.mono ?_ ?_⟩ <;>
    exact cthickening_subset_thickening' hδ (half_lt_self hδ) _
#align disjoint.exists_cthickenings Disjoint.exists_cthickenings

/-- If `s` is compact, `t` is open and `s ⊆ t`, some `cthickening` of `s` is contained in `t`. -/
theorem _root_.IsCompact.exists_cthickening_subset_open (hs : IsCompact s) (ht : IsOpen t)
    (hst : s ⊆ t) :
    ∃ δ, 0 < δ ∧ cthickening δ s ⊆ t :=
  (hst.disjoint_compl_right.exists_cthickenings hs ht.isClosed_compl).imp fun _ h =>
    ⟨h.1, disjoint_compl_right_iff_subset.1 <| h.2.mono_right <| self_subset_cthickening _⟩
#align is_compact.exists_cthickening_subset_open IsCompact.exists_cthickening_subset_open

theorem _root_.IsCompact.exists_isCompact_cthickening [LocallyCompactSpace α] (hs : IsCompact s) :
    ∃ δ, 0 < δ ∧ IsCompact (cthickening δ s) := by
  rcases exists_compact_superset hs with ⟨K, K_compact, hK⟩
  rcases hs.exists_cthickening_subset_open isOpen_interior hK with ⟨δ, δpos, hδ⟩
  refine ⟨δ, δpos, ?_⟩
  exact K_compact.of_isClosed_subset isClosed_cthickening (hδ.trans interior_subset)

theorem _root_.IsCompact.exists_thickening_subset_open (hs : IsCompact s) (ht : IsOpen t)
    (hst : s ⊆ t) : ∃ δ, 0 < δ ∧ thickening δ s ⊆ t :=
  let ⟨δ, h₀, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  ⟨δ, h₀, (thickening_subset_cthickening _ _).trans hδ⟩
#align is_compact.exists_thickening_subset_open IsCompact.exists_thickening_subset_open

theorem hasBasis_nhdsSet_thickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : ℝ => 0 < δ) fun δ => thickening δ K :=
  (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_thickening_subset_open hU.1 hU.2)
    fun _ => thickening_mem_nhdsSet K
#align metric.has_basis_nhds_set_thickening Metric.hasBasis_nhdsSet_thickening

theorem hasBasis_nhdsSet_cthickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : ℝ => 0 < δ) fun δ => cthickening δ K :=
  (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_cthickening_subset_open hU.1 hU.2)
    fun _ => cthickening_mem_nhdsSet K
#align metric.has_basis_nhds_set_cthickening Metric.hasBasis_nhdsSet_cthickening

theorem cthickening_eq_iInter_cthickening' {δ : ℝ} (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε ∈ s, cthickening ε E := by
  apply Subset.antisymm
  · exact subset_iInter₂ fun _ hε => cthickening_mono (le_of_lt (hsδ hε)) E
  · unfold cthickening
    intro x hx
    simp only [mem_iInter, mem_setOf_eq] at *
    apply ENNReal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (NNReal.coe_pos.mpr η_pos)) with ⟨ε, ⟨hsε, hε⟩⟩
    apply ((hx ε hsε).trans (ENNReal.ofReal_le_ofReal hε.2)).trans
    rw [ENNReal.coe_nnreal_eq η]
    exact ENNReal.ofReal_add_le
#align metric.cthickening_eq_Inter_cthickening' Metric.cthickening_eq_iInter_cthickening'

theorem cthickening_eq_iInter_cthickening {δ : ℝ} (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (_ : δ < ε), cthickening ε E := by
  apply cthickening_eq_iInter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε
#align metric.cthickening_eq_Inter_cthickening Metric.cthickening_eq_iInter_cthickening

theorem cthickening_eq_iInter_thickening' {δ : ℝ} (δ_nn : 0 ≤ δ) (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε ∈ s, thickening ε E := by
  refine (subset_iInter₂ fun ε hε => ?_).antisymm ?_
  · obtain ⟨ε', -, hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_lt δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
  · rw [cthickening_eq_iInter_cthickening' s hsδ hs E]
    exact iInter₂_mono fun ε _ => thickening_subset_cthickening ε E
#align metric.cthickening_eq_Inter_thickening' Metric.cthickening_eq_iInter_thickening'

theorem cthickening_eq_iInter_thickening {δ : ℝ} (δ_nn : 0 ≤ δ) (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (_ : δ < ε), thickening ε E := by
  apply cthickening_eq_iInter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε
#align metric.cthickening_eq_Inter_thickening Metric.cthickening_eq_iInter_thickening

theorem cthickening_eq_iInter_thickening'' (δ : ℝ) (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (_ : max 0 δ < ε), thickening ε E := by
  rw [← cthickening_max_zero, cthickening_eq_iInter_thickening]
  exact le_max_left _ _
#align metric.cthickening_eq_Inter_thickening'' Metric.cthickening_eq_iInter_thickening''

/-- The closure of a set equals the intersection of its closed thickenings of positive radii
accumulating at zero. -/
theorem closure_eq_iInter_cthickening' (E : Set α) (s : Set ℝ)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : closure E = ⋂ δ ∈ s, cthickening δ E := by
  by_cases hs₀ : s ⊆ Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_iInter_cthickening' _ hs₀ hs
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi, not_lt] at δ_nonpos
  apply Subset.antisymm
  · exact subset_iInter₂ fun ε _ => closure_subset_cthickening ε E
  · rw [← cthickening_of_nonpos δ_nonpos E]
    exact biInter_subset_of_mem hδs
#align metric.closure_eq_Inter_cthickening' Metric.closure_eq_iInter_cthickening'

/-- The closure of a set equals the intersection of its closed thickenings of positive radii. -/
theorem closure_eq_iInter_cthickening (E : Set α) :
    closure E = ⋂ (δ : ℝ) (_ : 0 < δ), cthickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_cthickening E
#align metric.closure_eq_Inter_cthickening Metric.closure_eq_iInter_cthickening

/-- The closure of a set equals the intersection of its open thickenings of positive radii
accumulating at zero. -/
theorem closure_eq_iInter_thickening' (E : Set α) (s : Set ℝ) (hs₀ : s ⊆ Ioi 0)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : closure E = ⋂ δ ∈ s, thickening δ E := by
  rw [← cthickening_zero]
  apply cthickening_eq_iInter_thickening' le_rfl _ hs₀ hs
#align metric.closure_eq_Inter_thickening' Metric.closure_eq_iInter_thickening'

/-- The closure of a set equals the intersection of its (open) thickenings of positive radii. -/
theorem closure_eq_iInter_thickening (E : Set α) :
    closure E = ⋂ (δ : ℝ) (_ : 0 < δ), thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_thickening rfl.ge E
#align metric.closure_eq_Inter_thickening Metric.closure_eq_iInter_thickening

/-- The frontier of the closed thickening of a set is contained in an `EMetric.infEdist` level
set. -/
theorem frontier_cthickening_subset (E : Set α) {δ : ℝ} :
    frontier (cthickening δ E) ⊆ { x : α | infEdist x E = ENNReal.ofReal δ } :=
  frontier_le_subset_eq continuous_infEdist continuous_const
#align metric.frontier_cthickening_subset Metric.frontier_cthickening_subset

/-- The closed ball of radius `δ` centered at a point of `E` is included in the closed
thickening of `E`. -/
theorem closedBall_subset_cthickening {α : Type*} [PseudoMetricSpace α] {x : α} {E : Set α}
    (hx : x ∈ E) (δ : ℝ) : closedBall x δ ⊆ cthickening δ E := by
  refine (closedBall_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ ?_)
  simpa using hx
#align metric.closed_ball_subset_cthickening Metric.closedBall_subset_cthickening

theorem cthickening_subset_iUnion_closedBall_of_lt {α : Type*} [PseudoMetricSpace α] (E : Set α)
    {δ δ' : ℝ} (hδ₀ : 0 < δ') (hδδ' : δ < δ') : cthickening δ E ⊆ ⋃ x ∈ E, closedBall x δ' := by
  refine (cthickening_subset_thickening' hδ₀ hδδ' E).trans fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := mem_thickening_iff.mp hx
  exact mem_iUnion₂.mpr ⟨y, hy₁, hy₂.le⟩
#align metric.cthickening_subset_Union_closed_ball_of_lt Metric.cthickening_subset_iUnion_closedBall_of_lt

/-- The closed thickening of a compact set `E` is the union of the balls `Metric.closedBall x δ`
over `x ∈ E`.

See also `Metric.cthickening_eq_biUnion_closedBall`. -/
theorem _root_.IsCompact.cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α]
    {δ : ℝ} {E : Set α} (hE : IsCompact E) (hδ : 0 ≤ δ) :
    cthickening δ E = ⋃ x ∈ E, closedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty]
  refine Subset.antisymm (fun x hx ↦ ?_)
    (iUnion₂_subset fun x hx ↦ closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ E, infEdist x E = edist x y := hE.exists_infEdist_eq_edist hne _
  have D1 : edist x y ≤ ENNReal.ofReal δ := (le_of_eq hy.symm).trans hx
  have D2 : dist x y ≤ δ := by
    rw [edist_dist] at D1
    exact (ENNReal.ofReal_le_ofReal_iff hδ).1 D1
  exact mem_biUnion yE D2
#align is_compact.cthickening_eq_bUnion_closed_ball IsCompact.cthickening_eq_biUnion_closedBall

theorem cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (E : Set α) (hδ : 0 ≤ δ) : cthickening δ E = ⋃ x ∈ closure E, closedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty, closure_empty]
  rw [← cthickening_closure]
  refine Subset.antisymm (fun x hx ↦ ?_)
    (iUnion₂_subset fun x hx ↦ closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ closure E, infDist x (closure E) = dist x y :=
    isClosed_closure.exists_infDist_eq_dist (closure_nonempty_iff.mpr hne) x
  replace hy : dist x y ≤ δ :=
    (ENNReal.ofReal_le_ofReal_iff hδ).mp
      (((congr_arg ENNReal.ofReal hy.symm).le.trans ENNReal.ofReal_toReal_le).trans hx)
  exact mem_biUnion yE hy
#align metric.cthickening_eq_bUnion_closed_ball Metric.cthickening_eq_biUnion_closedBall

nonrec theorem _root_.IsClosed.cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α]
    [ProperSpace α] {E : Set α} (hE : IsClosed E) (hδ : 0 ≤ δ) :
    cthickening δ E = ⋃ x ∈ E, closedBall x δ := by
  rw [cthickening_eq_biUnion_closedBall E hδ, hE.closure_eq]
#align is_closed.cthickening_eq_bUnion_closed_ball IsClosed.cthickening_eq_biUnion_closedBall

/-- For the equality, see `infEdist_cthickening`. -/
theorem infEdist_le_infEdist_cthickening_add :
    infEdist x s ≤ infEdist x (cthickening δ s) + ENNReal.ofReal δ := by
  refine le_of_forall_lt' fun r h => ?_
  simp_rw [← lt_tsub_iff_right, infEdist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact infEdist_le_edist_add_infEdist.trans_lt
    ((ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy).trans_eq
      (tsub_add_cancel_of_le <| le_self_add.trans (lt_tsub_iff_left.1 hxy).le))
#align metric.inf_edist_le_inf_edist_cthickening_add Metric.infEdist_le_infEdist_cthickening_add

/-- For the equality, see `infEdist_thickening`. -/
theorem infEdist_le_infEdist_thickening_add :
    infEdist x s ≤ infEdist x (thickening δ s) + ENNReal.ofReal δ :=
  infEdist_le_infEdist_cthickening_add.trans <|
    add_le_add_right (infEdist_anti <| thickening_subset_cthickening _ _) _
#align metric.inf_edist_le_inf_edist_thickening_add Metric.infEdist_le_infEdist_thickening_add

/-- For the equality, see `thickening_thickening`. -/
@[simp]
theorem thickening_thickening_subset (ε δ : ℝ) (s : Set α) :
    thickening ε (thickening δ s) ⊆ thickening (ε + δ) s := by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_add hε hδ]
  exact fun ⟨y, ⟨z, hz, hy⟩, hx⟩ =>
    ⟨z, hz, (edist_triangle _ _ _).trans_lt <| ENNReal.add_lt_add hx hy⟩
#align metric.thickening_thickening_subset Metric.thickening_thickening_subset

/-- For the equality, see `thickening_cthickening`. -/
@[simp]
theorem thickening_cthickening_subset (ε : ℝ) (hδ : 0 ≤ δ) (s : Set α) :
    thickening ε (cthickening δ s) ⊆ thickening (ε + δ) s := by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← infEdist_lt_iff,
    ENNReal.ofReal_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact infEdist_le_edist_add_infEdist.trans_lt
    (ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy)
#align metric.thickening_cthickening_subset Metric.thickening_cthickening_subset

/-- For the equality, see `cthickening_thickening`. -/
@[simp]
theorem cthickening_thickening_subset (hε : 0 ≤ ε) (δ : ℝ) (s : Set α) :
    cthickening ε (thickening δ s) ⊆ cthickening (ε + δ) s := by
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset]
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEdist_le_infEdist_thickening_add.trans (add_le_add_right hx _)
#align metric.cthickening_thickening_subset Metric.cthickening_thickening_subset

/-- For the equality, see `cthickening_cthickening`. -/
@[simp]
theorem cthickening_cthickening_subset (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : Set α) :
    cthickening ε (cthickening δ s) ⊆ cthickening (ε + δ) s := by
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEdist_le_infEdist_cthickening_add.trans (add_le_add_right hx _)
#align metric.cthickening_cthickening_subset Metric.cthickening_cthickening_subset

theorem frontier_cthickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : ℝ≥0 => frontier (cthickening r A)) := fun r₁ r₂ hr =>
  ((disjoint_singleton.2 <| by simpa).preimage _).mono (frontier_cthickening_subset _)
    (frontier_cthickening_subset _)
#align metric.frontier_cthickening_disjoint Metric.frontier_cthickening_disjoint

end Cthickening

end Metric
