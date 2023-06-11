/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.hausdorff_dimension
! leanprover-community/mathlib commit 8f9fea08977f7e450770933ee6abb20733b47c92
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.MeasureTheory.Measure.Hausdorff

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `measure_theory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `measure_theory.dimH (set.univ : set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorff_measure_of_lt_dimH`, `dimH_le_of_hausdorff_measure_ne_top`,
  `le_dimH_of_hausdorff_measure_eq_top`, `hausdorff_measure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorff_measure_ne_zero`, `dimH_of_hausdorff_measure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_Union`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `set.subsingleton.dimH_zero`, `set.countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `holder_with.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `holder_with`,
  `holder_on_with`, and locally Hölder maps, as well as for `set.image` and `set.range`.
* `lipschitz_with.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `isometry` or
  a `continuous_linear_equiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `real.dimH_of_nonempty_interior`: if `s` is a set in a finite dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `cont_diff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notations

We use the following notation localized in `measure_theory`. It is defined in
`measure_theory.measure.hausdorff`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[measurable_space X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[measurable_space X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/


open scoped MeasureTheory ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace FiniteDimensional Filter

variable {ι X Y : Type _} [EMetricSpace X] [EMetricSpace Y]

/-- Hausdorff dimension of a set in an (e)metric space. -/
noncomputable irreducible_def dimH (s : Set X) : ℝ≥0∞ := by borelize X;
  exact ⨆ (d : ℝ≥0) (hd : @hausdorff_measure X _ _ ⟨rfl⟩ d s = ∞), d
#align dimH dimH

/-!
### Basic properties
-/


section Measurable

variable [MeasurableSpace X] [BorelSpace X]

/-- Unfold the definition of `dimH` using `[measurable_space X] [borel_space X]` from the
environment. -/
theorem dimH_def (s : Set X) : dimH s = ⨆ (d : ℝ≥0) (hd : μH[d] s = ∞), d := by borelize X;
  rw [dimH]
#align dimH_def dimH_def

theorem hausdorffMeasure_of_lt_dimH {s : Set X} {d : ℝ≥0} (h : ↑d < dimH s) : μH[d] s = ∞ :=
  by
  simp only [dimH_def, lt_iSup_iff] at h 
  rcases h with ⟨d', hsd', hdd'⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hdd' 
  exact top_unique (hsd' ▸ hausdorff_measure_mono hdd'.le _)
#align hausdorff_measure_of_lt_dimH hausdorffMeasure_of_lt_dimH

theorem dimH_le {s : Set X} {d : ℝ≥0∞} (H : ∀ d' : ℝ≥0, μH[d'] s = ∞ → ↑d' ≤ d) : dimH s ≤ d :=
  (dimH_def s).trans_le <| iSup₂_le H
#align dimH_le dimH_le

theorem dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) : dimH s ≤ d :=
  le_of_not_lt <| mt hausdorffMeasure_of_lt_dimH h
#align dimH_le_of_hausdorff_measure_ne_top dimH_le_of_hausdorffMeasure_ne_top

theorem le_dimH_of_hausdorffMeasure_eq_top {s : Set X} {d : ℝ≥0} (h : μH[d] s = ∞) : ↑d ≤ dimH s :=
  by rw [dimH_def]; exact le_iSup₂ d h
#align le_dimH_of_hausdorff_measure_eq_top le_dimH_of_hausdorffMeasure_eq_top

theorem hausdorffMeasure_of_dimH_lt {s : Set X} {d : ℝ≥0} (h : dimH s < d) : μH[d] s = 0 :=
  by
  rw [dimH_def] at h 
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hd'd 
  exact (hausdorff_measure_zero_or_top hd'd s).resolve_right fun h => hsd'.not_le <| le_iSup₂ d' h
#align hausdorff_measure_of_dimH_lt hausdorffMeasure_of_dimH_lt

theorem measure_zero_of_dimH_lt {μ : Measure X} {d : ℝ≥0} (h : μ ≪ μH[d]) {s : Set X}
    (hd : dimH s < d) : μ s = 0 :=
  h <| hausdorffMeasure_of_dimH_lt hd
#align measure_zero_of_dimH_lt measure_zero_of_dimH_lt

theorem le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ 0) : ↑d ≤ dimH s :=
  le_of_not_lt <| mt hausdorffMeasure_of_dimH_lt h
#align le_dimH_of_hausdorff_measure_ne_zero le_dimH_of_hausdorffMeasure_ne_zero

theorem dimH_of_hausdorffMeasure_ne_zero_ne_top {d : ℝ≥0} {s : Set X} (h : μH[d] s ≠ 0)
    (h' : μH[d] s ≠ ∞) : dimH s = d :=
  le_antisymm (dimH_le_of_hausdorffMeasure_ne_top h') (le_dimH_of_hausdorffMeasure_ne_zero h)
#align dimH_of_hausdorff_measure_ne_zero_ne_top dimH_of_hausdorffMeasure_ne_zero_ne_top

end Measurable

@[mono]
theorem dimH_mono {s t : Set X} (h : s ⊆ t) : dimH s ≤ dimH t :=
  by
  borelize X
  exact dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top <| top_unique <| hd ▸ measure_mono h
#align dimH_mono dimH_mono

theorem dimH_subsingleton {s : Set X} (h : s.Subsingleton) : dimH s = 0 :=
  by
  borelize X
  apply le_antisymm _ (zero_le _)
  refine' dimH_le_of_hausdorffMeasure_ne_top _
  exact ((hausdorff_measure_le_one_of_subsingleton h le_rfl).trans_lt ENNReal.one_lt_top).Ne
#align dimH_subsingleton dimH_subsingleton

alias dimH_subsingleton ← Set.Subsingleton.dimH_zero
#align set.subsingleton.dimH_zero Set.Subsingleton.dimH_zero

@[simp]
theorem dimH_empty : dimH (∅ : Set X) = 0 :=
  subsingleton_empty.dimH_zero
#align dimH_empty dimH_empty

@[simp]
theorem dimH_singleton (x : X) : dimH ({x} : Set X) = 0 :=
  subsingleton_singleton.dimH_zero
#align dimH_singleton dimH_singleton

@[simp]
theorem dimH_iUnion [Encodable ι] (s : ι → Set X) : dimH (⋃ i, s i) = ⨆ i, dimH (s i) :=
  by
  borelize X
  refine' le_antisymm (dimH_le fun d hd => _) (iSup_le fun i => dimH_mono <| subset_Union _ _)
  contrapose! hd
  have : ∀ i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_Union_null this]
  exact ENNReal.zero_ne_top
#align dimH_Union dimH_iUnion

@[simp]
theorem dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι → Set X) :
    dimH (⋃ i ∈ s, t i) = ⨆ i ∈ s, dimH (t i) :=
  by
  haveI := hs.to_encodable
  rw [bUnion_eq_Union, dimH_iUnion, ← iSup_subtype'']
#align dimH_bUnion dimH_bUnion

@[simp]
theorem dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s := by
  rw [sUnion_eq_bUnion, dimH_bUnion hS]
#align dimH_sUnion dimH_sUnion

@[simp]
theorem dimH_union (s t : Set X) : dimH (s ∪ t) = max (dimH s) (dimH t) := by
  rw [union_eq_Union, dimH_iUnion, iSup_bool_eq, cond, cond, ENNReal.sup_eq_max]
#align dimH_union dimH_union

theorem dimH_countable {s : Set X} (hs : s.Countable) : dimH s = 0 :=
  biUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ENNReal.iSup_zero_eq_zero]
#align dimH_countable dimH_countable

alias dimH_countable ← Set.Countable.dimH_zero
#align set.countable.dimH_zero Set.Countable.dimH_zero

theorem dimH_finite {s : Set X} (hs : s.Finite) : dimH s = 0 :=
  hs.Countable.dimH_zero
#align dimH_finite dimH_finite

alias dimH_finite ← Set.Finite.dimH_zero
#align set.finite.dimH_zero Set.Finite.dimH_zero

@[simp]
theorem dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0 :=
  s.finite_toSet.dimH_zero
#align dimH_coe_finset dimH_coe_finset

alias dimH_coe_finset ← Finset.dimH_zero
#align finset.dimH_zero Finset.dimH_zero

/-!
### Hausdorff dimension as the supremum of local Hausdorff dimensions
-/


section

variable [SecondCountableTopology X]

/-- If `r` is less than the Hausdorff dimension of a set `s` in an (extended) metric space with
second countable topology, then there exists a point `x ∈ s` such that every neighborhood
`t` of `x` within `s` has Hausdorff dimension greater than `r`. -/
theorem exists_mem_nhdsWithin_lt_dimH_of_lt_dimH {s : Set X} {r : ℝ≥0∞} (h : r < dimH s) :
    ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, r < dimH t := by
  contrapose! h; choose! t htx htr using h
  rcases countable_cover_nhds_within htx with ⟨S, hSs, hSc, hSU⟩
  calc
    dimH s ≤ dimH (⋃ x ∈ S, t x) := dimH_mono hSU
    _ = ⨆ x ∈ S, dimH (t x) := (dimH_bUnion hSc _)
    _ ≤ r := iSup₂_le fun x hx => htr x <| hSs hx
#align exists_mem_nhds_within_lt_dimH_of_lt_dimH exists_mem_nhdsWithin_lt_dimH_of_lt_dimH

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` along
`(𝓝[s] x).small_sets`. -/
theorem bsupr_limsup_dimH (s : Set X) : (⨆ x ∈ s, limsup dimH (𝓝[s] x).smallSets) = dimH s :=
  by
  refine' le_antisymm (iSup₂_le fun x hx => _) _
  · refine' Limsup_le_of_le (by infer_param) (eventually_map.2 _)
    exact eventually_small_sets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · refine' le_of_forall_ge_of_dense fun r hr => _
    rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr with ⟨x, hxs, hxr⟩
    refine' le_iSup₂_of_le x hxs _; rw [limsup_eq]; refine' le_sInf fun b hb => _
    rcases eventually_small_sets.1 hb with ⟨t, htx, ht⟩
    exact (hxr t htx).le.trans (ht t subset.rfl)
#align bsupr_limsup_dimH bsupr_limsup_dimH

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` along
`(𝓝[s] x).small_sets`. -/
theorem iSup_limsup_dimH (s : Set X) : (⨆ x, limsup dimH (𝓝[s] x).smallSets) = dimH s :=
  by
  refine' le_antisymm (iSup_le fun x => _) _
  · refine' Limsup_le_of_le (by infer_param) (eventually_map.2 _)
    exact eventually_small_sets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _
#align supr_limsup_dimH iSup_limsup_dimH

end

/-!
### Hausdorff dimension and Hölder continuity
-/


variable {C K r : ℝ≥0} {f : X → Y} {s t : Set X}

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
theorem HolderOnWith.dimH_image_le (h : HolderOnWith C r f s) (hr : 0 < r) :
    dimH (f '' s) ≤ dimH s / r := by
  borelize X Y
  refine' dimH_le fun d hd => _
  have := h.hausdorff_measure_image_le hr d.coe_nonneg
  rw [hd, ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg, top_le_iff] at this 
  have Hrd : μH[(r * d : ℝ≥0)] s = ⊤ := by contrapose this;
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top this
  rw [ENNReal.le_div_iff_mul_le, mul_comm, ← ENNReal.coe_mul]
  exacts [le_dimH_of_hausdorffMeasure_eq_top Hrd, Or.inl (mt ENNReal.coe_eq_zero.1 hr.ne'),
    Or.inl ENNReal.coe_ne_top]
#align holder_on_with.dimH_image_le HolderOnWith.dimH_image_le

namespace HolderWith

/-- If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausdorff dimension
of the image of a set `s` is at most `dimH s / r`. -/
theorem dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) :
    dimH (f '' s) ≤ dimH s / r :=
  (h.HolderOnWith s).dimH_image_le hr
#align holder_with.dimH_image_le HolderWith.dimH_image_le

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dimension of its
range is at most the Hausdorff dimension of its domain divided by `r`. -/
theorem dimH_range_le (h : HolderWith C r f) (hr : 0 < r) :
    dimH (range f) ≤ dimH (univ : Set X) / r :=
  @image_univ _ _ f ▸ h.dimH_image_le hr univ
#align holder_with.dimH_range_le HolderWith.dimH_range_le

end HolderWith

/-- If `s` is a set in a space `X` with second countable topology and `f : X → Y` is Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same positive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `f '' s` is at most
the Hausdorff dimension of `s` divided by `r`. -/
theorem dimH_image_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) {s : Set X} (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C r f t) :
    dimH (f '' s) ≤ dimH s / r := by
  choose! C t htn hC using hf
  rcases countable_cover_nhds_within htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_Union₂] at huU 
  rw [← huU, image_Union₂, dimH_bUnion huc, dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono fun x hx => ((hC x (hus hx)).mono (inter_subset_right _ _)).dimH_image_le hr
#align dimH_image_le_of_locally_holder_on dimH_image_le_of_locally_holder_on

/-- If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` with the same
positive exponent `r` but possibly different coefficients, then the Hausdorff dimension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`. -/
theorem dimH_range_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, HolderOnWith C r f s) :
    dimH (range f) ≤ dimH (univ : Set X) / r :=
  by
  rw [← image_univ]
  refine' dimH_image_le_of_locally_holder_on hr fun x _ => _
  simpa only [exists_prop, nhdsWithin_univ] using hf x
#align dimH_range_le_of_locally_holder_on dimH_range_le_of_locally_holder_on

/-!
### Hausdorff dimension and Lipschitz continuity
-/


/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
theorem LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) ≤ dimH s := by
  simpa using h.holder_on_with.dimH_image_le zero_lt_one
#align lipschitz_on_with.dimH_image_le LipschitzOnWith.dimH_image_le

namespace LipschitzWith

/-- If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`. -/
theorem dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) ≤ dimH s :=
  (h.LipschitzOnWith s).dimH_image_le
#align lipschitz_with.dimH_image_le LipschitzWith.dimH_image_le

/-- If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range is at most the
Hausdorff dimension of its domain. -/
theorem dimH_range_le (h : LipschitzWith K f) : dimH (range f) ≤ dimH (univ : Set X) :=
  @image_univ _ _ f ▸ h.dimH_image_le univ
#align lipschitz_with.dimH_range_le LipschitzWith.dimH_range_le

end LipschitzWith

/-- If `s` is a set in an extended metric space `X` with second countable topology and `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausdorff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`. -/
theorem dimH_image_le_of_locally_lipschitz_on [SecondCountableTopology X] {f : X → Y} {s : Set X}
    (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith C f t) : dimH (f '' s) ≤ dimH s :=
  by
  have : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C 1 f t := by
    simpa only [holderOnWith_one] using hf
  simpa only [ENNReal.coe_one, div_one] using dimH_image_le_of_locally_holder_on zero_lt_one this
#align dimH_image_le_of_locally_lipschitz_on dimH_image_le_of_locally_lipschitz_on

/-- If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Hausdorff
dimension of `range f` is at most the Hausdorff dimension of `X`. -/
theorem dimH_range_le_of_locally_lipschitz_on [SecondCountableTopology X] {f : X → Y}
    (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s) :
    dimH (range f) ≤ dimH (univ : Set X) :=
  by
  rw [← image_univ]
  refine' dimH_image_le_of_locally_lipschitz_on fun x _ => _
  simpa only [exists_prop, nhdsWithin_univ] using hf x
#align dimH_range_le_of_locally_lipschitz_on dimH_range_le_of_locally_lipschitz_on

namespace AntilipschitzWith

theorem dimH_preimage_le (hf : AntilipschitzWith K f) (s : Set Y) : dimH (f ⁻¹' s) ≤ dimH s :=
  by
  borelize X Y
  refine' dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top _
  have := hf.hausdorff_measure_preimage_le d.coe_nonneg s
  rw [hd, top_le_iff] at this 
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this
#align antilipschitz_with.dimH_preimage_le AntilipschitzWith.dimH_preimage_le

theorem le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s ≤ dimH (f '' s) :=
  calc
    dimH s ≤ dimH (f ⁻¹' (f '' s)) := dimH_mono (subset_preimage_image _ _)
    _ ≤ dimH (f '' s) := hf.dimH_preimage_le _
#align antilipschitz_with.le_dimH_image AntilipschitzWith.le_dimH_image

end AntilipschitzWith

/-!
### Isometries preserve Hausdorff dimension
-/


theorem Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s :=
  le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)
#align isometry.dimH_image Isometry.dimH_image

namespace IsometryEquiv

@[simp]
theorem dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s :=
  e.Isometry.dimH_image s
#align isometry_equiv.dimH_image IsometryEquiv.dimH_image

@[simp]
theorem dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm, e.symm.dimH_image]
#align isometry_equiv.dimH_preimage IsometryEquiv.dimH_preimage

theorem dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y) := by
  rw [← e.dimH_preimage univ, preimage_univ]
#align isometry_equiv.dimH_univ IsometryEquiv.dimH_univ

end IsometryEquiv

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
theorem dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s :=
  le_antisymm (e.lipschitz.dimH_image_le s) <| by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)
#align continuous_linear_equiv.dimH_image ContinuousLinearEquiv.dimH_image

@[simp]
theorem dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm_eq_preimage, e.symm.dimH_image]
#align continuous_linear_equiv.dimH_preimage ContinuousLinearEquiv.dimH_preimage

theorem dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F) := by
  rw [← e.dimH_preimage, preimage_univ]
#align continuous_linear_equiv.dimH_univ ContinuousLinearEquiv.dimH_univ

end ContinuousLinearEquiv

/-!
### Hausdorff dimension in a real vector space
-/


namespace Real

variable {E : Type _} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem dimH_ball_pi (x : ι → ℝ) {r : ℝ} (hr : 0 < r) : dimH (Metric.ball x r) = Fintype.card ι :=
  by
  cases isEmpty_or_nonempty ι
  · rwa [dimH_subsingleton, eq_comm, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact fun x _ y _ => Subsingleton.elim x y
  · rw [← ENNReal.coe_nat]
    have : μH[Fintype.card ι] (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
      rw [hausdorff_measure_pi_real, Real.volume_pi_ball _ hr]
    refine' dimH_of_hausdorffMeasure_ne_zero_ne_top _ _ <;> rw [NNReal.coe_nat_cast, this]
    · simp [pow_pos (mul_pos (zero_lt_two' ℝ) hr)]
    · exact ENNReal.ofReal_ne_top
#align real.dimH_ball_pi Real.dimH_ball_pi

theorem dimH_ball_pi_fin {n : ℕ} (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = n := by rw [dimH_ball_pi x hr, Fintype.card_fin]
#align real.dimH_ball_pi_fin Real.dimH_ball_pi_fin

theorem dimH_univ_pi (ι : Type _) [Fintype ι] : dimH (univ : Set (ι → ℝ)) = Fintype.card ι := by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι → ℝ), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]
#align real.dimH_univ_pi Real.dimH_univ_pi

theorem dimH_univ_pi_fin (n : ℕ) : dimH (univ : Set (Fin n → ℝ)) = n := by
  rw [dimH_univ_pi, Fintype.card_fin]
#align real.dimH_univ_pi_fin Real.dimH_univ_pi_fin

theorem dimH_of_mem_nhds {x : E} {s : Set E} (h : s ∈ 𝓝 x) : dimH s = finrank ℝ E :=
  by
  have e : E ≃L[ℝ] Fin (finrank ℝ E) → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (FiniteDimensional.finrank_fin_fun ℝ).symm
  rw [← e.dimH_image]
  refine' le_antisymm _ _
  · exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)
  · have : e '' s ∈ 𝓝 (e x) := by rw [← e.map_nhds_eq]; exact image_mem_map h
    rcases metric.nhds_basis_ball.mem_iff.1 this with ⟨r, hr0, hr⟩
    simpa only [dimH_ball_pi_fin (e x) hr0] using dimH_mono hr
#align real.dimH_of_mem_nhds Real.dimH_of_mem_nhds

theorem dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s = finrank ℝ E :=
  let ⟨x, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)
#align real.dimH_of_nonempty_interior Real.dimH_of_nonempty_interior

variable (E)

theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank ℝ E :=
  dimH_of_mem_nhds (@univ_mem _ (𝓝 0))
#align real.dimH_univ_eq_finrank Real.dimH_univ_eq_finrank

theorem dimH_univ : dimH (univ : Set ℝ) = 1 := by
  rw [dimH_univ_eq_finrank ℝ, FiniteDimensional.finrank_self, Nat.cast_one]
#align real.dimH_univ Real.dimH_univ

end Real

variable {E F : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank ℝ E) : Dense (sᶜ) :=
  by
  refine' fun x => mem_closure_iff_nhds.2 fun t ht => nonempty_iff_ne_empty.2 fun he => hs.not_le _
  rw [← diff_eq, diff_eq_empty] at he 
  rw [← Real.dimH_of_mem_nhds ht]
  exact dimH_mono he
#align dense_compl_of_dimH_lt_finrank dense_compl_of_dimH_lt_finrank

/-!
### Hausdorff dimension and `C¹`-smooth maps

`C¹`-smooth maps are locally Lipschitz continuous, hence they do not increase the Hausdorff
dimension of sets.
-/


/-- Let `f` be a function defined on a finite dimensional real normed space. If `f` is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or equal to the Hausdorff
dimension of `s`.

TODO: do we actually need `convex ℝ s`? -/
theorem ContDiffOn.dimH_image_le {f : E → F} {s t : Set E} (hf : ContDiffOn ℝ 1 f s)
    (hc : Convex ℝ s) (ht : t ⊆ s) : dimH (f '' t) ≤ dimH t :=
  dimH_image_le_of_locally_lipschitz_on fun x hx =>
    let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitzOnWith hc
    ⟨C, u, nhdsWithin_mono _ ht hu, hf⟩
#align cont_diff_on.dimH_image_le ContDiffOn.dimH_image_le

/-- The Hausdorff dimension of the range of a `C¹`-smooth function defined on a finite dimensional
real normed space is at most the dimension of its domain as a vector space over `ℝ`. -/
theorem ContDiff.dimH_range_le {f : E → F} (h : ContDiff ℝ 1 f) : dimH (range f) ≤ finrank ℝ E :=
  calc
    dimH (range f) = dimH (f '' univ) := by rw [image_univ]
    _ ≤ dimH (univ : Set E) := (h.ContDiffOn.dimH_image_le convex_univ Subset.rfl)
    _ = finrank ℝ E := Real.dimH_univ_eq_finrank E
#align cont_diff.dimH_range_le ContDiff.dimH_range_le

/-- A particular case of Sard's Theorem. Let `f : E → F` be a map between finite dimensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is dense in `F`. -/
theorem ContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    {s t : Set E} (h : ContDiffOn ℝ 1 f s) (hc : Convex ℝ s) (ht : t ⊆ s)
    (htF : dimH t < finrank ℝ F) : Dense ((f '' t)ᶜ) :=
  dense_compl_of_dimH_lt_finrank <| (h.dimH_image_le hc ht).trans_lt htF
#align cont_diff_on.dense_compl_image_of_dimH_lt_finrank ContDiffOn.dense_compl_image_of_dimH_lt_finrank

/-- A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vector space to a
real vector space `F` of strictly larger dimension, then the complement of the range of `f` is dense
in `F`. -/
theorem ContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    (h : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) : Dense (range fᶜ) :=
  dense_compl_of_dimH_lt_finrank <| h.dimH_range_le.trans_lt <| Nat.cast_lt.2 hEF
#align cont_diff.dense_compl_range_of_finrank_lt_finrank ContDiff.dense_compl_range_of_finrank_lt_finrank

