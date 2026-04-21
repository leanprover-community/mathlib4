/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `MeasureTheory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `MeasureTheory.dimH (Set.univ : Set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorffMeasure_of_lt_dimH`, `dimH_le_of_hausdorffMeasure_ne_top`,
  `le_dimH_of_hausdorffMeasure_eq_top`, `hausdorffMeasure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorffMeasure_ne_zero`, `dimH_of_hausdorffMeasure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_iUnion`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `Set.Subsingleton.dimH_zero`, `Set.Countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `HolderWith.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `HolderWith`,
  `HolderOnWith`, and locally Hölder maps, as well as for `Set.image` and `Set.range`.
* `LipschitzWith.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `Isometry` or
  a `ContinuousLinearEquiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `Real.dimH_of_nonempty_interior`: if `s` is a set in a finite-dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite-dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `ContDiff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notation

We use the following notation localized in `MeasureTheory`. It is defined in
`MeasureTheory.Measure.Hausdorff`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[MeasurableSpace X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[MeasurableSpace X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open scoped MeasureTheory ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Module Filter

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/-- Hausdorff dimension of a set in an (e)metric space. -/
@[irreducible] noncomputable def dimH (s : Set X) : ℝ≥0∞ := by
  borelize X; exact ⨆ (d : ℝ≥0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d

/-!
### Basic properties
-/


section Measurable

variable [MeasurableSpace X] [BorelSpace X]

/-- Unfold the definition of `dimH` using `[MeasurableSpace X] [BorelSpace X]` from the
environment. -/
theorem dimH_def (s : Set X) : dimH s = ⨆ (d : ℝ≥0) (_ : μH[d] s = ∞), (d : ℝ≥0∞) := by
  borelize X; rw [dimH]

theorem hausdorffMeasure_of_lt_dimH {s : Set X} {d : ℝ≥0} (h : ↑d < dimH s) : μH[d] s = ∞ := by
  simp only [dimH_def, lt_iSup_iff] at h
  rcases h with ⟨d', hsd', hdd'⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hdd'
  exact top_unique (hsd' ▸ hausdorffMeasure_mono hdd'.le _)

theorem dimH_le {s : Set X} {d : ℝ≥0∞} (H : ∀ d' : ℝ≥0, μH[d'] s = ∞ → ↑d' ≤ d) : dimH s ≤ d :=
  (dimH_def s).trans_le <| iSup₂_le H

theorem dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ ∞) : dimH s ≤ d :=
  le_of_not_gt <| mt hausdorffMeasure_of_lt_dimH h

theorem le_dimH_of_hausdorffMeasure_eq_top {s : Set X} {d : ℝ≥0} (h : μH[d] s = ∞) :
    ↑d ≤ dimH s := by
  rw [dimH_def]; exact le_iSup₂ (α := ℝ≥0∞) d h

theorem hausdorffMeasure_of_dimH_lt {s : Set X} {d : ℝ≥0} (h : dimH s < d) : μH[d] s = 0 := by
  rw [dimH_def] at h
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at hd'd
  exact (hausdorffMeasure_zero_or_top hd'd s).resolve_right fun h₂ => hsd'.not_ge <|
    le_iSup₂ (α := ℝ≥0∞) d' h₂

theorem measure_zero_of_dimH_lt {μ : Measure X} {d : ℝ≥0} (h : μ ≪ μH[d]) {s : Set X}
    (hd : dimH s < d) : μ s = 0 :=
  h <| hausdorffMeasure_of_dimH_lt hd

theorem le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : ℝ≥0} (h : μH[d] s ≠ 0) : ↑d ≤ dimH s :=
  le_of_not_gt <| mt hausdorffMeasure_of_dimH_lt h

theorem dimH_of_hausdorffMeasure_ne_zero_ne_top {d : ℝ≥0} {s : Set X} (h : μH[d] s ≠ 0)
    (h' : μH[d] s ≠ ∞) : dimH s = d :=
  le_antisymm (dimH_le_of_hausdorffMeasure_ne_top h') (le_dimH_of_hausdorffMeasure_ne_zero h)

/-- The Hausdorff dimension of a set `s` is the infimum of all `d : ℝ≥0` such that the
`d`-dimensional Hausdorff measure of `s` is zero. This infimum is taken in `ℝ≥0∞`.
This gives an equivalent definition of the Hausdorff dimension. -/
theorem dimH_eq_iInf (s : Set X) : dimH s = ⨅ (d : ℝ≥0) (_ : μH[d] s = 0), (d : ℝ≥0∞) := by
  apply le_antisymm
  · rw [dimH_def]
    simp only [le_iInf_iff, iSup_le_iff, ENNReal.coe_le_coe]
    intro i hi j hj
    by_contra! hij
    simpa [hi, hj] using hausdorffMeasure_mono hij.le s
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hdim_lt, hlt⟩
    have h0 : μH[d'] s = 0 := hausdorffMeasure_of_dimH_lt hdim_lt
    exact hlt.not_ge (iInf₂_le d' h0)

end Measurable

@[mono]
theorem dimH_mono {s t : Set X} (h : s ⊆ t) : dimH s ≤ dimH t := by
  borelize X
  exact dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top <| top_unique <| hd ▸ measure_mono h

theorem dimH_subsingleton {s : Set X} (h : s.Subsingleton) : dimH s = 0 := by
  borelize X
  apply le_antisymm _ (zero_le _)
  refine dimH_le_of_hausdorffMeasure_ne_top ?_
  exact ((hausdorffMeasure_le_one_of_subsingleton h le_rfl).trans_lt ENNReal.one_lt_top).ne

alias Set.Subsingleton.dimH_zero := dimH_subsingleton

@[simp]
theorem dimH_empty : dimH (∅ : Set X) = 0 :=
  subsingleton_empty.dimH_zero

@[simp]
theorem dimH_singleton (x : X) : dimH ({x} : Set X) = 0 :=
  subsingleton_singleton.dimH_zero

@[simp]
theorem dimH_iUnion {ι : Sort*} [Countable ι] (s : ι → Set X) :
    dimH (⋃ i, s i) = ⨆ i, dimH (s i) := by
  borelize X
  refine le_antisymm (dimH_le fun d hd => ?_) (iSup_le fun i => dimH_mono <| subset_iUnion _ _)
  contrapose! hd
  have : ∀ i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_iUnion_null this]
  exact ENNReal.zero_ne_top

@[simp]
theorem dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι → Set X) :
    dimH (⋃ i ∈ s, t i) = ⨆ i ∈ s, dimH (t i) := by
  haveI := hs.toEncodable
  rw [biUnion_eq_iUnion, dimH_iUnion, ← iSup_subtype'']

@[simp]
theorem dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s ∈ S, dimH s := by
  rw [sUnion_eq_biUnion, dimH_bUnion hS]

@[simp]
theorem dimH_union (s t : Set X) : dimH (s ∪ t) = max (dimH s) (dimH t) := by
  rw [union_eq_iUnion, dimH_iUnion, iSup_bool_eq, cond, cond]

theorem dimH_countable {s : Set X} (hs : s.Countable) : dimH s = 0 :=
  biUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ENNReal.iSup_zero]

alias Set.Countable.dimH_zero := dimH_countable

theorem dimH_finite {s : Set X} (hs : s.Finite) : dimH s = 0 :=
  hs.countable.dimH_zero

alias Set.Finite.dimH_zero := dimH_finite

@[simp]
theorem dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0 :=
  s.finite_toSet.dimH_zero

alias Finset.dimH_zero := dimH_coe_finset

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
  rcases countable_cover_nhdsWithin htx with ⟨S, hSs, hSc, hSU⟩
  calc
    dimH s ≤ dimH (⋃ x ∈ S, t x) := dimH_mono hSU
    _ = ⨆ x ∈ S, dimH (t x) := dimH_bUnion hSc _
    _ ≤ r := iSup₂_le fun x hx => htr x <| hSs hx

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over `x ∈ s` of the limit superiors of `dimH t` along
`(𝓝[s] x).smallSets`. -/
theorem bsupr_limsup_dimH (s : Set X) : ⨆ x ∈ s, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr with ⟨x, hxs, hxr⟩
    refine le_iSup₂_of_le x hxs ?_; rw [limsup_eq]; refine le_sInf fun b hb => ?_
    rcases eventually_smallSets.1 hb with ⟨t, htx, ht⟩
    exact (hxr t htx).le.trans (ht t Subset.rfl)

/-- In an (extended) metric space with second countable topology, the Hausdorff dimension
of a set `s` is the supremum over all `x` of the limit superiors of `dimH t` along
`(𝓝[s] x).smallSets`. -/
theorem iSup_limsup_dimH (s : Set X) : ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _

end

/-!
### Hausdorff dimension and Hölder continuity
-/


variable {C K r : ℝ≥0} {f : X → Y} {s : Set X}

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then `dimH (f '' s) ≤ dimH s / r`. -/
theorem HolderOnWith.dimH_image_le (h : HolderOnWith C r f s) (hr : 0 < r) :
    dimH (f '' s) ≤ dimH s / r := by
  borelize X Y
  refine dimH_le fun d hd => ?_
  have := h.hausdorffMeasure_image_le hr d.coe_nonneg
  rw [hd, ← ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg, top_le_iff] at this
  have Hrd : μH[(r * d : ℝ≥0)] s = ⊤ := by
    contrapose this
    finiteness
  rw [ENNReal.le_div_iff_mul_le, mul_comm, ← ENNReal.coe_mul]
  exacts [le_dimH_of_hausdorffMeasure_eq_top Hrd, Or.inl (mt ENNReal.coe_eq_zero.1 hr.ne'),
    Or.inl ENNReal.coe_ne_top]

namespace HolderWith

/-- If `f : X → Y` is Hölder continuous with a positive exponent `r`, then the Hausdorff dimension
of the image of a set `s` is at most `dimH s / r`. -/
theorem dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) :
    dimH (f '' s) ≤ dimH s / r :=
  (h.holderOnWith s).dimH_image_le hr

/-- If `f` is a Hölder continuous map with exponent `r > 0`, then the Hausdorff dimension of its
range is at most the Hausdorff dimension of its domain divided by `r`. -/
theorem dimH_range_le (h : HolderWith C r f) (hr : 0 < r) :
    dimH (range f) ≤ dimH (univ : Set X) / r :=
  @image_univ _ _ f ▸ h.dimH_image_le hr univ

end HolderWith

/-- If `s` is a set in a space `X` with second countable topology and `f : X → Y` is Hölder
continuous in a neighborhood within `s` of every point `x ∈ s` with the same positive exponent `r`
but possibly different coefficients, then the Hausdorff dimension of the image `f '' s` is at most
the Hausdorff dimension of `s` divided by `r`. -/
theorem dimH_image_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) {s : Set X} (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C r f t) :
    dimH (f '' s) ≤ dimH s / r := by
  choose! C t htn hC using hf
  rcases countable_cover_nhdsWithin htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_iUnion₂] at huU
  rw [← huU, image_iUnion₂, dimH_bUnion huc, dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono fun x hx => ((hC x (hus hx)).mono inter_subset_right).dimH_image_le hr

/-- If `f : X → Y` is Hölder continuous in a neighborhood of every point `x : X` with the same
positive exponent `r` but possibly different coefficients, then the Hausdorff dimension of the range
of `f` is at most the Hausdorff dimension of `X` divided by `r`. -/
theorem dimH_range_le_of_locally_holder_on [SecondCountableTopology X] {r : ℝ≥0} {f : X → Y}
    (hr : 0 < r) (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, HolderOnWith C r f s) :
    dimH (range f) ≤ dimH (univ : Set X) / r := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_holder_on hr fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

/-!
### Hausdorff dimension and Lipschitz continuity
-/


set_option backward.isDefEq.respectTransparency false in
/-- If `f : X → Y` is Lipschitz continuous on `s`, then `dimH (f '' s) ≤ dimH s`. -/
theorem LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) ≤ dimH s := by
  simpa using h.holderOnWith.dimH_image_le zero_lt_one

namespace LipschitzWith

/-- If `f` is a Lipschitz continuous map, then `dimH (f '' s) ≤ dimH s`. -/
theorem dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) ≤ dimH s :=
  h.lipschitzOnWith.dimH_image_le

/-- If `f` is a Lipschitz continuous map, then the Hausdorff dimension of its range is at most the
Hausdorff dimension of its domain. -/
theorem dimH_range_le (h : LipschitzWith K f) : dimH (range f) ≤ dimH (univ : Set X) :=
  @image_univ _ _ f ▸ h.dimH_image_le univ

end LipschitzWith

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is a set in an extended metric space `X` with second countable topology and `f : X → Y`
is Lipschitz in a neighborhood within `s` of every point `x ∈ s`, then the Hausdorff dimension of
the image `f '' s` is at most the Hausdorff dimension of `s`. -/
theorem dimH_image_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X → Y} {s : Set X}
    (hf : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, LipschitzOnWith C f t) : dimH (f '' s) ≤ dimH s := by
  have : ∀ x ∈ s, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[s] x, HolderOnWith C 1 f t := by
    simpa only [holderOnWith_one] using hf
  simpa only [ENNReal.coe_one, div_one] using dimH_image_le_of_locally_holder_on zero_lt_one this

/-- If `f : X → Y` is Lipschitz in a neighborhood of each point `x : X`, then the Hausdorff
dimension of `range f` is at most the Hausdorff dimension of `X`. -/
theorem dimH_range_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X → Y}
    (hf : ∀ x : X, ∃ C : ℝ≥0, ∃ s ∈ 𝓝 x, LipschitzOnWith C f s) :
    dimH (range f) ≤ dimH (univ : Set X) := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_lipschitzOn fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

namespace AntilipschitzWith

theorem dimH_preimage_le (hf : AntilipschitzWith K f) (s : Set Y) : dimH (f ⁻¹' s) ≤ dimH s := by
  borelize X Y
  refine dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top ?_
  have := hf.hausdorffMeasure_preimage_le d.coe_nonneg s
  rw [hd, top_le_iff] at this
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this

theorem le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s ≤ dimH (f '' s) :=
  calc
    dimH s ≤ dimH (f ⁻¹' (f '' s)) := dimH_mono (subset_preimage_image _ _)
    _ ≤ dimH (f '' s) := hf.dimH_preimage_le _

end AntilipschitzWith

/-!
### Isometries preserve Hausdorff dimension
-/


theorem Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s :=
  le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

namespace IsometryEquiv

@[simp]
theorem dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s :=
  e.isometry.dimH_image s

@[simp]
theorem dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm, e.symm.dimH_image]

theorem dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y) := by
  rw [← e.dimH_preimage univ, preimage_univ]

end IsometryEquiv

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
theorem dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s :=
  le_antisymm (e.lipschitz.dimH_image_le s) <| by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]
theorem dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm_eq_preimage, e.symm.dimH_image]

theorem dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F) := by
  rw [← e.dimH_preimage, preimage_univ]

end ContinuousLinearEquiv

/-!
### Hausdorff dimension in a real vector space
-/


namespace Real

variable {E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem dimH_ball_pi (x : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = Fintype.card ι := by
  cases isEmpty_or_nonempty ι
  · rwa [dimH_subsingleton, eq_comm, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact fun x _ y _ => Subsingleton.elim x y
  · rw [← ENNReal.coe_natCast]
    have : μH[Fintype.card ι] (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
      rw [hausdorffMeasure_pi_real, Real.volume_pi_ball _ hr]
    refine dimH_of_hausdorffMeasure_ne_zero_ne_top ?_ ?_ <;> rw [NNReal.coe_natCast, this]
    · simp [pow_pos (mul_pos (zero_lt_two' ℝ) hr)]
    · exact ENNReal.ofReal_ne_top

theorem dimH_ball_pi_fin {n : ℕ} (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    dimH (Metric.ball x r) = n := by rw [dimH_ball_pi x hr, Fintype.card_fin]

theorem dimH_univ_pi (ι : Type*) [Fintype ι] : dimH (univ : Set (ι → ℝ)) = Fintype.card ι := by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι → ℝ), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]

theorem dimH_univ_pi_fin (n : ℕ) : dimH (univ : Set (Fin n → ℝ)) = n := by
  rw [dimH_univ_pi, Fintype.card_fin]

theorem dimH_of_mem_nhds {x : E} {s : Set E} (h : s ∈ 𝓝 x) : dimH s = finrank ℝ E := by
  have e : E ≃L[ℝ] Fin (finrank ℝ E) → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  rw [← e.dimH_image]
  refine le_antisymm ?_ ?_
  · exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)
  · have : e '' s ∈ 𝓝 (e x) := by rw [← e.map_nhds_eq]; exact image_mem_map h
    rcases Metric.nhds_basis_ball.mem_iff.1 this with ⟨r, hr0, hr⟩
    simpa only [dimH_ball_pi_fin (e x) hr0] using dimH_mono hr

theorem dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s = finrank ℝ E :=
  let ⟨_, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

set_option backward.isDefEq.respectTransparency false in
/-- The Hausdorff dimension of a nonempty convex set equals the dimension of its affine span. -/
theorem Convex.dimH_eq_finrank_vectorSpan {s : Set E} (hcvx : Convex ℝ s) (hne : s.Nonempty) :
    dimH s = finrank ℝ (vectorSpan ℝ s) := by
  have := hne.to_subtype
  let φ := AffineIsometryEquiv.constVSub ℝ
    (⟨hne.some, subset_affineSpan ℝ s hne.some_mem⟩ : affineSpan ℝ s)
  have hs_eq : s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan ℝ s)) :=
    (image_preimage_eq_of_subset <| (subset_affineSpan ℝ s).trans Subtype.range_coe.superset).symm
  rw [hs_eq, isometry_subtype_coe.dimH_image, ← φ.isometry.dimH_image,
      Real.dimH_of_nonempty_interior, direction_affineSpan ℝ s, ← hs_eq]
  simp_rw [← AffineIsometryEquiv.coe_toHomeomorph, ← φ.toHomeomorph.image_interior, image_nonempty]
  simpa [intrinsicInterior] using (intrinsicInterior_nonempty hcvx).mpr hne

variable (E)

theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank ℝ E :=
  dimH_of_mem_nhds (@univ_mem _ (𝓝 0))

theorem dimH_univ : dimH (univ : Set ℝ) = 1 := by
  rw [dimH_univ_eq_finrank ℝ, Module.finrank_self, Nat.cast_one]

variable {E}

/-- The Hausdorff dimension of any set in a finite-dimensional real normed space is finite. -/
theorem dimH_lt_top (s : Set E) : dimH s < ⊤ := by calc
  dimH s ≤ dimH (univ : Set E) := dimH_mono (subset_univ s)
  _ = finrank ℝ E := dimH_univ_eq_finrank E
  _ < ⊤ := by simp

theorem dimH_ne_top (s : Set E) : dimH s ≠ ⊤ := (dimH_lt_top s).ne

lemma hausdorffMeasure_of_finrank_lt [MeasurableSpace E] [BorelSpace E] {d : ℝ}
    (hd : finrank ℝ E < d) : (μH[d] : Measure E) = 0 := by
  lift d to ℝ≥0 using (Nat.cast_nonneg _).trans hd.le
  rw [← measure_univ_eq_zero]
  apply hausdorffMeasure_of_dimH_lt
  rw [dimH_univ_eq_finrank]
  exact mod_cast hd

/-- The Hausdorff dimension of a non-degenerate segment in a real normed space is 1. -/
theorem dimH_segment {x y : E} (h : x ≠ y) :
    dimH (segment ℝ x y) = 1 := by
  rw [Convex.dimH_eq_finrank_vectorSpan (convex_segment x y) ⟨x, left_mem_segment ℝ x y⟩,
      vectorSpan_segment]
  simp [finrank_span_singleton (sub_ne_zero.mpr h.symm)]

end Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank ℝ E) : Dense sᶜ := by
  refine fun x => mem_closure_iff_nhds.2 fun t ht => nonempty_iff_ne_empty.2 fun he => hs.not_ge ?_
  rw [← diff_eq, diff_eq_empty] at he
  rw [← Real.dimH_of_mem_nhds ht]
  exact dimH_mono he

/-!
### Hausdorff dimension and `C¹`-smooth maps

`C¹`-smooth maps are locally Lipschitz continuous, hence they do not increase the Hausdorff
dimension of sets.
-/


/-- Let `f` be a function defined on a finite-dimensional real normed space. If `f` is `C¹`-smooth
on a convex set `s`, then the Hausdorff dimension of `f '' s` is less than or equal to the Hausdorff
dimension of `s`.

TODO: do we actually need `Convex ℝ s`? -/
theorem ContDiffOn.dimH_image_le {f : E → F} {s t : Set E} (hf : ContDiffOn ℝ 1 f s)
    (hc : Convex ℝ s) (ht : t ⊆ s) : dimH (f '' t) ≤ dimH t :=
  dimH_image_le_of_locally_lipschitzOn fun x hx =>
    let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitzOnWith hc
    ⟨C, u, nhdsWithin_mono _ ht hu, hf⟩

/-- The Hausdorff dimension of the range of a `C¹`-smooth function defined on a finite-dimensional
real normed space is at most the dimension of its domain as a vector space over `ℝ`. -/
theorem ContDiff.dimH_range_le {f : E → F} (h : ContDiff ℝ 1 f) : dimH (range f) ≤ finrank ℝ E :=
  calc
    dimH (range f) = dimH (f '' univ) := by rw [image_univ]
    _ ≤ dimH (univ : Set E) := h.contDiffOn.dimH_image_le convex_univ Subset.rfl
    _ = finrank ℝ E := Real.dimH_univ_eq_finrank E

/-- A particular case of Sard's Theorem. Let `f : E → F` be a map between finite-dimensional real
vector spaces. Suppose that `f` is `C¹` smooth on a convex set `s` of Hausdorff dimension strictly
less than the dimension of `F`. Then the complement of the image `f '' s` is dense in `F`. -/
theorem ContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    {s t : Set E} (h : ContDiffOn ℝ 1 f s) (hc : Convex ℝ s) (ht : t ⊆ s)
    (htF : dimH t < finrank ℝ F) : Dense (f '' t)ᶜ :=
  dense_compl_of_dimH_lt_finrank <| (h.dimH_image_le hc ht).trans_lt htF

/-- A particular case of Sard's Theorem. If `f` is a `C¹` smooth map from a real vector space to a
real vector space `F` of strictly larger dimension, then the complement of the range of `f` is dense
in `F`. -/
theorem ContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional ℝ F] {f : E → F}
    (h : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) : Dense (range f)ᶜ :=
  dense_compl_of_dimH_lt_finrank <| h.dimH_range_le.trans_lt <| Nat.cast_lt.2 hEF

/--
The Hausdorff dimension of the orthogonal projection of a set `s` onto a subspace `K`
is less than or equal to the Hausdorff dimension of `s`.
-/
theorem dimH_orthogonalProjection_le {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (s : Set E) :
    dimH (K.orthogonalProjection '' s) ≤ dimH s :=
  K.lipschitzWith_orthogonalProjection.dimH_image_le s
