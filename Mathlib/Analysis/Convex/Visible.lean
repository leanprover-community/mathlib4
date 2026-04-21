/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.Monotone

/-!
# Points in sight

This file defines the relation of visibility with respect to a set, and lower bounds how many
elements of a set a point sees in terms of the dimension of that set.

## TODO

The art gallery problem can be stated using the visibility predicate: A set `A` (the art gallery) is
guarded by a finite set `G` (the guards) iff `∀ a ∈ A, ∃ g ∈ G, IsVisible ℝ sᶜ a g`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open AffineMap Filter Finset Set
open scoped Cardinal Pointwise Topology

variable {𝕜 V P : Type*}

section AddTorsor
variable [Field 𝕜] [LinearOrder 𝕜] [IsOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
  {s t : Set P} {x y z : P}

omit [IsOrderedRing 𝕜] in
variable (𝕜) in
/-- Two points are visible to each other through a set if no point of that set lies strictly
between them.

By convention, a point `x` sees itself through any set `s`, even when `x ∈ s`. -/
def IsVisible (s : Set P) (x y : P) : Prop := ∀ ⦃z⦄, z ∈ s → ¬ Sbtw 𝕜 x z y

@[simp, refl]
lemma IsVisible.rfl : IsVisible 𝕜 s x x := by simp [IsVisible]

lemma isVisible_comm : IsVisible 𝕜 s x y ↔ IsVisible 𝕜 s y x := by
  simp [IsVisible, sbtw_comm]

@[symm] alias ⟨IsVisible.symm, _⟩ := isVisible_comm

omit [IsOrderedRing 𝕜] in
lemma IsVisible.mono (hst : s ⊆ t) (ht : IsVisible 𝕜 t x y) : IsVisible 𝕜 s x y :=
  fun _z hz ↦ ht <| hst hz

lemma isVisible_iff_lineMap (hxy : x ≠ y) :
    IsVisible 𝕜 s x y ↔ ∀ δ ∈ Set.Ioo (0 : 𝕜) 1, lineMap x y δ ∉ s := by
  simp [IsVisible, sbtw_iff_mem_image_Ioo_and_ne, hxy]
  aesop

end AddTorsor

section Module
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {s : Set V} {x y z : V}

/-- If a point `x` sees a convex combination of points of a set `s` through `convexHull ℝ s ∌ x`,
then it sees all terms of that combination.

Note that the converse does not hold. -/
lemma IsVisible.of_convexHull_of_pos {ι : Type*} {t : Finset ι} {a : ι → V} {w : ι → 𝕜}
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1) (ha : ∀ i ∈ t, a i ∈ s)
    (hx : x ∉ convexHull 𝕜 s) (hw : IsVisible 𝕜 (convexHull 𝕜 s) x (∑ i ∈ t, w i • a i)) {i : ι}
    (hi : i ∈ t) (hwi : 0 < w i) : IsVisible 𝕜 (convexHull 𝕜 s) x (a i) := by
  classical
  obtain hwi | hwi : w i = 1 ∨ w i < 1 := eq_or_lt_of_le <| (single_le_sum hw₀ hi).trans_eq hw₁
  · convert hw
    rw [← one_smul 𝕜 (a i), ← hwi, eq_comm]
    rw [← hwi, ← sub_eq_zero, ← sum_erase_eq_sub hi,
      sum_eq_zero_iff_of_nonneg fun j hj ↦ hw₀ _ <| erase_subset _ _ hj] at hw₁
    refine sum_eq_single _ (fun j hj hji ↦ ?_) (by simp [hi])
    rw [hw₁ _ <| mem_erase.2 ⟨hji, hj⟩, zero_smul]
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, h⟩
  replace hε₀ : 0 < ε := hε₀.lt_of_ne <| by rintro rfl; simp at h
  replace hε₁ : ε < 1 := hε₁.lt_of_ne <| by rintro rfl; simp at h
  have : 0 < 1 - ε := by linarith
  have hwi : 0 < 1 - w i := by linarith
  refine hw (z := lineMap x (∑ j ∈ t, w j • a j) ((w i)⁻¹ / ((1 - ε) / ε + (w i)⁻¹)))
    ?_ <| sbtw_lineMap_iff.2 ⟨(ne_of_mem_of_not_mem ((convex_convexHull ..).sum_mem hw₀ hw₁
    fun i hi ↦ subset_convexHull _ _ <| ha _ hi) hx).symm, by positivity,
    (div_lt_one <| by positivity).2 ?_⟩
  · have : Wbtw 𝕜
      (lineMap x (a i) ε)
      (lineMap x (∑ j ∈ t, w j • a j) ((w i)⁻¹ / ((1 - ε) / ε + (w i)⁻¹)))
      (∑ j ∈ t.erase i, (w j / (1 - w i)) • a j) := by
      refine ⟨((1 - w i) / w i) / ((1 - ε) / ε + (1 - w i) / w i + 1), ⟨by positivity, ?_⟩, ?_⟩
      · refine (div_le_one <| by positivity).2 ?_
        calc
          (1 - w i) / w i = 0 + (1 - w i) / w i + 0 := by simp
          _ ≤ (1 - ε) / ε + (1 - w i) / w i + 1 := by gcongr <;> positivity
      have :
        w i • a i + (1 - w i) • ∑ j ∈ t.erase i, (w j / (1 - w i)) • a j = ∑ j ∈ t, w j • a j := by
        rw [smul_sum]
        simp_rw [smul_smul, mul_div_cancel₀ _ hwi.ne']
        exact add_sum_erase _ (fun i ↦ w i • a i) hi
      simp_rw [lineMap_apply_module, ← this]
      match_scalars <;> field
    refine (convex_convexHull _ _).mem_of_wbtw this hε <| (convex_convexHull _ _).sum_mem ?_ ?_ ?_
    · intro j hj
      positivity [hw₀ j <| erase_subset _ _ hj]
    · rw [← sum_div, sum_erase_eq_sub hi, hw₁, div_self hwi.ne']
    · exact fun j hj ↦ subset_convexHull _ _ <| ha _ <| erase_subset _ _ hj
  · exact lt_add_of_pos_left _ <| by positivity

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V]

/-- One cannot see any point in the interior of a set. -/
lemma IsVisible.eq_of_mem_interior (hsxy : IsVisible 𝕜 s x y) (hy : y ∈ interior s) :
    x = y := by
  by_contra! hxy
  suffices h : ∀ᶠ (_δ : 𝕜) in 𝓝[>] 0, False by obtain ⟨_, ⟨⟩⟩ := h.exists
  have hmem : ∀ᶠ (δ : 𝕜) in 𝓝[>] 0, lineMap y x δ ∈ s :=
    lineMap_continuous.continuousWithinAt.eventually_mem
      (by simpa using mem_interior_iff_mem_nhds.1 hy)
  filter_upwards [hmem, Ioo_mem_nhdsGT zero_lt_one] with δ hmem hsbt using hsxy.symm hmem (by aesop)

/-- One cannot see any point of an open set. -/
lemma IsOpen.eq_of_isVisible_of_left_mem (hs : IsOpen s) (hsxy : IsVisible 𝕜 s x y) (hy : y ∈ s) :
    x = y :=
  hsxy.eq_of_mem_interior (by simpa [hs.interior_eq])

end Module

section Real
variable [AddCommGroup V] [Module ℝ V] {s : Set V} {x y z : V}

/-- All points of the convex hull of a set `s` visible from a point `x ∉ convexHull ℝ s` lie in the
convex hull of such points that actually lie in `s`.

Note that the converse does not hold. -/
lemma IsVisible.mem_convexHull_isVisible (hx : x ∉ convexHull ℝ s) (hy : y ∈ convexHull ℝ s)
    (hxy : IsVisible ℝ (convexHull ℝ s) x y) :
    y ∈ convexHull ℝ {z ∈ s | IsVisible ℝ (convexHull ℝ s) x z} := by
  classical
  obtain ⟨ι, _, w, a, hw₀, hw₁, ha, rfl⟩ := mem_convexHull_iff_exists_fintype.1 hy
  rw [← Fintype.sum_subset (s := {i | w i ≠ 0})
    fun i hi ↦ mem_filter.2 ⟨mem_univ _, left_ne_zero_of_smul hi⟩]
  exact (convex_convexHull ..).sum_mem (fun i _ ↦ hw₀ _) (by rwa [sum_filter_ne_zero])
    fun i hi ↦ subset_convexHull _ _ ⟨ha _, IsVisible.of_convexHull_of_pos (fun _ _ ↦ hw₀ _) hw₁
      (by simpa) hx hxy (mem_univ _) <| (hw₀ _).lt_of_ne' (mem_filter.1 hi).2⟩

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- If `s` is a closed set, then any point `x` sees some point of `s` in any direction where there
is something to see. -/
lemma IsClosed.exists_wbtw_isVisible (hs : IsClosed s) (hy : y ∈ s) (x : V) :
    ∃ z ∈ s, Wbtw ℝ x z y ∧ IsVisible ℝ s x z := by
  let t : Set ℝ := Ici 0 ∩ lineMap x y ⁻¹' s
  have ht₁ : 1 ∈ t := by simpa [t]
  have ht : BddBelow t := bddBelow_Ici.inter_of_left
  let δ : ℝ := sInf t
  have hδ₁ : δ ≤ 1 := csInf_le ht ht₁
  obtain ⟨hδ₀, hδ⟩ : 0 ≤ δ ∧ lineMap x y δ ∈ s :=
    (isClosed_Ici.inter <| hs.preimage lineMap_continuous).csInf_mem ⟨1, ht₁⟩ ht
  refine ⟨lineMap x y δ, hδ, wbtw_lineMap_iff.2 <| .inr ⟨hδ₀, hδ₁⟩, ?_⟩
  rintro _ hε ⟨⟨ε, ⟨hε₀, hε₁⟩, rfl⟩, -, h⟩
  replace hδ₀ : 0 < δ := hδ₀.lt_of_ne' <| by rintro hδ₀; simp [hδ₀] at h
  replace hε₁ : ε < 1 := hε₁.lt_of_ne <| by rintro rfl; simp at h
  rw [lineMap_lineMap_right] at hε
  exact (csInf_le ht ⟨mul_nonneg hε₀ hδ₀.le, hε⟩).not_gt <| mul_lt_of_lt_one_left hδ₀ hε₁

-- TODO: Once we have cone hulls, the RHS can be strengthened to
-- `coneHull ℝ x {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}`
/-- A set whose convex hull is closed lies in the cone based at a point `x` generated by its points
visible from `x` through its convex hull. -/
lemma IsClosed.convexHull_subset_affineSpan_isVisible (hs : IsClosed (convexHull ℝ s))
    (hx : x ∉ convexHull ℝ s) :
    convexHull ℝ s ⊆ affineSpan ℝ ({x} ∪ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) := by
  rintro y hy
  obtain ⟨z, hz, hxzy, hxz⟩ := hs.exists_wbtw_isVisible hy x
  -- TODO: `calc` doesn't work with `∈` :(
  exact AffineSubspace.right_mem_of_wbtw hxzy (subset_affineSpan _ _ <| subset_union_left rfl)
    (affineSpan_mono _ subset_union_right <| convexHull_subset_affineSpan _ <|
      hxz.mem_convexHull_isVisible hx hz) (ne_of_mem_of_not_mem hz hx).symm

open Submodule in
/-- If `s` is a closed set of dimension `d` and `x` is a point outside of its convex hull,
then `x` sees at least `d` points of the convex hull of `s` that actually lie in `s`. -/
lemma rank_le_card_isVisible (hs : IsClosed (convexHull ℝ s)) (hx : x ∉ convexHull ℝ s) :
    Module.rank ℝ (span ℝ (-x +ᵥ s)) ≤ #{y ∈ s | IsVisible ℝ (convexHull ℝ s) x y} := by
  calc
    Module.rank ℝ (span ℝ (-x +ᵥ s)) ≤
      Module.rank ℝ (span ℝ
        (-x +ᵥ affineSpan ℝ ({x} ∪ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) : Set V)) := by
      push_cast
      refine Submodule.rank_mono ?_
      gcongr
      exact (subset_convexHull ..).trans <| hs.convexHull_subset_affineSpan_isVisible hx
    _ = Module.rank ℝ (span ℝ (-x +ᵥ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y})) := by
      suffices h :
        -x +ᵥ (affineSpan ℝ ({x} ∪ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) : Set V) =
          span ℝ (-x +ᵥ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) by
        rw [AffineSubspace.coe_pointwise_vadd, h, span_span]
      simp [← AffineSubspace.coe_pointwise_vadd, AffineSubspace.pointwise_vadd_span,
        vadd_set_insert, -coe_affineSpan, affineSpan_insert_zero]
    _ ≤ #(-x +ᵥ {y ∈ s | IsVisible ℝ (convexHull ℝ s) x y}) := rank_span_le _
    _ = #{y ∈ s | IsVisible ℝ (convexHull ℝ s) x y} := by simp

end Real
