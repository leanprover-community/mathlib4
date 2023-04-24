/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module analysis.convex.join
! leanprover-community/mathlib commit 951bf1d9e98a2042979ced62c0620bcfb3587cf8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Combination

/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/


open Set

open BigOperators

variable {ι : Sort _} {𝕜 E : Type _}

section OrderedSemiring

variable (𝕜) [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] {s t s₁ s₂ t₁ t₂ u : Set E}
  {x y : E}

/-- The join of two sets is the union of the segments joining them. This can be interpreted as the
topological join, but within the original space. -/
def convexJoin (s t : Set E) : Set E :=
  ⋃ (x ∈ s) (y ∈ t), segment 𝕜 x y
#align convex_join convexJoin

variable {𝕜}

theorem mem_convexJoin : x ∈ convexJoin 𝕜 s t ↔ ∃ a ∈ s, ∃ b ∈ t, x ∈ segment 𝕜 a b := by
  simp [convexJoin]
#align mem_convex_join mem_convexJoin

theorem convexJoin_comm (s t : Set E) : convexJoin 𝕜 s t = convexJoin 𝕜 t s :=
  (unionᵢ₂_comm _).trans <| by simp_rw [convexJoin, segment_symm]
#align convex_join_comm convexJoin_comm

theorem convexJoin_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s₁ t₁ ⊆ convexJoin 𝕜 s₂ t₂ :=
  bunionᵢ_mono hs fun x hx => bunionᵢ_mono ht fun y hy => Subset.rfl
#align convex_join_mono convexJoin_mono

theorem convexJoin_mono_left (hs : s₁ ⊆ s₂) : convexJoin 𝕜 s₁ t ⊆ convexJoin 𝕜 s₂ t :=
  convexJoin_mono hs Subset.rfl
#align convex_join_mono_left convexJoin_mono_left

theorem convexJoin_mono_right (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s t₁ ⊆ convexJoin 𝕜 s t₂ :=
  convexJoin_mono Subset.rfl ht
#align convex_join_mono_right convexJoin_mono_right

@[simp]
theorem convexJoin_empty_left (t : Set E) : convexJoin 𝕜 ∅ t = ∅ := by simp [convexJoin]
#align convex_join_empty_left convexJoin_empty_left

@[simp]
theorem convexJoin_empty_right (s : Set E) : convexJoin 𝕜 s ∅ = ∅ := by simp [convexJoin]
#align convex_join_empty_right convexJoin_empty_right

@[simp]
theorem convexJoin_singleton_left (t : Set E) (x : E) :
    convexJoin 𝕜 {x} t = ⋃ y ∈ t, segment 𝕜 x y := by simp [convexJoin]
#align convex_join_singleton_left convexJoin_singleton_left

@[simp]
theorem convexJoin_singleton_right (s : Set E) (y : E) :
    convexJoin 𝕜 s {y} = ⋃ x ∈ s, segment 𝕜 x y := by simp [convexJoin]
#align convex_join_singleton_right convexJoin_singleton_right

@[simp]
theorem convexJoin_singletons (x : E) : convexJoin 𝕜 {x} {y} = segment 𝕜 x y := by simp [convexJoin]
#align convex_join_singletons convexJoin_singletons

@[simp]
theorem convexJoin_union_left (s₁ s₂ t : Set E) :
    convexJoin 𝕜 (s₁ ∪ s₂) t = convexJoin 𝕜 s₁ t ∪ convexJoin 𝕜 s₂ t := by
  simp_rw [convexJoin, mem_union, Union_or, Union_union_distrib]
#align convex_join_union_left convexJoin_union_left

@[simp]
theorem convexJoin_union_right (s t₁ t₂ : Set E) :
    convexJoin 𝕜 s (t₁ ∪ t₂) = convexJoin 𝕜 s t₁ ∪ convexJoin 𝕜 s t₂ := by
  simp_rw [convexJoin, mem_union, Union_or, Union_union_distrib]
#align convex_join_union_right convexJoin_union_right

@[simp]
theorem convexJoin_unionᵢ_left (s : ι → Set E) (t : Set E) :
    convexJoin 𝕜 (⋃ i, s i) t = ⋃ i, convexJoin 𝕜 (s i) t :=
  by
  simp_rw [convexJoin, mem_Union, Union_exists]
  exact Union_comm _
#align convex_join_Union_left convexJoin_unionᵢ_left

@[simp]
theorem convexJoin_unionᵢ_right (s : Set E) (t : ι → Set E) :
    convexJoin 𝕜 s (⋃ i, t i) = ⋃ i, convexJoin 𝕜 s (t i) := by
  simp_rw [convexJoin_comm s, convexJoin_unionᵢ_left]
#align convex_join_Union_right convexJoin_unionᵢ_right

theorem segment_subset_convexJoin (hx : x ∈ s) (hy : y ∈ t) : segment 𝕜 x y ⊆ convexJoin 𝕜 s t :=
  (subset_unionᵢ₂ y hy).trans (subset_unionᵢ₂ x hx)
#align segment_subset_convex_join segment_subset_convexJoin

theorem subset_convexJoin_left (h : t.Nonempty) : s ⊆ convexJoin 𝕜 s t := fun x hx =>
  let ⟨y, hy⟩ := h
  segment_subset_convexJoin hx hy <| left_mem_segment _ _ _
#align subset_convex_join_left subset_convexJoin_left

theorem subset_convexJoin_right (h : s.Nonempty) : t ⊆ convexJoin 𝕜 s t := fun y hy =>
  let ⟨x, hx⟩ := h
  segment_subset_convexJoin hx hy <| right_mem_segment _ _ _
#align subset_convex_join_right subset_convexJoin_right

theorem convexJoin_subset (hs : s ⊆ u) (ht : t ⊆ u) (hu : Convex 𝕜 u) : convexJoin 𝕜 s t ⊆ u :=
  unionᵢ₂_subset fun x hx => unionᵢ₂_subset fun y hy => hu.segment_subset (hs hx) (ht hy)
#align convex_join_subset convexJoin_subset

theorem convexJoin_subset_convexHull (s t : Set E) : convexJoin 𝕜 s t ⊆ convexHull 𝕜 (s ∪ t) :=
  convexJoin_subset ((subset_union_left _ _).trans <| subset_convexHull _ _)
      ((subset_union_right _ _).trans <| subset_convexHull _ _) <|
    convex_convexHull _ _
#align convex_join_subset_convex_hull convexJoin_subset_convexHull

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t u : Set E} {x y : E}

theorem convexJoin_assoc_aux (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u ⊆ convexJoin 𝕜 s (convexJoin 𝕜 t u) :=
  by
  simp_rw [subset_def, mem_convexJoin]
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  obtain rfl | hb₂ := hb₂.eq_or_lt
  · refine' ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment _ _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, _⟩
    rw [add_zero] at hab₂
    rw [hab₂, one_smul, zero_smul, add_zero]
  have ha₂b₁ : 0 ≤ a₂ * b₁ := mul_nonneg ha₂ hb₁
  have hab : 0 < a₂ * b₁ + b₂ := add_pos_of_nonneg_of_pos ha₂b₁ hb₂
  refine'
    ⟨x, hx, (a₂ * b₁ / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
      ⟨y, hy, z, hz, _, _, _, _, _, rfl⟩, a₂ * a₁, a₂ * b₁ + b₂, mul_nonneg ha₂ ha₁, hab.le, _, _⟩
  · exact div_nonneg ha₂b₁ hab.le
  · exact div_nonneg hb₂.le hab.le
  · rw [← add_div, div_self hab.ne']
  · rw [← add_assoc, ← mul_add, hab₁, mul_one, hab₂]
  · simp_rw [smul_add, ← mul_smul, mul_div_cancel' _ hab.ne', add_assoc]
#align convex_join_assoc_aux convexJoin_assoc_aux

theorem convexJoin_assoc (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 s (convexJoin 𝕜 t u) :=
  by
  refine' (convexJoin_assoc_aux _ _ _).antisymm _
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  exact convexJoin_assoc_aux _ _ _
#align convex_join_assoc convexJoin_assoc

theorem convexJoin_left_comm (s t u : Set E) :
    convexJoin 𝕜 s (convexJoin 𝕜 t u) = convexJoin 𝕜 t (convexJoin 𝕜 s u) := by
  simp_rw [← convexJoin_assoc, convexJoin_comm]
#align convex_join_left_comm convexJoin_left_comm

theorem convexJoin_right_comm (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 (convexJoin 𝕜 s u) t := by
  simp_rw [convexJoin_assoc, convexJoin_comm]
#align convex_join_right_comm convexJoin_right_comm

theorem convexJoin_convexJoin_convexJoin_comm (s t u v : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) (convexJoin 𝕜 u v) =
      convexJoin 𝕜 (convexJoin 𝕜 s u) (convexJoin 𝕜 t v) :=
  by simp_rw [← convexJoin_assoc, convexJoin_right_comm]
#align convex_join_convex_join_convex_join_comm convexJoin_convexJoin_convexJoin_comm

theorem convexHull_insert (hs : s.Nonempty) :
    convexHull 𝕜 (insert x s) = convexJoin 𝕜 {x} (convexHull 𝕜 s) := by
  classical
    refine'
      (convexJoin_subset ((singleton_subset_iff.2 <| mem_insert _ _).trans <| subset_convexHull _ _)
              (convexHull_mono <| subset_insert _ _) <|
            convex_convexHull _ _).antisymm'
        fun x hx => _
    rw [convexHull_eq] at hx
    obtain ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩ := hx
    have :
      ((∑ i in t.filter fun i => z i = x, w i) • x + ∑ i in t.filter fun i => z i ≠ x, w i • z i) =
        t.center_mass w z :=
      by
      rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁, Finset.sum_smul]
      convert Finset.sum_filter_add_sum_filter_not _ _ (w • z) using 2
      refine' Finset.sum_congr rfl fun i hi => _
      rw [Pi.smul_apply', (Finset.mem_filter.1 hi).2]
    rw [← this]
    have hw₀' : ∀ i ∈ t.filter fun i => z i ≠ x, 0 ≤ w i := fun i hi =>
      hw₀ _ <| Finset.filter_subset _ _ hi
    obtain hw | hw := (Finset.sum_nonneg hw₀').eq_or_gt
    · rw [← Finset.sum_filter_add_sum_filter_not _ fun i => z i = x, hw, add_zero] at hw₁
      rw [hw₁, one_smul, Finset.sum_eq_zero, add_zero]
      · exact subset_convexJoin_left hs.convex_hull (mem_singleton _)
      simp_rw [Finset.sum_eq_zero_iff_of_nonneg hw₀'] at hw
      rintro i hi
      rw [hw _ hi, zero_smul]
    refine'
      mem_convexJoin.2
        ⟨x, mem_singleton _, (t.filter fun i => z i ≠ x).centerMass w z,
          Finset.centerMass_mem_convexHull _ hw₀' hw fun i hi => _,
          ∑ i in t.filter fun i => z i = x, w i, ∑ i in t.filter fun i => z i ≠ x, w i,
          Finset.sum_nonneg fun i hi => hw₀ _ <| Finset.filter_subset _ _ hi,
          Finset.sum_nonneg hw₀', _, _⟩
    · rw [Finset.mem_filter] at hi
      exact mem_of_mem_insert_of_ne (hz _ hi.1) hi.2
    · rw [Finset.sum_filter_add_sum_filter_not, hw₁]
    · rw [Finset.centerMass, smul_inv_smul₀ hw.ne', Finset.sum_smul]
#align convex_hull_insert convexHull_insert

theorem convexJoin_segments (a b c d : E) :
    convexJoin 𝕜 (segment 𝕜 a b) (segment 𝕜 c d) = convexHull 𝕜 {a, b, c, d} := by
  simp only [convexHull_insert, insert_nonempty, singleton_nonempty, convexHull_pair, ←
    convexJoin_assoc, convexJoin_singletons]
#align convex_join_segments convexJoin_segments

theorem convexJoin_segment_singleton (a b c : E) :
    convexJoin 𝕜 (segment 𝕜 a b) {c} = convexHull 𝕜 {a, b, c} := by
  rw [← pair_eq_singleton, ← convexJoin_segments, segment_same, pair_eq_singleton]
#align convex_join_segment_singleton convexJoin_segment_singleton

theorem convexJoin_singleton_segment (a b c : E) :
    convexJoin 𝕜 {a} (segment 𝕜 b c) = convexHull 𝕜 {a, b, c} := by
  rw [← segment_same 𝕜, convexJoin_segments, insert_idem]
#align convex_join_singleton_segment convexJoin_singleton_segment

protected theorem Convex.convexJoin (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (convexJoin 𝕜 s t) :=
  by
  rw [convex_iff_segment_subset] at ht hs⊢
  simp_rw [mem_convexJoin]
  rintro x ⟨xa, hxa, xb, hxb, hx⟩ y ⟨ya, hya, yb, hyb, hy⟩
  refine' (segment_subset_convexJoin hx hy).trans _
  have triv : ({xa, xb, ya, yb} : Set E) = {xa, ya, xb, yb} := by simp only [Set.insert_comm]
  rw [convexJoin_segments, triv, ← convexJoin_segments]
  exact convexJoin_mono (hs hxa hya) (ht hxb hyb)
#align convex.convex_join Convex.convexJoin

protected theorem Convex.convexHull_union (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hs₀ : s.Nonempty)
    (ht₀ : t.Nonempty) : convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 s t :=
  (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _
#align convex.convex_hull_union Convex.convexHull_union

theorem convexHull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 (convexHull 𝕜 s) (convexHull 𝕜 t) :=
  by
  rw [← convexHull_convexHull_union_left, ← convexHull_convexHull_union_right]
  exact
    (convex_convexHull 𝕜 s).convexHull_union (convex_convexHull 𝕜 t) hs.convex_hull ht.convex_hull
#align convex_hull_union convexHull_union

end LinearOrderedField

