/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Combination

#align_import analysis.convex.join from "leanprover-community/mathlib"@"951bf1d9e98a2042979ced62c0620bcfb3587cf8"

/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/


open Set

open BigOperators

variable {ι : Sort*} {𝕜 E : Type*}

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
  -- 🎉 no goals
#align mem_convex_join mem_convexJoin

theorem convexJoin_comm (s t : Set E) : convexJoin 𝕜 s t = convexJoin 𝕜 t s :=
  (iUnion₂_comm _).trans <| by simp_rw [convexJoin, segment_symm]
                               -- 🎉 no goals
#align convex_join_comm convexJoin_comm

theorem convexJoin_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s₁ t₁ ⊆ convexJoin 𝕜 s₂ t₂ :=
  biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht
#align convex_join_mono convexJoin_mono

theorem convexJoin_mono_left (hs : s₁ ⊆ s₂) : convexJoin 𝕜 s₁ t ⊆ convexJoin 𝕜 s₂ t :=
  convexJoin_mono hs Subset.rfl
#align convex_join_mono_left convexJoin_mono_left

theorem convexJoin_mono_right (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s t₁ ⊆ convexJoin 𝕜 s t₂ :=
  convexJoin_mono Subset.rfl ht
#align convex_join_mono_right convexJoin_mono_right

@[simp]
theorem convexJoin_empty_left (t : Set E) : convexJoin 𝕜 ∅ t = ∅ := by simp [convexJoin]
                                                                       -- 🎉 no goals
#align convex_join_empty_left convexJoin_empty_left

@[simp]
theorem convexJoin_empty_right (s : Set E) : convexJoin 𝕜 s ∅ = ∅ := by simp [convexJoin]
                                                                        -- 🎉 no goals
#align convex_join_empty_right convexJoin_empty_right

@[simp]
theorem convexJoin_singleton_left (t : Set E) (x : E) :
    convexJoin 𝕜 {x} t = ⋃ y ∈ t, segment 𝕜 x y := by simp [convexJoin]
                                                      -- 🎉 no goals
#align convex_join_singleton_left convexJoin_singleton_left

@[simp]
theorem convexJoin_singleton_right (s : Set E) (y : E) :
    convexJoin 𝕜 s {y} = ⋃ x ∈ s, segment 𝕜 x y := by simp [convexJoin]
                                                      -- 🎉 no goals
#align convex_join_singleton_right convexJoin_singleton_right

-- porting note: simp can prove it
theorem convexJoin_singletons (x : E) : convexJoin 𝕜 {x} {y} = segment 𝕜 x y := by simp
                                                                                   -- 🎉 no goals
#align convex_join_singletons convexJoin_singletons

@[simp]
theorem convexJoin_union_left (s₁ s₂ t : Set E) :
    convexJoin 𝕜 (s₁ ∪ s₂) t = convexJoin 𝕜 s₁ t ∪ convexJoin 𝕜 s₂ t := by
  simp_rw [convexJoin, mem_union, iUnion_or, iUnion_union_distrib]
  -- 🎉 no goals
#align convex_join_union_left convexJoin_union_left

@[simp]
theorem convexJoin_union_right (s t₁ t₂ : Set E) :
    convexJoin 𝕜 s (t₁ ∪ t₂) = convexJoin 𝕜 s t₁ ∪ convexJoin 𝕜 s t₂ := by
  simp_rw [convexJoin_comm s, convexJoin_union_left]
  -- 🎉 no goals
#align convex_join_union_right convexJoin_union_right

@[simp]
theorem convexJoin_iUnion_left (s : ι → Set E) (t : Set E) :
    convexJoin 𝕜 (⋃ i, s i) t = ⋃ i, convexJoin 𝕜 (s i) t := by
  simp_rw [convexJoin, mem_iUnion, iUnion_exists]
  -- ⊢ ⋃ (x : E) (i : ι) (_ : x ∈ s i) (y : E) (_ : y ∈ t), segment 𝕜 x y = ⋃ (i :  …
  exact iUnion_comm _
  -- 🎉 no goals
#align convex_join_Union_left convexJoin_iUnion_left

@[simp]
theorem convexJoin_iUnion_right (s : Set E) (t : ι → Set E) :
    convexJoin 𝕜 s (⋃ i, t i) = ⋃ i, convexJoin 𝕜 s (t i) := by
  simp_rw [convexJoin_comm s, convexJoin_iUnion_left]
  -- 🎉 no goals
#align convex_join_Union_right convexJoin_iUnion_right

theorem segment_subset_convexJoin (hx : x ∈ s) (hy : y ∈ t) : segment 𝕜 x y ⊆ convexJoin 𝕜 s t :=
  subset_iUnion₂_of_subset x hx <| subset_iUnion₂ (s := fun y _ ↦ segment 𝕜 x y) y hy
#align segment_subset_convex_join segment_subset_convexJoin

theorem subset_convexJoin_left (h : t.Nonempty) : s ⊆ convexJoin 𝕜 s t := fun _x hx =>
  let ⟨_y, hy⟩ := h
  segment_subset_convexJoin hx hy <| left_mem_segment _ _ _
#align subset_convex_join_left subset_convexJoin_left

theorem subset_convexJoin_right (h : s.Nonempty) : t ⊆ convexJoin 𝕜 s t :=
  convexJoin_comm (𝕜 := 𝕜) t s ▸ subset_convexJoin_left h
#align subset_convex_join_right subset_convexJoin_right

theorem convexJoin_subset (hs : s ⊆ u) (ht : t ⊆ u) (hu : Convex 𝕜 u) : convexJoin 𝕜 s t ⊆ u :=
  iUnion₂_subset fun _x hx => iUnion₂_subset fun _y hy => hu.segment_subset (hs hx) (ht hy)
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
    convexJoin 𝕜 (convexJoin 𝕜 s t) u ⊆ convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  simp_rw [subset_def, mem_convexJoin]
  -- ⊢ ∀ (x : E), (∃ a, (∃ a_1, a_1 ∈ s ∧ ∃ b, b ∈ t ∧ a ∈ segment 𝕜 a_1 b) ∧ ∃ b,  …
  rintro _ ⟨z, ⟨x, hx, y, hy, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩, z, hz, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩
  -- ⊢ ∃ a, a ∈ s ∧ ∃ b, (∃ a, a ∈ t ∧ ∃ b_1, b_1 ∈ u ∧ b ∈ segment 𝕜 a b_1) ∧ a₂ • …
  obtain rfl | hb₂ := hb₂.eq_or_lt
  -- ⊢ ∃ a, a ∈ s ∧ ∃ b, (∃ a, a ∈ t ∧ ∃ b_1, b_1 ∈ u ∧ b ∈ segment 𝕜 a b_1) ∧ a₂ • …
  · refine' ⟨x, hx, y, ⟨y, hy, z, hz, left_mem_segment 𝕜 _ _⟩, a₁, b₁, ha₁, hb₁, hab₁, _⟩
    -- ⊢ a₁ • x + b₁ • y = a₂ • (a₁ • x + b₁ • y) + 0 • z
    rw [add_zero] at hab₂
    -- ⊢ a₁ • x + b₁ • y = a₂ • (a₁ • x + b₁ • y) + 0 • z
    rw [hab₂, one_smul, zero_smul, add_zero]
    -- 🎉 no goals
  have ha₂b₁ : 0 ≤ a₂ * b₁ := mul_nonneg ha₂ hb₁
  -- ⊢ ∃ a, a ∈ s ∧ ∃ b, (∃ a, a ∈ t ∧ ∃ b_1, b_1 ∈ u ∧ b ∈ segment 𝕜 a b_1) ∧ a₂ • …
  have hab : 0 < a₂ * b₁ + b₂ := add_pos_of_nonneg_of_pos ha₂b₁ hb₂
  -- ⊢ ∃ a, a ∈ s ∧ ∃ b, (∃ a, a ∈ t ∧ ∃ b_1, b_1 ∈ u ∧ b ∈ segment 𝕜 a b_1) ∧ a₂ • …
  refine'
    ⟨x, hx, (a₂ * b₁ / (a₂ * b₁ + b₂)) • y + (b₂ / (a₂ * b₁ + b₂)) • z,
      ⟨y, hy, z, hz, _, _, _, _, _, rfl⟩, a₂ * a₁, a₂ * b₁ + b₂, mul_nonneg ha₂ ha₁, hab.le, _, _⟩
  · exact div_nonneg ha₂b₁ hab.le
    -- 🎉 no goals
  · exact div_nonneg hb₂.le hab.le
    -- 🎉 no goals
  · rw [← add_div, div_self hab.ne']
    -- 🎉 no goals
  · rw [← add_assoc, ← mul_add, hab₁, mul_one, hab₂]
    -- 🎉 no goals
  · simp_rw [smul_add, ← mul_smul, mul_div_cancel' _ hab.ne', add_assoc]
    -- 🎉 no goals
#align convex_join_assoc_aux convexJoin_assoc_aux

theorem convexJoin_assoc (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 s (convexJoin 𝕜 t u) := by
  refine' (convexJoin_assoc_aux _ _ _).antisymm _
  -- ⊢ convexJoin 𝕜 s (convexJoin 𝕜 t u) ⊆ convexJoin 𝕜 (convexJoin 𝕜 s t) u
  simp_rw [convexJoin_comm s, convexJoin_comm _ u]
  -- ⊢ convexJoin 𝕜 (convexJoin 𝕜 u t) s ⊆ convexJoin 𝕜 u (convexJoin 𝕜 t s)
  exact convexJoin_assoc_aux _ _ _
  -- 🎉 no goals
#align convex_join_assoc convexJoin_assoc

theorem convexJoin_left_comm (s t u : Set E) :
    convexJoin 𝕜 s (convexJoin 𝕜 t u) = convexJoin 𝕜 t (convexJoin 𝕜 s u) := by
  simp_rw [← convexJoin_assoc, convexJoin_comm]
  -- 🎉 no goals
#align convex_join_left_comm convexJoin_left_comm

theorem convexJoin_right_comm (s t u : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) u = convexJoin 𝕜 (convexJoin 𝕜 s u) t := by
  simp_rw [convexJoin_assoc, convexJoin_comm]
  -- 🎉 no goals
#align convex_join_right_comm convexJoin_right_comm

theorem convexJoin_convexJoin_convexJoin_comm (s t u v : Set E) :
    convexJoin 𝕜 (convexJoin 𝕜 s t) (convexJoin 𝕜 u v) =
      convexJoin 𝕜 (convexJoin 𝕜 s u) (convexJoin 𝕜 t v) :=
  by simp_rw [← convexJoin_assoc, convexJoin_right_comm]
     -- 🎉 no goals
#align convex_join_convex_join_convex_join_comm convexJoin_convexJoin_convexJoin_comm

-- porting note: moved 3 lemmas from below to golf
protected theorem Convex.convexJoin (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (convexJoin 𝕜 s t) := by
  simp only [Convex, StarConvex, convexJoin, mem_iUnion]
  -- ⊢ ∀ ⦃x : E⦄, (∃ i h i_1 i_2, x ∈ [i-[𝕜]i_1]) → ∀ ⦃y : E⦄, (∃ i h i_1 i_2, y ∈  …
  rintro _ ⟨x₁, hx₁, y₁, hy₁, a₁, b₁, ha₁, hb₁, hab₁, rfl⟩
    _ ⟨x₂, hx₂, y₂, hy₂, a₂, b₂, ha₂, hb₂, hab₂, rfl⟩ p q hp hq hpq
  rcases hs.exists_mem_add_smul_eq hx₁ hx₂ (mul_nonneg hp ha₁) (mul_nonneg hq ha₂) with ⟨x, hxs, hx⟩
  -- ⊢ ∃ i h i_1 i_2, p • (a₁ • x₁ + b₁ • y₁) + q • (a₂ • x₂ + b₂ • y₂) ∈ [i-[𝕜]i_1]
  rcases ht.exists_mem_add_smul_eq hy₁ hy₂ (mul_nonneg hp hb₁) (mul_nonneg hq hb₂) with ⟨y, hyt, hy⟩
  -- ⊢ ∃ i h i_1 i_2, p • (a₁ • x₁ + b₁ • y₁) + q • (a₂ • x₂ + b₂ • y₂) ∈ [i-[𝕜]i_1]
  refine ⟨_, hxs, _, hyt, p * a₁ + q * a₂, p * b₁ + q * b₂, ?_, ?_, ?_, ?_⟩ <;> try positivity
                                                                                -- 🎉 no goals
                                                                                -- 🎉 no goals
                                                                                -- ⊢ p * a₁ + q * a₂ + (p * b₁ + q * b₂) = 1
                                                                                -- ⊢ (p * a₁ + q * a₂) • x + (p * b₁ + q * b₂) • y = p • (a₁ • x₁ + b₁ • y₁) + q  …
  · rwa [add_add_add_comm, ← mul_add, ← mul_add, hab₁, hab₂, mul_one, mul_one]
    -- 🎉 no goals
  · rw [hx, hy, add_add_add_comm]
    -- ⊢ (p * a₁) • x₁ + (p * b₁) • y₁ + ((q * a₂) • x₂ + (q * b₂) • y₂) = p • (a₁ •  …
    simp only [smul_add, smul_smul]
    -- 🎉 no goals
#align convex.convex_join Convex.convexJoin

protected theorem Convex.convexHull_union (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hs₀ : s.Nonempty)
    (ht₀ : t.Nonempty) : convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 s t :=
  (convexHull_min (union_subset (subset_convexJoin_left ht₀) <| subset_convexJoin_right hs₀) <|
        hs.convexJoin ht).antisymm <|
    convexJoin_subset_convexHull _ _
#align convex.convex_hull_union Convex.convexHull_union

theorem convexHull_union (hs : s.Nonempty) (ht : t.Nonempty) :
    convexHull 𝕜 (s ∪ t) = convexJoin 𝕜 (convexHull 𝕜 s) (convexHull 𝕜 t) := by
  rw [← convexHull_convexHull_union_left, ← convexHull_convexHull_union_right]
  -- ⊢ ↑(convexHull 𝕜) (↑(convexHull 𝕜) s ∪ ↑(convexHull 𝕜) t) = convexJoin 𝕜 (↑(co …
  exact (convex_convexHull 𝕜 s).convexHull_union (convex_convexHull 𝕜 t) hs.convexHull ht.convexHull
  -- 🎉 no goals
#align convex_hull_union convexHull_union

theorem convexHull_insert (hs : s.Nonempty) :
    convexHull 𝕜 (insert x s) = convexJoin 𝕜 {x} (convexHull 𝕜 s) := by
  rw [insert_eq, convexHull_union (singleton_nonempty _) hs, convexHull_singleton]
  -- 🎉 no goals
#align convex_hull_insert convexHull_insert

theorem convexJoin_segments (a b c d : E) :
    convexJoin 𝕜 (segment 𝕜 a b) (segment 𝕜 c d) = convexHull 𝕜 {a, b, c, d} := by
  simp_rw [← convexHull_pair, convexHull_insert (insert_nonempty _ _),
    convexHull_insert (singleton_nonempty _), convexJoin_assoc,
    convexHull_singleton]
#align convex_join_segments convexJoin_segments

theorem convexJoin_segment_singleton (a b c : E) :
    convexJoin 𝕜 (segment 𝕜 a b) {c} = convexHull 𝕜 {a, b, c} := by
  rw [← pair_eq_singleton, ← convexJoin_segments, segment_same, pair_eq_singleton]
  -- 🎉 no goals
#align convex_join_segment_singleton convexJoin_segment_singleton

theorem convexJoin_singleton_segment (a b c : E) :
    convexJoin 𝕜 {a} (segment 𝕜 b c) = convexHull 𝕜 {a, b, c} := by
  rw [← segment_same 𝕜, convexJoin_segments, insert_idem]
  -- 🎉 no goals
#align convex_join_singleton_segment convexJoin_singleton_segment

-- porting note: moved 3 lemmas up to golf

end LinearOrderedField
