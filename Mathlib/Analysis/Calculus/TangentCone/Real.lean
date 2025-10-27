/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Convex.Topology

/-!
# Unique differentiability property in real normed spaces

In this file we prove that

- `uniqueDiffOn_convex`: a convex set with nonempty interior in a real normed space
  has the unique differentiability property;
- `uniqueDiffOn_Ioc` etc: intervals on the real line have the unique differentiability property.
-/

open Filter Set
open scoped Topology

theorem mem_tangentConeAt_of_pow_smul {r : 𝕜} (hr₀ : r ≠ 0) (hr : ‖r‖ < 1)
    (hs : ∀ᶠ n : ℕ in atTop, x + r ^ n • y ∈ s) : y ∈ tangentConeAt 𝕜 s x := by
  apply mem_tangentConeAt_of_seq (c := fun n ↦ (r ^ n)⁻¹) _ hs
  · simp [hr₀, tendsto_const_nhds]
  · simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).smul_const y

section RealNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a subset of a real vector space contains an open segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentConeAt_of_openSegment_subset {s : Set E} {x y : E} (h : openSegment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x := by
  refine mem_tangentConeAt_of_pow_smul one_half_pos.ne' (by norm_num) ?_
  refine (eventually_ne_atTop 0).mono fun n hn ↦ (h ?_)
  rw [openSegment_eq_image]
  refine ⟨(1 / 2) ^ n, ⟨?_, ?_⟩, ?_⟩
  · exact pow_pos one_half_pos _
  · exact pow_lt_one₀ one_half_pos.le one_half_lt_one hn
  · simp only [sub_smul, one_smul, smul_sub]; abel

@[deprecated (since := "2025-04-27")]
alias mem_tangentCone_of_openSegment_subset := mem_tangentConeAt_of_openSegment_subset

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
theorem mem_tangentConeAt_of_segment_subset {s : Set E} {x y : E} (h : segment ℝ x y ⊆ s) :
    y - x ∈ tangentConeAt ℝ s x :=
  mem_tangentConeAt_of_openSegment_subset ((openSegment_subset_segment ℝ x y).trans h)

@[deprecated (since := "2025-04-27")]
alias mem_tangentCone_of_segment_subset := mem_tangentConeAt_of_segment_subset

theorem Convex.span_tangentConeAt {s : Set E} (conv : Convex ℝ s) (hs : (interior s).Nonempty)
    {x : E} (hx : x ∈ closure s) : Submodule.span ℝ (tangentConeAt ℝ s x) = ⊤ := by
  rcases hs with ⟨y, hy⟩
  suffices y - x ∈ interior (tangentConeAt ℝ s x) by
    apply (Submodule.span ℝ (tangentConeAt ℝ s x)).eq_top_of_nonempty_interior'
    exact ⟨y - x, interior_mono Submodule.subset_span this⟩
  rw [mem_interior_iff_mem_nhds]
  replace hy : interior s ∈ 𝓝 y := IsOpen.mem_nhds isOpen_interior hy
  apply mem_of_superset ((isOpenMap_sub_right x).image_mem_nhds hy)
  rintro _ ⟨z, zs, rfl⟩
  refine mem_tangentConeAt_of_openSegment_subset (Subset.trans ?_ interior_subset)
  exact conv.openSegment_closure_interior_subset_interior hx zs

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability at every point of its closure. -/
theorem uniqueDiffWithinAt_convex {s : Set E} (conv : Convex ℝ s) (hs : (interior s).Nonempty)
    {x : E} (hx : x ∈ closure s) : UniqueDiffWithinAt ℝ s x := by
  simp [uniqueDiffWithinAt_iff, conv.span_tangentConeAt hs hx, hx]

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem uniqueDiffOn_convex {s : Set E} (conv : Convex ℝ s) (hs : (interior s).Nonempty) :
    UniqueDiffOn ℝ s :=
  fun _ xs => uniqueDiffWithinAt_convex conv hs (subset_closure xs)

end RealNormed

section Real

theorem uniqueDiffOn_Ici (a : ℝ) : UniqueDiffOn ℝ (Ici a) :=
  uniqueDiffOn_convex (convex_Ici a) <| by simp only [interior_Ici, nonempty_Ioi]

theorem uniqueDiffOn_Iic (a : ℝ) : UniqueDiffOn ℝ (Iic a) :=
  uniqueDiffOn_convex (convex_Iic a) <| by simp only [interior_Iic, nonempty_Iio]

theorem uniqueDiffOn_Ioi (a : ℝ) : UniqueDiffOn ℝ (Ioi a) :=
  isOpen_Ioi.uniqueDiffOn

theorem uniqueDiffOn_Iio (a : ℝ) : UniqueDiffOn ℝ (Iio a) :=
  isOpen_Iio.uniqueDiffOn

theorem uniqueDiffOn_Icc {a b : ℝ} (hab : a < b) : UniqueDiffOn ℝ (Icc a b) :=
  uniqueDiffOn_convex (convex_Icc a b) <| by simp only [interior_Icc, nonempty_Ioo, hab]

theorem uniqueDiffOn_Ico (a b : ℝ) : UniqueDiffOn ℝ (Ico a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ico a b) <| by simp only [interior_Ico, nonempty_Ioo, hab]
  else by simp only [Ico_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioc (a b : ℝ) : UniqueDiffOn ℝ (Ioc a b) :=
  if hab : a < b then
    uniqueDiffOn_convex (convex_Ioc a b) <| by simp only [interior_Ioc, nonempty_Ioo, hab]
  else by simp only [Ioc_eq_empty hab, uniqueDiffOn_empty]

theorem uniqueDiffOn_Ioo (a b : ℝ) : UniqueDiffOn ℝ (Ioo a b) :=
  isOpen_Ioo.uniqueDiffOn

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
theorem uniqueDiffOn_Icc_zero_one : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) :=
  uniqueDiffOn_Icc zero_lt_one

theorem uniqueDiffWithinAt_Ioo {a b t : ℝ} (ht : t ∈ Set.Ioo a b) :
    UniqueDiffWithinAt ℝ (Set.Ioo a b) t :=
  IsOpen.uniqueDiffWithinAt isOpen_Ioo ht

theorem uniqueDiffWithinAt_Ioi (a : ℝ) : UniqueDiffWithinAt ℝ (Ioi a) a :=
  uniqueDiffWithinAt_convex (convex_Ioi a) (by simp) (by simp)

theorem uniqueDiffWithinAt_Iio (a : ℝ) : UniqueDiffWithinAt ℝ (Iio a) a :=
  uniqueDiffWithinAt_convex (convex_Iio a) (by simp) (by simp)

theorem uniqueDiffWithinAt_Ici (x : ℝ) : UniqueDiffWithinAt ℝ (Ici x) x :=
  (uniqueDiffWithinAt_Ioi x).mono Set.Ioi_subset_Ici_self

theorem uniqueDiffWithinAt_Iic (x : ℝ) : UniqueDiffWithinAt ℝ (Iic x) x :=
  (uniqueDiffWithinAt_Iio x).mono Set.Iio_subset_Iic_self

end Real
