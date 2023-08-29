/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.GCongr

#align_import analysis.convex.star from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Star-convex sets

This files defines star-convex sets (aka star domains, star-shaped set, radially convex set).

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Main declarations

* `StarConvex 𝕜 x s`: `s` is star-convex at `x` with scalars `𝕜`.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.

## TODO

Balanced sets are star-convex.

The closure of a star-convex set is star-convex.

Star-convex sets are contractible.

A nonempty open star-convex set in `ℝ^n` is diffeomorphic to the entire space.
-/


open Set

open Convex Pointwise

variable {𝕜 E F : Type*}

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (x : E) (s : Set E)

/-- Star-convexity of sets. `s` is star-convex at `x` if every segment from `x` to a point in `s` is
contained in `s`. -/
def StarConvex : Prop :=
  ∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s
#align star_convex StarConvex

variable {𝕜 x s} {t : Set E}

theorem starConvex_iff_segment_subset : StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s := by
  constructor
  -- ⊢ StarConvex 𝕜 x s → ∀ ⦃y : E⦄, y ∈ s → [x-[𝕜]y] ⊆ s
  · rintro h y hy z ⟨a, b, ha, hb, hab, rfl⟩
    -- ⊢ a • x + b • y ∈ s
    exact h hy ha hb hab
    -- 🎉 no goals
  · rintro h y hy a b ha hb hab
    -- ⊢ a • x + b • y ∈ s
    exact h hy ⟨a, b, ha, hb, hab, rfl⟩
    -- 🎉 no goals
#align star_convex_iff_segment_subset starConvex_iff_segment_subset

theorem StarConvex.segment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y ∈ s) : [x -[𝕜] y] ⊆ s :=
  starConvex_iff_segment_subset.1 h hy
#align star_convex.segment_subset StarConvex.segment_subset

theorem StarConvex.openSegment_subset (h : StarConvex 𝕜 x s) {y : E} (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hy)
#align star_convex.open_segment_subset StarConvex.openSegment_subset

/-- Alternative definition of star-convexity, in terms of pointwise set operations. -/
theorem starConvex_iff_pointwise_add_subset :
    StarConvex 𝕜 x s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • {x} + b • s ⊆ s := by
  refine'
    ⟨_, fun h y hy a b ha hb hab =>
      h ha hb hab (add_mem_add (smul_mem_smul_set <| mem_singleton _) ⟨_, hy, rfl⟩)⟩
  rintro hA a b ha hb hab w ⟨au, bv, ⟨u, rfl : u = x, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩
  -- ⊢ (fun x x_1 => x + x_1) ((fun x => a • x) u) ((fun x => b • x) v) ∈ s
  exact hA hv ha hb hab
  -- 🎉 no goals
#align star_convex_iff_pointwise_add_subset starConvex_iff_pointwise_add_subset

theorem starConvex_empty (x : E) : StarConvex 𝕜 x ∅ := fun _ hy => hy.elim
#align star_convex_empty starConvex_empty

theorem starConvex_univ (x : E) : StarConvex 𝕜 x univ := fun _ _ _ _ _ _ _ => trivial
#align star_convex_univ starConvex_univ

theorem StarConvex.inter (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) : StarConvex 𝕜 x (s ∩ t) :=
  fun _ hy _ _ ha hb hab => ⟨hs hy.left ha hb hab, ht hy.right ha hb hab⟩
#align star_convex.inter StarConvex.inter

theorem starConvex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋂₀ S) := fun _ hy _ _ ha hb hab s hs => h s hs (hy s hs) ha hb hab
#align star_convex_sInter starConvex_sInter

theorem starConvex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋂ i, s i) :=
  sInter_range s ▸ starConvex_sInter <| forall_range_iff.2 h
#align star_convex_Inter starConvex_iInter

theorem StarConvex.union (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 x t) :
    StarConvex 𝕜 x (s ∪ t) := by
  rintro y (hy | hy) a b ha hb hab
  -- ⊢ a • x + b • y ∈ s ∪ t
  · exact Or.inl (hs hy ha hb hab)
    -- 🎉 no goals
  · exact Or.inr (ht hy ha hb hab)
    -- 🎉 no goals
#align star_convex.union StarConvex.union

theorem starConvex_iUnion {ι : Sort*} {s : ι → Set E} (hs : ∀ i, StarConvex 𝕜 x (s i)) :
    StarConvex 𝕜 x (⋃ i, s i) := by
  rintro y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ ⋃ (i : ι), s i
  rw [mem_iUnion] at hy ⊢
  -- ⊢ ∃ i, a • x + b • y ∈ s i
  obtain ⟨i, hy⟩ := hy
  -- ⊢ ∃ i, a • x + b • y ∈ s i
  exact ⟨i, hs i hy ha hb hab⟩
  -- 🎉 no goals
#align star_convex_Union starConvex_iUnion

theorem starConvex_sUnion {S : Set (Set E)} (hS : ∀ s ∈ S, StarConvex 𝕜 x s) :
    StarConvex 𝕜 x (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  -- ⊢ StarConvex 𝕜 x (⋃ (i : ↑S), ↑i)
  exact starConvex_iUnion fun s => hS _ s.2
  -- 🎉 no goals
#align star_convex_sUnion starConvex_sUnion

theorem StarConvex.prod {y : F} {s : Set E} {t : Set F} (hs : StarConvex 𝕜 x s)
    (ht : StarConvex 𝕜 y t) : StarConvex 𝕜 (x, y) (s ×ˢ t) := fun _ hy _ _ ha hb hab =>
  ⟨hs hy.1 ha hb hab, ht hy.2 ha hb hab⟩
#align star_convex.prod StarConvex.prod

theorem starConvex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {x : ∀ i, E i} {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → StarConvex 𝕜 (x i) (t i)) :
    StarConvex 𝕜 x (s.pi t) := fun _ hy _ _ ha hb hab i hi => ht hi (hy i hi) ha hb hab
#align star_convex_pi starConvex_pi

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {x y z : E} {s : Set E}

theorem StarConvex.mem (hs : StarConvex 𝕜 x s) (h : s.Nonempty) : x ∈ s := by
  obtain ⟨y, hy⟩ := h
  -- ⊢ x ∈ s
  convert hs hy zero_le_one le_rfl (add_zero 1)
  -- ⊢ x = 1 • x + 0 • y
  rw [one_smul, zero_smul, add_zero]
  -- 🎉 no goals
#align star_convex.mem StarConvex.mem

theorem starConvex_iff_forall_pos (hx : x ∈ s) : StarConvex 𝕜 x s ↔
    ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine' ⟨fun h y hy a b ha hb hab => h hy ha.le hb.le hab, _⟩
  -- ⊢ (∀ ⦃y : E⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ …
  intro h y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ s
  obtain rfl | ha := ha.eq_or_lt
  -- ⊢ 0 • x + b • y ∈ s
  · rw [zero_add] at hab
    -- ⊢ 0 • x + b • y ∈ s
    rwa [hab, one_smul, zero_smul, zero_add]
    -- 🎉 no goals
  obtain rfl | hb := hb.eq_or_lt
  -- ⊢ a • x + 0 • y ∈ s
  · rw [add_zero] at hab
    -- ⊢ a • x + 0 • y ∈ s
    rwa [hab, one_smul, zero_smul, add_zero]
    -- 🎉 no goals
  exact h hy ha hb hab
  -- 🎉 no goals
#align star_convex_iff_forall_pos starConvex_iff_forall_pos

theorem starConvex_iff_forall_ne_pos (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔
      ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine' ⟨fun h y hy _ a b ha hb hab => h hy ha.le hb.le hab, _⟩
  -- ⊢ (∀ ⦃y : E⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + …
  intro h y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ s
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ 0 • x + b • y ∈ s
  · rw [zero_add] at hab
    -- ⊢ 0 • x + b • y ∈ s
    rwa [hab, zero_smul, one_smul, zero_add]
    -- 🎉 no goals
  obtain rfl | hb' := hb.eq_or_lt
  -- ⊢ a • x + 0 • y ∈ s
  · rw [add_zero] at hab
    -- ⊢ a • x + 0 • y ∈ s
    rwa [hab, zero_smul, one_smul, add_zero]
    -- 🎉 no goals
  obtain rfl | hxy := eq_or_ne x y
  -- ⊢ a • x + b • x ∈ s
  · rwa [Convex.combo_self hab]
    -- 🎉 no goals
  exact h hy hxy ha' hb' hab
  -- 🎉 no goals
#align star_convex_iff_forall_ne_pos starConvex_iff_forall_ne_pos

theorem starConvex_iff_openSegment_subset (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  starConvex_iff_segment_subset.trans <|
    forall₂_congr fun _ hy => (openSegment_subset_iff_segment_subset hx hy).symm
#align star_convex_iff_open_segment_subset starConvex_iff_openSegment_subset

theorem starConvex_singleton (x : E) : StarConvex 𝕜 x {x} := by
  rintro y (rfl : y = x) a b _ _ hab
  -- ⊢ a • y + b • y ∈ {y}
  exact Convex.combo_self hab _
  -- 🎉 no goals
#align star_convex_singleton starConvex_singleton

theorem StarConvex.linear_image (hs : StarConvex 𝕜 x s) (f : E →ₗ[𝕜] F) :
    StarConvex 𝕜 (f x) (s.image f) := by
  intro y hy a b ha hb hab
  -- ⊢ a • ↑f x + b • y ∈ ↑f '' s
  obtain ⟨y', hy', rfl⟩ := hy
  -- ⊢ a • ↑f x + b • ↑f y' ∈ ↑f '' s
  exact ⟨a • x + b • y', hs hy' ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩
  -- 🎉 no goals
#align star_convex.linear_image StarConvex.linear_image

theorem StarConvex.is_linear_image (hs : StarConvex 𝕜 x s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    StarConvex 𝕜 (f x) (f '' s) :=
  hs.linear_image <| hf.mk' f
#align star_convex.is_linear_image StarConvex.is_linear_image

theorem StarConvex.linear_preimage {s : Set F} (f : E →ₗ[𝕜] F) (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (s.preimage f) := by
  intro y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ ↑f ⁻¹' s
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  -- ⊢ a • ↑f x + b • ↑f y ∈ s
  exact hs hy ha hb hab
  -- 🎉 no goals
#align star_convex.linear_preimage StarConvex.linear_preimage

theorem StarConvex.is_linear_preimage {s : Set F} {f : E → F} (hs : StarConvex 𝕜 (f x) s)
    (hf : IsLinearMap 𝕜 f) : StarConvex 𝕜 x (preimage f s) :=
  hs.linear_preimage <| hf.mk' f
#align star_convex.is_linear_preimage StarConvex.is_linear_preimage

theorem StarConvex.add {t : Set E} (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x + y) (s + t) := by
  rw [← add_image_prod]
  -- ⊢ StarConvex 𝕜 (x + y) ((fun x => x.fst + x.snd) '' s ×ˢ t)
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add
  -- 🎉 no goals
#align star_convex.add StarConvex.add

theorem StarConvex.add_left (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (z + x) ((fun x => z + x) '' s) := by
  intro y hy a b ha hb hab
  -- ⊢ a • (z + x) + b • y ∈ (fun x => z + x) '' s
  obtain ⟨y', hy', rfl⟩ := hy
  -- ⊢ a • (z + x) + b • (fun x => z + x) y' ∈ (fun x => z + x) '' s
  refine' ⟨a • x + b • y', hs hy' ha hb hab, _⟩
  -- ⊢ (fun x => z + x) (a • x + b • y') = a • (z + x) + b • (fun x => z + x) y'
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  -- 🎉 no goals
#align star_convex.add_left StarConvex.add_left

theorem StarConvex.add_right (hs : StarConvex 𝕜 x s) (z : E) :
    StarConvex 𝕜 (x + z) ((fun x => x + z) '' s) := by
  intro y hy a b ha hb hab
  -- ⊢ a • (x + z) + b • y ∈ (fun x => x + z) '' s
  obtain ⟨y', hy', rfl⟩ := hy
  -- ⊢ a • (x + z) + b • (fun x => x + z) y' ∈ (fun x => x + z) '' s
  refine' ⟨a • x + b • y', hs hy' ha hb hab, _⟩
  -- ⊢ (fun x => x + z) (a • x + b • y') = a • (x + z) + b • (fun x => x + z) y'
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]
  -- 🎉 no goals
#align star_convex.add_right StarConvex.add_right

/-- The translation of a star-convex set is also star-convex. -/
theorem StarConvex.preimage_add_right (hs : StarConvex 𝕜 (z + x) s) :
    StarConvex 𝕜 x ((fun x => z + x) ⁻¹' s) := by
  intro y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ (fun x => z + x) ⁻¹' s
  have h := hs hy ha hb hab
  -- ⊢ a • x + b • y ∈ (fun x => z + x) ⁻¹' s
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h
  -- 🎉 no goals
#align star_convex.preimage_add_right StarConvex.preimage_add_right

/-- The translation of a star-convex set is also star-convex. -/
theorem StarConvex.preimage_add_left (hs : StarConvex 𝕜 (x + z) s) :
    StarConvex 𝕜 x ((fun x => x + z) ⁻¹' s) := by
  rw [add_comm] at hs
  -- ⊢ StarConvex 𝕜 x ((fun x => x + z) ⁻¹' s)
  simpa only [add_comm] using hs.preimage_add_right
  -- 🎉 no goals
#align star_convex.preimage_add_left StarConvex.preimage_add_left

end Module

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x y : E}

theorem StarConvex.sub' {s : Set (E × E)} (hs : StarConvex 𝕜 (x, y) s) :
    StarConvex 𝕜 (x - y) ((fun x : E × E => x.1 - x.2) '' s) :=
  hs.is_linear_image IsLinearMap.isLinearMap_sub
#align star_convex.sub' StarConvex.sub'

end AddCommGroup

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {x : E} {s : Set E}

theorem StarConvex.smul (hs : StarConvex 𝕜 x s) (c : 𝕜) : StarConvex 𝕜 (c • x) (c • s) :=
  hs.linear_image <| LinearMap.lsmul _ _ c
#align star_convex.smul StarConvex.smul

theorem StarConvex.preimage_smul {c : 𝕜} (hs : StarConvex 𝕜 (c • x) s) :
    StarConvex 𝕜 x ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)
#align star_convex.preimage_smul StarConvex.preimage_smul

theorem StarConvex.affinity (hs : StarConvex 𝕜 x s) (z : E) (c : 𝕜) :
    StarConvex 𝕜 (z + c • x) ((fun x => z + c • x) '' s) := by
  have h := (hs.smul c).add_left z
  -- ⊢ StarConvex 𝕜 (z + c • x) ((fun x => z + c • x) '' s)
  rwa [← image_smul, image_image] at h
  -- 🎉 no goals
#align star_convex.affinity StarConvex.affinity

end AddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [SMulWithZero 𝕜 E] {s : Set E}

theorem starConvex_zero_iff :
    StarConvex 𝕜 0 s ↔ ∀ ⦃x : E⦄, x ∈ s → ∀ ⦃a : 𝕜⦄, 0 ≤ a → a ≤ 1 → a • x ∈ s := by
  refine'
    forall_congr' fun x => forall_congr' fun _ => ⟨fun h a ha₀ ha₁ => _, fun h a b ha hb hab => _⟩
  · simpa only [sub_add_cancel, eq_self_iff_true, forall_true_left, zero_add, smul_zero] using
      h (sub_nonneg_of_le ha₁) ha₀
  · rw [smul_zero, zero_add]
    -- ⊢ b • x ∈ s
    exact h hb (by rw [← hab]; exact le_add_of_nonneg_left ha)
    -- 🎉 no goals
#align star_convex_zero_iff starConvex_zero_iff

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {x y : E} {s t : Set E}

theorem StarConvex.add_smul_mem (hs : StarConvex 𝕜 x s) (hy : x + y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  -- ⊢ (1 - t) • x + t • (x + y) ∈ s
  exact hs hy (sub_nonneg_of_le ht₁) ht₀ (sub_add_cancel _ _)
  -- 🎉 no goals
#align star_convex.add_smul_mem StarConvex.add_smul_mem

theorem StarConvex.smul_mem (hs : StarConvex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : t • x ∈ s := by simpa using hs.add_smul_mem (by simpa using hx) ht₀ ht₁
                                    -- 🎉 no goals
#align star_convex.smul_mem StarConvex.smul_mem

theorem StarConvex.add_smul_sub_mem (hs : StarConvex 𝕜 x s) (hy : y ∈ s) {t : 𝕜} (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) : x + t • (y - x) ∈ s := by
  apply hs.segment_subset hy
  -- ⊢ x + t • (y - x) ∈ [x-[𝕜]y]
  rw [segment_eq_image']
  -- ⊢ x + t • (y - x) ∈ (fun θ => x + θ • (y - x)) '' Icc 0 1
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩
  -- 🎉 no goals
#align star_convex.add_smul_sub_mem StarConvex.add_smul_sub_mem

/-- The preimage of a star-convex set under an affine map is star-convex. -/
theorem StarConvex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : StarConvex 𝕜 (f x) s) :
    StarConvex 𝕜 x (f ⁻¹' s) := by
  intro y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ ↑f ⁻¹' s
  rw [mem_preimage, Convex.combo_affine_apply hab]
  -- ⊢ a • ↑f x + b • ↑f y ∈ s
  exact hs hy ha hb hab
  -- 🎉 no goals
#align star_convex.affine_preimage StarConvex.affine_preimage

/-- The image of a star-convex set under an affine map is star-convex. -/
theorem StarConvex.affine_image (f : E →ᵃ[𝕜] F) {s : Set E} (hs : StarConvex 𝕜 x s) :
    StarConvex 𝕜 (f x) (f '' s) := by
  rintro y ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  -- ⊢ a • ↑f x + b • y ∈ ↑f '' s
  refine' ⟨a • x + b • y', ⟨hs hy' ha hb hab, _⟩⟩
  -- ⊢ ↑f (a • x + b • y') = a • ↑f x + b • y
  rw [Convex.combo_affine_apply hab, hy'f]
  -- 🎉 no goals
#align star_convex.affine_image StarConvex.affine_image

theorem StarConvex.neg (hs : StarConvex 𝕜 x s) : StarConvex 𝕜 (-x) (-s) := by
  rw [← image_neg]
  -- ⊢ StarConvex 𝕜 (-x) (Neg.neg '' s)
  exact hs.is_linear_image IsLinearMap.isLinearMap_neg
  -- 🎉 no goals
#align star_convex.neg StarConvex.neg

theorem StarConvex.sub (hs : StarConvex 𝕜 x s) (ht : StarConvex 𝕜 y t) :
    StarConvex 𝕜 (x - y) (s - t) := by
  simp_rw [sub_eq_add_neg]
  -- ⊢ StarConvex 𝕜 (x + -y) (s + -t)
  exact hs.add ht.neg
  -- 🎉 no goals
#align star_convex.sub StarConvex.sub

end AddCommGroup

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] {x : E} {s : Set E}

/-- Alternative definition of star-convexity, using division. -/
theorem starConvex_iff_div : StarConvex 𝕜 x s ↔ ∀ ⦃y⦄, y ∈ s →
    ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  ⟨fun h y hy a b ha hb hab => by
    apply h hy
    · positivity
      -- 🎉 no goals
    · positivity
      -- 🎉 no goals
    · rw [← add_div]
      -- ⊢ (a + b) / (a + b) = 1
      exact div_self hab.ne',
      -- 🎉 no goals
  fun h y hy a b ha hb hab => by
    have h' := h hy ha hb
    -- ⊢ a • x + b • y ∈ s
    rw [hab, div_one, div_one] at h'
    -- ⊢ a • x + b • y ∈ s
    exact h' zero_lt_one⟩
    -- 🎉 no goals
#align star_convex_iff_div starConvex_iff_div

theorem StarConvex.mem_smul (hs : StarConvex 𝕜 0 s) (hx : x ∈ s) {t : 𝕜} (ht : 1 ≤ t) :
    x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  -- ⊢ t⁻¹ • x ∈ s
  exact hs.smul_mem hx (by positivity) (inv_le_one ht)
  -- 🎉 no goals
#align star_convex.mem_smul StarConvex.mem_smul

end AddCommGroup

end LinearOrderedField

/-!
#### Star-convex sets in an ordered space

Relates `starConvex` and `Set.ordConnected`.
-/


section OrdConnected

theorem Set.OrdConnected.starConvex [OrderedSemiring 𝕜] [OrderedAddCommMonoid E] [Module 𝕜 E]
    [OrderedSMul 𝕜 E] {x : E} {s : Set E} (hs : s.OrdConnected) (hx : x ∈ s)
    (h : ∀ y ∈ s, x ≤ y ∨ y ≤ x) : StarConvex 𝕜 x s := by
  intro y hy a b ha hb hab
  -- ⊢ a • x + b • y ∈ s
  obtain hxy | hyx := h _ hy
  -- ⊢ a • x + b • y ∈ s
  · refine' hs.out hx hy (mem_Icc.2 ⟨_, _⟩)
    -- ⊢ x ≤ a • x + b • y
    calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ ≤ a • x + b • y := by gcongr
    calc
      a • x + b • y ≤ a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _
  · refine' hs.out hy hx (mem_Icc.2 ⟨_, _⟩)
    -- ⊢ y ≤ a • x + b • y
    calc
      y = a • y + b • y := (Convex.combo_self hab _).symm
      _ ≤ a • x + b • y := by gcongr
    calc
      a • x + b • y ≤ a • x + b • x := by gcongr
      _ = x := Convex.combo_self hab _
#align set.ord_connected.star_convex Set.OrdConnected.starConvex

theorem starConvex_iff_ordConnected [LinearOrderedField 𝕜] {x : 𝕜} {s : Set 𝕜} (hx : x ∈ s) :
    StarConvex 𝕜 x s ↔ s.OrdConnected := by
  simp_rw [ordConnected_iff_uIcc_subset_left hx, starConvex_iff_segment_subset, segment_eq_uIcc]
  -- 🎉 no goals
#align star_convex_iff_ord_connected starConvex_iff_ordConnected

alias ⟨StarConvex.ordConnected, _⟩ := starConvex_iff_ordConnected
#align star_convex.ord_connected StarConvex.ordConnected

end OrdConnected
