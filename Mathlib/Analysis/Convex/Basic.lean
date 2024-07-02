/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Analysis.Convex.Star
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace

#align_import analysis.convex.basic from "leanprover-community/mathlib"@"92bd7b1ffeb306a89f450bee126ddd8a284c259d"

/-!
# Convex sets and functions in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `Convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.
* `stdSimplex 𝕜 ι`: The standard simplex in `ι → 𝕜` (currently requires `Fintype ι`). It is the
  intersection of the positive quadrant with the hyperplane `s.sum = 1`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## TODO

Generalize all this file to affine spaces.
-/


variable {𝕜 E F β : Type*}

open LinearMap Set

open scoped Convex Pointwise

/-! ### Convexity of sets -/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E) {x : E}

/-- Convexity of sets. -/
def Convex : Prop :=
  ∀ ⦃x : E⦄, x ∈ s → StarConvex 𝕜 x s
#align convex Convex

variable {𝕜 s}

theorem Convex.starConvex (hs : Convex 𝕜 s) (hx : x ∈ s) : StarConvex 𝕜 x s :=
  hs hx
#align convex.star_convex Convex.starConvex

theorem convex_iff_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → [x -[𝕜] y] ⊆ s :=
  forall₂_congr fun _ _ => starConvex_iff_segment_subset
#align convex_iff_segment_subset convex_iff_segment_subset

theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    [x -[𝕜] y] ⊆ s :=
  convex_iff_segment_subset.1 h hx hy
#align convex.segment_subset Convex.segment_subset

theorem Convex.openSegment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s :=
  (openSegment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)
#align convex.open_segment_subset Convex.openSegment_subset

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
theorem convex_iff_pointwise_add_subset :
    Convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h x hx y hy a b ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)
#align convex_iff_pointwise_add_subset convex_iff_pointwise_add_subset

alias ⟨Convex.set_combo_subset, _⟩ := convex_iff_pointwise_add_subset
#align convex.set_combo_subset Convex.set_combo_subset

theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun _ => False.elim
#align convex_empty convex_empty

theorem convex_univ : Convex 𝕜 (Set.univ : Set E) := fun _ _ => starConvex_univ _
#align convex_univ convex_univ

theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ∩ t) :=
  fun _ hx => (hs hx.1).inter (ht hx.2)
#align convex.inter Convex.inter

theorem convex_sInter {S : Set (Set E)} (h : ∀ s ∈ S, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) := fun _ hx =>
  starConvex_sInter fun _ hs => h _ hs <| hx _ hs
#align convex_sInter convex_sInter

theorem convex_iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) :
    Convex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ convex_sInter <| forall_mem_range.2 h
#align convex_Inter convex_iInter

theorem convex_iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : ∀ i, κ i → Set E}
    (h : ∀ i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i j) :=
  convex_iInter fun i => convex_iInter <| h i
#align convex_Inter₂ convex_iInter₂

theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
    Convex 𝕜 (s ×ˢ t) := fun _ hx => (hs hx.1).prod (ht hx.2)
#align convex.prod Convex.prod

theorem convex_pi {ι : Type*} {E : ι → Type*} [∀ i, AddCommMonoid (E i)] [∀ i, SMul 𝕜 (E i)]
    {s : Set ι} {t : ∀ i, Set (E i)} (ht : ∀ ⦃i⦄, i ∈ s → Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) :=
  fun _ hx => starConvex_pi fun _ hi => ht hi <| hx _ hi
#align convex_pi convex_pi

theorem Directed.convex_iUnion {ι : Sort*} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hc : ∀ ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy a b ha hb hab
  rw [mem_iUnion] at hx hy ⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩
#align directed.convex_Union Directed.convex_iUnion

theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) c)
    (hc : ∀ ⦃A : Set E⦄, A ∈ c → Convex 𝕜 A) : Convex 𝕜 (⋃₀ c) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).convex_iUnion fun A => hc A.2
#align directed_on.convex_sUnion DirectedOn.convex_sUnion

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

theorem convex_iff_openSegment_subset :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → openSegment 𝕜 x y ⊆ s :=
  forall₂_congr fun _ => starConvex_iff_openSegment_subset
#align convex_iff_open_segment_subset convex_iff_openSegment_subset

theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔
      ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  forall₂_congr fun _ => starConvex_iff_forall_pos
#align convex_iff_forall_pos convex_iff_forall_pos

theorem convex_iff_pairwise_pos : Convex 𝕜 s ↔
    s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, ?_⟩
  intro h x hx y hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
  · exact h hx hy hxy ha hb hab
#align convex_iff_pairwise_pos convex_iff_pairwise_pos

theorem Convex.starConvex_iff (hs : Convex 𝕜 s) (h : s.Nonempty) : StarConvex 𝕜 x s ↔ x ∈ s :=
  ⟨fun hxs => hxs.mem h, hs.starConvex⟩
#align convex.star_convex_iff Convex.starConvex_iff

protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.pairwise _)
#align set.subsingleton.convex Set.Subsingleton.convex

theorem convex_singleton (c : E) : Convex 𝕜 ({c} : Set E) :=
  subsingleton_singleton.convex
#align convex_singleton convex_singleton

theorem convex_zero : Convex 𝕜 (0 : Set E) :=
  convex_singleton _
#align convex_zero convex_zero

theorem convex_segment (x y : E) : Convex 𝕜 [x -[𝕜] y] := by
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_add, habp, habq, mul_one, mul_one, hab]
  · simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_comm _ _ _ _
#align convex_segment convex_segment

theorem Convex.linear_image (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  exact ⟨a • x + b • y, hs hx hy ha hb hab, by rw [f.map_add, f.map_smul, f.map_smul]⟩
#align convex.linear_image Convex.linear_image

theorem Convex.is_linear_image (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f '' s) :=
  hs.linear_image <| hf.mk' f
#align convex.is_linear_image Convex.is_linear_image

theorem Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) :
    Convex 𝕜 (f ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy ha hb hab
#align convex.linear_preimage Convex.linear_preimage

theorem Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f ⁻¹' s) :=
  hs.linear_preimage <| hf.mk' f
#align convex.is_linear_preimage Convex.is_linear_preimage

theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.isLinearMap_add
#align convex.add Convex.add

variable (𝕜 E)

/-- The convex sets form an additive submonoid under pointwise addition. -/
def convexAddSubmonoid : AddSubmonoid (Set E) where
  carrier := {s : Set E | Convex 𝕜 s}
  zero_mem' := convex_zero
  add_mem' := Convex.add
#align convex_add_submonoid convexAddSubmonoid

@[simp, norm_cast]
theorem coe_convexAddSubmonoid : ↑(convexAddSubmonoid 𝕜 E) = {s : Set E | Convex 𝕜 s} :=
  rfl
#align coe_convex_add_submonoid coe_convexAddSubmonoid

variable {𝕜 E}

@[simp]
theorem mem_convexAddSubmonoid {s : Set E} : s ∈ convexAddSubmonoid 𝕜 E ↔ Convex 𝕜 s :=
  Iff.rfl
#align mem_convex_add_submonoid mem_convexAddSubmonoid

theorem convex_list_sum {l : List (Set E)} (h : ∀ i ∈ l, Convex 𝕜 i) : Convex 𝕜 l.sum :=
  (convexAddSubmonoid 𝕜 E).list_sum_mem h
#align convex_list_sum convex_list_sum

theorem convex_multiset_sum {s : Multiset (Set E)} (h : ∀ i ∈ s, Convex 𝕜 i) : Convex 𝕜 s.sum :=
  (convexAddSubmonoid 𝕜 E).multiset_sum_mem _ h
#align convex_multiset_sum convex_multiset_sum

theorem convex_sum {ι} {s : Finset ι} (t : ι → Set E) (h : ∀ i ∈ s, Convex 𝕜 (t i)) :
    Convex 𝕜 (∑ i ∈ s, t i) :=
  (convexAddSubmonoid 𝕜 E).sum_mem h
#align convex_sum convex_sum

theorem Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s) := by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs
#align convex.vadd Convex.vadd

theorem Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) '' s) :=
  hs.vadd _
#align convex.translate Convex.translate

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h
#align convex.translate_preimage_right Convex.translate_preimage_right

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) :
    Convex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.translate_preimage_right z
#align convex.translate_preimage_left Convex.translate_preimage_left

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] [Module 𝕜 β] [OrderedSMul 𝕜 β]

theorem convex_Iic (r : β) : Convex 𝕜 (Iic r) := fun x hx y hy a b ha hb hab =>
  calc
    a • x + b • y ≤ a • r + b • r :=
      add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ = r := Convex.combo_self hab _
#align convex_Iic convex_Iic

theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
  @convex_Iic 𝕜 βᵒᵈ _ _ _ _ r
#align convex_Ici convex_Ici

theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)
#align convex_Icc convex_Icc

theorem convex_halfspace_le {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w ≤ r } :=
  (convex_Iic r).is_linear_preimage h
#align convex_halfspace_le convex_halfspace_le

theorem convex_halfspace_ge {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r ≤ f w } :=
  (convex_Ici r).is_linear_preimage h
#align convex_halfspace_ge convex_halfspace_ge

theorem convex_hyperplane {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w = r } := by
  simp_rw [le_antisymm_iff]
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r)
#align convex_hyperplane convex_hyperplane

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid β] [Module 𝕜 β] [OrderedSMul 𝕜 β]

theorem convex_Iio (r : β) : Convex 𝕜 (Iio r) := by
  intro x hx y hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    rwa [zero_smul, zero_add, hab, one_smul]
  rw [mem_Iio] at hx hy
  calc
    a • x + b • y < a • r + b • r := add_lt_add_of_lt_of_le
        (smul_lt_smul_of_pos_left hx ha') (smul_le_smul_of_nonneg_left hy.le hb)
    _ = r := Convex.combo_self hab _
#align convex_Iio convex_Iio

theorem convex_Ioi (r : β) : Convex 𝕜 (Ioi r) :=
  @convex_Iio 𝕜 βᵒᵈ _ _ _ _ r
#align convex_Ioi convex_Ioi

theorem convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)
#align convex_Ioo convex_Ioo

theorem convex_Ico (r s : β) : Convex 𝕜 (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)
#align convex_Ico convex_Ico

theorem convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)
#align convex_Ioc convex_Ioc

theorem convex_halfspace_lt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h
#align convex_halfspace_lt convex_halfspace_lt

theorem convex_halfspace_gt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h
#align convex_halfspace_gt convex_halfspace_gt

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid β] [Module 𝕜 β] [OrderedSMul 𝕜 β]

theorem convex_uIcc (r s : β) : Convex 𝕜 (uIcc r s) :=
  convex_Icc _ _
#align convex_uIcc convex_uIcc

end LinearOrderedAddCommMonoid

end Module

end AddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [OrderedAddCommMonoid β] [Module 𝕜 E] [OrderedSMul 𝕜 E]
  {s : Set E} {f : E → β}

theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x ≤ r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' { x | f x ≤ r } hx.2 hy.2)⟩
#align monotone_on.convex_le MonotoneOn.convex_le

theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) := fun x hx y hy _ _ ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1)
          (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' { x | f x < r } hx.2 hy.2)⟩
#align monotone_on.convex_lt MonotoneOn.convex_lt

theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  @MonotoneOn.convex_le 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r
#align monotone_on.convex_ge MonotoneOn.convex_ge

theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  @MonotoneOn.convex_lt 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r
#align monotone_on.convex_gt MonotoneOn.convex_gt

theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  @MonotoneOn.convex_ge 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r
#align antitone_on.convex_le AntitoneOn.convex_le

theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) :=
  @MonotoneOn.convex_gt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r
#align antitone_on.convex_lt AntitoneOn.convex_lt

theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  @MonotoneOn.convex_le 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r
#align antitone_on.convex_ge AntitoneOn.convex_ge

theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  @MonotoneOn.convex_lt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r
#align antitone_on.convex_gt AntitoneOn.convex_gt

theorem Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)
#align monotone.convex_le Monotone.convex_le

theorem Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)
#align monotone.convex_lt Monotone.convex_lt

theorem Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_ge convex_univ r)
#align monotone.convex_ge Monotone.convex_ge

theorem Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.monotoneOn univ).convex_le convex_univ r)
#align monotone.convex_gt Monotone.convex_gt

theorem Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_le convex_univ r)
#align antitone.convex_le Antitone.convex_le

theorem Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_lt convex_univ r)
#align antitone.convex_lt Antitone.convex_lt

theorem Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_ge convex_univ r)
#align antitone.convex_ge Antitone.convex_ge

theorem Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x } :=
  Set.sep_univ.subst ((hf.antitoneOn univ).convex_gt convex_univ r)
#align antitone.convex_gt Antitone.convex_gt

end LinearOrderedAddCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)
#align convex.smul Convex.smul

theorem Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)
#align convex.smul_preimage Convex.smul_preimage

theorem Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) :
    Convex 𝕜 ((fun x => z + c • x) '' s) := by
  simpa only [← image_smul, ← image_vadd, image_image] using (hs.smul c).vadd z
#align convex.affinity Convex.affinity

end AddCommMonoid

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [StrictOrderedCommSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem convex_openSegment (a b : E) : Convex 𝕜 (openSegment 𝕜 a b) := by
  rw [convex_iff_openSegment_subset]
  rintro p ⟨ap, bp, hap, hbp, habp, rfl⟩ q ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨a * ap + b * aq, a * bp + b * bq, by positivity, by positivity, ?_, ?_⟩
  · rw [add_add_add_comm, ← mul_add, ← mul_add, habp, habq, mul_one, mul_one, hab]
  · simp_rw [add_smul, mul_smul, smul_add, add_add_add_comm]
#align convex_open_segment convex_openSegment

end StrictOrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E}

@[simp]
theorem convex_vadd (a : E) : Convex 𝕜 (a +ᵥ s) ↔ Convex 𝕜 s :=
  ⟨fun h ↦ by simpa using h.vadd (-a), fun h ↦ h.vadd _⟩

theorem Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)
#align convex.add_smul_mem Convex.add_smul_mem

theorem Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
    {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) ht
#align convex.smul_mem_of_zero_mem Convex.smul_mem_of_zero_mem

theorem Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s := by
  simpa only [mapsTo', segment_eq_image_lineMap] using h.segment_subset hx hy

theorem Convex.lineMap_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc 0 1) : AffineMap.lineMap x y t ∈ s :=
  h.mapsTo_lineMap hx hy ht

theorem Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : x + t • (y - x) ∈ s := by
  rw [add_comm]
  exact h.lineMap_mem hx hy ht
#align convex.add_smul_sub_mem Convex.add_smul_sub_mem

/-- Affine subspaces are convex. -/
theorem AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E) :=
  fun x hx y hy a b _ _ hab ↦ by simpa [Convex.combo_eq_smul_sub_add hab] using Q.2 _ hy hx hx
#align affine_subspace.convex AffineSubspace.convex

/-- The preimage of a convex set under an affine map is convex. -/
theorem Convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s) :=
  fun _ hx => (hs hx).affine_preimage _
#align convex.affine_preimage Convex.affine_preimage

/-- The image of a convex set under an affine map is convex. -/
theorem Convex.affine_image (f : E →ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hs hx).affine_image _
#align convex.affine_image Convex.affine_image

theorem Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg
#align convex.neg Convex.neg

theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg
#align convex.sub Convex.sub

end AddCommGroup

end OrderedRing

section LinearOrderedRing

variable [LinearOrderedRing 𝕜] [AddCommMonoid E]

theorem Convex_subadditive_le [SMul 𝕜 E] {f : E → 𝕜} (hf1 : ∀ x y, f (x + y) ≤ (f x) + (f y))
    (hf2 : ∀ ⦃c⦄ x, 0 ≤ c → f (c • x) ≤ c * f x) (B : 𝕜) :
    Convex 𝕜 { x | f x ≤ B } := by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ ≤ a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ ≤ a • B + b • B :=
        add_le_add (smul_le_smul_of_nonneg_left hx ha) (smul_le_smul_of_nonneg_left hy hb)
    _ ≤ B := by rw [← add_smul, hs, one_smul]

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-- Alternative definition of set convexity, using division. -/
theorem convex_iff_div :
    Convex 𝕜 s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  forall₂_congr fun _ _ => starConvex_iff_div
#align convex_iff_div convex_iff_div

theorem Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s)
    {t : 𝕜} (ht : 1 ≤ t) : x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩
#align convex.mem_smul_of_zero_mem Convex.mem_smul_of_zero_mem

theorem Convex.exists_mem_add_smul_eq (h : Convex 𝕜 s) {x y : E} {p q : 𝕜} (hx : x ∈ s) (hy : y ∈ s)
    (hp : 0 ≤ p) (hq : 0 ≤ q) : ∃ z ∈ s, (p + q) • z = p • x + q • y := by
  rcases _root_.em (p = 0 ∧ q = 0) with (⟨rfl, rfl⟩ | hpq)
  · use x, hx
    simp
  · replace hpq : 0 < p + q := (add_nonneg hp hq).lt_of_ne' (mt (add_eq_zero_iff' hp hq).1 hpq)
    refine ⟨_, convex_iff_div.1 h hx hy hp hq hpq, ?_⟩
    simp only [smul_add, smul_smul, mul_div_cancel₀ _ hpq.ne']

theorem Convex.add_smul (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) • s = p • s + q • s := (add_smul_subset _ _ _).antisymm <| by
  rintro _ ⟨_, ⟨v₁, h₁, rfl⟩, _, ⟨v₂, h₂, rfl⟩, rfl⟩
  exact h_conv.exists_mem_add_smul_eq h₁ h₂ hp hq
#align convex.add_smul Convex.add_smul

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `Convex` and `OrdConnected`.
-/


section

theorem Set.OrdConnected.convex_of_chain [OrderedSemiring 𝕜] [OrderedAddCommMonoid E] [Module 𝕜 E]
    [OrderedSMul 𝕜 E] {s : Set E} (hs : s.OrdConnected) (h : IsChain (· ≤ ·) s) : Convex 𝕜 s := by
  refine convex_iff_segment_subset.mpr fun x hx y hy => ?_
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)
#align set.ord_connected.convex_of_chain Set.OrdConnected.convex_of_chain

theorem Set.OrdConnected.convex [OrderedSemiring 𝕜] [LinearOrderedAddCommMonoid E] [Module 𝕜 E]
    [OrderedSMul 𝕜 E] {s : Set E} (hs : s.OrdConnected) : Convex 𝕜 s :=
  hs.convex_of_chain <| isChain_of_trichotomous s
#align set.ord_connected.convex Set.OrdConnected.convex

theorem convex_iff_ordConnected [LinearOrderedField 𝕜] {s : Set 𝕜} :
    Convex 𝕜 s ↔ s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_uIcc, ordConnected_iff_uIcc_subset]
#align convex_iff_ord_connected convex_iff_ordConnected

alias ⟨Convex.ordConnected, _⟩ := convex_iff_ordConnected
#align convex.ord_connected Convex.ordConnected

end

/-! #### Convexity of submodules/subspaces -/


namespace Submodule

variable [OrderedSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

protected theorem convex (K : Submodule 𝕜 E) : Convex 𝕜 (↑K : Set E) := by
  repeat' intro
  refine add_mem (smul_mem _ _ ?_) (smul_mem _ _ ?_) <;> assumption
#align submodule.convex Submodule.convex

protected theorem starConvex (K : Submodule 𝕜 E) : StarConvex 𝕜 (0 : E) K :=
  K.convex K.zero_mem
#align submodule.star_convex Submodule.starConvex

end Submodule

/-! ### Simplex -/


section Simplex

section OrderedSemiring

variable (𝕜) (ι : Type*) [OrderedSemiring 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
def stdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }
#align std_simplex stdSimplex

theorem stdSimplex_eq_inter : stdSimplex 𝕜 ι = (⋂ x, { f | 0 ≤ f x }) ∩ { f | ∑ x, f x = 1 } := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
#align std_simplex_eq_inter stdSimplex_eq_inter

theorem convex_stdSimplex : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · erw [Finset.sum_add_distrib]
    simp only [Pi.smul_apply] -- Porting note: `erw` failed to rewrite with `← Finset.smul_sum`
    rw [← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]
    exact hab
#align convex_std_simplex convex_stdSimplex

@[nontriviality] lemma stdSimplex_of_subsingleton [Subsingleton 𝕜] : stdSimplex 𝕜 ι = univ :=
  eq_univ_of_forall fun _ ↦ ⟨fun _ ↦ (Subsingleton.elim _ _).le, Subsingleton.elim _ _⟩

/-- The standard simplex in the zero-dimensional space is empty. -/
lemma stdSimplex_of_isEmpty_index [IsEmpty ι] [Nontrivial 𝕜] : stdSimplex 𝕜 ι = ∅ :=
  eq_empty_of_forall_not_mem <| by rintro f ⟨-, hf⟩; simp at hf

lemma stdSimplex_unique [Unique ι] : stdSimplex 𝕜 ι = {fun _ ↦ 1} := by
  refine eq_singleton_iff_unique_mem.2 ⟨⟨fun _ ↦ zero_le_one, Fintype.sum_unique _⟩, ?_⟩
  rintro f ⟨-, hf⟩
  rw [Fintype.sum_unique] at hf
  exact funext (Unique.forall_iff.2 hf)

variable {ι} [DecidableEq ι]

theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 ∈ stdSimplex 𝕜 ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ ↦ le_rfl⟩, by simp⟩

theorem ite_eq_mem_stdSimplex (i : ι) : (if i = · then (1 : 𝕜) else 0) ∈ stdSimplex 𝕜 ι := by
  simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_stdSimplex 𝕜 i
#align ite_eq_mem_std_simplex ite_eq_mem_stdSimplex

#adaptation_note /-- as of `nightly-2024-03-11`, we need a type annotation on the segment in the
following two lemmas. -/

/-- The edges are contained in the simplex. -/
lemma segment_single_subset_stdSimplex (i j : ι) :
    ([Pi.single i 1 -[𝕜] Pi.single j 1] : Set (ι → 𝕜)) ⊆ stdSimplex 𝕜 ι :=
  (convex_stdSimplex 𝕜 ι).segment_subset (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

lemma stdSimplex_fin_two :
    stdSimplex 𝕜 (Fin 2) = ([Pi.single 0 1 -[𝕜] Pi.single 1 1] : Set (Fin 2 → 𝕜)) := by
  refine Subset.antisymm ?_ (segment_single_subset_stdSimplex 𝕜 (0 : Fin 2) 1)
  rintro f ⟨hf₀, hf₁⟩
  rw [Fin.sum_univ_two] at hf₁
  refine ⟨f 0, f 1, hf₀ 0, hf₀ 1, hf₁, funext <| Fin.forall_fin_two.2 ?_⟩
  simp

end OrderedSemiring

section OrderedRing

variable (𝕜) [OrderedRing 𝕜]

/-- The standard one-dimensional simplex in `Fin 2 → 𝕜` is equivalent to the unit interval. -/
@[simps (config := .asFn)]
def stdSimplexEquivIcc : stdSimplex 𝕜 (Fin 2) ≃ Icc (0 : 𝕜) 1 where
  toFun f := ⟨f.1 0, f.2.1 _, f.2.2 ▸
    Finset.single_le_sum (fun i _ ↦ f.2.1 i) (Finset.mem_univ _)⟩
  invFun x := ⟨![x, 1 - x], Fin.forall_fin_two.2 ⟨x.2.1, sub_nonneg.2 x.2.2⟩,
    calc
      ∑ i : Fin 2, ![(x : 𝕜), 1 - x] i = x + (1 - x) := Fin.sum_univ_two _
      _ = 1 := add_sub_cancel _ _⟩
  left_inv f := Subtype.eq <| funext <| Fin.forall_fin_two.2 <| .intro rfl <|
      calc
        (1 : 𝕜) - f.1 0 = f.1 0 + f.1 1 - f.1 0 := by rw [← Fin.sum_univ_two f.1, f.2.2]
        _ = f.1 1 := add_sub_cancel_left _ _
  right_inv x := Subtype.eq rfl

end OrderedRing

end Simplex
