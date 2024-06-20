/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.Basic

#align_import analysis.convex.strict from "leanprover-community/mathlib"@"84dc0bd6619acaea625086d6f53cb35cdd554219"

/-!
# Strictly convex sets

This file defines strictly convex sets.

A set is strictly convex if the open segment between any two distinct points lies in its interior.
-/


open Set

open Convex Pointwise

variable {𝕜 𝕝 E F β : Type*}

open Function Set

open Convex

section OrderedSemiring

variable [OrderedSemiring 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section SMul

variable (𝕜)
variable [SMul 𝕜 E] [SMul 𝕜 F] (s : Set E)

/-- A set is strictly convex if the open segment between any two distinct points lies is in its
interior. This basically means "convex and not flat on the boundary". -/
def StrictConvex : Prop :=
  s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ interior s
#align strict_convex StrictConvex

variable {𝕜 s}
variable {x y : E} {a b : 𝕜}

theorem strictConvex_iff_openSegment_subset :
    StrictConvex 𝕜 s ↔ s.Pairwise fun x y => openSegment 𝕜 x y ⊆ interior s :=
  forall₅_congr fun _ _ _ _ _ => (openSegment_subset_iff 𝕜).symm
#align strict_convex_iff_open_segment_subset strictConvex_iff_openSegment_subset

theorem StrictConvex.openSegment_subset (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s)
    (h : x ≠ y) : openSegment 𝕜 x y ⊆ interior s :=
  strictConvex_iff_openSegment_subset.1 hs hx hy h
#align strict_convex.open_segment_subset StrictConvex.openSegment_subset

theorem strictConvex_empty : StrictConvex 𝕜 (∅ : Set E) :=
  pairwise_empty _
#align strict_convex_empty strictConvex_empty

theorem strictConvex_univ : StrictConvex 𝕜 (univ : Set E) := by
  intro x _ y _ _ a b _ _ _
  rw [interior_univ]
  exact mem_univ _
#align strict_convex_univ strictConvex_univ

protected nonrec theorem StrictConvex.eq (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (h : a • x + b • y ∉ interior s) : x = y :=
  hs.eq hx hy fun H => h <| H ha hb hab
#align strict_convex.eq StrictConvex.eq

protected theorem StrictConvex.inter {t : Set E} (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s ∩ t) := by
  intro x hx y hy hxy a b ha hb hab
  rw [interior_inter]
  exact ⟨hs hx.1 hy.1 hxy ha hb hab, ht hx.2 hy.2 hxy ha hb hab⟩
#align strict_convex.inter StrictConvex.inter

theorem Directed.strictConvex_iUnion {ι : Sort*} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hs : ∀ ⦃i : ι⦄, StrictConvex 𝕜 (s i)) : StrictConvex 𝕜 (⋃ i, s i) := by
  rintro x hx y hy hxy a b ha hb hab
  rw [mem_iUnion] at hx hy
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact interior_mono (subset_iUnion s k) (hs (hik hx) (hjk hy) hxy ha hb hab)
#align directed.strict_convex_Union Directed.strictConvex_iUnion

theorem DirectedOn.strictConvex_sUnion {S : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) S)
    (hS : ∀ s ∈ S, StrictConvex 𝕜 s) : StrictConvex 𝕜 (⋃₀ S) := by
  rw [sUnion_eq_iUnion]
  exact (directedOn_iff_directed.1 hdir).strictConvex_iUnion fun s => hS _ s.2
#align directed_on.strict_convex_sUnion DirectedOn.strictConvex_sUnion

end SMul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

protected theorem StrictConvex.convex (hs : StrictConvex 𝕜 s) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.2 fun _ hx _ hy hxy _ _ ha hb hab =>
    interior_subset <| hs hx hy hxy ha hb hab
#align strict_convex.convex StrictConvex.convex

/-- An open convex set is strictly convex. -/
protected theorem Convex.strictConvex_of_isOpen (h : IsOpen s) (hs : Convex 𝕜 s) :
    StrictConvex 𝕜 s :=
  fun _ hx _ hy _ _ _ ha hb hab => h.interior_eq.symm ▸ hs hx hy ha.le hb.le hab
#align convex.strict_convex_of_open Convex.strictConvex_of_isOpen

theorem IsOpen.strictConvex_iff (h : IsOpen s) : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, Convex.strictConvex_of_isOpen h⟩
#align is_open.strict_convex_iff IsOpen.strictConvex_iff

theorem strictConvex_singleton (c : E) : StrictConvex 𝕜 ({c} : Set E) :=
  pairwise_singleton _ _
#align strict_convex_singleton strictConvex_singleton

theorem Set.Subsingleton.strictConvex (hs : s.Subsingleton) : StrictConvex 𝕜 s :=
  hs.pairwise _
#align set.subsingleton.strict_convex Set.Subsingleton.strictConvex

theorem StrictConvex.linear_image [Semiring 𝕝] [Module 𝕝 E] [Module 𝕝 F]
    [LinearMap.CompatibleSMul E F 𝕜 𝕝] (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕝] F) (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  refine hf.image_interior_subset _ ⟨a • x + b • y, hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, ?_⟩
  rw [map_add, f.map_smul_of_tower a, f.map_smul_of_tower b]
#align strict_convex.linear_image StrictConvex.linear_image

theorem StrictConvex.is_linear_image (hs : StrictConvex 𝕜 s) {f : E → F} (h : IsLinearMap 𝕜 f)
    (hf : IsOpenMap f) : StrictConvex 𝕜 (f '' s) :=
  hs.linear_image (h.mk' f) hf
#align strict_convex.is_linear_image StrictConvex.is_linear_image

theorem StrictConvex.linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) (f : E →ₗ[𝕜] F)
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (s.preimage f) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy (hfinj.ne hxy) ha hb hab
#align strict_convex.linear_preimage StrictConvex.linear_preimage

theorem StrictConvex.is_linear_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E → F}
    (h : IsLinearMap 𝕜 f) (hf : Continuous f) (hfinj : Injective f) :
    StrictConvex 𝕜 (s.preimage f) :=
  hs.linear_preimage (h.mk' f) hf hfinj
#align strict_convex.is_linear_preimage StrictConvex.is_linear_preimage

section LinearOrderedCancelAddCommMonoid

variable [TopologicalSpace β] [LinearOrderedCancelAddCommMonoid β] [OrderTopology β] [Module 𝕜 β]
  [OrderedSMul 𝕜 β]

protected theorem Set.OrdConnected.strictConvex {s : Set β} (hs : OrdConnected s) :
    StrictConvex 𝕜 s := by
  refine strictConvex_iff_openSegment_subset.2 fun x hx y hy hxy => ?_
  cases' hxy.lt_or_lt with hlt hlt <;> [skip; rw [openSegment_symm]] <;>
    exact
      (openSegment_subset_Ioo hlt).trans
        (isOpen_Ioo.subset_interior_iff.2 <| Ioo_subset_Icc_self.trans <| hs.out ‹_› ‹_›)
#align set.ord_connected.strict_convex Set.OrdConnected.strictConvex

theorem strictConvex_Iic (r : β) : StrictConvex 𝕜 (Iic r) :=
  ordConnected_Iic.strictConvex
#align strict_convex_Iic strictConvex_Iic

theorem strictConvex_Ici (r : β) : StrictConvex 𝕜 (Ici r) :=
  ordConnected_Ici.strictConvex
#align strict_convex_Ici strictConvex_Ici

theorem strictConvex_Iio (r : β) : StrictConvex 𝕜 (Iio r) :=
  ordConnected_Iio.strictConvex
#align strict_convex_Iio strictConvex_Iio

theorem strictConvex_Ioi (r : β) : StrictConvex 𝕜 (Ioi r) :=
  ordConnected_Ioi.strictConvex
#align strict_convex_Ioi strictConvex_Ioi

theorem strictConvex_Icc (r s : β) : StrictConvex 𝕜 (Icc r s) :=
  ordConnected_Icc.strictConvex
#align strict_convex_Icc strictConvex_Icc

theorem strictConvex_Ioo (r s : β) : StrictConvex 𝕜 (Ioo r s) :=
  ordConnected_Ioo.strictConvex
#align strict_convex_Ioo strictConvex_Ioo

theorem strictConvex_Ico (r s : β) : StrictConvex 𝕜 (Ico r s) :=
  ordConnected_Ico.strictConvex
#align strict_convex_Ico strictConvex_Ico

theorem strictConvex_Ioc (r s : β) : StrictConvex 𝕜 (Ioc r s) :=
  ordConnected_Ioc.strictConvex
#align strict_convex_Ioc strictConvex_Ioc

theorem strictConvex_uIcc (r s : β) : StrictConvex 𝕜 (uIcc r s) :=
  strictConvex_Icc _ _
#align strict_convex_uIcc strictConvex_uIcc

theorem strictConvex_uIoc (r s : β) : StrictConvex 𝕜 (uIoc r s) :=
  strictConvex_Ioc _ _
#align strict_convex_uIoc strictConvex_uIoc

end LinearOrderedCancelAddCommMonoid

end Module

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [ContinuousAdd E] [Module 𝕜 E] {s : Set E}

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.preimage_add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage (continuous_add_left _) ?_
  have h := hs hx hy ((add_right_injective _).ne hxy) ha hb hab
  rwa [smul_add, smul_add, add_add_add_comm, ← _root_.add_smul, hab, one_smul] at h
#align strict_convex.preimage_add_right StrictConvex.preimage_add_right

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.preimage_add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [add_comm] using hs.preimage_add_right z
#align strict_convex.preimage_add_left StrictConvex.preimage_add_left

end AddCancelCommMonoid

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

section continuous_add

variable [ContinuousAdd E] {s t : Set E}

theorem StrictConvex.add (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) :
    StrictConvex 𝕜 (s + t) := by
  rintro _ ⟨v, hv, w, hw, rfl⟩ _ ⟨x, hx, y, hy, rfl⟩ h a b ha hb hab
  rw [smul_add, smul_add, add_add_add_comm]
  obtain rfl | hvx := eq_or_ne v x
  · refine interior_mono (add_subset_add (singleton_subset_iff.2 hv) Subset.rfl) ?_
    rw [Convex.combo_self hab, singleton_add]
    exact
      (isOpenMap_add_left _).image_interior_subset _
        (mem_image_of_mem _ <| ht hw hy (ne_of_apply_ne _ h) ha hb hab)
  exact
    subset_interior_add_left
      (add_mem_add (hs hv hx hvx ha hb hab) <| ht.convex hw hy ha.le hb.le hab)
#align strict_convex.add StrictConvex.add

theorem StrictConvex.add_left (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => z + x) '' s) := by
  simpa only [singleton_add] using (strictConvex_singleton z).add hs
#align strict_convex.add_left StrictConvex.add_left

theorem StrictConvex.add_right (hs : StrictConvex 𝕜 s) (z : E) :
    StrictConvex 𝕜 ((fun x => x + z) '' s) := by simpa only [add_comm] using hs.add_left z
#align strict_convex.add_right StrictConvex.add_right

/-- The translation of a strictly convex set is also strictly convex. -/
theorem StrictConvex.vadd (hs : StrictConvex 𝕜 s) (x : E) : StrictConvex 𝕜 (x +ᵥ s) :=
  hs.add_left x
#align strict_convex.vadd StrictConvex.vadd

end continuous_add

section ContinuousSMul

variable [LinearOrderedField 𝕝] [Module 𝕝 E] [ContinuousConstSMul 𝕝 E]
  [LinearMap.CompatibleSMul E E 𝕜 𝕝] {s : Set E} {x : E}

theorem StrictConvex.smul (hs : StrictConvex 𝕜 s) (c : 𝕝) : StrictConvex 𝕜 (c • s) := by
  obtain rfl | hc := eq_or_ne c 0
  · exact (subsingleton_zero_smul_set _).strictConvex
  · exact hs.linear_image (LinearMap.lsmul _ _ c) (isOpenMap_smul₀ hc)
#align strict_convex.smul StrictConvex.smul

theorem StrictConvex.affinity [ContinuousAdd E] (hs : StrictConvex 𝕜 s) (z : E) (c : 𝕝) :
    StrictConvex 𝕜 (z +ᵥ c • s) :=
  (hs.smul c).vadd z
#align strict_convex.affinity StrictConvex.affinity

end ContinuousSMul

end AddCommGroup

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [TopologicalSpace E]

section AddCommGroup

variable [AddCommGroup E] [Module 𝕜 E] [NoZeroSMulDivisors 𝕜 E] [ContinuousConstSMul 𝕜 E]
  {s : Set E}

theorem StrictConvex.preimage_smul (hs : StrictConvex 𝕜 s) (c : 𝕜) :
    StrictConvex 𝕜 ((fun z => c • z) ⁻¹' s) := by
  classical
    obtain rfl | hc := eq_or_ne c 0
    · simp_rw [zero_smul, preimage_const]
      split_ifs
      · exact strictConvex_univ
      · exact strictConvex_empty
    refine hs.linear_preimage (LinearMap.lsmul _ _ c) ?_ (smul_right_injective E hc)
    unfold LinearMap.lsmul LinearMap.mk₂ LinearMap.mk₂' LinearMap.mk₂'ₛₗ
    exact continuous_const_smul _
#align strict_convex.preimage_smul StrictConvex.preimage_smul

end AddCommGroup

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜] [TopologicalSpace E] [TopologicalSpace F]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E} {x y : E}

theorem StrictConvex.eq_of_openSegment_subset_frontier [Nontrivial 𝕜] [DenselyOrdered 𝕜]
    (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (h : openSegment 𝕜 x y ⊆ frontier s) :
    x = y := by
  obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
  classical
    by_contra hxy
    exact
      (h ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, rfl⟩).2
        (hs hx hy hxy ha₀ (sub_pos_of_lt ha₁) <| add_sub_cancel _ _)
#align strict_convex.eq_of_open_segment_subset_frontier StrictConvex.eq_of_openSegment_subset_frontier

theorem StrictConvex.add_smul_mem (hs : StrictConvex 𝕜 s) (hx : x ∈ s) (hxy : x + y ∈ s)
    (hy : y ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • y ∈ interior s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assoc, ← _root_.add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hx hxy (fun h => hy <| add_left_cancel (a := x) (by rw [← h, add_zero]))
    (sub_pos_of_lt ht₁) ht₀ (sub_add_cancel 1 t)
#align strict_convex.add_smul_mem StrictConvex.add_smul_mem

theorem StrictConvex.smul_mem_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s)
    (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : t • x ∈ interior s := by
  simpa using hs.add_smul_mem zero_mem (by simpa using hx) hx₀ ht₀ ht₁
#align strict_convex.smul_mem_of_zero_mem StrictConvex.smul_mem_of_zero_mem

theorem StrictConvex.add_smul_sub_mem (h : StrictConvex 𝕜 s) (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {t : 𝕜} (ht₀ : 0 < t) (ht₁ : t < 1) : x + t • (y - x) ∈ interior s := by
  apply h.openSegment_subset hx hy hxy
  rw [openSegment_eq_image']
  exact mem_image_of_mem _ ⟨ht₀, ht₁⟩
#align strict_convex.add_smul_sub_mem StrictConvex.add_smul_sub_mem

/-- The preimage of a strictly convex set under an affine map is strictly convex. -/
theorem StrictConvex.affine_preimage {s : Set F} (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F}
    (hf : Continuous f) (hfinj : Injective f) : StrictConvex 𝕜 (f ⁻¹' s) := by
  intro x hx y hy hxy a b ha hb hab
  refine preimage_interior_subset_interior_preimage hf ?_
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs hx hy (hfinj.ne hxy) ha hb hab
#align strict_convex.affine_preimage StrictConvex.affine_preimage

/-- The image of a strictly convex set under an affine map is strictly convex. -/
theorem StrictConvex.affine_image (hs : StrictConvex 𝕜 s) {f : E →ᵃ[𝕜] F} (hf : IsOpenMap f) :
    StrictConvex 𝕜 (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy a b ha hb hab
  exact
    hf.image_interior_subset _
      ⟨a • x + b • y, ⟨hs hx hy (ne_of_apply_ne _ hxy) ha hb hab, Convex.combo_affine_apply hab⟩⟩
#align strict_convex.affine_image StrictConvex.affine_image

variable [TopologicalAddGroup E]

theorem StrictConvex.neg (hs : StrictConvex 𝕜 s) : StrictConvex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.isLinearMap_neg continuous_id.neg neg_injective
#align strict_convex.neg StrictConvex.neg

theorem StrictConvex.sub (hs : StrictConvex 𝕜 s) (ht : StrictConvex 𝕜 t) : StrictConvex 𝕜 (s - t) :=
  (sub_eq_add_neg s t).symm ▸ hs.add ht.neg
#align strict_convex.sub StrictConvex.sub

end AddCommGroup

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace E]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E} {x : E}

/-- Alternative definition of set strict convexity, using division. -/
theorem strictConvex_iff_div :
    StrictConvex 𝕜 s ↔
      s.Pairwise fun x y =>
        ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → (a / (a + b)) • x + (b / (a + b)) • y ∈ interior s :=
  ⟨fun h x hx y hy hxy a b ha hb => by
    apply h hx hy hxy (div_pos ha <| add_pos ha hb) (div_pos hb <| add_pos ha hb)
    rw [← add_div]
    exact div_self (add_pos ha hb).ne', fun h x hx y hy hxy a b ha hb hab => by
    convert h hx hy hxy ha hb <;> rw [hab, div_one]⟩
#align strict_convex_iff_div strictConvex_iff_div

theorem StrictConvex.mem_smul_of_zero_mem (hs : StrictConvex 𝕜 s) (zero_mem : (0 : E) ∈ s)
    (hx : x ∈ s) (hx₀ : x ≠ 0) {t : 𝕜} (ht : 1 < t) : x ∈ t • interior s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans ht).ne']
  exact hs.smul_mem_of_zero_mem zero_mem hx hx₀ (inv_pos.2 <| zero_lt_one.trans ht) (inv_lt_one ht)
#align strict_convex.mem_smul_of_zero_mem StrictConvex.mem_smul_of_zero_mem

end AddCommGroup

end LinearOrderedField

/-!
#### Convex sets in an ordered space

Relates `Convex` and `Set.OrdConnected`.
-/


section

variable [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {s : Set 𝕜}

/-- A set in a linear ordered field is strictly convex if and only if it is convex. -/
@[simp]
theorem strictConvex_iff_convex : StrictConvex 𝕜 s ↔ Convex 𝕜 s :=
  ⟨StrictConvex.convex, fun hs => hs.ordConnected.strictConvex⟩
#align strict_convex_iff_convex strictConvex_iff_convex

theorem strictConvex_iff_ordConnected : StrictConvex 𝕜 s ↔ s.OrdConnected :=
  strictConvex_iff_convex.trans convex_iff_ordConnected
#align strict_convex_iff_ord_connected strictConvex_iff_ordConnected

alias ⟨StrictConvex.ordConnected, _⟩ := strictConvex_iff_ordConnected
#align strict_convex.ord_connected StrictConvex.ordConnected

end
