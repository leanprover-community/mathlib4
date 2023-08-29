/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import Mathlib.Data.Set.Lattice

#align_import data.set.intervals.disjoint from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `Data.Set.Intervals.Basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `Data.Set.Lattice`, including `Disjoint`.
-/


universe u v w

variable {ι : Sort u} {α : Type v} {β : Type w}

open Set

open OrderDual (toDual)

namespace Set

section Preorder

variable [Preorder α] {a b c : α}

@[simp]
theorem Iic_disjoint_Ioi (h : a ≤ b) : Disjoint (Iic a) (Ioi b) :=
  disjoint_left.mpr fun _ ha hb => (h.trans_lt hb).not_le ha
#align set.Iic_disjoint_Ioi Set.Iic_disjoint_Ioi

@[simp]
theorem Iic_disjoint_Ioc (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  (Iic_disjoint_Ioi h).mono le_rfl fun _ => And.left
#align set.Iic_disjoint_Ioc Set.Iic_disjoint_Ioc

@[simp]
theorem Ioc_disjoint_Ioc_same {a b c : α} : Disjoint (Ioc a b) (Ioc b c) :=
  (Iic_disjoint_Ioc (le_refl b)).mono (fun _ => And.right) le_rfl
#align set.Ioc_disjoint_Ioc_same Set.Ioc_disjoint_Ioc_same

@[simp]
theorem Ico_disjoint_Ico_same {a b c : α} : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.mpr fun _ hab hbc => hab.2.not_le hbc.1
#align set.Ico_disjoint_Ico_same Set.Ico_disjoint_Ico_same

@[simp]
theorem Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a ≤ b := by
  rw [Set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]
  -- 🎉 no goals
#align set.Ici_disjoint_Iic Set.Ici_disjoint_Iic

@[simp]
theorem Iic_disjoint_Ici : Disjoint (Iic a) (Ici b) ↔ ¬b ≤ a :=
  disjoint_comm.trans Ici_disjoint_Iic
#align set.Iic_disjoint_Ici Set.Iic_disjoint_Ici

@[simp]
theorem iUnion_Iic : ⋃ a : α, Iic a = univ :=
  iUnion_eq_univ_iff.2 fun x => ⟨x, right_mem_Iic⟩
#align set.Union_Iic Set.iUnion_Iic

@[simp]
theorem iUnion_Ici : ⋃ a : α, Ici a = univ :=
  iUnion_eq_univ_iff.2 fun x => ⟨x, left_mem_Ici⟩
#align set.Union_Ici Set.iUnion_Ici

@[simp]
theorem iUnion_Icc_right (a : α) : ⋃ b, Icc a b = Ici a := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]
  -- 🎉 no goals
#align set.Union_Icc_right Set.iUnion_Icc_right

@[simp]
theorem iUnion_Ioc_right (a : α) : ⋃ b, Ioc a b = Ioi a := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]
  -- 🎉 no goals
#align set.Union_Ioc_right Set.iUnion_Ioc_right

@[simp]
theorem iUnion_Icc_left (b : α) : ⋃ a, Icc a b = Iic b := by
  simp only [← Ici_inter_Iic, ← iUnion_inter, iUnion_Ici, univ_inter]
  -- 🎉 no goals
#align set.Union_Icc_left Set.iUnion_Icc_left

@[simp]
theorem iUnion_Ico_left (b : α) : ⋃ a, Ico a b = Iio b := by
  simp only [← Ici_inter_Iio, ← iUnion_inter, iUnion_Ici, univ_inter]
  -- 🎉 no goals
#align set.Union_Ico_left Set.iUnion_Ico_left

@[simp]
theorem iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ :=
  iUnion_eq_univ_iff.2 exists_gt
#align set.Union_Iio Set.iUnion_Iio

@[simp]
theorem iUnion_Ioi [NoMinOrder α] : ⋃ a : α, Ioi a = univ :=
  iUnion_eq_univ_iff.2 exists_lt
#align set.Union_Ioi Set.iUnion_Ioi

@[simp]
theorem iUnion_Ico_right [NoMaxOrder α] (a : α) : ⋃ b, Ico a b = Ici a := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]
  -- 🎉 no goals
#align set.Union_Ico_right Set.iUnion_Ico_right

@[simp]
theorem iUnion_Ioo_right [NoMaxOrder α] (a : α) : ⋃ b, Ioo a b = Ioi a := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]
  -- 🎉 no goals
#align set.Union_Ioo_right Set.iUnion_Ioo_right

@[simp]
theorem iUnion_Ioc_left [NoMinOrder α] (b : α) : ⋃ a, Ioc a b = Iic b := by
  simp only [← Ioi_inter_Iic, ← iUnion_inter, iUnion_Ioi, univ_inter]
  -- 🎉 no goals
#align set.Union_Ioc_left Set.iUnion_Ioc_left

@[simp]
theorem iUnion_Ioo_left [NoMinOrder α] (b : α) : ⋃ a, Ioo a b = Iio b := by
  simp only [← Ioi_inter_Iio, ← iUnion_inter, iUnion_Ioi, univ_inter]
  -- 🎉 no goals
#align set.Union_Ioo_left Set.iUnion_Ioo_left

end Preorder

section LinearOrder

variable [LinearOrder α] {a₁ a₂ b₁ b₂ : α}

@[simp]
theorem Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, inf_eq_min, sup_eq_max,
    not_lt]
#align set.Ico_disjoint_Ico Set.Ico_disjoint_Ico

@[simp]
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  have h : _ ↔ min (toDual a₁) (toDual b₁) ≤ max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  -- ⊢ Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁
  simpa only [dual_Ico] using h
  -- 🎉 no goals
#align set.Ioc_disjoint_Ioc Set.Ioc_disjoint_Ioc

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ ∈ Ico y₁ y₂) : y₁ = x₂ := by
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h
  -- ⊢ y₁ = x₂
  apply le_antisymm h2.1
  -- ⊢ x₂ ≤ y₁
  exact h.elim (fun h => absurd hx (not_lt_of_le h)) id
  -- 🎉 no goals
#align set.eq_of_Ico_disjoint Set.eq_of_Ico_disjoint

@[simp]
theorem iUnion_Ico_eq_Iio_self_iff {f : ι → α} {a : α} :
    ⋃ i, Ico (f i) a = Iio a ↔ ∀ x < a, ∃ i, f i ≤ x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]
  -- 🎉 no goals
#align set.Union_Ico_eq_Iio_self_iff Set.iUnion_Ico_eq_Iio_self_iff

@[simp]
theorem iUnion_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} :
    ⋃ i, Ioc a (f i) = Ioi a ↔ ∀ x, a < x → ∃ i, x ≤ f i := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]
  -- 🎉 no goals
#align set.Union_Ioc_eq_Ioi_self_iff Set.iUnion_Ioc_eq_Ioi_self_iff

@[simp]
theorem biUnion_Ico_eq_Iio_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    ⋃ (i) (hi : p i), Ico (f i hi) a = Iio a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]
  -- 🎉 no goals
#align set.bUnion_Ico_eq_Iio_self_iff Set.biUnion_Ico_eq_Iio_self_iff

@[simp]
theorem biUnion_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    ⋃ (i) (hi : p i), Ioc a (f i hi) = Ioi a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]
  -- 🎉 no goals
#align set.bUnion_Ioc_eq_Ioi_self_iff Set.biUnion_Ioc_eq_Ioi_self_iff

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι → α}

theorem IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x ∈ s, Ioi x = Ioi a := by
  refine' (iUnion₂_subset fun x hx => _).antisymm fun x hx => _
  -- ⊢ Ioi x ⊆ Ioi a
  · exact Ioi_subset_Ioi (h.1 hx)
    -- 🎉 no goals
  · rcases h.exists_between hx with ⟨y, hys, _, hyx⟩
    -- ⊢ x ∈ ⋃ (i : α) (_ : i ∈ s), Ioi i
    exact mem_biUnion hys hyx
    -- 🎉 no goals
#align is_glb.bUnion_Ioi_eq IsGLB.biUnion_Ioi_eq

theorem IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, Ioi (f x) = Ioi a :=
  biUnion_range.symm.trans h.biUnion_Ioi_eq
#align is_glb.Union_Ioi_eq IsGLB.iUnion_Ioi_eq

theorem IsLUB.biUnion_Iio_eq (h : IsLUB s a) : ⋃ x ∈ s, Iio x = Iio a :=
  h.dual.biUnion_Ioi_eq
#align is_lub.bUnion_Iio_eq IsLUB.biUnion_Iio_eq

theorem IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, Iio (f x) = Iio a :=
  h.dual.iUnion_Ioi_eq
#align is_lub.Union_Iio_eq IsLUB.iUnion_Iio_eq

theorem IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (a_not_mem : a ∉ s) :
    ⋃ x ∈ s, Ici x = Ioi a := by
  refine' (iUnion₂_subset fun x hx => _).antisymm fun x hx => _
  -- ⊢ Ici x ⊆ Ioi a
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_not_mem) hx)
    -- 🎉 no goals
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    -- ⊢ x ∈ ⋃ (i : α) (_ : i ∈ s), Ici i
    apply mem_iUnion₂.mpr
    -- ⊢ ∃ i j, x ∈ Ici i
    refine' ⟨y, hys, hyx.le⟩
    -- 🎉 no goals
#align is_glb.bUnion_Ici_eq_Ioi IsGLB.biUnion_Ici_eq_Ioi

theorem IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a ∈ s) :
    ⋃ x ∈ s, Ici x = Ici a := by
  refine' (iUnion₂_subset fun x hx => _).antisymm fun x hx => _
  -- ⊢ Ici x ⊆ Ici a
  · exact Ici_subset_Ici.mpr (mem_lowerBounds.mp a_glb.1 x hx)
    -- 🎉 no goals
  · apply mem_iUnion₂.mpr
    -- ⊢ ∃ i j, x ∈ Ici i
    refine' ⟨a, a_mem, hx⟩
    -- 🎉 no goals
#align is_glb.bUnion_Ici_eq_Ici IsGLB.biUnion_Ici_eq_Ici

theorem IsLUB.biUnion_Iic_eq_Iio (a_lub : IsLUB s a) (a_not_mem : a ∉ s) :
    ⋃ x ∈ s, Iic x = Iio a :=
  a_lub.dual.biUnion_Ici_eq_Ioi a_not_mem
#align is_lub.bUnion_Iic_eq_Iio IsLUB.biUnion_Iic_eq_Iio

theorem IsLUB.biUnion_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a ∈ s) : ⋃ x ∈ s, Iic x = Iic a :=
  a_lub.dual.biUnion_Ici_eq_Ici a_mem
#align is_lub.bUnion_Iic_eq_Iic IsLUB.biUnion_Iic_eq_Iic

theorem iUnion_Ici_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (no_least_elem : ⨅ i, f i ∉ range f) : ⋃ i : ι, Ici (f i) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ioi (@isGLB_iInf _ _ _ f) no_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']
#align Union_Ici_eq_Ioi_infi iUnion_Ici_eq_Ioi_iInf

theorem iUnion_Iic_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (no_greatest_elem : (⨆ i, f i) ∉ range f) : ⋃ i : ι, Iic (f i) = Iio (⨆ i, f i) :=
  @iUnion_Ici_eq_Ioi_iInf ι (OrderDual R) _ f no_greatest_elem
#align Union_Iic_eq_Iio_supr iUnion_Iic_eq_Iio_iSup

theorem iUnion_Ici_eq_Ici_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (has_least_elem : (⨅ i, f i) ∈ range f) : ⋃ i : ι, Ici (f i) = Ici (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ici (@isGLB_iInf _ _ _ f) has_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']
#align Union_Ici_eq_Ici_infi iUnion_Ici_eq_Ici_iInf

theorem iUnion_Iic_eq_Iic_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (has_greatest_elem : (⨆ i, f i) ∈ range f) : ⋃ i : ι, Iic (f i) = Iic (⨆ i, f i) :=
  @iUnion_Ici_eq_Ici_iInf ι (OrderDual R) _ f has_greatest_elem
#align Union_Iic_eq_Iic_supr iUnion_Iic_eq_Iic_iSup

end UnionIxx
