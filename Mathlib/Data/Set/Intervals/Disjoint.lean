/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov

! This file was ported from Lean 3 source module data.set.intervals.disjoint
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `data.set.intervals.basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `data.set.lattice`, including `disjoint`.
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
  disjoint_left.mpr fun x ha hb => (h.trans_lt hb).not_le ha
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
  disjoint_left.mpr fun x hab hbc => hab.2.not_le hbc.1
#align set.Ico_disjoint_Ico_same Set.Ico_disjoint_Ico_same

@[simp]
theorem Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a ≤ b := by
  rw [Set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]
#align set.Ici_disjoint_Iic Set.Ici_disjoint_Iic

@[simp]
theorem Iic_disjoint_Ici : Disjoint (Iic a) (Ici b) ↔ ¬b ≤ a :=
  Disjoint.comm.trans Ici_disjoint_Iic
#align set.Iic_disjoint_Ici Set.Iic_disjoint_Ici

@[simp]
theorem Union_Iic : (⋃ a : α, Iic a) = univ :=
  Union_eq_univ_iff.2 fun x => ⟨x, right_mem_Iic⟩
#align set.Union_Iic Set.Union_Iic

@[simp]
theorem Union_Ici : (⋃ a : α, Ici a) = univ :=
  Union_eq_univ_iff.2 fun x => ⟨x, left_mem_Ici⟩
#align set.Union_Ici Set.Union_Ici

@[simp]
theorem Union_Icc_right (a : α) : (⋃ b, Icc a b) = Ici a := by
  simp only [← Ici_inter_Iic, ← inter_Union, Union_Iic, inter_univ]
#align set.Union_Icc_right Set.Union_Icc_right

@[simp]
theorem Union_Ioc_right (a : α) : (⋃ b, Ioc a b) = Ioi a := by
  simp only [← Ioi_inter_Iic, ← inter_Union, Union_Iic, inter_univ]
#align set.Union_Ioc_right Set.Union_Ioc_right

@[simp]
theorem Union_Icc_left (b : α) : (⋃ a, Icc a b) = Iic b := by
  simp only [← Ici_inter_Iic, ← Union_inter, Union_Ici, univ_inter]
#align set.Union_Icc_left Set.Union_Icc_left

@[simp]
theorem Union_Ico_left (b : α) : (⋃ a, Ico a b) = Iio b := by
  simp only [← Ici_inter_Iio, ← Union_inter, Union_Ici, univ_inter]
#align set.Union_Ico_left Set.Union_Ico_left

@[simp]
theorem Union_Iio [NoMaxOrder α] : (⋃ a : α, Iio a) = univ :=
  Union_eq_univ_iff.2 exists_gt
#align set.Union_Iio Set.Union_Iio

@[simp]
theorem Union_Ioi [NoMinOrder α] : (⋃ a : α, Ioi a) = univ :=
  Union_eq_univ_iff.2 exists_lt
#align set.Union_Ioi Set.Union_Ioi

@[simp]
theorem Union_Ico_right [NoMaxOrder α] (a : α) : (⋃ b, Ico a b) = Ici a := by
  simp only [← Ici_inter_Iio, ← inter_Union, Union_Iio, inter_univ]
#align set.Union_Ico_right Set.Union_Ico_right

@[simp]
theorem Union_Ioo_right [NoMaxOrder α] (a : α) : (⋃ b, Ioo a b) = Ioi a := by
  simp only [← Ioi_inter_Iio, ← inter_Union, Union_Iio, inter_univ]
#align set.Union_Ioo_right Set.Union_Ioo_right

@[simp]
theorem Union_Ioc_left [NoMinOrder α] (b : α) : (⋃ a, Ioc a b) = Iic b := by
  simp only [← Ioi_inter_Iic, ← Union_inter, Union_Ioi, univ_inter]
#align set.Union_Ioc_left Set.Union_Ioc_left

@[simp]
theorem Union_Ioo_left [NoMinOrder α] (b : α) : (⋃ a, Ioo a b) = Iio b := by
  simp only [← Ioi_inter_Iio, ← Union_inter, Union_Ioi, univ_inter]
#align set.Union_Ioo_left Set.Union_Ioo_left

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
  simpa only [dual_Ico] using h
#align set.Ioc_disjoint_Ioc Set.Ioc_disjoint_Ioc

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ ∈ Ico y₁ y₂) : y₁ = x₂ := by
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_le h)) id
#align set.eq_of_Ico_disjoint Set.eq_of_Ico_disjoint

@[simp]
theorem Union_Ico_eq_Iio_self_iff {f : ι → α} {a : α} :
    (⋃ i, Ico (f i) a) = Iio a ↔ ∀ x < a, ∃ i, f i ≤ x := by
  simp [← Ici_inter_Iio, ← Union_inter, subset_def]
#align set.Union_Ico_eq_Iio_self_iff Set.Union_Ico_eq_Iio_self_iff

@[simp]
theorem Union_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} :
    (⋃ i, Ioc a (f i)) = Ioi a ↔ ∀ x, a < x → ∃ i, x ≤ f i := by
  simp [← Ioi_inter_Iic, ← inter_Union, subset_def]
#align set.Union_Ioc_eq_Ioi_self_iff Set.Union_Ioc_eq_Ioi_self_iff

@[simp]
theorem bUnion_Ico_eq_Iio_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    (⋃ (i) (hi : p i), Ico (f i hi) a) = Iio a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x := by
  simp [← Ici_inter_Iio, ← Union_inter, subset_def]
#align set.bUnion_Ico_eq_Iio_self_iff Set.bUnion_Ico_eq_Iio_self_iff

@[simp]
theorem bUnion_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    (⋃ (i) (hi : p i), Ioc a (f i hi)) = Ioi a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi := by
  simp [← Ioi_inter_Iic, ← inter_Union, subset_def]
#align set.bUnion_Ioc_eq_Ioi_self_iff Set.bUnion_Ioc_eq_Ioi_self_iff

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι → α}

theorem IsGLB.bUnion_Ioi_eq (h : IsGLB s a) : (⋃ x ∈ s, Ioi x) = Ioi a := by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, hay, hyx⟩
    exact mem_bUnion hys hyx
#align is_glb.bUnion_Ioi_eq IsGLB.bUnion_Ioi_eq

theorem IsGLB.Union_Ioi_eq (h : IsGLB (range f) a) : (⋃ x, Ioi (f x)) = Ioi a :=
  bUnion_range.symm.trans h.bUnion_Ioi_eq
#align is_glb.Union_Ioi_eq IsGLB.Union_Ioi_eq

theorem IsLUB.bUnion_Iio_eq (h : IsLUB s a) : (⋃ x ∈ s, Iio x) = Iio a :=
  h.dual.bUnion_Ioi_eq
#align is_lub.bUnion_Iio_eq IsLUB.bUnion_Iio_eq

theorem IsLUB.Union_Iio_eq (h : IsLUB (range f) a) : (⋃ x, Iio (f x)) = Iio a :=
  h.dual.Union_Ioi_eq
#align is_lub.Union_Iio_eq IsLUB.Union_Iio_eq

theorem IsGLB.bUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (a_not_mem : a ∉ s) :
    (⋃ x ∈ s, Ici x) = Ioi a := by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_not_mem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, hay, hyx⟩
    apply mem_Union₂.mpr
    refine' ⟨y, hys, hyx.le⟩
#align is_glb.bUnion_Ici_eq_Ioi IsGLB.bUnion_Ici_eq_Ioi

theorem IsGLB.bUnion_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a ∈ s) : (⋃ x ∈ s, Ici x) = Ici a := by
  refine' (Union₂_subset fun x hx => _).antisymm fun x hx => _
  · exact Ici_subset_Ici.mpr (mem_lower_bounds.mp a_glb.1 x hx)
  · apply mem_Union₂.mpr
    refine' ⟨a, a_mem, hx⟩
#align is_glb.bUnion_Ici_eq_Ici IsGLB.bUnion_Ici_eq_Ici

theorem IsLUB.bUnion_Iic_eq_Iio (a_lub : IsLUB s a) (a_not_mem : a ∉ s) :
    (⋃ x ∈ s, Iic x) = Iio a :=
  a_lub.dual.bUnion_Ici_eq_Ioi a_not_mem
#align is_lub.bUnion_Iic_eq_Iio IsLUB.bUnion_Iic_eq_Iio

theorem IsLUB.bUnion_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a ∈ s) : (⋃ x ∈ s, Iic x) = Iic a :=
  a_lub.dual.bUnion_Ici_eq_Ici a_mem
#align is_lub.bUnion_Iic_eq_Iic IsLUB.bUnion_Iic_eq_Iic

theorem Union_Ici_eq_Ioi_infi {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (no_least_elem : (⨅ i, f i) ∉ range f) : (⋃ i : ι, Ici (f i)) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.bUnion_Ici_eq_Ioi (@is_glb_infi _ _ _ f) no_least_elem, mem_range,
    Union_exists, Union_Union_eq']
#align Union_Ici_eq_Ioi_infi Union_Ici_eq_Ioi_infi

theorem Union_Iic_eq_Iio_supr {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (no_greatest_elem : (⨆ i, f i) ∉ range f) : (⋃ i : ι, Iic (f i)) = Iio (⨆ i, f i) :=
  @Union_Ici_eq_Ioi_infi ι (OrderDual R) _ f no_greatest_elem
#align Union_Iic_eq_Iio_supr Union_Iic_eq_Iio_supr

theorem Union_Ici_eq_Ici_infi {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (has_least_elem : (⨅ i, f i) ∈ range f) : (⋃ i : ι, Ici (f i)) = Ici (⨅ i, f i) := by
  simp only [← IsGLB.bUnion_Ici_eq_Ici (@is_glb_infi _ _ _ f) has_least_elem, mem_range,
    Union_exists, Union_Union_eq']
#align Union_Ici_eq_Ici_infi Union_Ici_eq_Ici_infi

theorem Union_Iic_eq_Iic_supr {R : Type _} [CompleteLinearOrder R] {f : ι → R}
    (has_greatest_elem : (⨆ i, f i) ∈ range f) : (⋃ i : ι, Iic (f i)) = Iic (⨆ i, f i) :=
  @Union_Ici_eq_Ici_infi ι (OrderDual R) _ f has_greatest_elem
#align Union_Iic_eq_Iic_supr Union_Iic_eq_Iic_supr

end UnionIxx

