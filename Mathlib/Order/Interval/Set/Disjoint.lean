/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into `Order.Interval.Set.Basic`
because this would create an `import` cycle. Namely, lemmas in this file can use definitions
from `Data.Set.Lattice`, including `Disjoint`.

We consider various intersections and unions of half infinite intervals.
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
  disjoint_left.mpr fun _ ha hb => (h.trans_lt hb).not_ge ha

@[simp]
theorem Iio_disjoint_Ici (h : a ≤ b) : Disjoint (Iio a) (Ici b) :=
  disjoint_left.mpr fun _ ha hb => (h.trans_lt' ha).not_ge hb

@[simp]
theorem Iic_disjoint_Ioc (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  (Iic_disjoint_Ioi h).mono le_rfl Ioc_subset_Ioi_self

@[simp]
theorem Ioc_disjoint_Ioc_of_le {d : α} (h : b ≤ c) : Disjoint (Ioc a b) (Ioc c d) :=
  (Iic_disjoint_Ioc h).mono Ioc_subset_Iic_self le_rfl

@[simp]
theorem Ico_disjoint_Ico_same : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.mpr fun _ hab hbc => hab.2.not_ge hbc.1

@[simp]
theorem Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a ≤ b := by
  rw [Set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]

@[simp]
theorem Iic_disjoint_Ici : Disjoint (Iic a) (Ici b) ↔ ¬b ≤ a :=
  disjoint_comm.trans Ici_disjoint_Iic

@[simp]
theorem Ioc_disjoint_Ioi (h : b ≤ c) : Disjoint (Ioc a b) (Ioi c) :=
  disjoint_left.mpr (fun _ hx hy ↦ (hx.2.trans h).not_gt hy)

theorem Ioc_disjoint_Ioi_same : Disjoint (Ioc a b) (Ioi b) :=
  Ioc_disjoint_Ioi le_rfl

theorem Ioi_disjoint_Iio_of_not_lt (h : ¬a < b) : Disjoint (Ioi a) (Iio b) :=
  disjoint_left.mpr fun _ hx hy ↦ h (hx.trans hy)

theorem Ioi_disjoint_Iio_of_le (h : a ≤ b) : Disjoint (Ioi b) (Iio a) :=
  Ioi_disjoint_Iio_of_not_lt (not_lt_of_ge h)

@[simp]
theorem Ioi_disjoint_Iio_same : Disjoint (Ioi a) (Iio a) :=
  Ioi_disjoint_Iio_of_le le_rfl

@[simp]
theorem Ioi_disjoint_Iio_iff [DenselyOrdered α] : Disjoint (Ioi a) (Iio b) ↔ ¬a < b :=
  ⟨fun h hab ↦ (exists_between hab).elim
    fun _ hc ↦ h.notMem_of_mem_left hc.left hc.right,
    Ioi_disjoint_Iio_of_not_lt⟩

theorem Iio_disjoint_Ioi_of_not_lt (h : ¬a < b) : Disjoint (Iio b) (Ioi a) :=
  disjoint_comm.mp (Ioi_disjoint_Iio_of_not_lt h)

theorem Iio_disjoint_Ioi_of_le (h : a ≤ b) : Disjoint (Iio a) (Ioi b) :=
  disjoint_comm.mp (Ioi_disjoint_Iio_of_le h)

@[simp]
theorem Iio_disjoint_Ioi_same : Disjoint (Iio a) (Ioi a) :=
  Iio_disjoint_Ioi_of_le le_rfl

@[simp]
theorem Iio_disjoint_Ioi_iff [DenselyOrdered α] : Disjoint (Iio a) (Ioi b) ↔ ¬b < a :=
  disjoint_comm.trans Ioi_disjoint_Iio_iff

@[simp]
theorem iUnion_Iic : ⋃ a : α, Iic a = univ :=
  iUnion_eq_univ_iff.2 fun x => ⟨x, right_mem_Iic⟩

@[simp]
theorem iUnion_Ici : ⋃ a : α, Ici a = univ :=
  iUnion_eq_univ_iff.2 fun x => ⟨x, left_mem_Ici⟩

@[simp]
theorem iUnion_Icc_right (a : α) : ⋃ b, Icc a b = Ici a := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[simp]
theorem iUnion_Ioc_right (a : α) : ⋃ b, Ioc a b = Ioi a := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[simp]
theorem iUnion_Icc_left (b : α) : ⋃ a, Icc a b = Iic b := by
  simp only [← Ici_inter_Iic, ← iUnion_inter, iUnion_Ici, univ_inter]

@[simp]
theorem iUnion_Ico_left (b : α) : ⋃ a, Ico a b = Iio b := by
  simp only [← Ici_inter_Iio, ← iUnion_inter, iUnion_Ici, univ_inter]

@[simp]
theorem iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ :=
  iUnion_eq_univ_iff.2 exists_gt

@[simp]
theorem iUnion_Ioi [NoMinOrder α] : ⋃ a : α, Ioi a = univ :=
  iUnion_eq_univ_iff.2 exists_lt

@[simp]
theorem iUnion_Ico_right [NoMaxOrder α] (a : α) : ⋃ b, Ico a b = Ici a := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

@[simp]
theorem iUnion_Ioo_right [NoMaxOrder α] (a : α) : ⋃ b, Ioo a b = Ioi a := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

@[simp]
theorem iUnion_Ioc_left [NoMinOrder α] (b : α) : ⋃ a, Ioc a b = Iic b := by
  simp only [← Ioi_inter_Iic, ← iUnion_inter, iUnion_Ioi, univ_inter]

@[simp]
theorem iUnion_Ioo_left [NoMinOrder α] (b : α) : ⋃ a, Ioo a b = Iio b := by
  simp only [← Ioi_inter_Iio, ← iUnion_inter, iUnion_Ioi, univ_inter]

end Preorder

section LinearOrder

variable [LinearOrder α] {a₁ a₂ b₁ b₂ : α}

@[simp]
theorem Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, not_lt]

@[simp]
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  have h : _ ↔ min (toDual a₁) (toDual b₁) ≤ max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [Ico_toDual] using h

@[simp]
theorem Ioo_disjoint_Ioo [DenselyOrdered α] :
    Disjoint (Set.Ioo a₁ a₂) (Set.Ioo b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ ∈ Ico y₁ y₂) : y₁ = x₂ := by
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_ge h)) id

@[simp]
theorem iUnion_Ico_eq_Iio_self_iff {f : ι → α} {a : α} :
    ⋃ i, Ico (f i) a = Iio a ↔ ∀ x < a, ∃ i, f i ≤ x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]
theorem iUnion_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} :
    ⋃ i, Ioc a (f i) = Ioi a ↔ ∀ x, a < x → ∃ i, x ≤ f i := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

@[simp]
theorem biUnion_Ico_eq_Iio_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    ⋃ (i) (hi : p i), Ico (f i hi) a = Iio a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]
theorem biUnion_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    ⋃ (i) (hi : p i), Ioc a (f i hi) = Ioi a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι → α}

theorem IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x ∈ s, Ioi x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, _, hyx⟩
    exact mem_biUnion hys hyx

theorem IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, Ioi (f x) = Ioi a :=
  biUnion_range.symm.trans h.biUnion_Ioi_eq

theorem IsLUB.biUnion_Iio_eq (h : IsLUB s a) : ⋃ x ∈ s, Iio x = Iio a :=
  h.dual.biUnion_Ioi_eq

theorem IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, Iio (f x) = Iio a :=
  h.dual.iUnion_Ioi_eq

theorem IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (a_notMem : a ∉ s) :
    ⋃ x ∈ s, Ici x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_notMem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx.le⟩

theorem IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a ∈ s) :
    ⋃ x ∈ s, Ici x = Ici a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ici.mpr (mem_lowerBounds.mp a_glb.1 x hx)
  · exact mem_iUnion₂.mpr ⟨a, a_mem, hx⟩

theorem IsLUB.biUnion_Iic_eq_Iio (a_lub : IsLUB s a) (a_notMem : a ∉ s) :
    ⋃ x ∈ s, Iic x = Iio a :=
  a_lub.dual.biUnion_Ici_eq_Ioi a_notMem

theorem IsLUB.biUnion_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a ∈ s) : ⋃ x ∈ s, Iic x = Iic a :=
  a_lub.dual.biUnion_Ici_eq_Ici a_mem

theorem iUnion_Ici_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (no_least_elem : ⨅ i, f i ∉ range f) : ⋃ i : ι, Ici (f i) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ioi (@isGLB_iInf _ _ _ f) no_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

theorem iUnion_Iic_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (no_greatest_elem : (⨆ i, f i) ∉ range f) : ⋃ i : ι, Iic (f i) = Iio (⨆ i, f i) :=
  @iUnion_Ici_eq_Ioi_iInf ι (OrderDual R) _ f no_greatest_elem

theorem iUnion_Ici_eq_Ici_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (has_least_elem : (⨅ i, f i) ∈ range f) : ⋃ i : ι, Ici (f i) = Ici (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ici (@isGLB_iInf _ _ _ f) has_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']

theorem iUnion_Iic_eq_Iic_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (has_greatest_elem : (⨆ i, f i) ∈ range f) : ⋃ i : ι, Iic (f i) = Iic (⨆ i, f i) :=
  @iUnion_Ici_eq_Ici_iInf ι (OrderDual R) _ f has_greatest_elem

theorem iUnion_Iio_eq_univ_iff : ⋃ i, Iio (f i) = univ ↔ (¬ BddAbove (range f)) := by
  simp [not_bddAbove_iff, Set.eq_univ_iff_forall]

theorem iUnion_Iic_of_not_bddAbove_range (hf : ¬ BddAbove (range f)) : ⋃ i, Iic (f i) = univ := by
  refine  Set.eq_univ_of_subset ?_ (iUnion_Iio_eq_univ_iff.mpr hf)
  gcongr
  exact Iio_subset_Iic_self

theorem iInter_Iic_eq_empty_iff : ⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f) := by
  simp [not_bddBelow_iff, Set.eq_empty_iff_forall_notMem]

theorem iInter_Iio_of_not_bddBelow_range (hf : ¬ BddBelow (range f)) : ⋂ i, Iio (f i) = ∅ := by
  refine eq_empty_of_subset_empty ?_
  rw [← iInter_Iic_eq_empty_iff.mpr hf]
  gcongr
  exact Iio_subset_Iic_self

end UnionIxx
