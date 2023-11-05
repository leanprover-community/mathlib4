/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.LocallyFinite

#align_import data.multiset.locally_finite from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Intervals as multisets

This file provides basic results about all the `Multiset.Ixx`, which are defined in
`Order.LocallyFinite`.

Note that intervals of multisets themselves (`Multiset.LocallyFiniteOrder`) are defined elsewhere.
-/


variable {α : Type*}

namespace Multiset

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] {a b c : α}

theorem nodup_Icc : (Icc a b).Nodup :=
  Finset.nodup _

theorem nodup_Ico : (Ico a b).Nodup :=
  Finset.nodup _

theorem nodup_Ioc : (Ioc a b).Nodup :=
  Finset.nodup _

theorem nodup_Ioo : (Ioo a b).Nodup :=
  Finset.nodup _

@[simp]
theorem Icc_eq_zero_iff : Icc a b = 0 ↔ ¬a ≤ b := by
  rw [Icc, Finset.val_eq_zero, Finset.Icc_eq_empty_iff]

@[simp]
theorem Ico_eq_zero_iff : Ico a b = 0 ↔ ¬a < b := by
  rw [Ico, Finset.val_eq_zero, Finset.Ico_eq_empty_iff]

@[simp]
theorem Ioc_eq_zero_iff : Ioc a b = 0 ↔ ¬a < b := by
  rw [Ioc, Finset.val_eq_zero, Finset.Ioc_eq_empty_iff]

@[simp]
theorem Ioo_eq_zero_iff [DenselyOrdered α] : Ioo a b = 0 ↔ ¬a < b := by
  rw [Ioo, Finset.val_eq_zero, Finset.Ioo_eq_empty_iff]

alias ⟨_, Icc_eq_zero⟩ := Icc_eq_zero_iff

alias ⟨_, Ico_eq_zero⟩ := Ico_eq_zero_iff

alias ⟨_, Ioc_eq_zero⟩ := Ioc_eq_zero_iff

@[simp]
theorem Ioo_eq_zero (h : ¬a < b) : Ioo a b = 0 :=
  eq_zero_iff_forall_not_mem.2 fun _x hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)

@[simp]
theorem Icc_eq_zero_of_lt (h : b < a) : Icc a b = 0 :=
  Icc_eq_zero h.not_le

@[simp]
theorem Ico_eq_zero_of_le (h : b ≤ a) : Ico a b = 0 :=
  Ico_eq_zero h.not_lt

@[simp]
theorem Ioc_eq_zero_of_le (h : b ≤ a) : Ioc a b = 0 :=
  Ioc_eq_zero h.not_lt

@[simp]
theorem Ioo_eq_zero_of_le (h : b ≤ a) : Ioo a b = 0 :=
  Ioo_eq_zero h.not_lt

variable (a)

-- Porting note: simp can prove this -- @[simp]
theorem Ico_self : Ico a a = 0 := by rw [Ico, Finset.Ico_self, Finset.empty_val]

-- Porting note: simp can prove this -- @[simp]
theorem Ioc_self : Ioc a a = 0 := by rw [Ioc, Finset.Ioc_self, Finset.empty_val]

-- Porting note: simp can prove this -- @[simp]
theorem Ioo_self : Ioo a a = 0 := by rw [Ioo, Finset.Ioo_self, Finset.empty_val]

variable {a}

theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b :=
  Finset.left_mem_Icc

theorem left_mem_Ico : a ∈ Ico a b ↔ a < b :=
  Finset.left_mem_Ico

theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b :=
  Finset.right_mem_Icc

theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b :=
  Finset.right_mem_Ioc

-- Porting note: simp can prove this -- @[simp]
theorem left_not_mem_Ioc : a ∉ Ioc a b :=
  Finset.left_not_mem_Ioc

-- Porting note: simp can prove this -- @[simp]
theorem left_not_mem_Ioo : a ∉ Ioo a b :=
  Finset.left_not_mem_Ioo

-- Porting note: simp can prove this -- @[simp]
theorem right_not_mem_Ico : b ∉ Ico a b :=
  Finset.right_not_mem_Ico

-- Porting note: simp can prove this -- @[simp]
theorem right_not_mem_Ioo : b ∉ Ioo a b :=
  Finset.right_not_mem_Ioo

theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => x < c) = ∅ := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_left hca]
  rfl

theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    ((Ico a b).filter fun x => x < c) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_right_le hbc]

theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    ((Ico a b).filter fun x => x < c) = Ico a c := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_lt_of_le_right hcb]
  rfl

theorem Ico_filter_le_of_le_left [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    ((Ico a b).filter fun x => c ≤ x) = Ico a b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_le_left hca]

theorem Ico_filter_le_of_right_le [DecidablePred ((· ≤ ·) b)] :
    ((Ico a b).filter fun x => b ≤ x) = ∅ := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_right_le]
  rfl

theorem Ico_filter_le_of_left_le [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    ((Ico a b).filter fun x => c ≤ x) = Ico c b := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_of_left_le hac]
  rfl

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b : α}

@[simp]
theorem Icc_self (a : α) : Icc a a = {a} := by rw [Icc, Finset.Icc_self, Finset.singleton_val]

theorem Ico_cons_right (h : a ≤ b) : b ::ₘ Ico a b = Icc a b := by
  classical
    rw [Ico, ← Finset.insert_val_of_not_mem right_not_mem_Ico, Finset.Ico_insert_right h]
    rfl

theorem Ioo_cons_left (h : a < b) : a ::ₘ Ioo a b = Ico a b := by
  classical
    rw [Ioo, ← Finset.insert_val_of_not_mem left_not_mem_Ioo, Finset.Ioo_insert_left h]
    rfl

theorem Ico_disjoint_Ico {a b c d : α} (h : b ≤ c) : (Ico a b).Disjoint (Ico c d) :=
  fun x hab hbc => by
  rw [mem_Ico] at hab hbc
  exact hab.2.not_le (h.trans hbc.1)

@[simp]
theorem Ico_inter_Ico_of_le [DecidableEq α] {a b c d : α} (h : b ≤ c) : Ico a b ∩ Ico c d = 0 :=
  Multiset.inter_eq_zero_iff_disjoint.2 <| Ico_disjoint_Ico h

theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((Ico a b).filter fun x => x ≤ a) = {a} := by
  rw [Ico, ← Finset.filter_val, Finset.Ico_filter_le_left hab]
  rfl

theorem card_Ico_eq_card_Icc_sub_one (a b : α) : card (Ico a b) = card (Icc a b) - 1 :=
  Finset.card_Ico_eq_card_Icc_sub_one _ _

theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : card (Ioc a b) = card (Icc a b) - 1 :=
  Finset.card_Ioc_eq_card_Icc_sub_one _ _

theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : card (Ioo a b) = card (Ico a b) - 1 :=
  Finset.card_Ioo_eq_card_Ico_sub_one _ _

theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : card (Ioo a b) = card (Icc a b) - 2 :=
  Finset.card_Ioo_eq_card_Icc_sub_two _ _

end PartialOrder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a b c d : α}

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  Finset.Ico_subset_Ico_iff h

theorem Ico_add_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    Ico a b + Ico b c = Ico a c := by
  rw [add_eq_union_iff_disjoint.2 (Ico_disjoint_Ico le_rfl), Ico, Ico, Ico, ← Finset.union_val,
    Finset.Ico_union_Ico_eq_Ico hab hbc]

theorem Ico_inter_Ico : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [Ico, Ico, Ico, ← Finset.inter_val, Finset.Ico_inter_Ico]

@[simp]
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min b c) := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_lt]

@[simp]
theorem Ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c ≤ x) = Ico (max a c) b := by
  rw [Ico, Ico, ← Finset.filter_val, Finset.Ico_filter_le]

@[simp]
theorem Ico_sub_Ico_left (a b c : α) : Ico a b - Ico a c = Ico (max a c) b := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_left]

@[simp]
theorem Ico_sub_Ico_right (a b c : α) : Ico a b - Ico c b = Ico a (min b c) := by
  rw [Ico, Ico, Ico, ← Finset.sdiff_val, Finset.Ico_diff_Ico_right]

end LinearOrder

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]

theorem map_add_left_Icc (a b c : α) : (Icc a b).map ((· + ·) c) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_left_Ico (a b c : α) : (Ico a b).map ((· + ·) c) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_left_Ioc (a b c : α) : (Ioc a b).map ((· + ·) c) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_left_Ioo (a b c : α) : (Ioo a b).map ((· + ·) c) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]

theorem map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _

theorem map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _

theorem map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _

theorem map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _

end OrderedCancelAddCommMonoid

end Multiset
