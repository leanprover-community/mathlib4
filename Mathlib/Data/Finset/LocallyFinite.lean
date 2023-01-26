/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies

! This file was ported from Lean 3 source module data.finset.locally_finite
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.LocallyFinite
import Mathbin.Data.Set.Intervals.Monoid

/-!
# Intervals as finsets

This file provides basic results about all the `finset.Ixx`, which are defined in
`order.locally_finite`.

## TODO

This file was originally only about `finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `data.x.intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/


open Function OrderDual

open BigOperators FinsetInterval

variable {ι α : Type _}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[simp]
theorem nonempty_icc : (icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]
#align finset.nonempty_Icc Finset.nonempty_icc

@[simp]
theorem nonempty_ico : (ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]
#align finset.nonempty_Ico Finset.nonempty_ico

@[simp]
theorem nonempty_ioc : (ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioc, Set.nonempty_Ioc]
#align finset.nonempty_Ioc Finset.nonempty_ioc

@[simp]
theorem nonempty_ioo [DenselyOrdered α] : (ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]
#align finset.nonempty_Ioo Finset.nonempty_ioo

@[simp]
theorem icc_eq_empty_iff : icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]
#align finset.Icc_eq_empty_iff Finset.icc_eq_empty_iff

@[simp]
theorem ico_eq_empty_iff : ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]
#align finset.Ico_eq_empty_iff Finset.ico_eq_empty_iff

@[simp]
theorem ioc_eq_empty_iff : ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_eq_empty_iff]
#align finset.Ioc_eq_empty_iff Finset.ioc_eq_empty_iff

@[simp]
theorem ioo_eq_empty_iff [DenselyOrdered α] : ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]
#align finset.Ioo_eq_empty_iff Finset.ioo_eq_empty_iff

alias Icc_eq_empty_iff ↔ _ Icc_eq_empty
#align finset.Icc_eq_empty Finset.icc_eq_empty

alias Ico_eq_empty_iff ↔ _ Ico_eq_empty
#align finset.Ico_eq_empty Finset.ico_eq_empty

alias Ioc_eq_empty_iff ↔ _ Ioc_eq_empty
#align finset.Ioc_eq_empty Finset.ioc_eq_empty

@[simp]
theorem ioo_eq_empty (h : ¬a < b) : ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun x hx => h ((mem_ioo.1 hx).1.trans (mem_ioo.1 hx).2)
#align finset.Ioo_eq_empty Finset.ioo_eq_empty

@[simp]
theorem icc_eq_empty_of_lt (h : b < a) : icc a b = ∅ :=
  icc_eq_empty h.not_le
#align finset.Icc_eq_empty_of_lt Finset.icc_eq_empty_of_lt

@[simp]
theorem ico_eq_empty_of_le (h : b ≤ a) : ico a b = ∅ :=
  ico_eq_empty h.not_lt
#align finset.Ico_eq_empty_of_le Finset.ico_eq_empty_of_le

@[simp]
theorem ioc_eq_empty_of_le (h : b ≤ a) : ioc a b = ∅ :=
  ioc_eq_empty h.not_lt
#align finset.Ioc_eq_empty_of_le Finset.ioc_eq_empty_of_le

@[simp]
theorem ioo_eq_empty_of_le (h : b ≤ a) : ioo a b = ∅ :=
  ioo_eq_empty h.not_lt
#align finset.Ioo_eq_empty_of_le Finset.ioo_eq_empty_of_le

@[simp]
theorem left_mem_icc : a ∈ icc a b ↔ a ≤ b := by simp only [mem_Icc, true_and_iff, le_rfl]
#align finset.left_mem_Icc Finset.left_mem_icc

@[simp]
theorem left_mem_ico : a ∈ ico a b ↔ a < b := by simp only [mem_Ico, true_and_iff, le_refl]
#align finset.left_mem_Ico Finset.left_mem_ico

@[simp]
theorem right_mem_icc : b ∈ icc a b ↔ a ≤ b := by simp only [mem_Icc, and_true_iff, le_rfl]
#align finset.right_mem_Icc Finset.right_mem_icc

@[simp]
theorem right_mem_ioc : b ∈ ioc a b ↔ a < b := by simp only [mem_Ioc, and_true_iff, le_rfl]
#align finset.right_mem_Ioc Finset.right_mem_ioc

@[simp]
theorem left_not_mem_ioc : a ∉ ioc a b := fun h => lt_irrefl _ (mem_ioc.1 h).1
#align finset.left_not_mem_Ioc Finset.left_not_mem_ioc

@[simp]
theorem left_not_mem_ioo : a ∉ ioo a b := fun h => lt_irrefl _ (mem_ioo.1 h).1
#align finset.left_not_mem_Ioo Finset.left_not_mem_ioo

@[simp]
theorem right_not_mem_ico : b ∉ ico a b := fun h => lt_irrefl _ (mem_ico.1 h).2
#align finset.right_not_mem_Ico Finset.right_not_mem_ico

@[simp]
theorem right_not_mem_ioo : b ∉ ioo a b := fun h => lt_irrefl _ (mem_ioo.1 h).2
#align finset.right_not_mem_Ioo Finset.right_not_mem_ioo

theorem icc_subset_icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : icc a₁ b₁ ⊆ icc a₂ b₂ := by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb
#align finset.Icc_subset_Icc Finset.icc_subset_icc

theorem ico_subset_ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : ico a₁ b₁ ⊆ ico a₂ b₂ := by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb
#align finset.Ico_subset_Ico Finset.ico_subset_ico

theorem ioc_subset_ioc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : ioc a₁ b₁ ⊆ ioc a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb
#align finset.Ioc_subset_Ioc Finset.ioc_subset_ioc

theorem ioo_subset_ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : ioo a₁ b₁ ⊆ ioo a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb
#align finset.Ioo_subset_Ioo Finset.ioo_subset_ioo

theorem icc_subset_icc_left (h : a₁ ≤ a₂) : icc a₂ b ⊆ icc a₁ b :=
  icc_subset_icc h le_rfl
#align finset.Icc_subset_Icc_left Finset.icc_subset_icc_left

theorem ico_subset_ico_left (h : a₁ ≤ a₂) : ico a₂ b ⊆ ico a₁ b :=
  ico_subset_ico h le_rfl
#align finset.Ico_subset_Ico_left Finset.ico_subset_ico_left

theorem ioc_subset_ioc_left (h : a₁ ≤ a₂) : ioc a₂ b ⊆ ioc a₁ b :=
  ioc_subset_ioc h le_rfl
#align finset.Ioc_subset_Ioc_left Finset.ioc_subset_ioc_left

theorem ioo_subset_ioo_left (h : a₁ ≤ a₂) : ioo a₂ b ⊆ ioo a₁ b :=
  ioo_subset_ioo h le_rfl
#align finset.Ioo_subset_Ioo_left Finset.ioo_subset_ioo_left

theorem icc_subset_icc_right (h : b₁ ≤ b₂) : icc a b₁ ⊆ icc a b₂ :=
  icc_subset_icc le_rfl h
#align finset.Icc_subset_Icc_right Finset.icc_subset_icc_right

theorem ico_subset_ico_right (h : b₁ ≤ b₂) : ico a b₁ ⊆ ico a b₂ :=
  ico_subset_ico le_rfl h
#align finset.Ico_subset_Ico_right Finset.ico_subset_ico_right

theorem ioc_subset_ioc_right (h : b₁ ≤ b₂) : ioc a b₁ ⊆ ioc a b₂ :=
  ioc_subset_ioc le_rfl h
#align finset.Ioc_subset_Ioc_right Finset.ioc_subset_ioc_right

theorem ioo_subset_ioo_right (h : b₁ ≤ b₂) : ioo a b₁ ⊆ ioo a b₂ :=
  ioo_subset_ioo le_rfl h
#align finset.Ioo_subset_Ioo_right Finset.ioo_subset_ioo_right

theorem ico_subset_ioo_left (h : a₁ < a₂) : ico a₂ b ⊆ ioo a₁ b :=
  by
  rw [← coe_subset, coe_Ico, coe_Ioo]
  exact Set.Ico_subset_Ioo_left h
#align finset.Ico_subset_Ioo_left Finset.ico_subset_ioo_left

theorem ioc_subset_ioo_right (h : b₁ < b₂) : ioc a b₁ ⊆ ioo a b₂ :=
  by
  rw [← coe_subset, coe_Ioc, coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h
#align finset.Ioc_subset_Ioo_right Finset.ioc_subset_ioo_right

theorem icc_subset_ico_right (h : b₁ < b₂) : icc a b₁ ⊆ ico a b₂ :=
  by
  rw [← coe_subset, coe_Icc, coe_Ico]
  exact Set.Icc_subset_Ico_right h
#align finset.Icc_subset_Ico_right Finset.icc_subset_ico_right

theorem ioo_subset_ico_self : ioo a b ⊆ ico a b :=
  by
  rw [← coe_subset, coe_Ioo, coe_Ico]
  exact Set.Ioo_subset_Ico_self
#align finset.Ioo_subset_Ico_self Finset.ioo_subset_ico_self

theorem ioo_subset_ioc_self : ioo a b ⊆ ioc a b :=
  by
  rw [← coe_subset, coe_Ioo, coe_Ioc]
  exact Set.Ioo_subset_Ioc_self
#align finset.Ioo_subset_Ioc_self Finset.ioo_subset_ioc_self

theorem ico_subset_icc_self : ico a b ⊆ icc a b :=
  by
  rw [← coe_subset, coe_Ico, coe_Icc]
  exact Set.Ico_subset_Icc_self
#align finset.Ico_subset_Icc_self Finset.ico_subset_icc_self

theorem ioc_subset_icc_self : ioc a b ⊆ icc a b :=
  by
  rw [← coe_subset, coe_Ioc, coe_Icc]
  exact Set.Ioc_subset_Icc_self
#align finset.Ioc_subset_Icc_self Finset.ioc_subset_icc_self

theorem ioo_subset_icc_self : ioo a b ⊆ icc a b :=
  ioo_subset_ico_self.trans ico_subset_icc_self
#align finset.Ioo_subset_Icc_self Finset.ioo_subset_icc_self

theorem icc_subset_icc_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Icc, coe_Icc, Set.Icc_subset_Icc_iff h₁]
#align finset.Icc_subset_Icc_iff Finset.icc_subset_icc_iff

theorem icc_subset_ioo_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ioo, Set.Icc_subset_Ioo_iff h₁]
#align finset.Icc_subset_Ioo_iff Finset.icc_subset_ioo_iff

theorem icc_subset_ico_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico, Set.Icc_subset_Ico_iff h₁]
#align finset.Icc_subset_Ico_iff Finset.icc_subset_ico_iff

theorem icc_subset_ioc_iff (h₁ : a₁ ≤ b₁) : icc a₁ b₁ ⊆ ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  (icc_subset_ico_iff h₁.dual).trans and_comm
#align finset.Icc_subset_Ioc_iff Finset.icc_subset_ioc_iff

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`
theorem icc_sSubset_icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : icc a₁ b₁ ⊂ icc a₂ b₂ :=
  by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb
#align finset.Icc_ssubset_Icc_left Finset.icc_sSubset_icc_left

theorem icc_sSubset_icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
    icc a₁ b₁ ⊂ icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb
#align finset.Icc_ssubset_Icc_right Finset.icc_sSubset_icc_right

variable (a)

@[simp]
theorem ico_self : ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _
#align finset.Ico_self Finset.ico_self

@[simp]
theorem ioc_self : ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _
#align finset.Ioc_self Finset.ioc_self

@[simp]
theorem ioo_self : ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _
#align finset.Ioo_self Finset.ioo_self

variable {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def Set.fintypeOfMemBounds {s : Set α} [DecidablePred (· ∈ s)] (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) fun x hx => ⟨ha hx, hb hx⟩
#align set.fintype_of_mem_bounds Set.fintypeOfMemBounds

theorem BddBelow.finite_of_bddAbove {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) : s.Finite :=
  by
  let ⟨a, ha⟩ := h₀
  let ⟨b, hb⟩ := h₁
  classical exact ⟨Set.fintypeOfMemBounds ha hb⟩
#align bdd_below.finite_of_bdd_above BddBelow.finite_of_bddAbove

section Filter

theorem ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    (ico a b).filter (· < c) = ∅ :=
  filter_false_of_mem fun x hx => (hca.trans (mem_ico.1 hx).1).not_lt
#align finset.Ico_filter_lt_of_le_left Finset.ico_filter_lt_of_le_left

theorem ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    (ico a b).filter (· < c) = ico a b :=
  filter_true_of_mem fun x hx => (mem_ico.1 hx).2.trans_le hbc
#align finset.Ico_filter_lt_of_right_le Finset.ico_filter_lt_of_right_le

theorem ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    (ico a b).filter (· < c) = ico a c := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_right_comm]
  exact and_iff_left_of_imp fun h => h.2.trans_le hcb
#align finset.Ico_filter_lt_of_le_right Finset.ico_filter_lt_of_le_right

theorem ico_filter_le_of_le_left {a b c : α} [DecidablePred ((· ≤ ·) c)] (hca : c ≤ a) :
    (ico a b).filter ((· ≤ ·) c) = ico a b :=
  filter_true_of_mem fun x hx => hca.trans (mem_ico.1 hx).1
#align finset.Ico_filter_le_of_le_left Finset.ico_filter_le_of_le_left

theorem ico_filter_le_of_right_le {a b : α} [DecidablePred ((· ≤ ·) b)] :
    (ico a b).filter ((· ≤ ·) b) = ∅ :=
  filter_false_of_mem fun x hx => (mem_ico.1 hx).2.not_le
#align finset.Ico_filter_le_of_right_le Finset.ico_filter_le_of_right_le

theorem ico_filter_le_of_left_le {a b c : α} [DecidablePred ((· ≤ ·) c)] (hac : a ≤ c) :
    (ico a b).filter ((· ≤ ·) c) = ico c b := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_comm', and_left_comm]
  exact and_iff_right_of_imp fun h => hac.trans h.1
#align finset.Ico_filter_le_of_left_le Finset.ico_filter_le_of_left_le

theorem icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    (icc a b).filter (· < c) = icc a b :=
  (Finset.filter_eq_self _).2 fun x hx => lt_of_le_of_lt (mem_icc.1 hx).2 h
#align finset.Icc_filter_lt_of_lt_right Finset.icc_filter_lt_of_lt_right

theorem ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    (ioc a b).filter (· < c) = ioc a b :=
  (Finset.filter_eq_self _).2 fun x hx => lt_of_le_of_lt (mem_ioc.1 hx).2 h
#align finset.Ioc_filter_lt_of_lt_right Finset.ioc_filter_lt_of_lt_right

theorem iic_filter_lt_of_lt_right {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
    [DecidablePred (· < c)] (h : a < c) : (iic a).filter (· < c) = iic a :=
  (Finset.filter_eq_self _).2 fun x hx => lt_of_le_of_lt (mem_iic.1 hx) h
#align finset.Iic_filter_lt_of_lt_right Finset.iic_filter_lt_of_lt_right

variable (a b) [Fintype α]

theorem filter_lt_lt_eq_ioo [DecidablePred fun j => a < j ∧ j < b] :
    (univ.filter fun j => a < j ∧ j < b) = ioo a b :=
  by
  ext
  simp
#align finset.filter_lt_lt_eq_Ioo Finset.filter_lt_lt_eq_ioo

theorem filter_lt_le_eq_ioc [DecidablePred fun j => a < j ∧ j ≤ b] :
    (univ.filter fun j => a < j ∧ j ≤ b) = ioc a b :=
  by
  ext
  simp
#align finset.filter_lt_le_eq_Ioc Finset.filter_lt_le_eq_ioc

theorem filter_le_lt_eq_ico [DecidablePred fun j => a ≤ j ∧ j < b] :
    (univ.filter fun j => a ≤ j ∧ j < b) = ico a b :=
  by
  ext
  simp
#align finset.filter_le_lt_eq_Ico Finset.filter_le_lt_eq_ico

theorem filter_le_le_eq_icc [DecidablePred fun j => a ≤ j ∧ j ≤ b] :
    (univ.filter fun j => a ≤ j ∧ j ≤ b) = icc a b :=
  by
  ext
  simp
#align finset.filter_le_le_eq_Icc Finset.filter_le_le_eq_icc

end Filter

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

theorem icc_subset_ici_self : icc a b ⊆ ici a := by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self
#align finset.Icc_subset_Ici_self Finset.icc_subset_ici_self

theorem ico_subset_ici_self : ico a b ⊆ ici a := by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self
#align finset.Ico_subset_Ici_self Finset.ico_subset_ici_self

theorem ioc_subset_ioi_self : ioc a b ⊆ ioi a := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self
#align finset.Ioc_subset_Ioi_self Finset.ioc_subset_ioi_self

theorem ioo_subset_ioi_self : ioo a b ⊆ ioi a := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self
#align finset.Ioo_subset_Ioi_self Finset.ioo_subset_ioi_self

theorem ioc_subset_ici_self : ioc a b ⊆ ici a :=
  ioc_subset_icc_self.trans icc_subset_ici_self
#align finset.Ioc_subset_Ici_self Finset.ioc_subset_ici_self

theorem ioo_subset_ici_self : ioo a b ⊆ ici a :=
  ioo_subset_ico_self.trans ico_subset_ici_self
#align finset.Ioo_subset_Ici_self Finset.ioo_subset_ici_self

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

theorem icc_subset_iic_self : icc a b ⊆ iic b := by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self
#align finset.Icc_subset_Iic_self Finset.icc_subset_iic_self

theorem ioc_subset_iic_self : ioc a b ⊆ iic b := by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self
#align finset.Ioc_subset_Iic_self Finset.ioc_subset_iic_self

theorem ico_subset_iio_self : ico a b ⊆ iio b := by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self
#align finset.Ico_subset_Iio_self Finset.ico_subset_iio_self

theorem ioo_subset_iio_self : ioo a b ⊆ iio b := by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self
#align finset.Ioo_subset_Iio_self Finset.ioo_subset_iio_self

theorem ico_subset_iic_self : ico a b ⊆ iic b :=
  ico_subset_icc_self.trans icc_subset_iic_self
#align finset.Ico_subset_Iic_self Finset.ico_subset_iic_self

theorem ioo_subset_iic_self : ioo a b ⊆ iic b :=
  ioo_subset_ioc_self.trans ioc_subset_iic_self
#align finset.Ioo_subset_Iic_self Finset.ioo_subset_iic_self

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

theorem ioi_subset_ici_self : ioi a ⊆ ici a := by simpa [← coe_subset] using Set.Ioi_subset_Ici_self
#align finset.Ioi_subset_Ici_self Finset.ioi_subset_ici_self

theorem BddBelow.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
  (ici a).finite_to_set.Subset fun x hx => mem_ici.2 <| ha hx
#align bdd_below.finite BddBelow.finite

variable [Fintype α]

theorem filter_lt_eq_ioi [DecidablePred ((· < ·) a)] : univ.filter ((· < ·) a) = ioi a :=
  by
  ext
  simp
#align finset.filter_lt_eq_Ioi Finset.filter_lt_eq_ioi

theorem filter_le_eq_ici [DecidablePred ((· ≤ ·) a)] : univ.filter ((· ≤ ·) a) = ici a :=
  by
  ext
  simp
#align finset.filter_le_eq_Ici Finset.filter_le_eq_ici

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a : α}

theorem iio_subset_iic_self : iio a ⊆ iic a := by simpa [← coe_subset] using Set.Iio_subset_Iic_self
#align finset.Iio_subset_Iic_self Finset.iio_subset_iic_self

theorem BddAbove.finite {s : Set α} (hs : BddAbove s) : s.Finite :=
  hs.dual.Finite
#align bdd_above.finite BddAbove.finite

variable [Fintype α]

theorem filter_gt_eq_iio [DecidablePred (· < a)] : univ.filter (· < a) = iio a :=
  by
  ext
  simp
#align finset.filter_gt_eq_Iio Finset.filter_gt_eq_iio

theorem filter_ge_eq_iic [DecidablePred (· ≤ a)] : univ.filter (· ≤ a) = iic a :=
  by
  ext
  simp
#align finset.filter_ge_eq_Iic Finset.filter_ge_eq_iic

end LocallyFiniteOrderBot

variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem disjoint_ioi_iio (a : α) : Disjoint (ioi a) (iio a) :=
  disjoint_left.2 fun b hab hba => (mem_ioi.1 hab).not_lt <| mem_iio.1 hba
#align finset.disjoint_Ioi_Iio Finset.disjoint_ioi_iio

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
theorem icc_self (a : α) : icc a a = {a} := by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]
#align finset.Icc_self Finset.icc_self

@[simp]
theorem icc_eq_singleton_iff : icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]
#align finset.Icc_eq_singleton_iff Finset.icc_eq_singleton_iff

theorem ico_disjoint_ico_consecutive (a b c : α) : Disjoint (ico a b) (ico b c) :=
  disjoint_left.2 fun x hab hbc => (mem_ico.mp hab).2.not_le (mem_ico.mp hbc).1
#align finset.Ico_disjoint_Ico_consecutive Finset.ico_disjoint_ico_consecutive

section DecidableEq

variable [DecidableEq α]

@[simp]
theorem icc_erase_left (a b : α) : (icc a b).erase a = ioc a b := by simp [← coe_inj]
#align finset.Icc_erase_left Finset.icc_erase_left

@[simp]
theorem icc_erase_right (a b : α) : (icc a b).erase b = ico a b := by simp [← coe_inj]
#align finset.Icc_erase_right Finset.icc_erase_right

@[simp]
theorem ico_erase_left (a b : α) : (ico a b).erase a = ioo a b := by simp [← coe_inj]
#align finset.Ico_erase_left Finset.ico_erase_left

@[simp]
theorem ioc_erase_right (a b : α) : (ioc a b).erase b = ioo a b := by simp [← coe_inj]
#align finset.Ioc_erase_right Finset.ioc_erase_right

@[simp]
theorem icc_diff_both (a b : α) : icc a b \ {a, b} = ioo a b := by simp [← coe_inj]
#align finset.Icc_diff_both Finset.icc_diff_both

@[simp]
theorem ico_insert_right (h : a ≤ b) : insert b (ico a b) = icc a b := by
  rw [← coe_inj, coe_insert, coe_Icc, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ico_union_right h]
#align finset.Ico_insert_right Finset.ico_insert_right

@[simp]
theorem ioc_insert_left (h : a ≤ b) : insert a (ioc a b) = icc a b := by
  rw [← coe_inj, coe_insert, coe_Ioc, coe_Icc, Set.insert_eq, Set.union_comm, Set.Ioc_union_left h]
#align finset.Ioc_insert_left Finset.ioc_insert_left

@[simp]
theorem ioo_insert_left (h : a < b) : insert a (ioo a b) = ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]
#align finset.Ioo_insert_left Finset.ioo_insert_left

@[simp]
theorem ioo_insert_right (h : a < b) : insert b (ioo a b) = ioc a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ioc, Set.insert_eq, Set.union_comm, Set.Ioo_union_right h]
#align finset.Ioo_insert_right Finset.ioo_insert_right

@[simp]
theorem icc_diff_ico_self (h : a ≤ b) : icc a b \ ico a b = {b} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ico_self Finset.icc_diff_ico_self

@[simp]
theorem icc_diff_ioc_self (h : a ≤ b) : icc a b \ ioc a b = {a} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ioc_self Finset.icc_diff_ioc_self

@[simp]
theorem icc_diff_ioo_self (h : a ≤ b) : icc a b \ ioo a b = {a, b} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ioo_self Finset.icc_diff_ioo_self

@[simp]
theorem ico_diff_ioo_self (h : a < b) : ico a b \ ioo a b = {a} := by simp [← coe_inj, h]
#align finset.Ico_diff_Ioo_self Finset.ico_diff_ioo_self

@[simp]
theorem ioc_diff_ioo_self (h : a < b) : ioc a b \ ioo a b = {b} := by simp [← coe_inj, h]
#align finset.Ioc_diff_Ioo_self Finset.ioc_diff_ioo_self

@[simp]
theorem ico_inter_ico_consecutive (a b c : α) : ico a b ∩ ico b c = ∅ :=
  (ico_disjoint_ico_consecutive a b c).eq_bot
#align finset.Ico_inter_Ico_consecutive Finset.ico_inter_ico_consecutive

end DecidableEq

-- Those lemmas are purposefully the other way around
theorem icc_eq_cons_ico (h : a ≤ b) : icc a b = (ico a b).cons b right_not_mem_ico := by
  classical rw [cons_eq_insert, Ico_insert_right h]
#align finset.Icc_eq_cons_Ico Finset.icc_eq_cons_ico

theorem icc_eq_cons_ioc (h : a ≤ b) : icc a b = (ioc a b).cons a left_not_mem_ioc := by
  classical rw [cons_eq_insert, Ioc_insert_left h]
#align finset.Icc_eq_cons_Ioc Finset.icc_eq_cons_ioc

theorem ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((ico a b).filter fun x => x ≤ a) = {a} := by
  ext x
  rw [mem_filter, mem_Ico, mem_singleton, and_right_comm, ← le_antisymm_iff, eq_comm]
  exact and_iff_left_of_imp fun h => h.le.trans_lt hab
#align finset.Ico_filter_le_left Finset.ico_filter_le_left

theorem card_ico_eq_card_icc_sub_one (a b : α) : (ico a b).card = (icc a b).card - 1 := by
  classical
    by_cases h : a ≤ b
    · rw [← Ico_insert_right h, card_insert_of_not_mem right_not_mem_Ico]
      exact (Nat.add_sub_cancel _ _).symm
    · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, zero_tsub]
#align finset.card_Ico_eq_card_Icc_sub_one Finset.card_ico_eq_card_icc_sub_one

theorem card_ioc_eq_card_icc_sub_one (a b : α) : (ioc a b).card = (icc a b).card - 1 :=
  @card_ico_eq_card_icc_sub_one αᵒᵈ _ _ _ _
#align finset.card_Ioc_eq_card_Icc_sub_one Finset.card_ioc_eq_card_icc_sub_one

theorem card_ioo_eq_card_ico_sub_one (a b : α) : (ioo a b).card = (ico a b).card - 1 := by
  classical
    by_cases h : a ≤ b
    · obtain rfl | h' := h.eq_or_lt
      · rw [Ioo_self, Ico_self, card_empty]
      rw [← Ioo_insert_left h', card_insert_of_not_mem left_not_mem_Ioo]
      exact (Nat.add_sub_cancel _ _).symm
    · rw [Ioo_eq_empty fun h' => h h'.le, Ico_eq_empty fun h' => h h'.le, card_empty, zero_tsub]
#align finset.card_Ioo_eq_card_Ico_sub_one Finset.card_ioo_eq_card_ico_sub_one

theorem card_ioo_eq_card_ioc_sub_one (a b : α) : (ioo a b).card = (ioc a b).card - 1 :=
  @card_ioo_eq_card_ico_sub_one αᵒᵈ _ _ _ _
#align finset.card_Ioo_eq_card_Ioc_sub_one Finset.card_ioo_eq_card_ioc_sub_one

theorem card_ioo_eq_card_icc_sub_two (a b : α) : (ioo a b).card = (icc a b).card - 2 :=
  by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl
#align finset.card_Ioo_eq_card_Icc_sub_two Finset.card_ioo_eq_card_icc_sub_two

end PartialOrder

section BoundedPartialOrder

variable [PartialOrder α]

section OrderTop

variable [LocallyFiniteOrderTop α]

@[simp]
theorem ici_erase [DecidableEq α] (a : α) : (ici a).erase a = ioi a :=
  by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm', ne_comm]
#align finset.Ici_erase Finset.ici_erase

@[simp]
theorem ioi_insert [DecidableEq α] (a : α) : insert a (ioi a) = ici a :=
  by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm', eq_comm]
#align finset.Ioi_insert Finset.ioi_insert

@[simp]
theorem not_mem_ioi_self {b : α} : b ∉ ioi b := fun h => lt_irrefl _ (mem_ioi.1 h)
#align finset.not_mem_Ioi_self Finset.not_mem_ioi_self

-- Purposefully written the other way around
theorem ici_eq_cons_ioi (a : α) : ici a = (ioi a).cons a not_mem_ioi_self := by
  classical rw [cons_eq_insert, Ioi_insert]
#align finset.Ici_eq_cons_Ioi Finset.ici_eq_cons_ioi

theorem card_ioi_eq_card_ici_sub_one (a : α) : (ioi a).card = (ici a).card - 1 := by
  rw [Ici_eq_cons_Ioi, card_cons, add_tsub_cancel_right]
#align finset.card_Ioi_eq_card_Ici_sub_one Finset.card_ioi_eq_card_ici_sub_one

end OrderTop

section OrderBot

variable [LocallyFiniteOrderBot α]

@[simp]
theorem iic_erase [DecidableEq α] (b : α) : (iic b).erase b = iio b :=
  by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm']
#align finset.Iic_erase Finset.iic_erase

@[simp]
theorem iio_insert [DecidableEq α] (b : α) : insert b (iio b) = iic b :=
  by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm']
#align finset.Iio_insert Finset.iio_insert

@[simp]
theorem not_mem_iio_self {b : α} : b ∉ iio b := fun h => lt_irrefl _ (mem_iio.1 h)
#align finset.not_mem_Iio_self Finset.not_mem_iio_self

-- Purposefully written the other way around
theorem iic_eq_cons_iio (b : α) : iic b = (iio b).cons b not_mem_iio_self := by
  classical rw [cons_eq_insert, Iio_insert]
#align finset.Iic_eq_cons_Iio Finset.iic_eq_cons_iio

theorem card_iio_eq_card_iic_sub_one (a : α) : (iio a).card = (iic a).card - 1 := by
  rw [Iic_eq_cons_Iio, card_cons, add_tsub_cancel_right]
#align finset.card_Iio_eq_card_Iic_sub_one Finset.card_iio_eq_card_iic_sub_one

end OrderBot

end BoundedPartialOrder

section LinearOrder

variable [LinearOrder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b : α}

theorem ico_subset_ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    ico a₁ b₁ ⊆ ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]
#align finset.Ico_subset_Ico_iff Finset.ico_subset_ico_iff

theorem ico_union_ico_eq_ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    ico a b ∪ ico b c = ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]
#align finset.Ico_union_Ico_eq_Ico Finset.ico_union_ico_eq_ico

@[simp]
theorem ioc_union_ioc_eq_ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) : ioc a b ∪ ioc b c = ioc a c :=
  by rw [← coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]
#align finset.Ioc_union_Ioc_eq_Ioc Finset.ioc_union_ioc_eq_ioc

theorem ico_subset_ico_union_ico {a b c : α} : ico a c ⊆ ico a b ∪ ico b c :=
  by
  rw [← coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico
#align finset.Ico_subset_Ico_union_Ico Finset.ico_subset_ico_union_ico

theorem ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
    ico a b ∪ ico c d = ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]
#align finset.Ico_union_Ico' Finset.ico_union_Ico'

theorem ico_union_ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    ico a b ∪ ico c d = ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]
#align finset.Ico_union_Ico Finset.ico_union_ico

theorem ico_inter_ico {a b c d : α} : ico a b ∩ ico c d = ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, ← inf_eq_min, ← sup_eq_max,
    Set.Ico_inter_Ico]
#align finset.Ico_inter_Ico Finset.ico_inter_ico

@[simp]
theorem ico_filter_lt (a b c : α) : ((ico a b).filter fun x => x < c) = ico a (min b c) :=
  by
  cases le_total b c
  · rw [Ico_filter_lt_of_right_le h, min_eq_left h]
  · rw [Ico_filter_lt_of_le_right h, min_eq_right h]
#align finset.Ico_filter_lt Finset.ico_filter_lt

@[simp]
theorem ico_filter_le (a b c : α) : ((ico a b).filter fun x => c ≤ x) = ico (max a c) b :=
  by
  cases le_total a c
  · rw [Ico_filter_le_of_left_le h, max_eq_right h]
  · rw [Ico_filter_le_of_le_left h, max_eq_left h]
#align finset.Ico_filter_le Finset.ico_filter_le

@[simp]
theorem ioo_filter_lt (a b c : α) : (ioo a b).filter (· < c) = ioo a (min b c) :=
  by
  ext
  simp [and_assoc']
#align finset.Ioo_filter_lt Finset.ioo_filter_lt

@[simp]
theorem iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) :
    (iio a).filter (· < b) = iio (min a b) := by
  ext
  simp [and_assoc']
#align finset.Iio_filter_lt Finset.iio_filter_lt

@[simp]
theorem ico_diff_ico_left (a b c : α) : ico a b \ ico a c = ico (max a c) b :=
  by
  cases le_total a c
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, max_eq_right h, and_right_comm, not_and, not_lt]
    exact and_congr_left' ⟨fun hx => hx.2 hx.1, fun hx => ⟨h.trans hx, fun _ => hx⟩⟩
  · rw [Ico_eq_empty_of_le h, sdiff_empty, max_eq_left h]
#align finset.Ico_diff_Ico_left Finset.ico_diff_ico_left

@[simp]
theorem ico_diff_ico_right (a b c : α) : ico a b \ ico c b = ico a (min b c) :=
  by
  cases le_total b c
  · rw [Ico_eq_empty_of_le h, sdiff_empty, min_eq_left h]
  · ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, min_eq_right h, and_assoc', not_and', not_le]
    exact and_congr_right' ⟨fun hx => hx.2 hx.1, fun hx => ⟨hx.trans_le h, fun _ => hx⟩⟩
#align finset.Ico_diff_Ico_right Finset.ico_diff_ico_right

end LocallyFiniteOrder

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem ioi_disjUnion_iio (a : α) :
    (ioi a).disjUnion (iio a) (disjoint_ioi_iio a) = ({a} : Finset α)ᶜ :=
  by
  ext
  simp [eq_comm]
#align finset.Ioi_disj_union_Iio Finset.ioi_disjUnion_iio

end LinearOrder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

theorem uIcc_toDual (a b : α) : [toDual a, toDual b] = [a, b].map toDual.toEmbedding :=
  icc_toDual _ _
#align finset.uIcc_to_dual Finset.uIcc_toDual

@[simp]
theorem uIcc_of_le (h : a ≤ b) : [a, b] = icc a b := by rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]
#align finset.uIcc_of_le Finset.uIcc_of_le

@[simp]
theorem uIcc_of_ge (h : b ≤ a) : [a, b] = icc b a := by rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]
#align finset.uIcc_of_ge Finset.uIcc_of_ge

theorem uIcc_comm (a b : α) : [a, b] = [b, a] := by rw [uIcc, uIcc, inf_comm, sup_comm]
#align finset.uIcc_comm Finset.uIcc_comm

@[simp]
theorem uIcc_self : [a, a] = {a} := by simp [uIcc]
#align finset.uIcc_self Finset.uIcc_self

@[simp]
theorem nonempty_uIcc : Finset.Nonempty [a, b] :=
  nonempty_icc.2 inf_le_sup
#align finset.nonempty_uIcc Finset.nonempty_uIcc

theorem icc_subset_uIcc : icc a b ⊆ [a, b] :=
  icc_subset_icc inf_le_left le_sup_right
#align finset.Icc_subset_uIcc Finset.icc_subset_uIcc

theorem icc_subset_uIcc' : icc b a ⊆ [a, b] :=
  icc_subset_icc inf_le_right le_sup_left
#align finset.Icc_subset_uIcc' Finset.icc_subset_uIcc'

@[simp]
theorem left_mem_uIcc : a ∈ [a, b] :=
  mem_icc.2 ⟨inf_le_left, le_sup_left⟩
#align finset.left_mem_uIcc Finset.left_mem_uIcc

@[simp]
theorem right_mem_uIcc : b ∈ [a, b] :=
  mem_icc.2 ⟨inf_le_right, le_sup_right⟩
#align finset.right_mem_uIcc Finset.right_mem_uIcc

theorem mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [a, b] :=
  Icc_subset_uIcc <| mem_icc.2 ⟨ha, hb⟩
#align finset.mem_uIcc_of_le Finset.mem_uIcc_of_le

theorem mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [a, b] :=
  Icc_subset_uIcc' <| mem_icc.2 ⟨hb, ha⟩
#align finset.mem_uIcc_of_ge Finset.mem_uIcc_of_ge

theorem uIcc_subset_uIcc (h₁ : a₁ ∈ [a₂, b₂]) (h₂ : b₁ ∈ [a₂, b₂]) : [a₁, b₁] ⊆ [a₂, b₂] :=
  by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (le_inf h₁.1 h₂.1) (sup_le h₁.2 h₂.2)
#align finset.uIcc_subset_uIcc Finset.uIcc_subset_uIcc

theorem uIcc_subset_icc (ha : a₁ ∈ icc a₂ b₂) (hb : b₁ ∈ icc a₂ b₂) : [a₁, b₁] ⊆ icc a₂ b₂ :=
  by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (le_inf ha.1 hb.1) (sup_le ha.2 hb.2)
#align finset.uIcc_subset_Icc Finset.uIcc_subset_icc

theorem uIcc_subset_uIcc_iff_mem : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₁ ∈ [a₂, b₂] ∧ b₁ ∈ [a₂, b₂] :=
  ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩
#align finset.uIcc_subset_uIcc_iff_mem Finset.uIcc_subset_uIcc_iff_mem

theorem uIcc_subset_uIcc_iff_le' : [a₁, b₁] ⊆ [a₂, b₂] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  icc_subset_icc_iff inf_le_sup
#align finset.uIcc_subset_uIcc_iff_le' Finset.uIcc_subset_uIcc_iff_le'

theorem uIcc_subset_uIcc_right (h : x ∈ [a, b]) : [x, b] ⊆ [a, b] :=
  uIcc_subset_uIcc h right_mem_uIcc
#align finset.uIcc_subset_uIcc_right Finset.uIcc_subset_uIcc_right

theorem uIcc_subset_uIcc_left (h : x ∈ [a, b]) : [a, x] ⊆ [a, b] :=
  uIcc_subset_uIcc left_mem_uIcc h
#align finset.uIcc_subset_uIcc_left Finset.uIcc_subset_uIcc_left

end Lattice

section DistribLattice

variable [DistribLattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

theorem eq_of_mem_uIcc_of_mem_uIcc : a ∈ [b, c] → b ∈ [a, c] → a = b :=
  by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc
#align finset.eq_of_mem_uIcc_of_mem_uIcc Finset.eq_of_mem_uIcc_of_mem_uIcc

theorem eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [a, c] → c ∈ [a, b] → b = c :=
  by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'
#align finset.eq_of_mem_uIcc_of_mem_uIcc' Finset.eq_of_mem_uIcc_of_mem_uIcc'

theorem uIcc_injective_right (a : α) : Injective fun b => [b, a] := fun b c h =>
  by
  rw [ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)
#align finset.uIcc_injective_right Finset.uIcc_injective_right

theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a
#align finset.uIcc_injective_left Finset.uIcc_injective_left

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

theorem icc_min_max : icc (min a b) (max a b) = [a, b] :=
  rfl
#align finset.Icc_min_max Finset.icc_min_max

theorem uIcc_of_not_le (h : ¬a ≤ b) : [a, b] = icc b a :=
  uIcc_of_ge <| le_of_not_ge h
#align finset.uIcc_of_not_le Finset.uIcc_of_not_le

theorem uIcc_of_not_ge (h : ¬b ≤ a) : [a, b] = icc a b :=
  uIcc_of_le <| le_of_not_ge h
#align finset.uIcc_of_not_ge Finset.uIcc_of_not_ge

theorem uIcc_eq_union : [a, b] = icc a b ∪ icc b a :=
  coe_injective <| by
    push_cast
    exact Set.uIcc_eq_union
#align finset.uIcc_eq_union Finset.uIcc_eq_union

theorem mem_uIcc' : a ∈ [b, c] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]
#align finset.mem_uIcc' Finset.mem_uIcc'

theorem not_mem_uIcc_of_lt : c < a → c < b → c ∉ [a, b] :=
  by
  rw [mem_uIcc]
  exact Set.not_mem_uIcc_of_lt
#align finset.not_mem_uIcc_of_lt Finset.not_mem_uIcc_of_lt

theorem not_mem_uIcc_of_gt : a < c → b < c → c ∉ [a, b] :=
  by
  rw [mem_uIcc]
  exact Set.not_mem_uIcc_of_gt
#align finset.not_mem_uIcc_of_gt Finset.not_mem_uIcc_of_gt

theorem uIcc_subset_uIcc_iff_le :
    [a₁, b₁] ⊆ [a₂, b₂] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'
#align finset.uIcc_subset_uIcc_iff_le Finset.uIcc_subset_uIcc_iff_le

/-- A sort of triangle inequality. -/
theorem uIcc_subset_uIcc_union_uIcc : [a, c] ⊆ [a, b] ∪ [b, c] :=
  coe_subset.1 <| by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc
#align finset.uIcc_subset_uIcc_union_uIcc Finset.uIcc_subset_uIcc_union_uIcc

end LinearOrder

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α] [ExistsAddOfLE α] [LocallyFiniteOrder α]

@[simp]
theorem map_add_left_icc (a b c : α) : (icc a b).map (addLeftEmbedding c) = icc (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Icc, coe_Icc]
  exact Set.image_const_add_Icc _ _ _
#align finset.map_add_left_Icc Finset.map_add_left_icc

@[simp]
theorem map_add_right_icc (a b c : α) : (icc a b).map (addRightEmbedding c) = icc (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Icc, coe_Icc]
  exact Set.image_add_const_Icc _ _ _
#align finset.map_add_right_Icc Finset.map_add_right_icc

@[simp]
theorem map_add_left_ico (a b c : α) : (ico a b).map (addLeftEmbedding c) = ico (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Ico, coe_Ico]
  exact Set.image_const_add_Ico _ _ _
#align finset.map_add_left_Ico Finset.map_add_left_ico

@[simp]
theorem map_add_right_ico (a b c : α) : (ico a b).map (addRightEmbedding c) = ico (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Ico, coe_Ico]
  exact Set.image_add_const_Ico _ _ _
#align finset.map_add_right_Ico Finset.map_add_right_ico

@[simp]
theorem map_add_left_ioc (a b c : α) : (ioc a b).map (addLeftEmbedding c) = ioc (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc]
  exact Set.image_const_add_Ioc _ _ _
#align finset.map_add_left_Ioc Finset.map_add_left_ioc

@[simp]
theorem map_add_right_ioc (a b c : α) : (ioc a b).map (addRightEmbedding c) = ioc (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc]
  exact Set.image_add_const_Ioc _ _ _
#align finset.map_add_right_Ioc Finset.map_add_right_ioc

@[simp]
theorem map_add_left_ioo (a b c : α) : (ioo a b).map (addLeftEmbedding c) = ioo (c + a) (c + b) :=
  by
  rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo]
  exact Set.image_const_add_Ioo _ _ _
#align finset.map_add_left_Ioo Finset.map_add_left_ioo

@[simp]
theorem map_add_right_ioo (a b c : α) : (ioo a b).map (addRightEmbedding c) = ioo (a + c) (b + c) :=
  by
  rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo]
  exact Set.image_add_const_Ioo _ _ _
#align finset.map_add_right_Ioo Finset.map_add_right_ioo

variable [DecidableEq α]

@[simp]
theorem image_add_left_icc (a b c : α) : (icc a b).image ((· + ·) c) = icc (c + a) (c + b) :=
  by
  rw [← map_add_left_Icc, map_eq_image]
  rfl
#align finset.image_add_left_Icc Finset.image_add_left_icc

@[simp]
theorem image_add_left_ico (a b c : α) : (ico a b).image ((· + ·) c) = ico (c + a) (c + b) :=
  by
  rw [← map_add_left_Ico, map_eq_image]
  rfl
#align finset.image_add_left_Ico Finset.image_add_left_ico

@[simp]
theorem image_add_left_ioc (a b c : α) : (ioc a b).image ((· + ·) c) = ioc (c + a) (c + b) :=
  by
  rw [← map_add_left_Ioc, map_eq_image]
  rfl
#align finset.image_add_left_Ioc Finset.image_add_left_ioc

@[simp]
theorem image_add_left_ioo (a b c : α) : (ioo a b).image ((· + ·) c) = ioo (c + a) (c + b) :=
  by
  rw [← map_add_left_Ioo, map_eq_image]
  rfl
#align finset.image_add_left_Ioo Finset.image_add_left_ioo

@[simp]
theorem image_add_right_icc (a b c : α) : (icc a b).image (· + c) = icc (a + c) (b + c) :=
  by
  rw [← map_add_right_Icc, map_eq_image]
  rfl
#align finset.image_add_right_Icc Finset.image_add_right_icc

theorem image_add_right_ico (a b c : α) : (ico a b).image (· + c) = ico (a + c) (b + c) :=
  by
  rw [← map_add_right_Ico, map_eq_image]
  rfl
#align finset.image_add_right_Ico Finset.image_add_right_ico

theorem image_add_right_ioc (a b c : α) : (ioc a b).image (· + c) = ioc (a + c) (b + c) :=
  by
  rw [← map_add_right_Ioc, map_eq_image]
  rfl
#align finset.image_add_right_Ioc Finset.image_add_right_ioc

theorem image_add_right_ioo (a b c : α) : (ioo a b).image (· + c) = ioo (a + c) (b + c) :=
  by
  rw [← map_add_right_Ioo, map_eq_image]
  rfl
#align finset.image_add_right_Ioo Finset.image_add_right_ioo

end OrderedCancelAddCommMonoid

@[to_additive]
theorem prod_prod_ioi_mul_eq_prod_prod_off_diag [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderTop ι] [LocallyFiniteOrderBot ι] [CommMonoid α] (f : ι → ι → α) :
    (∏ i, ∏ j in ioi i, f j i * f i j) = ∏ i, ∏ j in {i}ᶜ, f j i :=
  by
  simp_rw [← Ioi_disj_union_Iio, prod_disj_union, prod_mul_distrib]
  congr 1
  rw [prod_sigma', prod_sigma']
  refine' prod_bij' (fun i hi => ⟨i.2, i.1⟩) _ _ (fun i hi => ⟨i.2, i.1⟩) _ _ _ <;> simp
#align finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag Finset.prod_prod_ioi_mul_eq_prod_prod_off_diag
#align finset.sum_sum_Ioi_add_eq_sum_sum_off_diag Finset.sum_sum_ioi_add_eq_sum_sum_off_diag

end Finset

