/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies
-/
import Mathlib.Order.Cover
import Mathlib.Order.Interval.Finset.Defs

#align_import data.finset.locally_finite from "leanprover-community/mathlib"@"442a83d738cb208d3600056c489be16900ba701d"

/-!
# Intervals as finsets

This file provides basic results about all the `Finset.Ixx`, which are defined in
`Order.Interval.Finset.Defs`.

In addition, it shows that in a locally finite order `≤` and `<` are the transitive closures of,
respectively, `⩿` and `⋖`, which then leads to a characterization of monotone and strictly
functions whose domain is a locally finite order. In particular, this file proves:

* `le_iff_transGen_wcovBy`: `≤` is the transitive closure of `⩿`
* `lt_iff_transGen_covBy`: `≤` is the transitive closure of `⩿`
* `monotone_iff_forall_wcovBy`: Characterization of monotone functions
* `strictMono_iff_forall_covBy`: Characterization of strictly monotone functions

## TODO

This file was originally only about `Finset.Ico a b` where `a b : ℕ`. No care has yet been taken to
generalize these lemmas properly and many lemmas about `Icc`, `Ioc`, `Ioo` are missing. In general,
what's to do is taking the lemmas in `Data.X.Intervals` and abstract away the concrete structure.

Complete the API. See
https://github.com/leanprover-community/mathlib/pull/14448#discussion_r906109235
for some ideas.
-/

assert_not_exists MonoidWithZero
assert_not_exists Finset.sum

open Function OrderDual

open FinsetInterval

variable {ι α : Type*}

namespace Finset

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b := by
  rw [← coe_nonempty, coe_Icc, Set.nonempty_Icc]
#align finset.nonempty_Icc Finset.nonempty_Icc

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ico, Set.nonempty_Ico]
#align finset.nonempty_Ico Finset.nonempty_Ico

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem nonempty_Ioc : (Ioc a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioc, Set.nonempty_Ioc]
#align finset.nonempty_Ioc Finset.nonempty_Ioc

-- TODO: This is nonsense. A locally finite order is never densely ordered
@[simp]
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b := by
  rw [← coe_nonempty, coe_Ioo, Set.nonempty_Ioo]
#align finset.nonempty_Ioo Finset.nonempty_Ioo

@[simp]
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  rw [← coe_eq_empty, coe_Icc, Set.Icc_eq_empty_iff]
#align finset.Icc_eq_empty_iff Finset.Icc_eq_empty_iff

@[simp]
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ico, Set.Ico_eq_empty_iff]
#align finset.Ico_eq_empty_iff Finset.Ico_eq_empty_iff

@[simp]
theorem Ioc_eq_empty_iff : Ioc a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioc, Set.Ioc_eq_empty_iff]
#align finset.Ioc_eq_empty_iff Finset.Ioc_eq_empty_iff

-- TODO: This is nonsense. A locally finite order is never densely ordered
@[simp]
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  rw [← coe_eq_empty, coe_Ioo, Set.Ioo_eq_empty_iff]
#align finset.Ioo_eq_empty_iff Finset.Ioo_eq_empty_iff

alias ⟨_, Icc_eq_empty⟩ := Icc_eq_empty_iff
#align finset.Icc_eq_empty Finset.Icc_eq_empty

alias ⟨_, Ico_eq_empty⟩ := Ico_eq_empty_iff
#align finset.Ico_eq_empty Finset.Ico_eq_empty

alias ⟨_, Ioc_eq_empty⟩ := Ioc_eq_empty_iff
#align finset.Ioc_eq_empty Finset.Ioc_eq_empty

@[simp]
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_not_mem.2 fun _ hx => h ((mem_Ioo.1 hx).1.trans (mem_Ioo.1 hx).2)
#align finset.Ioo_eq_empty Finset.Ioo_eq_empty

@[simp]
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_le
#align finset.Icc_eq_empty_of_lt Finset.Icc_eq_empty_of_lt

@[simp]
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_lt
#align finset.Ico_eq_empty_of_le Finset.Ico_eq_empty_of_le

@[simp]
theorem Ioc_eq_empty_of_le (h : b ≤ a) : Ioc a b = ∅ :=
  Ioc_eq_empty h.not_lt
#align finset.Ioc_eq_empty_of_le Finset.Ioc_eq_empty_of_le

@[simp]
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_lt
#align finset.Ioo_eq_empty_of_le Finset.Ioo_eq_empty_of_le

-- porting note (#10618): simp can prove this
-- @[simp]
theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, true_and_iff, le_rfl]
#align finset.left_mem_Icc Finset.left_mem_Icc

-- porting note (#10618): simp can prove this
-- @[simp]
theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp only [mem_Ico, true_and_iff, le_refl]
#align finset.left_mem_Ico Finset.left_mem_Ico

-- porting note (#10618): simp can prove this
-- @[simp]
theorem right_mem_Icc : b ∈ Icc a b ↔ a ≤ b := by simp only [mem_Icc, and_true_iff, le_rfl]
#align finset.right_mem_Icc Finset.right_mem_Icc

-- porting note (#10618): simp can prove this
-- @[simp]
theorem right_mem_Ioc : b ∈ Ioc a b ↔ a < b := by simp only [mem_Ioc, and_true_iff, le_rfl]
#align finset.right_mem_Ioc Finset.right_mem_Ioc

-- porting note (#10618): simp can prove this
-- @[simp]
theorem left_not_mem_Ioc : a ∉ Ioc a b := fun h => lt_irrefl _ (mem_Ioc.1 h).1
#align finset.left_not_mem_Ioc Finset.left_not_mem_Ioc

-- porting note (#10618): simp can prove this
-- @[simp]
theorem left_not_mem_Ioo : a ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).1
#align finset.left_not_mem_Ioo Finset.left_not_mem_Ioo

-- porting note (#10618): simp can prove this
-- @[simp]
theorem right_not_mem_Ico : b ∉ Ico a b := fun h => lt_irrefl _ (mem_Ico.1 h).2
#align finset.right_not_mem_Ico Finset.right_not_mem_Ico

-- porting note (#10618): simp can prove this
-- @[simp]
theorem right_not_mem_Ioo : b ∉ Ioo a b := fun h => lt_irrefl _ (mem_Ioo.1 h).2
#align finset.right_not_mem_Ioo Finset.right_not_mem_Ioo

theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := by
  simpa [← coe_subset] using Set.Icc_subset_Icc ha hb
#align finset.Icc_subset_Icc Finset.Icc_subset_Icc

theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := by
  simpa [← coe_subset] using Set.Ico_subset_Ico ha hb
#align finset.Ico_subset_Ico Finset.Ico_subset_Ico

theorem Ioc_subset_Ioc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioc a₁ b₁ ⊆ Ioc a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioc ha hb
#align finset.Ioc_subset_Ioc Finset.Ioc_subset_Ioc

theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioo ha hb
#align finset.Ioo_subset_Ioo Finset.Ioo_subset_Ioo

theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl
#align finset.Icc_subset_Icc_left Finset.Icc_subset_Icc_left

theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl
#align finset.Ico_subset_Ico_left Finset.Ico_subset_Ico_left

theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl
#align finset.Ioc_subset_Ioc_left Finset.Ioc_subset_Ioc_left

theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl
#align finset.Ioo_subset_Ioo_left Finset.Ioo_subset_Ioo_left

theorem Icc_subset_Icc_right (h : b₁ ≤ b₂) : Icc a b₁ ⊆ Icc a b₂ :=
  Icc_subset_Icc le_rfl h
#align finset.Icc_subset_Icc_right Finset.Icc_subset_Icc_right

theorem Ico_subset_Ico_right (h : b₁ ≤ b₂) : Ico a b₁ ⊆ Ico a b₂ :=
  Ico_subset_Ico le_rfl h
#align finset.Ico_subset_Ico_right Finset.Ico_subset_Ico_right

theorem Ioc_subset_Ioc_right (h : b₁ ≤ b₂) : Ioc a b₁ ⊆ Ioc a b₂ :=
  Ioc_subset_Ioc le_rfl h
#align finset.Ioc_subset_Ioc_right Finset.Ioc_subset_Ioc_right

theorem Ioo_subset_Ioo_right (h : b₁ ≤ b₂) : Ioo a b₁ ⊆ Ioo a b₂ :=
  Ioo_subset_Ioo le_rfl h
#align finset.Ioo_subset_Ioo_right Finset.Ioo_subset_Ioo_right

theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b := by
  rw [← coe_subset, coe_Ico, coe_Ioo]
  exact Set.Ico_subset_Ioo_left h
#align finset.Ico_subset_Ioo_left Finset.Ico_subset_Ioo_left

theorem Ioc_subset_Ioo_right (h : b₁ < b₂) : Ioc a b₁ ⊆ Ioo a b₂ := by
  rw [← coe_subset, coe_Ioc, coe_Ioo]
  exact Set.Ioc_subset_Ioo_right h
#align finset.Ioc_subset_Ioo_right Finset.Ioc_subset_Ioo_right

theorem Icc_subset_Ico_right (h : b₁ < b₂) : Icc a b₁ ⊆ Ico a b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico]
  exact Set.Icc_subset_Ico_right h
#align finset.Icc_subset_Ico_right Finset.Icc_subset_Ico_right

theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := by
  rw [← coe_subset, coe_Ioo, coe_Ico]
  exact Set.Ioo_subset_Ico_self
#align finset.Ioo_subset_Ico_self Finset.Ioo_subset_Ico_self

theorem Ioo_subset_Ioc_self : Ioo a b ⊆ Ioc a b := by
  rw [← coe_subset, coe_Ioo, coe_Ioc]
  exact Set.Ioo_subset_Ioc_self
#align finset.Ioo_subset_Ioc_self Finset.Ioo_subset_Ioc_self

theorem Ico_subset_Icc_self : Ico a b ⊆ Icc a b := by
  rw [← coe_subset, coe_Ico, coe_Icc]
  exact Set.Ico_subset_Icc_self
#align finset.Ico_subset_Icc_self Finset.Ico_subset_Icc_self

theorem Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := by
  rw [← coe_subset, coe_Ioc, coe_Icc]
  exact Set.Ioc_subset_Icc_self
#align finset.Ioc_subset_Icc_self Finset.Ioc_subset_Icc_self

theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self
#align finset.Ioo_subset_Icc_self Finset.Ioo_subset_Icc_self

theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Icc, coe_Icc, Set.Icc_subset_Icc_iff h₁]
#align finset.Icc_subset_Icc_iff Finset.Icc_subset_Icc_iff

theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ioo, Set.Icc_subset_Ioo_iff h₁]
#align finset.Icc_subset_Ioo_iff Finset.Icc_subset_Ioo_iff

theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ := by
  rw [← coe_subset, coe_Icc, coe_Ico, Set.Icc_subset_Ico_iff h₁]
#align finset.Icc_subset_Ico_iff Finset.Icc_subset_Ico_iff

theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  (Icc_subset_Ico_iff h₁.dual).trans and_comm
#align finset.Icc_subset_Ioc_iff Finset.Icc_subset_Ioc_iff

--TODO: `Ico_subset_Ioo_iff`, `Ioc_subset_Ioo_iff`
theorem Icc_ssubset_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_left hI ha hb
#align finset.Icc_ssubset_Icc_left Finset.Icc_ssubset_Icc_left

theorem Icc_ssubset_Icc_right (hI : a₂ ≤ b₂) (ha : a₂ ≤ a₁) (hb : b₁ < b₂) :
    Icc a₁ b₁ ⊂ Icc a₂ b₂ := by
  rw [← coe_ssubset, coe_Icc, coe_Icc]
  exact Set.Icc_ssubset_Icc_right hI ha hb
#align finset.Icc_ssubset_Icc_right Finset.Icc_ssubset_Icc_right

variable (a)

-- porting note (#10618): simp can prove this
-- @[simp]
theorem Ico_self : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _
#align finset.Ico_self Finset.Ico_self

-- porting note (#10618): simp can prove this
-- @[simp]
theorem Ioc_self : Ioc a a = ∅ :=
  Ioc_eq_empty <| lt_irrefl _
#align finset.Ioc_self Finset.Ioc_self

-- porting note (#10618): simp can prove this
-- @[simp]
theorem Ioo_self : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _
#align finset.Ioo_self Finset.Ioo_self

variable {a}

/-- A set with upper and lower bounds in a locally finite order is a fintype -/
def _root_.Set.fintypeOfMemBounds {s : Set α} [DecidablePred (· ∈ s)] (ha : a ∈ lowerBounds s)
    (hb : b ∈ upperBounds s) : Fintype s :=
  Set.fintypeSubset (Set.Icc a b) fun _ hx => ⟨ha hx, hb hx⟩
#align set.fintype_of_mem_bounds Set.fintypeOfMemBounds

section Filter

theorem Ico_filter_lt_of_le_left [DecidablePred (· < c)] (hca : c ≤ a) :
    (Ico a b).filter (· < c) = ∅ :=
  filter_false_of_mem fun _ hx => (hca.trans (mem_Ico.1 hx).1).not_lt
#align finset.Ico_filter_lt_of_le_left Finset.Ico_filter_lt_of_le_left

theorem Ico_filter_lt_of_right_le [DecidablePred (· < c)] (hbc : b ≤ c) :
    (Ico a b).filter (· < c) = Ico a b :=
  filter_true_of_mem fun _ hx => (mem_Ico.1 hx).2.trans_le hbc
#align finset.Ico_filter_lt_of_right_le Finset.Ico_filter_lt_of_right_le

theorem Ico_filter_lt_of_le_right [DecidablePred (· < c)] (hcb : c ≤ b) :
    (Ico a b).filter (· < c) = Ico a c := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_right_comm]
  exact and_iff_left_of_imp fun h => h.2.trans_le hcb
#align finset.Ico_filter_lt_of_le_right Finset.Ico_filter_lt_of_le_right

theorem Ico_filter_le_of_le_left {a b c : α} [DecidablePred (c ≤ ·)] (hca : c ≤ a) :
    (Ico a b).filter (c ≤ ·) = Ico a b :=
  filter_true_of_mem fun _ hx => hca.trans (mem_Ico.1 hx).1
#align finset.Ico_filter_le_of_le_left Finset.Ico_filter_le_of_le_left

theorem Ico_filter_le_of_right_le {a b : α} [DecidablePred (b ≤ ·)] :
    (Ico a b).filter (b ≤ ·) = ∅ :=
  filter_false_of_mem fun _ hx => (mem_Ico.1 hx).2.not_le
#align finset.Ico_filter_le_of_right_le Finset.Ico_filter_le_of_right_le

theorem Ico_filter_le_of_left_le {a b c : α} [DecidablePred (c ≤ ·)] (hac : a ≤ c) :
    (Ico a b).filter (c ≤ ·) = Ico c b := by
  ext x
  rw [mem_filter, mem_Ico, mem_Ico, and_comm, and_left_comm]
  exact and_iff_right_of_imp fun h => hac.trans h.1
#align finset.Ico_filter_le_of_left_le Finset.Ico_filter_le_of_left_le

theorem Icc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    (Icc a b).filter (· < c) = Icc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Icc.1 hx).2 h
#align finset.Icc_filter_lt_of_lt_right Finset.Icc_filter_lt_of_lt_right

theorem Ioc_filter_lt_of_lt_right {a b c : α} [DecidablePred (· < c)] (h : b < c) :
    (Ioc a b).filter (· < c) = Ioc a b :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Ioc.1 hx).2 h
#align finset.Ioc_filter_lt_of_lt_right Finset.Ioc_filter_lt_of_lt_right

theorem Iic_filter_lt_of_lt_right {α} [Preorder α] [LocallyFiniteOrderBot α] {a c : α}
    [DecidablePred (· < c)] (h : a < c) : (Iic a).filter (· < c) = Iic a :=
  filter_true_of_mem fun _ hx => lt_of_le_of_lt (mem_Iic.1 hx) h
#align finset.Iic_filter_lt_of_lt_right Finset.Iic_filter_lt_of_lt_right

variable (a b) [Fintype α]

theorem filter_lt_lt_eq_Ioo [DecidablePred fun j => a < j ∧ j < b] :
    (univ.filter fun j => a < j ∧ j < b) = Ioo a b := by
  ext
  simp
#align finset.filter_lt_lt_eq_Ioo Finset.filter_lt_lt_eq_Ioo

theorem filter_lt_le_eq_Ioc [DecidablePred fun j => a < j ∧ j ≤ b] :
    (univ.filter fun j => a < j ∧ j ≤ b) = Ioc a b := by
  ext
  simp
#align finset.filter_lt_le_eq_Ioc Finset.filter_lt_le_eq_Ioc

theorem filter_le_lt_eq_Ico [DecidablePred fun j => a ≤ j ∧ j < b] :
    (univ.filter fun j => a ≤ j ∧ j < b) = Ico a b := by
  ext
  simp
#align finset.filter_le_lt_eq_Ico Finset.filter_le_lt_eq_Ico

theorem filter_le_le_eq_Icc [DecidablePred fun j => a ≤ j ∧ j ≤ b] :
    (univ.filter fun j => a ≤ j ∧ j ≤ b) = Icc a b := by
  ext
  simp
#align finset.filter_le_le_eq_Icc Finset.filter_le_le_eq_Icc

end Filter

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
lemma nonempty_Ici : (Ici a).Nonempty := ⟨a, mem_Ici.2 le_rfl⟩
@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
lemma nonempty_Ioi : (Ioi a).Nonempty ↔ ¬ IsMax a := by simp [Finset.Nonempty]

theorem Icc_subset_Ici_self : Icc a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Icc_subset_Ici_self
#align finset.Icc_subset_Ici_self Finset.Icc_subset_Ici_self

theorem Ico_subset_Ici_self : Ico a b ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ico_subset_Ici_self
#align finset.Ico_subset_Ici_self Finset.Ico_subset_Ici_self

theorem Ioc_subset_Ioi_self : Ioc a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioc_subset_Ioi_self
#align finset.Ioc_subset_Ioi_self Finset.Ioc_subset_Ioi_self

theorem Ioo_subset_Ioi_self : Ioo a b ⊆ Ioi a := by
  simpa [← coe_subset] using Set.Ioo_subset_Ioi_self
#align finset.Ioo_subset_Ioi_self Finset.Ioo_subset_Ioi_self

theorem Ioc_subset_Ici_self : Ioc a b ⊆ Ici a :=
  Ioc_subset_Icc_self.trans Icc_subset_Ici_self
#align finset.Ioc_subset_Ici_self Finset.Ioc_subset_Ici_self

theorem Ioo_subset_Ici_self : Ioo a b ⊆ Ici a :=
  Ioo_subset_Ico_self.trans Ico_subset_Ici_self
#align finset.Ioo_subset_Ici_self Finset.Ioo_subset_Ici_self

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α]

@[simp] lemma nonempty_Iic : (Iic a).Nonempty := ⟨a, mem_Iic.2 le_rfl⟩
@[simp] lemma nonempty_Iio : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [Finset.Nonempty]

theorem Icc_subset_Iic_self : Icc a b ⊆ Iic b := by
  simpa [← coe_subset] using Set.Icc_subset_Iic_self
#align finset.Icc_subset_Iic_self Finset.Icc_subset_Iic_self

theorem Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := by
  simpa [← coe_subset] using Set.Ioc_subset_Iic_self
#align finset.Ioc_subset_Iic_self Finset.Ioc_subset_Iic_self

theorem Ico_subset_Iio_self : Ico a b ⊆ Iio b := by
  simpa [← coe_subset] using Set.Ico_subset_Iio_self
#align finset.Ico_subset_Iio_self Finset.Ico_subset_Iio_self

theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := by
  simpa [← coe_subset] using Set.Ioo_subset_Iio_self
#align finset.Ioo_subset_Iio_self Finset.Ioo_subset_Iio_self

theorem Ico_subset_Iic_self : Ico a b ⊆ Iic b :=
  Ico_subset_Icc_self.trans Icc_subset_Iic_self
#align finset.Ico_subset_Iic_self Finset.Ico_subset_Iic_self

theorem Ioo_subset_Iic_self : Ioo a b ⊆ Iic b :=
  Ioo_subset_Ioc_self.trans Ioc_subset_Iic_self
#align finset.Ioo_subset_Iic_self Finset.Ioo_subset_Iic_self

end LocallyFiniteOrderBot

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α] {a : α}

theorem Ioi_subset_Ici_self : Ioi a ⊆ Ici a := by
  simpa [← coe_subset] using Set.Ioi_subset_Ici_self
#align finset.Ioi_subset_Ici_self Finset.Ioi_subset_Ici_self

theorem _root_.BddBelow.finite {s : Set α} (hs : BddBelow s) : s.Finite :=
  let ⟨a, ha⟩ := hs
  (Ici a).finite_toSet.subset fun _ hx => mem_Ici.2 <| ha hx
#align bdd_below.finite BddBelow.finite

theorem _root_.Set.Infinite.not_bddBelow {s : Set α} : s.Infinite → ¬BddBelow s :=
  mt BddBelow.finite
#align set.infinite.not_bdd_below Set.Infinite.not_bddBelow

variable [Fintype α]

theorem filter_lt_eq_Ioi [DecidablePred (a < ·)] : univ.filter (a < ·) = Ioi a := by
  ext
  simp
#align finset.filter_lt_eq_Ioi Finset.filter_lt_eq_Ioi

theorem filter_le_eq_Ici [DecidablePred (a ≤ ·)] : univ.filter (a ≤ ·) = Ici a := by
  ext
  simp
#align finset.filter_le_eq_Ici Finset.filter_le_eq_Ici

end LocallyFiniteOrderTop

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a : α}

theorem Iio_subset_Iic_self : Iio a ⊆ Iic a := by
  simpa [← coe_subset] using Set.Iio_subset_Iic_self
#align finset.Iio_subset_Iic_self Finset.Iio_subset_Iic_self

theorem _root_.BddAbove.finite {s : Set α} (hs : BddAbove s) : s.Finite :=
  hs.dual.finite
#align bdd_above.finite BddAbove.finite

theorem _root_.Set.Infinite.not_bddAbove {s : Set α} : s.Infinite → ¬BddAbove s :=
  mt BddAbove.finite
#align set.infinite.not_bdd_above Set.Infinite.not_bddAbove

variable [Fintype α]

theorem filter_gt_eq_Iio [DecidablePred (· < a)] : univ.filter (· < a) = Iio a := by
  ext
  simp
#align finset.filter_gt_eq_Iio Finset.filter_gt_eq_Iio

theorem filter_ge_eq_Iic [DecidablePred (· ≤ a)] : univ.filter (· ≤ a) = Iic a := by
  ext
  simp
#align finset.filter_ge_eq_Iic Finset.filter_ge_eq_Iic

end LocallyFiniteOrderBot

variable [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem disjoint_Ioi_Iio (a : α) : Disjoint (Ioi a) (Iio a) :=
  disjoint_left.2 fun _ hab hba => (mem_Ioi.1 hab).not_lt <| mem_Iio.1 hba
#align finset.disjoint_Ioi_Iio Finset.disjoint_Ioi_Iio

end Preorder

section PartialOrder

variable [PartialOrder α] [LocallyFiniteOrder α] {a b c : α}

@[simp]
theorem Icc_self (a : α) : Icc a a = {a} := by rw [← coe_eq_singleton, coe_Icc, Set.Icc_self]
#align finset.Icc_self Finset.Icc_self

@[simp]
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  rw [← coe_eq_singleton, coe_Icc, Set.Icc_eq_singleton_iff]
#align finset.Icc_eq_singleton_iff Finset.Icc_eq_singleton_iff

theorem Ico_disjoint_Ico_consecutive (a b c : α) : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.2 fun _ hab hbc => (mem_Ico.mp hab).2.not_le (mem_Ico.mp hbc).1
#align finset.Ico_disjoint_Ico_consecutive Finset.Ico_disjoint_Ico_consecutive

section DecidableEq

variable [DecidableEq α]

@[simp]
theorem Icc_erase_left (a b : α) : (Icc a b).erase a = Ioc a b := by simp [← coe_inj]
#align finset.Icc_erase_left Finset.Icc_erase_left

@[simp]
theorem Icc_erase_right (a b : α) : (Icc a b).erase b = Ico a b := by simp [← coe_inj]
#align finset.Icc_erase_right Finset.Icc_erase_right

@[simp]
theorem Ico_erase_left (a b : α) : (Ico a b).erase a = Ioo a b := by simp [← coe_inj]
#align finset.Ico_erase_left Finset.Ico_erase_left

@[simp]
theorem Ioc_erase_right (a b : α) : (Ioc a b).erase b = Ioo a b := by simp [← coe_inj]
#align finset.Ioc_erase_right Finset.Ioc_erase_right

@[simp]
theorem Icc_diff_both (a b : α) : Icc a b \ {a, b} = Ioo a b := by simp [← coe_inj]
#align finset.Icc_diff_both Finset.Icc_diff_both

@[simp]
theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Icc, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ico_union_right h]
#align finset.Ico_insert_right Finset.Ico_insert_right

@[simp]
theorem Ioc_insert_left (h : a ≤ b) : insert a (Ioc a b) = Icc a b := by
  rw [← coe_inj, coe_insert, coe_Ioc, coe_Icc, Set.insert_eq, Set.union_comm, Set.Ioc_union_left h]
#align finset.Ioc_insert_left Finset.Ioc_insert_left

@[simp]
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ico, Set.insert_eq, Set.union_comm, Set.Ioo_union_left h]
#align finset.Ioo_insert_left Finset.Ioo_insert_left

@[simp]
theorem Ioo_insert_right (h : a < b) : insert b (Ioo a b) = Ioc a b := by
  rw [← coe_inj, coe_insert, coe_Ioo, coe_Ioc, Set.insert_eq, Set.union_comm, Set.Ioo_union_right h]
#align finset.Ioo_insert_right Finset.Ioo_insert_right

@[simp]
theorem Icc_diff_Ico_self (h : a ≤ b) : Icc a b \ Ico a b = {b} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ico_self Finset.Icc_diff_Ico_self

@[simp]
theorem Icc_diff_Ioc_self (h : a ≤ b) : Icc a b \ Ioc a b = {a} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ioc_self Finset.Icc_diff_Ioc_self

@[simp]
theorem Icc_diff_Ioo_self (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by simp [← coe_inj, h]
#align finset.Icc_diff_Ioo_self Finset.Icc_diff_Ioo_self

@[simp]
theorem Ico_diff_Ioo_self (h : a < b) : Ico a b \ Ioo a b = {a} := by simp [← coe_inj, h]
#align finset.Ico_diff_Ioo_self Finset.Ico_diff_Ioo_self

@[simp]
theorem Ioc_diff_Ioo_self (h : a < b) : Ioc a b \ Ioo a b = {b} := by simp [← coe_inj, h]
#align finset.Ioc_diff_Ioo_self Finset.Ioc_diff_Ioo_self

@[simp]
theorem Ico_inter_Ico_consecutive (a b c : α) : Ico a b ∩ Ico b c = ∅ :=
  (Ico_disjoint_Ico_consecutive a b c).eq_bot
#align finset.Ico_inter_Ico_consecutive Finset.Ico_inter_Ico_consecutive

end DecidableEq

-- Those lemmas are purposefully the other way around

/-- `Finset.cons` version of `Finset.Ico_insert_right`. -/
theorem Icc_eq_cons_Ico (h : a ≤ b) : Icc a b = (Ico a b).cons b right_not_mem_Ico := by
  classical rw [cons_eq_insert, Ico_insert_right h]
#align finset.Icc_eq_cons_Ico Finset.Icc_eq_cons_Ico

/-- `Finset.cons` version of `Finset.Ioc_insert_left`. -/
theorem Icc_eq_cons_Ioc (h : a ≤ b) : Icc a b = (Ioc a b).cons a left_not_mem_Ioc := by
  classical rw [cons_eq_insert, Ioc_insert_left h]
#align finset.Icc_eq_cons_Ioc Finset.Icc_eq_cons_Ioc

/-- `Finset.cons` version of `Finset.Ioo_insert_right`. -/
theorem Ioc_eq_cons_Ioo (h : a < b) : Ioc a b = (Ioo a b).cons b right_not_mem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_right h]
#align finset.Ioc_eq_cons_Ioo Finset.Ioc_eq_cons_Ioo

/-- `Finset.cons` version of `Finset.Ioo_insert_left`. -/
theorem Ico_eq_cons_Ioo (h : a < b) : Ico a b = (Ioo a b).cons a left_not_mem_Ioo := by
  classical rw [cons_eq_insert, Ioo_insert_left h]
#align finset.Ico_eq_cons_Ioo Finset.Ico_eq_cons_Ioo

theorem Ico_filter_le_left {a b : α} [DecidablePred (· ≤ a)] (hab : a < b) :
    ((Ico a b).filter fun x => x ≤ a) = {a} := by
  ext x
  rw [mem_filter, mem_Ico, mem_singleton, and_right_comm, ← le_antisymm_iff, eq_comm]
  exact and_iff_left_of_imp fun h => h.le.trans_lt hab
#align finset.Ico_filter_le_left Finset.Ico_filter_le_left

theorem card_Ico_eq_card_Icc_sub_one (a b : α) : (Ico a b).card = (Icc a b).card - 1 := by
  classical
    by_cases h : a ≤ b
    · rw [Icc_eq_cons_Ico h, card_cons]
      exact (Nat.add_sub_cancel _ _).symm
    · rw [Ico_eq_empty fun h' => h h'.le, Icc_eq_empty h, card_empty, Nat.zero_sub]
#align finset.card_Ico_eq_card_Icc_sub_one Finset.card_Ico_eq_card_Icc_sub_one

theorem card_Ioc_eq_card_Icc_sub_one (a b : α) : (Ioc a b).card = (Icc a b).card - 1 :=
  @card_Ico_eq_card_Icc_sub_one αᵒᵈ _ _ _ _
#align finset.card_Ioc_eq_card_Icc_sub_one Finset.card_Ioc_eq_card_Icc_sub_one

theorem card_Ioo_eq_card_Ico_sub_one (a b : α) : (Ioo a b).card = (Ico a b).card - 1 := by
  classical
    by_cases h : a < b
    · rw [Ico_eq_cons_Ioo h, card_cons]
      exact (Nat.add_sub_cancel _ _).symm
    · rw [Ioo_eq_empty h, Ico_eq_empty h, card_empty, Nat.zero_sub]
#align finset.card_Ioo_eq_card_Ico_sub_one Finset.card_Ioo_eq_card_Ico_sub_one

theorem card_Ioo_eq_card_Ioc_sub_one (a b : α) : (Ioo a b).card = (Ioc a b).card - 1 :=
  @card_Ioo_eq_card_Ico_sub_one αᵒᵈ _ _ _ _
#align finset.card_Ioo_eq_card_Ioc_sub_one Finset.card_Ioo_eq_card_Ioc_sub_one

theorem card_Ioo_eq_card_Icc_sub_two (a b : α) : (Ioo a b).card = (Icc a b).card - 2 := by
  rw [card_Ioo_eq_card_Ico_sub_one, card_Ico_eq_card_Icc_sub_one]
  rfl
#align finset.card_Ioo_eq_card_Icc_sub_two Finset.card_Ioo_eq_card_Icc_sub_two

end PartialOrder

section BoundedPartialOrder

variable [PartialOrder α]

section OrderTop

variable [LocallyFiniteOrderTop α]

@[simp]
theorem Ici_erase [DecidableEq α] (a : α) : (Ici a).erase a = Ioi a := by
  ext
  simp_rw [Finset.mem_erase, mem_Ici, mem_Ioi, lt_iff_le_and_ne, and_comm, ne_comm]
#align finset.Ici_erase Finset.Ici_erase

@[simp]
theorem Ioi_insert [DecidableEq α] (a : α) : insert a (Ioi a) = Ici a := by
  ext
  simp_rw [Finset.mem_insert, mem_Ici, mem_Ioi, le_iff_lt_or_eq, or_comm, eq_comm]
#align finset.Ioi_insert Finset.Ioi_insert

-- porting note (#10618): simp can prove this
-- @[simp]
theorem not_mem_Ioi_self {b : α} : b ∉ Ioi b := fun h => lt_irrefl _ (mem_Ioi.1 h)
#align finset.not_mem_Ioi_self Finset.not_mem_Ioi_self

-- Purposefully written the other way around
/-- `Finset.cons` version of `Finset.Ioi_insert`. -/
theorem Ici_eq_cons_Ioi (a : α) : Ici a = (Ioi a).cons a not_mem_Ioi_self := by
  classical rw [cons_eq_insert, Ioi_insert]
#align finset.Ici_eq_cons_Ioi Finset.Ici_eq_cons_Ioi

theorem card_Ioi_eq_card_Ici_sub_one (a : α) : (Ioi a).card = (Ici a).card - 1 := by
  rw [Ici_eq_cons_Ioi, card_cons, Nat.add_sub_cancel_right]
#align finset.card_Ioi_eq_card_Ici_sub_one Finset.card_Ioi_eq_card_Ici_sub_one

end OrderTop

section OrderBot

variable [LocallyFiniteOrderBot α]

@[simp]
theorem Iic_erase [DecidableEq α] (b : α) : (Iic b).erase b = Iio b := by
  ext
  simp_rw [Finset.mem_erase, mem_Iic, mem_Iio, lt_iff_le_and_ne, and_comm]
#align finset.Iic_erase Finset.Iic_erase

@[simp]
theorem Iio_insert [DecidableEq α] (b : α) : insert b (Iio b) = Iic b := by
  ext
  simp_rw [Finset.mem_insert, mem_Iic, mem_Iio, le_iff_lt_or_eq, or_comm]
#align finset.Iio_insert Finset.Iio_insert

-- porting note (#10618): simp can prove this
-- @[simp]
theorem not_mem_Iio_self {b : α} : b ∉ Iio b := fun h => lt_irrefl _ (mem_Iio.1 h)
#align finset.not_mem_Iio_self Finset.not_mem_Iio_self

-- Purposefully written the other way around
/-- `Finset.cons` version of `Finset.Iio_insert`. -/
theorem Iic_eq_cons_Iio (b : α) : Iic b = (Iio b).cons b not_mem_Iio_self := by
  classical rw [cons_eq_insert, Iio_insert]
#align finset.Iic_eq_cons_Iio Finset.Iic_eq_cons_Iio

theorem card_Iio_eq_card_Iic_sub_one (a : α) : (Iio a).card = (Iic a).card - 1 := by
  rw [Iic_eq_cons_Iio, card_cons, Nat.add_sub_cancel_right]
#align finset.card_Iio_eq_card_Iic_sub_one Finset.card_Iio_eq_card_Iic_sub_one

end OrderBot

end BoundedPartialOrder

section SemilatticeSup
variable [SemilatticeSup α] [LocallyFiniteOrderBot α]

-- TODO: Why does `id_eq` simplify the LHS here but not the LHS of `Finset.sup_Iic`?
lemma sup'_Iic (a : α) : (Iic a).sup' nonempty_Iic id = a :=
  le_antisymm (sup'_le _ _ fun _ ↦ mem_Iic.1) <| le_sup' (f := id) <| mem_Iic.2 <| le_refl a

@[simp] lemma sup_Iic [OrderBot α] (a : α) : (Iic a).sup id = a :=
  le_antisymm (Finset.sup_le fun _ ↦ mem_Iic.1) <| le_sup (f := id) <| mem_Iic.2 <| le_refl a

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [LocallyFiniteOrderTop α]

lemma inf'_Ici (a : α) : (Ici a).inf' nonempty_Ici id = a :=
  ge_antisymm (le_inf' _ _ fun _ ↦ mem_Ici.1) <| inf'_le (f := id) <| mem_Ici.2 <| le_refl a

@[simp] lemma inf_Ici [OrderTop α] (a : α) : (Ici a).inf id = a :=
  le_antisymm (inf_le (f := id) <| mem_Ici.2 <| le_refl a) <| Finset.le_inf fun _ ↦ mem_Ici.1

end SemilatticeInf

section LinearOrder

variable [LinearOrder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α] {a b : α}

theorem Ico_subset_Ico_iff {a₁ b₁ a₂ b₂ : α} (h : a₁ < b₁) :
    Ico a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ := by
  rw [← coe_subset, coe_Ico, coe_Ico, Set.Ico_subset_Ico_iff h]
#align finset.Ico_subset_Ico_iff Finset.Ico_subset_Ico_iff

theorem Ico_union_Ico_eq_Ico {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    Ico a b ∪ Ico b c = Ico a c := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico_eq_Ico hab hbc]
#align finset.Ico_union_Ico_eq_Ico Finset.Ico_union_Ico_eq_Ico

@[simp]
theorem Ioc_union_Ioc_eq_Ioc {a b c : α} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    Ioc a b ∪ Ioc b c = Ioc a c := by
  rw [← coe_inj, coe_union, coe_Ioc, coe_Ioc, coe_Ioc, Set.Ioc_union_Ioc_eq_Ioc h₁ h₂]
#align finset.Ioc_union_Ioc_eq_Ioc Finset.Ioc_union_Ioc_eq_Ioc

theorem Ico_subset_Ico_union_Ico {a b c : α} : Ico a c ⊆ Ico a b ∪ Ico b c := by
  rw [← coe_subset, coe_union, coe_Ico, coe_Ico, coe_Ico]
  exact Set.Ico_subset_Ico_union_Ico
#align finset.Ico_subset_Ico_union_Ico Finset.Ico_subset_Ico_union_Ico

theorem Ico_union_Ico' {a b c d : α} (hcb : c ≤ b) (had : a ≤ d) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico' hcb had]
#align finset.Ico_union_Ico' Finset.Ico_union_Ico'

theorem Ico_union_Ico {a b c d : α} (h₁ : min a b ≤ max c d) (h₂ : min c d ≤ max a b) :
    Ico a b ∪ Ico c d = Ico (min a c) (max b d) := by
  rw [← coe_inj, coe_union, coe_Ico, coe_Ico, coe_Ico, Set.Ico_union_Ico h₁ h₂]
#align finset.Ico_union_Ico Finset.Ico_union_Ico

theorem Ico_inter_Ico {a b c d : α} : Ico a b ∩ Ico c d = Ico (max a c) (min b d) := by
  rw [← coe_inj, coe_inter, coe_Ico, coe_Ico, coe_Ico, ← inf_eq_min, ← sup_eq_max,
    Set.Ico_inter_Ico]
#align finset.Ico_inter_Ico Finset.Ico_inter_Ico

@[simp]
theorem Ico_filter_lt (a b c : α) : ((Ico a b).filter fun x => x < c) = Ico a (min b c) := by
  cases le_total b c with
  | inl h => rw [Ico_filter_lt_of_right_le h, min_eq_left h]
  | inr h => rw [Ico_filter_lt_of_le_right h, min_eq_right h]
#align finset.Ico_filter_lt Finset.Ico_filter_lt

@[simp]
theorem Ico_filter_le (a b c : α) : ((Ico a b).filter fun x => c ≤ x) = Ico (max a c) b := by
  cases le_total a c with
  | inl h => rw [Ico_filter_le_of_left_le h, max_eq_right h]
  | inr h => rw [Ico_filter_le_of_le_left h, max_eq_left h]
#align finset.Ico_filter_le Finset.Ico_filter_le

@[simp]
theorem Ioo_filter_lt (a b c : α) : (Ioo a b).filter (· < c) = Ioo a (min b c) := by
  ext
  simp [and_assoc]
#align finset.Ioo_filter_lt Finset.Ioo_filter_lt

@[simp]
theorem Iio_filter_lt {α} [LinearOrder α] [LocallyFiniteOrderBot α] (a b : α) :
    (Iio a).filter (· < b) = Iio (min a b) := by
  ext
  simp [and_assoc]
#align finset.Iio_filter_lt Finset.Iio_filter_lt

@[simp]
theorem Ico_diff_Ico_left (a b c : α) : Ico a b \ Ico a c = Ico (max a c) b := by
  cases le_total a c with
  | inl h =>
    ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, max_eq_right h, and_right_comm, not_and, not_lt]
    exact and_congr_left' ⟨fun hx => hx.2 hx.1, fun hx => ⟨h.trans hx, fun _ => hx⟩⟩
  | inr h => rw [Ico_eq_empty_of_le h, sdiff_empty, max_eq_left h]
#align finset.Ico_diff_Ico_left Finset.Ico_diff_Ico_left

@[simp]
theorem Ico_diff_Ico_right (a b c : α) : Ico a b \ Ico c b = Ico a (min b c) := by
  cases le_total b c with
  | inl h => rw [Ico_eq_empty_of_le h, sdiff_empty, min_eq_left h]
  | inr h =>
    ext x
    rw [mem_sdiff, mem_Ico, mem_Ico, mem_Ico, min_eq_right h, and_assoc, not_and', not_le]
    exact and_congr_right' ⟨fun hx => hx.2 hx.1, fun hx => ⟨hx.trans_le h, fun _ => hx⟩⟩
#align finset.Ico_diff_Ico_right Finset.Ico_diff_Ico_right

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [LocallyFiniteOrderBot α] {s : Set α}

theorem _root_.Set.Infinite.exists_gt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, a < b :=
  not_bddAbove_iff.1 hs.not_bddAbove
#align set.infinite.exists_gt Set.Infinite.exists_gt

theorem _root_.Set.infinite_iff_exists_gt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, a < b :=
  ⟨Set.Infinite.exists_gt, Set.infinite_of_forall_exists_gt⟩
#align set.infinite_iff_exists_gt Set.infinite_iff_exists_gt

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [LocallyFiniteOrderTop α] {s : Set α}

theorem _root_.Set.Infinite.exists_lt (hs : s.Infinite) : ∀ a, ∃ b ∈ s, b < a :=
  not_bddBelow_iff.1 hs.not_bddBelow
#align set.infinite.exists_lt Set.Infinite.exists_lt

theorem _root_.Set.infinite_iff_exists_lt [Nonempty α] : s.Infinite ↔ ∀ a, ∃ b ∈ s, b < a :=
  ⟨Set.Infinite.exists_lt, Set.infinite_of_forall_exists_lt⟩
#align set.infinite_iff_exists_lt Set.infinite_iff_exists_lt

end LocallyFiniteOrderTop

variable [Fintype α] [LocallyFiniteOrderTop α] [LocallyFiniteOrderBot α]

theorem Ioi_disjUnion_Iio (a : α) :
    (Ioi a).disjUnion (Iio a) (disjoint_Ioi_Iio a) = ({a} : Finset α)ᶜ := by
  ext
  simp [eq_comm]
#align finset.Ioi_disj_union_Iio Finset.Ioi_disjUnion_Iio

end LinearOrder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

theorem uIcc_toDual (a b : α) : [[toDual a, toDual b]] = [[a, b]].map toDual.toEmbedding :=
  Icc_toDual _ _
#align finset.uIcc_to_dual Finset.uIcc_toDual

@[simp]
theorem uIcc_of_le (h : a ≤ b) : [[a, b]] = Icc a b := by
  rw [uIcc, inf_eq_left.2 h, sup_eq_right.2 h]
#align finset.uIcc_of_le Finset.uIcc_of_le

@[simp]
theorem uIcc_of_ge (h : b ≤ a) : [[a, b]] = Icc b a := by
  rw [uIcc, inf_eq_right.2 h, sup_eq_left.2 h]
#align finset.uIcc_of_ge Finset.uIcc_of_ge

theorem uIcc_comm (a b : α) : [[a, b]] = [[b, a]] := by
  rw [uIcc, uIcc, inf_comm, sup_comm]
#align finset.uIcc_comm Finset.uIcc_comm

-- porting note (#10618): simp can prove this
-- @[simp]
theorem uIcc_self : [[a, a]] = {a} := by simp [uIcc]
#align finset.uIcc_self Finset.uIcc_self

@[simp]
theorem nonempty_uIcc : Finset.Nonempty [[a, b]] :=
  nonempty_Icc.2 inf_le_sup
#align finset.nonempty_uIcc Finset.nonempty_uIcc

theorem Icc_subset_uIcc : Icc a b ⊆ [[a, b]] :=
  Icc_subset_Icc inf_le_left le_sup_right
#align finset.Icc_subset_uIcc Finset.Icc_subset_uIcc

theorem Icc_subset_uIcc' : Icc b a ⊆ [[a, b]] :=
  Icc_subset_Icc inf_le_right le_sup_left
#align finset.Icc_subset_uIcc' Finset.Icc_subset_uIcc'

-- porting note (#10618): simp can prove this
-- @[simp]
theorem left_mem_uIcc : a ∈ [[a, b]] :=
  mem_Icc.2 ⟨inf_le_left, le_sup_left⟩
#align finset.left_mem_uIcc Finset.left_mem_uIcc

-- porting note (#10618): simp can prove this
-- @[simp]
theorem right_mem_uIcc : b ∈ [[a, b]] :=
  mem_Icc.2 ⟨inf_le_right, le_sup_right⟩
#align finset.right_mem_uIcc Finset.right_mem_uIcc

theorem mem_uIcc_of_le (ha : a ≤ x) (hb : x ≤ b) : x ∈ [[a, b]] :=
  Icc_subset_uIcc <| mem_Icc.2 ⟨ha, hb⟩
#align finset.mem_uIcc_of_le Finset.mem_uIcc_of_le

theorem mem_uIcc_of_ge (hb : b ≤ x) (ha : x ≤ a) : x ∈ [[a, b]] :=
  Icc_subset_uIcc' <| mem_Icc.2 ⟨hb, ha⟩
#align finset.mem_uIcc_of_ge Finset.mem_uIcc_of_ge

theorem uIcc_subset_uIcc (h₁ : a₁ ∈ [[a₂, b₂]]) (h₂ : b₁ ∈ [[a₂, b₂]]) :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] := by
  rw [mem_uIcc] at h₁ h₂
  exact Icc_subset_Icc (_root_.le_inf h₁.1 h₂.1) (_root_.sup_le h₁.2 h₂.2)
#align finset.uIcc_subset_uIcc Finset.uIcc_subset_uIcc

theorem uIcc_subset_Icc (ha : a₁ ∈ Icc a₂ b₂) (hb : b₁ ∈ Icc a₂ b₂) : [[a₁, b₁]] ⊆ Icc a₂ b₂ := by
  rw [mem_Icc] at ha hb
  exact Icc_subset_Icc (_root_.le_inf ha.1 hb.1) (_root_.sup_le ha.2 hb.2)
#align finset.uIcc_subset_Icc Finset.uIcc_subset_Icc

theorem uIcc_subset_uIcc_iff_mem : [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₁ ∈ [[a₂, b₂]] ∧ b₁ ∈ [[a₂, b₂]] :=
  ⟨fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩, fun h => uIcc_subset_uIcc h.1 h.2⟩
#align finset.uIcc_subset_uIcc_iff_mem Finset.uIcc_subset_uIcc_iff_mem

theorem uIcc_subset_uIcc_iff_le' :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ a₂ ⊓ b₂ ≤ a₁ ⊓ b₁ ∧ a₁ ⊔ b₁ ≤ a₂ ⊔ b₂ :=
  Icc_subset_Icc_iff inf_le_sup
#align finset.uIcc_subset_uIcc_iff_le' Finset.uIcc_subset_uIcc_iff_le'

theorem uIcc_subset_uIcc_right (h : x ∈ [[a, b]]) : [[x, b]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc h right_mem_uIcc
#align finset.uIcc_subset_uIcc_right Finset.uIcc_subset_uIcc_right

theorem uIcc_subset_uIcc_left (h : x ∈ [[a, b]]) : [[a, x]] ⊆ [[a, b]] :=
  uIcc_subset_uIcc left_mem_uIcc h
#align finset.uIcc_subset_uIcc_left Finset.uIcc_subset_uIcc_left

end Lattice

section DistribLattice

variable [DistribLattice α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

theorem eq_of_mem_uIcc_of_mem_uIcc : a ∈ [[b, c]] → b ∈ [[a, c]] → a = b := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc
#align finset.eq_of_mem_uIcc_of_mem_uIcc Finset.eq_of_mem_uIcc_of_mem_uIcc

theorem eq_of_mem_uIcc_of_mem_uIcc' : b ∈ [[a, c]] → c ∈ [[a, b]] → b = c := by
  simp_rw [mem_uIcc]
  exact Set.eq_of_mem_uIcc_of_mem_uIcc'
#align finset.eq_of_mem_uIcc_of_mem_uIcc' Finset.eq_of_mem_uIcc_of_mem_uIcc'

theorem uIcc_injective_right (a : α) : Injective fun b => [[b, a]] := fun b c h => by
  rw [ext_iff] at h
  exact eq_of_mem_uIcc_of_mem_uIcc ((h _).1 left_mem_uIcc) ((h _).2 left_mem_uIcc)
#align finset.uIcc_injective_right Finset.uIcc_injective_right

theorem uIcc_injective_left (a : α) : Injective (uIcc a) := by
  simpa only [uIcc_comm] using uIcc_injective_right a
#align finset.uIcc_injective_left Finset.uIcc_injective_left

end DistribLattice

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α] {a a₁ a₂ b b₁ b₂ c x : α}

theorem Icc_min_max : Icc (min a b) (max a b) = [[a, b]] :=
  rfl
#align finset.Icc_min_max Finset.Icc_min_max

theorem uIcc_of_not_le (h : ¬a ≤ b) : [[a, b]] = Icc b a :=
  uIcc_of_ge <| le_of_not_ge h
#align finset.uIcc_of_not_le Finset.uIcc_of_not_le

theorem uIcc_of_not_ge (h : ¬b ≤ a) : [[a, b]] = Icc a b :=
  uIcc_of_le <| le_of_not_ge h
#align finset.uIcc_of_not_ge Finset.uIcc_of_not_ge

theorem uIcc_eq_union : [[a, b]] = Icc a b ∪ Icc b a :=
  coe_injective <| by
    push_cast
    exact Set.uIcc_eq_union
#align finset.uIcc_eq_union Finset.uIcc_eq_union

theorem mem_uIcc' : a ∈ [[b, c]] ↔ b ≤ a ∧ a ≤ c ∨ c ≤ a ∧ a ≤ b := by simp [uIcc_eq_union]
#align finset.mem_uIcc' Finset.mem_uIcc'

theorem not_mem_uIcc_of_lt : c < a → c < b → c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.not_mem_uIcc_of_lt
#align finset.not_mem_uIcc_of_lt Finset.not_mem_uIcc_of_lt

theorem not_mem_uIcc_of_gt : a < c → b < c → c ∉ [[a, b]] := by
  rw [mem_uIcc]
  exact Set.not_mem_uIcc_of_gt
#align finset.not_mem_uIcc_of_gt Finset.not_mem_uIcc_of_gt

theorem uIcc_subset_uIcc_iff_le :
    [[a₁, b₁]] ⊆ [[a₂, b₂]] ↔ min a₂ b₂ ≤ min a₁ b₁ ∧ max a₁ b₁ ≤ max a₂ b₂ :=
  uIcc_subset_uIcc_iff_le'
#align finset.uIcc_subset_uIcc_iff_le Finset.uIcc_subset_uIcc_iff_le

/-- A sort of triangle inequality. -/
theorem uIcc_subset_uIcc_union_uIcc : [[a, c]] ⊆ [[a, b]] ∪ [[b, c]] :=
  coe_subset.1 <| by
    push_cast
    exact Set.uIcc_subset_uIcc_union_uIcc
#align finset.uIcc_subset_uIcc_union_uIcc Finset.uIcc_subset_uIcc_union_uIcc

end LinearOrder
end Finset

/-! ### `⩿`, `⋖` and monotonicity -/

section Cover

open Finset Relation

set_option linter.unusedVariables false in -- `have` for wf induction triggers linter
lemma transGen_wcovBy_of_le [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x ≤ y) :
    TransGen (· ⩿ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Icc x y`.
  -- It's impossible for the cardinality to be zero since `x ≤ y`
  have : (Ico x y).card < (Icc x y).card := card_lt_card <|
    ⟨Ico_subset_Icc_self, not_subset.mpr ⟨y, ⟨right_mem_Icc.mpr hxy, right_not_mem_Ico⟩⟩⟩
  by_cases hxy' : y ≤ x
  -- If `y ≤ x`, then `x ⩿ y`
  · exact .single <| wcovBy_of_le_of_le hxy hxy'
  /- and if `¬ y ≤ x`, then `x < y`, not because it is a linear order, but because `x ≤ y`
  already. In that case, since `z` is maximal in `Ico x y`, then `z ⩿ y` and we can use the
  induction hypothesis to show that `Relation.TransGen (· ⩿ ·) x z`. -/
  · have h_non : (Ico x y).Nonempty := ⟨x, mem_Ico.mpr ⟨le_rfl, lt_of_le_not_le hxy hxy'⟩⟩
    obtain ⟨z, z_mem, hz⟩ := (Ico x y).exists_maximal h_non
    have z_card : (Icc x z).card <(Icc x y).card := calc
      (Icc x z).card ≤ (Ico x y).card :=
        card_le_card <| Icc_subset_Ico_right (mem_Ico.mp z_mem).2
      _              < (Icc x y).card := this
    have h₁ := transGen_wcovBy_of_le (mem_Ico.mp z_mem).1
    have h₂ : z ⩿ y := by
      refine ⟨(mem_Ico.mp z_mem).2.le, fun c hzc hcy ↦ hz c ?_ hzc⟩
      exact mem_Ico.mpr <| ⟨(mem_Ico.mp z_mem).1.trans hzc.le, hcy⟩
    exact .tail h₁ h₂
termination_by (Icc x y).card

/-- In a locally finite preorder, `≤` is the transitive closure of `⩿`. -/
lemma le_iff_transGen_wcovBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x ≤ y ↔ TransGen (· ⩿ ·) x y := by
  refine ⟨transGen_wcovBy_of_le, fun h ↦ ?_⟩
  induction h with
  | single h => exact h.le
  | tail _ h₁ h₂ => exact h₂.trans h₁.le

/-- In a locally finite partial order, `≤` is the reflexive transitive closure of `⋖`. -/
lemma le_iff_reflTransGen_covBy [PartialOrder α] [LocallyFiniteOrder α] {x y : α} :
    x ≤ y ↔ ReflTransGen (· ⋖ ·) x y := by
  rw [le_iff_transGen_wcovBy, wcovBy_eq_reflGen_covBy, transGen_reflGen]

set_option linter.unusedVariables false in -- `have` for wf induction triggers linter
lemma transGen_covBy_of_lt [Preorder α] [LocallyFiniteOrder α] {x y : α} (hxy : x < y) :
    TransGen (· ⋖ ·) x y := by
  -- We proceed by well-founded induction on the cardinality of `Ico x y`.
  -- It's impossible for the cardinality to be zero since `x < y`
  have h_non : (Ico x y).Nonempty := ⟨x, mem_Ico.mpr ⟨le_rfl, hxy⟩⟩
  -- `Ico x y` is a nonempty finset and so contains a maximal element `z` and
  -- `Ico x z` has cardinality strictly less than the cardinality of `Ico x y`
  obtain ⟨z, z_mem, hz⟩ := (Ico x y).exists_maximal h_non
  have z_card : (Ico x z).card < (Ico x y).card := card_lt_card <| ssubset_iff_of_subset
    (Ico_subset_Ico le_rfl (mem_Ico.mp z_mem).2.le) |>.mpr ⟨z, z_mem, right_not_mem_Ico⟩
  /- Since `z` is maximal in `Ico x y`, `z ⋖ y`. -/
  have hzy : z ⋖ y := by
    refine ⟨(mem_Ico.mp z_mem).2, fun c hc hcy ↦ ?_⟩
    exact hz _ (mem_Ico.mpr ⟨((mem_Ico.mp z_mem).1.trans_lt hc).le, hcy⟩) hc
  by_cases hxz : x < z
  /- when `x < z`, then we may use the induction hypothesis to get a chain
  `Relation.TransGen (· ⋖ ·) x z`, which we can extend with `Relation.TransGen.tail`. -/
  · exact .tail (transGen_covBy_of_lt hxz) hzy
  /- when `¬ x < z`, then actually `z ≤ x` (not because it's a linear order, but because
  `x ≤ z`), and since `z ⋖ y` we conclude that `x ⋖ y` , then `Relation.TransGen.single`. -/
  · simp only [lt_iff_le_not_le, not_and, not_not] at hxz
    exact .single (hzy.of_le_of_lt (hxz (mem_Ico.mp z_mem).1) hxy)
termination_by (Ico x y).card

/-- In a locally finite preorder, `<` is the transitive closure of `⋖`. -/
lemma lt_iff_transGen_covBy [Preorder α] [LocallyFiniteOrder α] {x y : α} :
    x < y ↔ TransGen (· ⋖ ·) x y := by
  refine ⟨transGen_covBy_of_lt, fun h ↦ ?_⟩
  induction h with
  | single hx => exact hx.1
  | tail _ hb ih => exact ih.trans hb.1

variable {β : Type*}

/-- A function from a locally finite preorder is monotone if and only if it is monotone when
restricted to pairs satisfying `a ⩿ b`. -/
lemma monotone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Monotone f ↔ ∀ a b : α, a ⩿ b → f a ≤ f b := by
  refine ⟨fun hf _ _ h ↦ hf h.le, fun h a b hab ↦ ?_⟩
  simpa [transGen_eq_self (r := ((· : β) ≤ ·)) transitive_le]
    using TransGen.lift f h <| le_iff_transGen_wcovBy.mp hab

/-- A function from a locally finite partial order is monotone if and only if it is monotone when
restricted to pairs satisfying `a ⋖ b`. -/
lemma monotone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Monotone f ↔ ∀ a b : α, a ⋖ b → f a ≤ f b := by
  refine ⟨fun hf _ _ h ↦ hf h.le, fun h a b hab ↦ ?_⟩
  simpa [reflTransGen_eq_self (r := ((· : β) ≤ ·)) IsRefl.reflexive transitive_le]
    using ReflTransGen.lift f h <| le_iff_reflTransGen_covBy.mp hab

/-- A function from a locally finite preorder is strictly monotone if and only if it is strictly
monotone when restricted to pairs satisfying `a ⋖ b`. -/
lemma strictMono_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : StrictMono f ↔ ∀ a b : α, a ⋖ b → f a < f b := by
  refine ⟨fun hf _ _ h ↦ hf h.lt, fun h a b hab ↦ ?_⟩
  have := Relation.TransGen.lift f h (a := a) (b := b)
  rw [← lt_iff_transGen_covBy, transGen_eq_self (@lt_trans β _)] at this
  exact this hab

/-- A function from a locally finite preorder is antitone if and only if it is antitone when
restricted to pairs satisfying `a ⩿ b`. -/
lemma antitone_iff_forall_wcovBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Antitone f ↔ ∀ a b : α, a ⩿ b → f b ≤ f a :=
  monotone_iff_forall_wcovBy (β := βᵒᵈ) f

/-- A function from a locally finite partial order is antitone if and only if it is antitone when
restricted to pairs satisfying `a ⋖ b`. -/
lemma antitone_iff_forall_covBy [PartialOrder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : Antitone f ↔ ∀ a b : α, a ⋖ b → f b ≤ f a :=
  monotone_iff_forall_covBy (β := βᵒᵈ) f

/-- A function from a locally finite preorder is strictly antitone if and only if it is strictly
antitone when restricted to pairs satisfying `a ⋖ b`. -/
lemma strictAnti_iff_forall_covBy [Preorder α] [LocallyFiniteOrder α] [Preorder β]
    (f : α → β) : StrictAnti f ↔ ∀ a b : α, a ⋖ b → f b < f a :=
  strictMono_iff_forall_covBy (β := βᵒᵈ) f

end Cover
