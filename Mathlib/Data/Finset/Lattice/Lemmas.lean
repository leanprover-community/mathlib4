/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Lemmas about the lattice structure of finite sets

This file contains many results on the lattice structure of `Finset α`, in particular the
interaction between union, intersection, empty set and inserting elements.

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice Monoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

/-! #### union -/

@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| by simp

@[simp]
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext fun x => mem_union.trans <| by simp

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.inl {s t : Finset α} (h : s.Nonempty) : (s ∪ t).Nonempty :=
  h.mono subset_union_left

@[aesop unsafe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.inr {s t : Finset α} (h : t.Nonempty) : (s ∪ t).Nonempty :=
  h.mono subset_union_right

theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl

@[simp]
lemma singleton_union (x : α) (s : Finset α) : {x} ∪ s = insert x s :=
  rfl

@[simp]
lemma union_singleton (x : α) (s : Finset α) : s ∪ {x} = insert x s := by
  rw [Finset.union_comm, singleton_union]

@[simp]
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) := by
  simp only [insert_eq, union_assoc]

@[simp]
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  simp only [insert_eq, union_left_comm]

theorem insert_union_distrib (a : α) (s t : Finset α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by
  simp only [insert_union, union_insert, insert_idem]

/-- To prove a relation on pairs of `Finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `Finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union (P : Finset α → Finset α → Prop) (symm : ∀ {a b}, P a b → P b a)
    (empty_right : ∀ {a}, P a ∅) (singletons : ∀ {a b}, P {a} {b})
    (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) : ∀ a b, P a b := by
  intro a b
  refine Finset.induction_on b empty_right fun x s _xs hi => symm ?_
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine Finset.induction_on a empty_right fun a t _ta hi => symm ?_
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)

/-! #### inter -/

@[simp]
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext fun _ => mem_inter.trans <| by simp

@[simp]
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext fun _ => mem_inter.trans <| by simp

@[simp]
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) :
    insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext fun x => by
    have : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ := or_iff_right_of_imp <| by rintro rfl; exact h
    simp only [mem_inter, mem_insert, or_and_left, this]

@[simp]
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) :
    s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) := by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]
theorem insert_inter_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) :
    insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x ∈ s₂) := by rintro ⟨rfl, H⟩; exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or]

@[deprecated (since := "2025-05-23")] alias insert_inter_of_not_mem := insert_inter_of_notMem

@[simp]
theorem inter_insert_of_notMem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) :
    s₁ ∩ insert a s₂ = s₁ ∩ s₂ := by rw [inter_comm, insert_inter_of_notMem h, inter_comm]

@[deprecated (since := "2025-05-23")] alias inter_insert_of_not_mem := inter_insert_of_notMem

@[simp]
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]

@[simp]
theorem singleton_inter_of_notMem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_notMem <| by
    simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[deprecated (since := "2025-05-23")] alias singleton_inter_of_not_mem := singleton_inter_of_notMem

lemma singleton_inter {a : α} {s : Finset α} :
    {a} ∩ s = if a ∈ s then {a} else ∅ := by
  split_ifs with h <;> simp [h]

@[simp]
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} := by
  rw [inter_comm, singleton_inter_of_mem h]

@[simp]
theorem inter_singleton_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ := by
  rw [inter_comm, singleton_inter_of_notMem h]

@[deprecated (since := "2025-05-23")] alias inter_singleton_of_not_mem := inter_singleton_of_notMem

lemma inter_singleton {a : α} {s : Finset α} :
    s ∩ {a} = if a ∈ s then {a} else ∅ := by
  split_ifs with h <;> simp [h]

@[simp] lemma union_eq_empty : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := sup_eq_bot_iff
@[simp] lemma union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  mod_cast Set.union_nonempty (α := α) (s := s) (t := t)

theorem insert_union_comm (s t : Finset α) (a : α) : insert a s ∪ t = s ∪ insert a t := by
  rw [insert_union, union_insert]

end Lattice

end Finset

namespace List

variable [DecidableEq α] {l l' : List α}

@[simp]
theorem toFinset_append : toFinset (l ++ l') = l.toFinset ∪ l'.toFinset := by
  induction l with
  | nil => simp
  | cons hd tl hl => simp [hl]

end List
