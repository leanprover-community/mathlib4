/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
Kim Morrison
-/
import Mathlib.Data.List.Basic

/-!
# Lattice structure of lists

This files prove basic properties about `List.disjoint`, `List.union`, `List.inter` and
`List.bagInter`, which are defined in core Lean and `Data.List.Defs`.

`l₁ ∪ l₂` is the list where all elements of `l₁` have been inserted in `l₂` in order. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [1, 2, 4, 3, 3, 0]`

`l₁ ∩ l₂` is the list of elements of `l₁` in order which are in `l₂`. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [0, 0, 3]`

`List.bagInter l₁ l₂` is the list of elements that are in both `l₁` and `l₂`,
counted with multiplicity and in the order they appear in `l₁`.
As opposed to `List.inter`, `List.bagInter` copes well with multiplicity. For example,
`bagInter [0, 1, 2, 3, 2, 1, 0] [1, 0, 1, 4, 3] = [0, 1, 3, 1]`
-/


open Nat

namespace List

variable {α : Type*} {l₁ l₂ : List α} {p : α → Prop} {a : α}

/-! ### `Disjoint` -/


section Disjoint

@[symm]
theorem Disjoint.symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂

end Disjoint

variable [DecidableEq α]

/-! ### `union` -/


section Union

theorem mem_union_left (h : a ∈ l₁) (l₂ : List α) : a ∈ l₁ ∪ l₂ :=
  mem_union_iff.2 (Or.inl h)

theorem mem_union_right (l₁ : List α) (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
  mem_union_iff.2 (Or.inr h)

theorem sublist_suffix_of_union : ∀ l₁ l₂ : List α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
  | [], _ => ⟨[], by rfl, rfl⟩
  | a :: l₁, l₂ =>
    let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
    if h : a ∈ l₁ ∪ l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [e, cons_union, insert_of_mem h]⟩
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩

theorem suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁ ∪ l₂ :=
  (sublist_suffix_of_union l₁ l₂).imp fun _ => And.right

theorem union_sublist_append (l₁ l₂ : List α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
  let ⟨_, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s

theorem forall_mem_union : (∀ x ∈ l₁ ∪ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ ∀ x ∈ l₂, p x := by
  simp only [mem_union_iff, or_imp, forall_and]

theorem forall_mem_of_forall_mem_union_left (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₁, p x :=
  (forall_mem_union.1 h).1

theorem forall_mem_of_forall_mem_union_right (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₂, p x :=
  (forall_mem_union.1 h).2

theorem Subset.union_eq_right {xs ys : List α} (h : xs ⊆ ys) : xs ∪ ys = ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union, insert_of_mem <| mem_union_right _ <| h mem_cons_self,
      ih <| subset_of_cons_subset h]

end Union

/-! ### `inter` -/


section Inter

@[simp]
theorem inter_nil (l : List α) : [] ∩ l = [] :=
  rfl

@[simp]
theorem inter_cons_of_mem (l₁ : List α) (h : a ∈ l₂) : (a :: l₁) ∩ l₂ = a :: l₁ ∩ l₂ := by
  simp [Inter.inter, List.inter, h]

@[simp]
theorem inter_cons_of_notMem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁) ∩ l₂ = l₁ ∩ l₂ := by
  simp [Inter.inter, List.inter, h]

@[deprecated (since := "2025-05-23")] alias inter_cons_of_not_mem := inter_cons_of_notMem

@[simp]
theorem inter_nil' (l : List α) : l ∩ [] = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih => by_cases x ∈ xs <;> simp [ih]

theorem mem_of_mem_inter_left : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
  mem_of_mem_filter

theorem mem_of_mem_inter_right (h : a ∈ l₁ ∩ l₂) : a ∈ l₂ := by simpa using of_mem_filter h

theorem mem_inter_of_mem_of_mem (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) : a ∈ l₁ ∩ l₂ :=
  mem_filter_of_mem h₁ <| by simpa using h₂

theorem inter_subset_left {l₁ l₂ : List α} : l₁ ∩ l₂ ⊆ l₁ :=
  filter_subset' _

theorem inter_subset_right {l₁ l₂ : List α} : l₁ ∩ l₂ ⊆ l₂ := fun _ => mem_of_mem_inter_right

theorem subset_inter {l l₁ l₂ : List α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ := fun _ h =>
  mem_inter_iff.2 ⟨h₁ h, h₂ h⟩

theorem inter_eq_nil_iff_disjoint : l₁ ∩ l₂ = [] ↔ Disjoint l₁ l₂ := by
  simp only [eq_nil_iff_forall_not_mem, mem_inter_iff, not_and]
  rfl

alias ⟨_, Disjoint.inter_eq_nil⟩ := inter_eq_nil_iff_disjoint

theorem forall_mem_inter_of_forall_left (h : ∀ x ∈ l₁, p x) (l₂ : List α) :
    ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_left) h

theorem forall_mem_inter_of_forall_right (l₁ : List α) (h : ∀ x ∈ l₂, p x) :
    ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_right) h

@[simp]
theorem inter_reverse {xs ys : List α} : xs.inter ys.reverse = xs.inter ys := by
  simp only [List.inter, elem_eq_mem, mem_reverse]

theorem Subset.inter_eq_left {xs ys : List α} (h : xs ⊆ ys) : xs ∩ ys = xs :=
  List.filter_eq_self.mpr fun _ ha => elem_eq_true_of_mem (h ha)

end Inter

/-! ### `bagInter` -/


section BagInter

@[simp]
theorem nil_bagInter (l : List α) : [].bagInter l = [] := by cases l <;> rfl

@[simp]
theorem bagInter_nil (l : List α) : l.bagInter [] = [] := by cases l <;> rfl

@[simp]
theorem cons_bagInter_of_pos (l₁ : List α) (h : a ∈ l₂) :
    (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := by
  cases l₂
  · exact if_pos h
  · simp only [List.bagInter, if_pos (elem_eq_true_of_mem h)]

@[simp]
theorem cons_bagInter_of_neg (l₁ : List α) (h : a ∉ l₂) :
    (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := by
  cases l₂; · simp only [bagInter_nil]
  simp only [erase_of_not_mem h, List.bagInter, if_neg (mt mem_of_elem_eq_true h)]

@[simp]
theorem mem_bagInter {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁.bagInter l₂ ↔ a ∈ l₁ ∧ a ∈ l₂
  | [], l₂ => by simp only [nil_bagInter, not_mem_nil, false_and]
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂
    · rw [cons_bagInter_of_pos _ h, mem_cons, mem_cons, mem_bagInter]
      by_cases ba : a = b
      · simp only [ba, h, true_or, true_and]
      · simp only [mem_erase_of_ne ba, ba, false_or]
    · rw [cons_bagInter_of_neg _ h, mem_bagInter, mem_cons, or_and_right]
      symm
      apply or_iff_right_of_imp
      rintro ⟨rfl, h'⟩
      exact h.elim h'

@[simp]
theorem count_bagInter {a : α} :
    ∀ {l₁ l₂ : List α}, count a (l₁.bagInter l₂) = min (count a l₁) (count a l₂)
  | [], l₂ => by simp
  | l₁, [] => by simp
  | b :: l₁, l₂ => by
    by_cases hb : b ∈ l₂
    · rw [cons_bagInter_of_pos _ hb, count_cons, count_cons, count_bagInter, count_erase,
        ← Nat.add_min_add_right]
      by_cases ba : b = a
      · simp only [beq_iff_eq]
        rw [if_pos ba, Nat.sub_add_cancel]
        rwa [succ_le_iff, count_pos_iff, ← ba]
      · simp only [beq_iff_eq]
        rw [if_neg ba, Nat.sub_zero, Nat.add_zero, Nat.add_zero]
    · rw [cons_bagInter_of_neg _ hb, count_bagInter]
      by_cases ab : a = b
      · rw [← ab] at hb
        rw [count_eq_zero.2 hb, Nat.min_zero, Nat.min_zero]
      · rw [count_cons_of_ne (Ne.symm ab)]

theorem bagInter_sublist_left : ∀ l₁ l₂ : List α, l₁.bagInter l₂ <+ l₁
  | [], l₂ => by simp
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂ <;> simp only [h, cons_bagInter_of_pos, cons_bagInter_of_neg, not_false_iff]
    · exact (bagInter_sublist_left _ _).cons_cons _
    · apply sublist_cons_of_sublist
      apply bagInter_sublist_left

theorem bagInter_nil_iff_inter_nil : ∀ l₁ l₂ : List α, l₁.bagInter l₂ = [] ↔ l₁ ∩ l₂ = []
  | [], l₂ => by simp
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂
    · simp [h]
    · simpa [h] using bagInter_nil_iff_inter_nil l₁ l₂

end BagInter

end List
