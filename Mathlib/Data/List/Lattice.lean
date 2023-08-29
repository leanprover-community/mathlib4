/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
Scott Morrison
-/
import Mathlib.Data.List.Count
import Mathlib.Data.List.Infix
import Mathlib.Algebra.Order.Monoid.MinMax

#align_import data.list.lattice from "leanprover-community/mathlib"@"dd71334db81d0bd444af1ee339a29298bef40734"

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

variable {α : Type*} {l l₁ l₂ : List α} {p : α → Prop} {a : α}

/-! ### `Disjoint` -/


section Disjoint

@[symm]
theorem Disjoint.symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂
#align list.disjoint.symm List.Disjoint.symm

#align list.disjoint_comm List.disjoint_comm
#align list.disjoint_left List.disjoint_left
#align list.disjoint_right List.disjoint_right
#align list.disjoint_iff_ne List.disjoint_iff_ne
#align list.disjoint_of_subset_left List.disjoint_of_subset_leftₓ
#align list.disjoint_of_subset_right List.disjoint_of_subset_right
#align list.disjoint_of_disjoint_cons_left List.disjoint_of_disjoint_cons_left
#align list.disjoint_of_disjoint_cons_right List.disjoint_of_disjoint_cons_right
#align list.disjoint_nil_left List.disjoint_nil_left
#align list.disjoint_nil_right List.disjoint_nil_right
#align list.singleton_disjoint List.singleton_disjointₓ
#align list.disjoint_singleton List.disjoint_singleton
#align list.disjoint_append_left List.disjoint_append_leftₓ
#align list.disjoint_append_right List.disjoint_append_right
#align list.disjoint_cons_left List.disjoint_cons_leftₓ
#align list.disjoint_cons_right List.disjoint_cons_right
#align list.disjoint_of_disjoint_append_left_left List.disjoint_of_disjoint_append_left_leftₓ
#align list.disjoint_of_disjoint_append_left_right List.disjoint_of_disjoint_append_left_rightₓ
#align list.disjoint_of_disjoint_append_right_left List.disjoint_of_disjoint_append_right_left
#align list.disjoint_of_disjoint_append_right_right List.disjoint_of_disjoint_append_right_right
#align list.disjoint_take_drop List.disjoint_take_dropₓ

end Disjoint

variable [DecidableEq α]

/-! ### `union` -/


section Union

#align list.nil_union List.nil_union
#align list.cons_union List.cons_unionₓ
#align list.mem_union List.mem_union_iff

theorem mem_union_left (h : a ∈ l₁) (l₂ : List α) : a ∈ l₁ ∪ l₂ :=
  mem_union_iff.2 (Or.inl h)
#align list.mem_union_left List.mem_union_left

theorem mem_union_right (l₁ : List α) (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
  mem_union_iff.2 (Or.inr h)
#align list.mem_union_right List.mem_union_right

theorem sublist_suffix_of_union : ∀ l₁ l₂ : List α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
  | [], l₂ => ⟨[], by rfl, rfl⟩
                      -- 🎉 no goals
  | a :: l₁, l₂ =>
    let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
    if h : a ∈ l₁ ∪ l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [e, cons_union, insert_of_mem h]⟩
        -- 🎉 no goals
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩
        -- 🎉 no goals
#align list.sublist_suffix_of_union List.sublist_suffix_of_union

theorem suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁ ∪ l₂ :=
  (sublist_suffix_of_union l₁ l₂).imp fun _ => And.right
#align list.suffix_union_right List.suffix_union_right

theorem union_sublist_append (l₁ l₂ : List α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
  let ⟨_, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s
#align list.union_sublist_append List.union_sublist_append

theorem forall_mem_union : (∀ x ∈ l₁ ∪ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ ∀ x ∈ l₂, p x := by
  simp only [mem_union_iff, or_imp, forall_and]
  -- 🎉 no goals
#align list.forall_mem_union List.forall_mem_union

theorem forall_mem_of_forall_mem_union_left (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₁, p x :=
  (forall_mem_union.1 h).1
#align list.forall_mem_of_forall_mem_union_left List.forall_mem_of_forall_mem_union_left

theorem forall_mem_of_forall_mem_union_right (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₂, p x :=
  (forall_mem_union.1 h).2
#align list.forall_mem_of_forall_mem_union_right List.forall_mem_of_forall_mem_union_right

end Union

/-! ### `inter` -/


section Inter

@[simp]
theorem inter_nil (l : List α) : [] ∩ l = [] :=
  rfl
#align list.inter_nil List.inter_nil

@[simp]
theorem inter_cons_of_mem (l₁ : List α) (h : a ∈ l₂) : (a :: l₁) ∩ l₂ = a :: l₁ ∩ l₂ := by
  simp only [Inter.inter, List.inter, filter_cons_of_pos, h]
  -- 🎉 no goals
#align list.inter_cons_of_mem List.inter_cons_of_mem

@[simp]
theorem inter_cons_of_not_mem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁) ∩ l₂ = l₁ ∩ l₂ := by
  simp only [Inter.inter, List.inter, filter_cons_of_neg, h]
  -- 🎉 no goals
#align list.inter_cons_of_not_mem List.inter_cons_of_not_mem

theorem mem_of_mem_inter_left : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
  mem_of_mem_filter
#align list.mem_of_mem_inter_left List.mem_of_mem_inter_left

theorem mem_of_mem_inter_right (h : a ∈ l₁ ∩ l₂) : a ∈ l₂ := by simpa using of_mem_filter h
                                                                -- 🎉 no goals
#align list.mem_of_mem_inter_right List.mem_of_mem_inter_right

theorem mem_inter_of_mem_of_mem (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) : a ∈ l₁ ∩ l₂ :=
  mem_filter_of_mem h₁ $ by simpa using h₂
                            -- 🎉 no goals
#align list.mem_inter_of_mem_of_mem List.mem_inter_of_mem_of_mem

#align list.mem_inter List.mem_inter_iff

theorem inter_subset_left (l₁ l₂ : List α) : l₁ ∩ l₂ ⊆ l₁ :=
  filter_subset _
#align list.inter_subset_left List.inter_subset_left

theorem inter_subset_right (l₁ l₂ : List α) : l₁ ∩ l₂ ⊆ l₂ := fun _ => mem_of_mem_inter_right
#align list.inter_subset_right List.inter_subset_right

theorem subset_inter {l l₁ l₂ : List α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ := fun _ h =>
  mem_inter_iff.2 ⟨h₁ h, h₂ h⟩
#align list.subset_inter List.subset_inter

theorem inter_eq_nil_iff_disjoint : l₁ ∩ l₂ = [] ↔ Disjoint l₁ l₂ := by
  simp only [eq_nil_iff_forall_not_mem, mem_inter_iff, not_and]
  -- ⊢ (∀ (a : α), a ∈ l₁ → ¬a ∈ l₂) ↔ Disjoint l₁ l₂
  rfl
  -- 🎉 no goals
#align list.inter_eq_nil_iff_disjoint List.inter_eq_nil_iff_disjoint

theorem forall_mem_inter_of_forall_left (h : ∀ x ∈ l₁, p x) (l₂ : List α) :
    ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_left) h
#align list.forall_mem_inter_of_forall_left List.forall_mem_inter_of_forall_left

theorem forall_mem_inter_of_forall_right (l₁ : List α) (h : ∀ x ∈ l₂, p x) :
    ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_right) h
#align list.forall_mem_inter_of_forall_right List.forall_mem_inter_of_forall_right

@[simp]
theorem inter_reverse {xs ys : List α} : xs.inter ys.reverse = xs.inter ys := by
  simp only [List.inter, mem_reverse]
  -- 🎉 no goals
#align list.inter_reverse List.inter_reverse

end Inter

/-! ### `bagInter` -/


section BagInter

@[simp]
theorem nil_bagInter (l : List α) : [].bagInter l = [] := by cases l <;> rfl
                                                             -- ⊢ List.bagInter [] [] = []
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align list.nil_bag_inter List.nil_bagInter

@[simp]
theorem bagInter_nil (l : List α) : l.bagInter [] = [] := by cases l <;> rfl
                                                             -- ⊢ List.bagInter [] [] = []
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals
#align list.bag_inter_nil List.bagInter_nil

@[simp]
theorem cons_bagInter_of_pos (l₁ : List α) (h : a ∈ l₂) :
    (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := by
  cases l₂
  -- ⊢ List.bagInter (a :: l₁) [] = a :: List.bagInter l₁ (List.erase [] a)
  · exact if_pos h
    -- 🎉 no goals
  · simp only [List.bagInter, if_pos (elem_eq_true_of_mem h)]
    -- 🎉 no goals
#align list.cons_bag_inter_of_pos List.cons_bagInter_of_pos

@[simp]
theorem cons_bagInter_of_neg (l₁ : List α) (h : a ∉ l₂) :
    (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := by
  cases l₂; · simp only [bagInter_nil]
  -- ⊢ List.bagInter (a :: l₁) [] = List.bagInter l₁ []
              -- 🎉 no goals
  simp only [erase_of_not_mem h, List.bagInter, if_neg (mt mem_of_elem_eq_true h)]
  -- 🎉 no goals
#align list.cons_bag_inter_of_neg List.cons_bagInter_of_neg

@[simp]
theorem mem_bagInter {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁.bagInter l₂ ↔ a ∈ l₁ ∧ a ∈ l₂
  | [], l₂ => by simp only [nil_bagInter, not_mem_nil, false_and_iff]
                 -- 🎉 no goals
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂
    -- ⊢ a ∈ List.bagInter (b :: l₁) l₂ ↔ a ∈ b :: l₁ ∧ a ∈ l₂
    · rw [cons_bagInter_of_pos _ h, mem_cons, mem_cons, mem_bagInter]
      -- ⊢ a = b ∨ a ∈ l₁ ∧ a ∈ List.erase l₂ b ↔ (a = b ∨ a ∈ l₁) ∧ a ∈ l₂
      by_cases ba : a = b
      -- ⊢ a = b ∨ a ∈ l₁ ∧ a ∈ List.erase l₂ b ↔ (a = b ∨ a ∈ l₁) ∧ a ∈ l₂
      · simp only [ba, h, eq_self_iff_true, true_or_iff, true_and_iff]
        -- 🎉 no goals
      · simp only [mem_erase_of_ne ba, ba, false_or_iff]
        -- 🎉 no goals
    · rw [cons_bagInter_of_neg _ h, mem_bagInter, mem_cons, or_and_right]
      -- ⊢ a ∈ l₁ ∧ a ∈ l₂ ↔ a = b ∧ a ∈ l₂ ∨ a ∈ l₁ ∧ a ∈ l₂
      symm
      -- ⊢ a = b ∧ a ∈ l₂ ∨ a ∈ l₁ ∧ a ∈ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂
      apply or_iff_right_of_imp
      -- ⊢ a = b ∧ a ∈ l₂ → a ∈ l₁ ∧ a ∈ l₂
      rintro ⟨rfl, h'⟩
      -- ⊢ a ∈ l₁ ∧ a ∈ l₂
      exact h.elim h'
      -- 🎉 no goals
#align list.mem_bag_inter List.mem_bagInter

@[simp]
theorem count_bagInter {a : α} :
    ∀ {l₁ l₂ : List α}, count a (l₁.bagInter l₂) = min (count a l₁) (count a l₂)
  | [], l₂ => by simp
                 -- 🎉 no goals
  | l₁, [] => by simp
                 -- 🎉 no goals
  | b :: l₁, l₂ => by
    by_cases hb : b ∈ l₂
    -- ⊢ count a (List.bagInter (b :: l₁) l₂) = min (count a (b :: l₁)) (count a l₂)
    · rw [cons_bagInter_of_pos _ hb, count_cons, count_cons, count_bagInter, count_erase, ←
        min_add_add_right]
      by_cases ab : a = b
      -- ⊢ min (count a l₁ + if a = b then 1 else 0) ((count a l₂ - if a = b then 1 els …
      · rw [if_pos ab, @tsub_add_cancel_of_le]
        -- ⊢ 1 ≤ count a l₂
        rwa [succ_le_iff, count_pos_iff_mem, ab]
        -- 🎉 no goals
      · rw [if_neg ab, tsub_zero, add_zero, add_zero]
        -- 🎉 no goals
    · rw [cons_bagInter_of_neg _ hb, count_bagInter]
      -- ⊢ min (count a l₁) (count a l₂) = min (count a (b :: l₁)) (count a l₂)
      by_cases ab : a = b
      -- ⊢ min (count a l₁) (count a l₂) = min (count a (b :: l₁)) (count a l₂)
      · rw [← ab] at hb
        -- ⊢ min (count a l₁) (count a l₂) = min (count a (b :: l₁)) (count a l₂)
        rw [count_eq_zero.2 hb, min_zero, min_zero]
        -- 🎉 no goals
      · rw [count_cons_of_ne ab]
        -- 🎉 no goals
#align list.count_bag_inter List.count_bagInter

theorem bagInter_sublist_left : ∀ l₁ l₂ : List α, l₁.bagInter l₂ <+ l₁
  | [], l₂ => by simp
                 -- 🎉 no goals
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂ <;> simp only [h, cons_bagInter_of_pos, cons_bagInter_of_neg, not_false_iff]
    -- ⊢ List.bagInter (b :: l₁) l₂ <+ b :: l₁
                            -- ⊢ b :: List.bagInter l₁ (List.erase l₂ b) <+ b :: l₁
                            -- ⊢ List.bagInter l₁ l₂ <+ b :: l₁
    · exact (bagInter_sublist_left _ _).cons_cons _
      -- 🎉 no goals
    · apply sublist_cons_of_sublist
      -- ⊢ List.bagInter l₁ l₂ <+ l₁
      apply bagInter_sublist_left
      -- 🎉 no goals
#align list.bag_inter_sublist_left List.bagInter_sublist_left

theorem bagInter_nil_iff_inter_nil : ∀ l₁ l₂ : List α, l₁.bagInter l₂ = [] ↔ l₁ ∩ l₂ = []
  | [], l₂ => by simp
                 -- 🎉 no goals
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂ <;> simp [h]
    -- ⊢ List.bagInter (b :: l₁) l₂ = [] ↔ (b :: l₁) ∩ l₂ = []
                            -- 🎉 no goals
                            -- ⊢ List.bagInter l₁ l₂ = [] ↔ l₁ ∩ l₂ = []
    exact bagInter_nil_iff_inter_nil l₁ l₂
    -- 🎉 no goals
#align list.bag_inter_nil_iff_inter_nil List.bagInter_nil_iff_inter_nil

end BagInter

end List
