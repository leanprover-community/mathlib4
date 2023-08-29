/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import Mathlib.Init.Data.List.Basic
import Mathlib.Init.Function
import Mathlib.Init.Data.Nat.Lemmas

/-!
Lemmas for `List` not (yet) in `Std`
-/

#align_import init.data.list.lemmas from "leanprover-community/lean"@"4a03bdeb31b3688c31d02d7ff8e0ff2e5d6174db"

universe u v w w₁ w₂

variable {α : Type u} {β : Type v} {γ : Type w}

namespace List

open Nat

/-! append -/

#align list.nil_append List.nil_append
#align list.cons_append List.cons_append
#align list.append_nil List.append_nil
#align list.append_assoc List.append_assoc

/-! length -/

#align list.length_cons List.length_cons
#align list.length_append List.length_append
#align list.length_repeat List.length_replicate
#align list.length_tail List.length_tail
#align list.length_drop List.length_drop

/-! map -/

#align list.map_cons List.map_cons
#align list.map_append List.map_append
#align list.map_singleton List.map_singleton
#align list.map_id List.map_id
#align list.map_map List.map_map
#align list.length_map List.length_map

/-! bind -/

#align list.nil_bind List.nil_bind
#align list.cons_bind List.cons_bind
#align list.append_bind List.append_bind

/-! mem -/

#align list.mem_nil_iff List.mem_nil_iff
#align list.not_mem_nil List.not_mem_nil
#align list.mem_cons_self List.mem_cons_self
#align list.mem_cons_iff List.mem_cons

theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  propext List.mem_cons
#align list.mem_cons_eq List.mem_cons_eq

#align list.mem_cons_of_mem List.mem_cons_of_mem

alias ⟨eq_or_mem_of_mem_cons, _⟩ := mem_cons
#align list.eq_or_mem_of_mem_cons List.eq_or_mem_of_mem_cons

#align list.mem_append List.mem_append
#align list.mem_append_eq List.mem_append_eq
#align list.mem_append_left List.mem_append_left
#align list.mem_append_right List.mem_append_right

theorem not_bex_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x := fun ⟨_, hx, _⟩ => List.not_mem_nil _ hx
#align list.not_bex_nil List.not_bex_nil

#align list.ball_nil List.forall_mem_nil

theorem bex_cons (p : α → Prop) (a : α) (l : List α) : (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  ⟨fun ⟨x, h, px⟩ => by
    simp only [find?, mem_cons] at h
    -- ⊢ p a ∨ ∃ x, x ∈ l ∧ p x
    cases' h with h h
    -- ⊢ p a ∨ ∃ x, x ∈ l ∧ p x
    · cases h; exact Or.inl px;
      -- ⊢ p a ∨ ∃ x, x ∈ l ∧ p x
               -- 🎉 no goals
    · exact Or.inr ⟨x, h, px⟩,
      -- 🎉 no goals
  fun o =>
    o.elim (fun pa => ⟨a, mem_cons_self _ _, pa⟩) fun ⟨x, h, px⟩ => ⟨x, mem_cons_of_mem _ h, px⟩⟩
#align list.bex_cons List.bex_cons

#align list.ball_cons List.forall_mem_consₓ

/-! list subset -/

#align list.subset List.Subset
-- This is relying on an automatically generated instance name from Std.
-- See https://github.com/leanprover/lean4/issues/2343
#align list.has_subset List.instHasSubsetList
#align list.nil_subset List.nil_subset
#align list.subset.refl List.Subset.refl
#align list.subset.trans List.Subset.trans
#align list.subset_cons List.subset_cons
#align list.subset_of_cons_subset List.subset_of_cons_subset
#align list.cons_subset_cons List.cons_subset_cons
#align list.subset_append_left List.subset_append_left
#align list.subset_append_right List.subset_append_right
#align list.subset_cons_of_subset List.subset_cons_of_subset
#align list.eq_nil_of_length_eq_zero List.eq_nil_of_length_eq_zero
#align list.ne_nil_of_length_eq_succ List.ne_nil_of_length_eq_succ
#align list.length_map₂ List.length_zipWith
#align list.length_take List.length_take
#align list.length_take_le List.length_take_le
#align list.length_remove_nth List.length_removeNth
#align list.partition_eq_filter_filter List.partition_eq_filter_filterₓ

/-! sublists -/

#align list.sublist List.Sublist

alias length_le_of_sublist := Sublist.length_le
#align list.length_le_of_sublist List.length_le_of_sublist

/-! filter -/

#align list.filter_nil List.filter_nilₓ
#align list.filter_cons_of_pos List.filter_cons_of_posₓ
#align list.filter_cons_of_neg List.filter_cons_of_negₓ
#align list.filter_append List.filter_appendₓ
#align list.filter_sublist List.filter_sublistₓ

/-! map_accumr -/


section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over a list returning the intermediate results and a final result. -/
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
#align list.map_accumr List.mapAccumr

/-- Length of the list obtained by `mapAccumr`. -/
@[simp]
theorem length_mapAccumr :
    ∀ (f : α → σ → σ × β) (x : List α) (s : σ), length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congr_arg succ (length_mapAccumr f x s)
  | _, [], _ => rfl
#align list.length_map_accumr List.length_mapAccumr

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over two lists returning the intermediate results and a final result. -/
def mapAccumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
#align list.map_accumr₂ List.mapAccumr₂

/-- Length of a list obtained using `mapAccumr₂`. -/
@[simp]
theorem length_mapAccumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, _ :: x, _ :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))
  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl
#align list.length_map_accumr₂ List.length_mapAccumr₂

end MapAccumr₂

end List
