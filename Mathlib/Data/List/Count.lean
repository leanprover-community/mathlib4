/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.BigOperators.Basic

#align_import data.list.count from "leanprover-community/mathlib"@"47adfab39a11a072db552f47594bf8ed2cf8a722"

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Std.Data.List.Basic`.
-/

set_option autoImplicit true


open Nat

variable {l : List α}

namespace List

section CountP

variable (p q : α → Bool)









theorem countP_join : ∀ l : List (List α), countP p l.join = (l.map (countP p)).sum
  | [] => rfl
  | a :: l => by rw [join, countP_append, map_cons, sum_cons, countP_join l]




theorem length_filter_lt_length_iff_exists (l) :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  simpa [length_eq_countP_add_countP p l, countP_eq_length_filter] using
  countP_pos (fun x => ¬p x) (l := l)








end CountP

/-! ### count -/

section Count

variable [DecidableEq α]


@[deprecated] theorem count_cons' (a b : α) (l : List α) :
    count a (b :: l) = count a l + if a = b then 1 else 0 := by
  simp only [count, beq_iff_eq, countP_cons, add_right_inj]
  simp only [eq_comm]











theorem count_join (l : List (List α)) (a : α) : l.join.count a = (l.map (count a)).sum :=
  countP_join _ _















theorem count_bind {α β} [DecidableEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.bind f) = sum (map (count x ∘ f) l) := by rw [List.bind, count_join, map_map]

@[simp]
theorem count_map_of_injective {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map, (· ∘ ·), hf.beq_eq]





@[to_additive]
theorem prod_map_eq_pow_single [Monoid β] (a : α) (f : α → β)
    (hf : ∀ a', a' ≠ a → a' ∈ l → f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction' l with a' as h generalizing a
  · rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  · specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ]
    · rw [hf a' (Ne.symm ha') (List.mem_cons_self a' as), one_mul, add_zero]

@[to_additive]
theorem prod_eq_pow_single [Monoid α] (a : α)
    (h : ∀ a', a' ≠ a → a' ∈ l → a' = 1) : l.prod = a ^ l.count a :=
  _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)

end Count

end List
