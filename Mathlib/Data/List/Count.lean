/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

#align_import data.list.count from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Batteries.Data.List.Basic`.
-/

assert_not_exists Set.range
assert_not_exists GroupWithZero
assert_not_exists Ring

open Nat

variable {α : Type*} {l : List α}

namespace List

section CountP

variable (p q : α → Bool)

#align list.countp_nil List.countP_nil

#align list.countp_cons_of_pos List.countP_cons_of_pos

#align list.countp_cons_of_neg List.countP_cons_of_neg

#align list.countp_cons List.countP_cons

#align list.length_eq_countp_add_countp List.length_eq_countP_add_countP

#align list.countp_eq_length_filter List.countP_eq_length_filter

#align list.countp_le_length List.countP_le_length

#align list.countp_append List.countP_append

#align list.countp_pos List.countP_pos

#align list.countp_eq_zero List.countP_eq_zero

#align list.countp_eq_length List.countP_eq_length

theorem length_filter_lt_length_iff_exists (l) :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  simpa [length_eq_countP_add_countP p l, countP_eq_length_filter] using
  countP_pos (fun x => ¬p x) (l := l)
#align list.length_filter_lt_length_iff_exists List.length_filter_lt_length_iff_exists

#align list.sublist.countp_le List.Sublist.countP_le

#align list.countp_filter List.countP_filter

#align list.countp_true List.countP_true

#align list.countp_false List.countP_false

#align list.countp_map List.countP_map

-- Porting note: `Lean.Internal.coeM` forces us to type-ascript `{x // x ∈ l}`
lemma countP_attach (l : List α) : l.attach.countP (fun a : {x // x ∈ l} ↦ p a) = l.countP p := by
  simp_rw [← Function.comp_apply (g := Subtype.val), ← countP_map, attach_map_val]
#align list.countp_attach List.countP_attach

#align list.countp_mono_left List.countP_mono_left

#align list.countp_congr List.countP_congr

end CountP

/-! ### count -/

section Count

variable [DecidableEq α]

#align list.count_nil List.count_nil

@[deprecated] -- 2023-08-23
theorem count_cons' (a b : α) (l : List α) :
    count a (b :: l) = count a l + if a = b then 1 else 0 := by
  simp only [count, beq_iff_eq, countP_cons, Nat.add_right_inj]
  simp only [eq_comm]
#align list.count_cons' List.count_cons'

#align list.count_cons List.count_cons

#align list.count_cons_self List.count_cons_self

#align list.count_cons_of_ne List.count_cons_of_ne

#align list.count_tail List.count_tail

#align list.count_le_length List.count_le_length

#align list.sublist.count_le List.Sublist.count_le

#align list.count_le_count_cons List.count_le_count_cons

#align list.count_singleton List.count_singleton

#align list.count_singleton' List.count_singleton'

#align list.count_append List.count_append

#align list.count_concat List.count_concat

#align list.count_pos List.count_pos_iff_mem

#align list.one_le_count_iff_mem List.count_pos_iff_mem

#align list.count_eq_zero_of_not_mem List.count_eq_zero_of_not_mem

#align list.not_mem_of_count_eq_zero List.not_mem_of_count_eq_zero

#align list.count_eq_zero List.count_eq_zero

#align list.count_eq_length List.count_eq_length

#align list.count_replicate_self List.count_replicate_self

#align list.count_replicate List.count_replicate

#align list.filter_eq' List.filter_eq'

#align list.filter_eq List.filter_eq

#align list.le_count_iff_replicate_sublist List.le_count_iff_replicate_sublist

#align list.replicate_count_eq_of_count_eq_length List.replicate_count_eq_of_count_eq_length

#align list.count_filter List.count_filter

@[simp]
lemma count_attach (a : {x // x ∈ l}) : l.attach.count a = l.count ↑a :=
  Eq.trans (countP_congr fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _
#align list.count_attach List.count_attach

@[simp]
theorem count_map_of_injective {α β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map, (· ∘ ·), hf.beq_eq]
#align list.count_map_of_injective List.count_map_of_injective

#align list.count_le_count_map List.count_le_count_map

#align list.count_erase List.count_erase

#align list.count_erase_self List.count_erase_self

#align list.count_erase_of_ne List.count_erase_of_ne

end Count

end List
