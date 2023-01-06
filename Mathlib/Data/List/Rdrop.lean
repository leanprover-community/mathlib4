/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.list.rdrop
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.List.Infix

/-!

# Dropping or taking from lists on the right

Taking or removing element from the tail end of a list

## Main defintions

- `rdrop n`: drop `n : ℕ` elements from the tail
- `rtake n`: take `n : ℕ` elements from the tail
- `drop_while p`: remove all the elements that satisfy a decidable `p : α → Prop` from the tail of
  a list until hitting the first non-satisfying element
- `take_while p`: take all the elements that satisfy a decidable `p : α → Prop` from the tail of
  a list until hitting the first non-satisfying element

## Implementation detail

The two predicate-based methods operate by performing the regular "from-left" operation on
`list.reverse`, followed by another `list.reverse`, so they are not the most performant.
The other two rely on `list.length l` so they still traverse the list twice. One could construct
another function that takes a `L : ℕ` and use `L - n`. Under a proof condition that
`L = l.length`, the function would do the right thing.

-/


variable {α : Type _} (p : α → Prop) [DecidablePred p] (l : List α) (n : ℕ)

namespace List

/-- Drop `n` elements from the tail end of a list. -/
def rdrop : List α :=
  l.take (l.length - n)
#align list.rdrop List.rdrop

@[simp]
theorem rdrop_nil : rdrop ([] : List α) n = [] := by simp [rdrop]
#align list.rdrop_nil List.rdrop_nil

@[simp]
theorem rdrop_zero : rdrop l 0 = l := by simp [rdrop]
#align list.rdrop_zero List.rdrop_zero

theorem rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n) :=
  by
  rw [rdrop]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp [take_append]
    · simp [take_append_eq_append_take, IH]
#align list.rdrop_eq_reverse_drop_reverse List.rdrop_eq_reverse_drop_reverse

@[simp]
theorem rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n := by
  simp [rdrop_eq_reverse_drop_reverse]
#align list.rdrop_concat_succ List.rdrop_concat_succ

/-- Take `n` elements from the tail end of a list. -/
def rtake : List α :=
  l.drop (l.length - n)
#align list.rtake List.rtake

@[simp]
theorem rtake_nil : rtake ([] : List α) n = [] := by simp [rtake]
#align list.rtake_nil List.rtake_nil

@[simp]
theorem rtake_zero : rtake l 0 = [] := by simp [rtake]
#align list.rtake_zero List.rtake_zero

theorem rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n) :=
  by
  rw [rtake]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp
    · simp [drop_append_eq_append_drop, IH]
#align list.rtake_eq_reverse_take_reverse List.rtake_eq_reverse_take_reverse

@[simp]
theorem rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x] := by
  simp [rtake_eq_reverse_take_reverse]
#align list.rtake_concat_succ List.rtake_concat_succ

/-- Drop elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def rdropWhile : List α :=
  reverse (l.reverse.dropWhile p)
#align list.rdrop_while List.rdropWhile

@[simp]
theorem rdrop_while_nil : rdropWhile p ([] : List α) = [] := by simp [rdrop_while, drop_while]
#align list.rdrop_while_nil List.rdrop_while_nil

theorem rdrop_while_concat (x : α) :
    rdropWhile p (l ++ [x]) = if p x then rdropWhile p l else l ++ [x] :=
  by
  simp only [rdrop_while, drop_while, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h h <;> simp [h]
#align list.rdrop_while_concat List.rdrop_while_concat

@[simp]
theorem rdrop_while_concat_pos (x : α) (h : p x) : rdropWhile p (l ++ [x]) = rdropWhile p l := by
  rw [rdrop_while_concat, if_pos h]
#align list.rdrop_while_concat_pos List.rdrop_while_concat_pos

@[simp]
theorem rdrop_while_concat_neg (x : α) (h : ¬p x) : rdropWhile p (l ++ [x]) = l ++ [x] := by
  rw [rdrop_while_concat, if_neg h]
#align list.rdrop_while_concat_neg List.rdrop_while_concat_neg

theorem rdrop_while_singleton (x : α) : rdropWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], rdrop_while_concat, rdrop_while_nil]
#align list.rdrop_while_singleton List.rdrop_while_singleton

theorem rdrop_while_last_not (hl : l.rdropWhile p ≠ []) : ¬p ((rdropWhile p l).last hl) :=
  by
  simp_rw [rdrop_while]
  rw [last_reverse]
  exact drop_while_nth_le_zero_not _ _ _
#align list.rdrop_while_last_not List.rdrop_while_last_not

theorem rdrop_while_prefix : l.rdropWhile p <+: l :=
  by
  rw [← reverse_suffix, rdrop_while, reverse_reverse]
  exact drop_while_suffix _
#align list.rdrop_while_prefix List.rdrop_while_prefix

variable {p} {l}

@[simp]
theorem rdrop_while_eq_nil_iff : rdropWhile p l = [] ↔ ∀ x ∈ l, p x := by simp [rdrop_while]
#align list.rdrop_while_eq_nil_iff List.rdrop_while_eq_nil_iff

-- it is in this file because it requires `list.infix`
@[simp]
theorem drop_while_eq_self_iff : dropWhile p l = l ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) :=
  by
  induction' l with hd tl IH
  · simp
  · rw [drop_while]
    split_ifs
    · simp only [h, length, nth_le, Nat.succ_pos', not_true, forall_true_left, iff_false_iff]
      intro H
      refine' (cons_ne_self hd tl) (sublist.antisymm _ (sublist_cons _ _))
      rw [← H]
      exact (drop_while_suffix _).Sublist
    · simp [h]
#align list.drop_while_eq_self_iff List.drop_while_eq_self_iff

@[simp]
theorem rdrop_while_eq_self_iff : rdropWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.last hl) :=
  by
  simp only [rdrop_while, reverse_eq_iff, length_reverse, Ne.def, drop_while_eq_self_iff,
    last_eq_nth_le, ← length_eq_zero, pos_iff_ne_zero]
  refine' forall_congr' _
  intro h
  rw [nth_le_reverse']
  · simp
  · rw [← Ne.def, ← pos_iff_ne_zero] at h
    simp [tsub_lt_iff_right (Nat.succ_le_of_lt h)]
#align list.rdrop_while_eq_self_iff List.rdrop_while_eq_self_iff

variable (p) (l)

theorem drop_while_idempotent : dropWhile p (dropWhile p l) = dropWhile p l :=
  drop_while_eq_self_iff.mpr (dropWhile_nthLe_zero_not _ _)
#align list.drop_while_idempotent List.drop_while_idempotent

theorem rdrop_while_idempotent : rdropWhile p (rdropWhile p l) = rdropWhile p l :=
  rdrop_while_eq_self_iff.mpr (rdrop_while_last_not _ _)
#align list.rdrop_while_idempotent List.rdrop_while_idempotent

/-- Take elements from the tail end of a list that satisfy `p : α → Prop`.
Implemented naively via `list.reverse` -/
def rtakeWhile : List α :=
  reverse (l.reverse.takeWhile p)
#align list.rtake_while List.rtakeWhile

@[simp]
theorem rtake_while_nil : rtakeWhile p ([] : List α) = [] := by simp [rtake_while, take_while]
#align list.rtake_while_nil List.rtake_while_nil

theorem rtake_while_concat (x : α) :
    rtakeWhile p (l ++ [x]) = if p x then rtakeWhile p l ++ [x] else [] :=
  by
  simp only [rtake_while, take_while, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h h <;> simp [h]
#align list.rtake_while_concat List.rtake_while_concat

@[simp]
theorem rtake_while_concat_pos (x : α) (h : p x) :
    rtakeWhile p (l ++ [x]) = rtakeWhile p l ++ [x] := by rw [rtake_while_concat, if_pos h]
#align list.rtake_while_concat_pos List.rtake_while_concat_pos

@[simp]
theorem rtake_while_concat_neg (x : α) (h : ¬p x) : rtakeWhile p (l ++ [x]) = [] := by
  rw [rtake_while_concat, if_neg h]
#align list.rtake_while_concat_neg List.rtake_while_concat_neg

theorem rtake_while_suffix : l.rtakeWhile p <:+ l :=
  by
  rw [← reverse_prefix, rtake_while, reverse_reverse]
  exact take_while_prefix _
#align list.rtake_while_suffix List.rtake_while_suffix

variable {p} {l}

@[simp]
theorem rtake_while_eq_self_iff : rtakeWhile p l = l ↔ ∀ x ∈ l, p x := by
  simp [rtake_while, reverse_eq_iff]
#align list.rtake_while_eq_self_iff List.rtake_while_eq_self_iff

@[simp]
theorem rtake_while_eq_nil_iff : rtakeWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.last hl) := by
  induction l using List.reverseRecOn <;> simp [rtake_while]
#align list.rtake_while_eq_nil_iff List.rtake_while_eq_nil_iff

theorem mem_rtake_while_imp {x : α} (hx : x ∈ rtakeWhile p l) : p x :=
  by
  suffices x ∈ take_while p l.reverse by exact mem_take_while_imp this
  rwa [← mem_reverse, ← rtake_while]
#align list.mem_rtake_while_imp List.mem_rtake_while_imp

variable (p) (l)

theorem rtake_while_idempotent : rtakeWhile p (rtakeWhile p l) = rtakeWhile p l :=
  rtake_while_eq_self_iff.mpr fun _ => mem_rtake_while_imp
#align list.rtake_while_idempotent List.rtake_while_idempotent

end List

