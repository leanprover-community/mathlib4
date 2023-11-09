/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix

#align_import data.list.rdrop from "leanprover-community/mathlib"@"26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2"
/-!

# Dropping or taking from lists on the right

Taking or removing element from the tail end of a list

## Main definitions

- `dropRight n`: drop `n : ℕ` elements from the tail
- `takeRight n`: take `n : ℕ` elements from the tail
- `dropRightWhile p`: remove all the elements from the tail of a list until it finds the first
  element for which `p : α → Bool` returns false. This element and everything before is returned.
- `takeRightWhile p`:  Returns the longest terminal segment of a list for which `p : α → Bool`
  returns true.

## Implementation detail

The two predicate-based methods operate by performing the regular "from-left" operation on
`List.reverse`, followed by another `List.reverse`, so they are not the most performant.
The other two rely on `List.length l` so they still traverse the list twice. One could construct
another function that takes a `L : ℕ` and use `L - n`. Under a proof condition that
`L = l.length`, the function would do the right thing.

-/


variable {α : Type*} (p : α → Bool) (l : List α) (n : ℕ)

namespace List

/-- Drop `n` elements from the tail end of a list. -/
def dropRight : List α :=
  l.take (l.length - n)
#align list.rdrop List.dropRight

@[simp]
theorem dropRight_nil : dropRight ([] : List α) n = [] := by simp [dropRight]
#align list.rdrop_nil List.dropRight_nil

@[simp]
theorem dropRight_zero : dropRight l 0 = l := by simp [dropRight]
#align list.rdrop_zero List.dropRight_zero

theorem dropRight_eq_reverse_drop_reverse : l.dropRight n = reverse (l.reverse.drop n) := by
  rw [dropRight]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · simp [take_append]
    · simp [take_append_eq_append_take, IH]
#align list.rdrop_eq_reverse_drop_reverse List.dropRight_eq_reverse_drop_reverse

@[simp]
theorem dropRight_concat_succ (x : α) : dropRight (l ++ [x]) (n + 1) = dropRight l n := by
  simp [dropRight_eq_reverse_drop_reverse]
#align list.rdrop_concat_succ List.dropRight_concat_succ

/-- Take `n` elements from the tail end of a list. -/
def takeRight : List α :=
  l.drop (l.length - n)
#align list.rtake List.takeRight

@[simp]
theorem takeRight_nil : takeRight ([] : List α) n = [] := by simp [takeRight]
#align list.rtake_nil List.takeRight_nil

@[simp]
theorem takeRight_zero : takeRight l 0 = [] := by simp [takeRight]
#align list.rtake_zero List.takeRight_zero

theorem takeRight_eq_reverse_take_reverse : l.takeRight n = reverse (l.reverse.take n) := by
  rw [takeRight]
  induction' l using List.reverseRecOn with xs x IH generalizing n
  · simp
  · cases n
    · exact drop_length _
    · simp [drop_append_eq_append_drop, IH]
#align list.rtake_eq_reverse_take_reverse List.takeRight_eq_reverse_take_reverse

@[simp]
theorem takeRight_concat_succ (x : α) : takeRight (l ++ [x]) (n + 1) = takeRight l n ++ [x] := by
  simp [takeRight_eq_reverse_take_reverse]
#align list.rtake_concat_succ List.takeRight_concat_succ

/-- Drop elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse` -/
def dropRightWhile : List α :=
  reverse (l.reverse.dropWhile p)
#align list.rdrop_while List.dropRightWhile

@[simp]
theorem dropRightWhile_nil : dropRightWhile p ([] : List α) = [] := by
  simp [dropRightWhile, dropWhile]
#align list.rdrop_while_nil List.dropRightWhile_nil

theorem dropRightWhile_concat (x : α) :
    dropRightWhile p (l ++ [x]) = if p x then dropRightWhile p l else l ++ [x] := by
  simp only [dropRightWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]
#align list.rdrop_while_concat List.dropRightWhile_concat

@[simp]
theorem dropRightWhile_concat_pos (x : α) (h : p x) :
    dropRightWhile p (l ++ [x]) = dropRightWhile p l := by
  rw [dropRightWhile_concat, if_pos h]
#align list.rdrop_while_concat_pos List.dropRightWhile_concat_pos

@[simp]
theorem dropRightWhile_concat_neg (x : α) (h : ¬p x) : dropRightWhile p (l ++ [x]) = l ++ [x] := by
  rw [dropRightWhile_concat, if_neg h]
#align list.rdrop_while_concat_neg List.dropRightWhile_concat_neg

theorem dropRightWhile_singleton (x : α) : dropRightWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], dropRightWhile_concat, dropRightWhile_nil]
#align list.rdrop_while_singleton List.dropRightWhile_singleton

theorem dropRightWhile_last_not (hl : l.dropRightWhile p ≠ []) :
    ¬p ((dropRightWhile p l).getLast hl) := by
  simp_rw [dropRightWhile]
  rw [getLast_reverse]
  exact dropWhile_nthLe_zero_not _ _ _
#align list.rdrop_while_last_not List.dropRightWhile_last_not

theorem dropRightWhile_prefix : l.dropRightWhile p <+: l := by
  rw [← reverse_suffix, dropRightWhile, reverse_reverse]
  exact dropWhile_suffix _
#align list.rdrop_while_prefix List.dropRightWhile_prefix

variable {p} {l}

@[simp]
theorem dropRightWhile_eq_nil_iff : dropRightWhile p l = [] ↔ ∀ x ∈ l, p x := by
  simp [dropRightWhile]
#align list.rdrop_while_eq_nil_iff List.dropRightWhile_eq_nil_iff

-- it is in this file because it requires `List.Infix`
@[simp]
theorem dropWhile_eq_self_iff : dropWhile p l = l ↔ ∀ hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩) := by
  cases' l with hd tl
  · simp only [dropWhile, true_iff]
    intro h
    by_contra
    rwa [length_nil, lt_self_iff_false] at h
  · rw [dropWhile]
    refine' ⟨fun h => _, fun h => _⟩
    · intro _ H
      rw [get] at H
      refine' (cons_ne_self hd tl) (Sublist.antisymm _ (sublist_cons _ _))
      rw [← h]
      simp only [H]
      exact List.IsSuffix.sublist (dropWhile_suffix p)
    · have := h (by simp only [length, Nat.succ_pos])
      rw [get] at this
      simp_rw [this]
#align list.drop_while_eq_self_iff List.dropWhile_eq_self_iff

/- porting note: This proof is longer than it used to be because `simp` refuses to rewrite
 the `l ≠ []` condition if `hl` is not `intro`'d yet -/
@[simp]
theorem dropRightWhile_eq_self_iff : dropRightWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  simp only [dropRightWhile._eq_1, reverse_eq_iff, dropWhile_eq_self_iff, length_reverse,
    ←length_pos, ne_eq, Bool.not_eq_true, getLast_eq_get, ge_iff_le]
  refine forall_congr' ?_
  intro h
  rw [get_reverse']
  · simp
  · exact Nat.pred_lt h.ne'
#align list.rdrop_while_eq_self_iff List.dropRightWhile_eq_self_iff

variable (p) (l)

theorem dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l := by
  simp only [dropWhile_eq_self_iff]
  exact fun h => dropWhile_nthLe_zero_not p l h
#align list.drop_while_idempotent List.dropWhile_idempotent

theorem dropRightWhile_idempotent : dropRightWhile p (dropRightWhile p l) = dropRightWhile p l :=
  dropRightWhile_eq_self_iff.mpr (dropRightWhile_last_not _ _)
#align list.rdrop_while_idempotent List.dropRightWhile_idempotent

/-- Take elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse` -/
def takeRightWhile : List α :=
  reverse (l.reverse.takeWhile p)
#align list.rtake_while List.takeRightWhile

@[simp]
theorem takeRightWhile_nil : takeRightWhile p ([] : List α) = [] := by
  simp [takeRightWhile, takeWhile]
#align list.rtake_while_nil List.takeRightWhile_nil

theorem takeRightWhile_concat (x : α) :
    takeRightWhile p (l ++ [x]) = if p x then takeRightWhile p l ++ [x] else [] := by
  simp only [takeRightWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]
  split_ifs with h <;> simp [h]
#align list.rtake_while_concat List.takeRightWhile_concat

@[simp]
theorem takeRightWhile_concat_pos (x : α) (h : p x) :
    takeRightWhile p (l ++ [x]) = takeRightWhile p l ++ [x] := by
  rw [takeRightWhile_concat, if_pos h]
#align list.rtake_while_concat_pos List.takeRightWhile_concat_pos

@[simp]
theorem takeRightWhile_concat_neg (x : α) (h : ¬p x) : takeRightWhile p (l ++ [x]) = [] := by
  rw [takeRightWhile_concat, if_neg h]
#align list.rtake_while_concat_neg List.takeRightWhile_concat_neg

theorem takeRightWhile_suffix : l.takeRightWhile p <:+ l := by
  rw [← reverse_prefix, takeRightWhile, reverse_reverse]
  exact takeWhile_prefix _
#align list.rtake_while_suffix List.takeRightWhile_suffix

variable {p} {l}

@[simp]
theorem takeRightWhile_eq_self_iff : takeRightWhile p l = l ↔ ∀ x ∈ l, p x := by
  simp [takeRightWhile, reverse_eq_iff]
#align list.rtake_while_eq_self_iff List.takeRightWhile_eq_self_iff

-- Porting note: This needed a lot of rewriting.
@[simp]
theorem takeRightWhile_eq_nil_iff : takeRightWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  induction' l using List.reverseRecOn with l a
  · simp only [takeRightWhile, takeWhile, reverse_nil, true_iff]
    intro f; contradiction
  · simp only [takeRightWhile, reverse_append, takeWhile, reverse_eq_nil, getLast_append, ne_eq,
  append_eq_nil, and_false, forall_true_left]
    refine' ⟨fun h => _ , fun h => _⟩
    · intro pa; simp only [pa] at h
    · simp only [h]
#align list.rtake_while_eq_nil_iff List.takeRightWhile_eq_nil_iff

theorem mem_takeRightWhile_imp {x : α} (hx : x ∈ takeRightWhile p l) : p x := by
  rw [takeRightWhile, mem_reverse] at hx
  exact mem_takeWhile_imp hx
#align list.mem_rtake_while_imp List.mem_takeRightWhile_imp

variable (p) (l)

theorem takeRightWhile_idempotent : takeRightWhile p (takeRightWhile p l) = takeRightWhile p l :=
  takeRightWhile_eq_self_iff.mpr fun _ => mem_takeRightWhile_imp
#align list.rtake_while_idempotent List.takeRightWhile_idempotent

end List
