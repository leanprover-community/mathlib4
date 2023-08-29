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

- `rdrop n`: drop `n : ℕ` elements from the tail
- `rtake n`: take `n : ℕ` elements from the tail
- `rdropWhile p`: remove all the elements from the tail of a list until it finds the first element
  for which `p : α → Bool` returns false. This element and everything before is returned.
- `rtakeWhile p`:  Returns the longest terminal segment of a list for which `p : α → Bool` returns
  true.

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
def rdrop : List α :=
  l.take (l.length - n)
#align list.rdrop List.rdrop

@[simp]
theorem rdrop_nil : rdrop ([] : List α) n = [] := by simp [rdrop]
                                                     -- 🎉 no goals
#align list.rdrop_nil List.rdrop_nil

@[simp]
theorem rdrop_zero : rdrop l 0 = l := by simp [rdrop]
                                         -- 🎉 no goals
#align list.rdrop_zero List.rdrop_zero

theorem rdrop_eq_reverse_drop_reverse : l.rdrop n = reverse (l.reverse.drop n) := by
  rw [rdrop]
  -- ⊢ take (length l - n) l = reverse (drop n (reverse l))
  induction' l using List.reverseRecOn with xs x IH generalizing n
  -- ⊢ take (length [] - n) [] = reverse (drop n (reverse []))
  · simp
    -- 🎉 no goals
  · cases n
    -- ⊢ take (length (xs ++ [x]) - Nat.zero) (xs ++ [x]) = reverse (drop Nat.zero (r …
    · simp [take_append]
      -- 🎉 no goals
    · simp [take_append_eq_append_take, IH]
      -- 🎉 no goals
#align list.rdrop_eq_reverse_drop_reverse List.rdrop_eq_reverse_drop_reverse

@[simp]
theorem rdrop_concat_succ (x : α) : rdrop (l ++ [x]) (n + 1) = rdrop l n := by
  simp [rdrop_eq_reverse_drop_reverse]
  -- 🎉 no goals
#align list.rdrop_concat_succ List.rdrop_concat_succ

/-- Take `n` elements from the tail end of a list. -/
def rtake : List α :=
  l.drop (l.length - n)
#align list.rtake List.rtake

@[simp]
theorem rtake_nil : rtake ([] : List α) n = [] := by simp [rtake]
                                                     -- 🎉 no goals
#align list.rtake_nil List.rtake_nil

@[simp]
theorem rtake_zero : rtake l 0 = [] := by simp [rtake]
                                          -- 🎉 no goals
#align list.rtake_zero List.rtake_zero

theorem rtake_eq_reverse_take_reverse : l.rtake n = reverse (l.reverse.take n) := by
  rw [rtake]
  -- ⊢ drop (length l - n) l = reverse (take n (reverse l))
  induction' l using List.reverseRecOn with xs x IH generalizing n
  -- ⊢ drop (length [] - n) [] = reverse (take n (reverse []))
  · simp
    -- 🎉 no goals
  · cases n
    -- ⊢ drop (length (xs ++ [x]) - Nat.zero) (xs ++ [x]) = reverse (take Nat.zero (r …
    · exact drop_length _
      -- 🎉 no goals
    · simp [drop_append_eq_append_drop, IH]
      -- 🎉 no goals
#align list.rtake_eq_reverse_take_reverse List.rtake_eq_reverse_take_reverse

@[simp]
theorem rtake_concat_succ (x : α) : rtake (l ++ [x]) (n + 1) = rtake l n ++ [x] := by
  simp [rtake_eq_reverse_take_reverse]
  -- 🎉 no goals
#align list.rtake_concat_succ List.rtake_concat_succ

/-- Drop elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse` -/
def rdropWhile : List α :=
  reverse (l.reverse.dropWhile p)
#align list.rdrop_while List.rdropWhile

@[simp]
theorem rdropWhile_nil : rdropWhile p ([] : List α) = [] := by simp [rdropWhile, dropWhile]
                                                               -- 🎉 no goals
#align list.rdrop_while_nil List.rdropWhile_nil

theorem rdropWhile_concat (x : α) :
    rdropWhile p (l ++ [x]) = if p x then rdropWhile p l else l ++ [x] := by
  simp only [rdropWhile, dropWhile, reverse_append, reverse_singleton, singleton_append]
  -- ⊢ reverse
  split_ifs with h <;> simp [h]
                       -- 🎉 no goals
                       -- 🎉 no goals
#align list.rdrop_while_concat List.rdropWhile_concat

@[simp]
theorem rdropWhile_concat_pos (x : α) (h : p x) : rdropWhile p (l ++ [x]) = rdropWhile p l := by
  rw [rdropWhile_concat, if_pos h]
  -- 🎉 no goals
#align list.rdrop_while_concat_pos List.rdropWhile_concat_pos

@[simp]
theorem rdropWhile_concat_neg (x : α) (h : ¬p x) : rdropWhile p (l ++ [x]) = l ++ [x] := by
  rw [rdropWhile_concat, if_neg h]
  -- 🎉 no goals
#align list.rdrop_while_concat_neg List.rdropWhile_concat_neg

theorem rdropWhile_singleton (x : α) : rdropWhile p [x] = if p x then [] else [x] := by
  rw [← nil_append [x], rdropWhile_concat, rdropWhile_nil]
  -- 🎉 no goals
#align list.rdrop_while_singleton List.rdropWhile_singleton

theorem rdropWhile_last_not (hl : l.rdropWhile p ≠ []) : ¬p ((rdropWhile p l).getLast hl) := by
  simp_rw [rdropWhile]
  -- ⊢ ¬p (getLast (reverse (dropWhile p (reverse l))) (_ : reverse (dropWhile p (r …
  rw [getLast_reverse]
  -- ⊢ ¬p (get (dropWhile p (reverse l)) { val := 0, isLt := (_ : 0 < length (dropW …
  exact dropWhile_nthLe_zero_not _ _ _
  -- 🎉 no goals
#align list.rdrop_while_last_not List.rdropWhile_last_not

theorem rdropWhile_prefix : l.rdropWhile p <+: l := by
  rw [← reverse_suffix, rdropWhile, reverse_reverse]
  -- ⊢ dropWhile p (reverse l) <:+ reverse l
  exact dropWhile_suffix _
  -- 🎉 no goals
#align list.rdrop_while_prefix List.rdropWhile_prefix

variable {p} {l}

@[simp]
theorem rdropWhile_eq_nil_iff : rdropWhile p l = [] ↔ ∀ x ∈ l, p x := by simp [rdropWhile]
                                                                         -- 🎉 no goals
#align list.rdrop_while_eq_nil_iff List.rdropWhile_eq_nil_iff

-- it is in this file because it requires `List.Infix`
@[simp]
theorem dropWhile_eq_self_iff : dropWhile p l = l ↔ ∀ hl : 0 < l.length, ¬p (l.nthLe 0 hl) := by
  cases' l with hd tl
  -- ⊢ dropWhile p [] = [] ↔ ∀ (hl : 0 < length []), ¬p (nthLe [] 0 hl) = true
  · simp only [dropWhile, true_iff]
    -- ⊢ ∀ (hl : 0 < length []), ¬p (nthLe [] 0 hl) = true
    intro h
    -- ⊢ ¬p (nthLe [] 0 h) = true
    by_contra
    -- ⊢ False
    rwa [length_nil, lt_self_iff_false] at h
    -- 🎉 no goals
  · rw [dropWhile]
    -- ⊢ (match p hd with
    refine' ⟨fun h => _, fun h => _⟩
    · intro _ H
      -- ⊢ False
      rw [nthLe, get] at H
      -- ⊢ False
      refine' (cons_ne_self hd tl) (Sublist.antisymm _ (sublist_cons _ _))
      -- ⊢ hd :: tl <+ tl
      rw [← h]
      -- ⊢ (match p hd with
      simp only [H]
      -- ⊢ dropWhile p tl <+ tl
      exact List.isSuffix.sublist (dropWhile_suffix p)
      -- 🎉 no goals
    · have := h (by simp only [length, Nat.succ_pos])
      -- ⊢ (match p hd with
      rw [nthLe, get] at this
      -- ⊢ (match p hd with
      simp_rw [this]
      -- 🎉 no goals
#align list.drop_while_eq_self_iff List.dropWhile_eq_self_iff

/- porting note: This proof is longer than it used to be because `simp` refuses to rewrite
 the `l ≠ []` condition if `hl` is not `intro`'d yet -/
@[simp]
theorem rdropWhile_eq_self_iff : rdropWhile p l = l ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  simp only [rdropWhile, reverse_eq_iff, dropWhile_eq_self_iff, getLast_eq_get]
  -- ⊢ (∀ (hl : 0 < length (reverse l)), ¬p (nthLe (reverse l) 0 hl) = true) ↔ ∀ (h …
  refine' ⟨fun h hl => _, fun h hl => _⟩
  -- ⊢ ¬p (get l { val := length l - 1, isLt := (_ : length l - 1 < length l) }) =  …
  · rw [← length_pos, ← length_reverse] at hl
    -- ⊢ ¬p (get l { val := length l - 1, isLt := (_ : length l - 1 < length l) }) =  …
    have := h hl
    -- ⊢ ¬p (get l { val := length l - 1, isLt := (_ : length l - 1 < length l) }) =  …
    rwa [nthLe, get_reverse'] at this
    -- 🎉 no goals
  · rw [length_reverse, length_pos] at hl
    -- ⊢ ¬p (nthLe (reverse l) 0 hl✝) = true
    have := h hl
    -- ⊢ ¬p (nthLe (reverse l) 0 hl✝) = true
    rwa [nthLe, get_reverse']
    -- 🎉 no goals
#align list.rdrop_while_eq_self_iff List.rdropWhile_eq_self_iff

variable (p) (l)

theorem dropWhile_idempotent : dropWhile p (dropWhile p l) = dropWhile p l := by
  simp only [dropWhile_eq_self_iff]
  -- ⊢ ∀ (hl : 0 < length (dropWhile p l)), ¬p (nthLe (dropWhile p l) 0 hl) = true
  exact fun h => dropWhile_nthLe_zero_not p l h
  -- 🎉 no goals
#align list.drop_while_idempotent List.dropWhile_idempotent

theorem rdropWhile_idempotent : rdropWhile p (rdropWhile p l) = rdropWhile p l :=
  rdropWhile_eq_self_iff.mpr (rdropWhile_last_not _ _)
#align list.rdrop_while_idempotent List.rdropWhile_idempotent

/-- Take elements from the tail end of a list that satisfy `p : α → Bool`.
Implemented naively via `List.reverse` -/
def rtakeWhile : List α :=
  reverse (l.reverse.takeWhile p)
#align list.rtake_while List.rtakeWhile

@[simp]
theorem rtakeWhile_nil : rtakeWhile p ([] : List α) = [] := by simp [rtakeWhile, takeWhile]
                                                               -- 🎉 no goals
#align list.rtake_while_nil List.rtakeWhile_nil

theorem rtakeWhile_concat (x : α) :
    rtakeWhile p (l ++ [x]) = if p x then rtakeWhile p l ++ [x] else [] := by
  simp only [rtakeWhile, takeWhile, reverse_append, reverse_singleton, singleton_append]
  -- ⊢ reverse
  split_ifs with h <;> simp [h]
                       -- 🎉 no goals
                       -- 🎉 no goals
#align list.rtake_while_concat List.rtakeWhile_concat

@[simp]
theorem rtakeWhile_concat_pos (x : α) (h : p x) :
    rtakeWhile p (l ++ [x]) = rtakeWhile p l ++ [x] := by rw [rtakeWhile_concat, if_pos h]
                                                          -- 🎉 no goals
#align list.rtake_while_concat_pos List.rtakeWhile_concat_pos

@[simp]
theorem rtakeWhile_concat_neg (x : α) (h : ¬p x) : rtakeWhile p (l ++ [x]) = [] := by
  rw [rtakeWhile_concat, if_neg h]
  -- 🎉 no goals
#align list.rtake_while_concat_neg List.rtakeWhile_concat_neg

theorem rtakeWhile_suffix : l.rtakeWhile p <:+ l := by
  rw [← reverse_prefix, rtakeWhile, reverse_reverse]
  -- ⊢ takeWhile p (reverse l) <+: reverse l
  exact takeWhile_prefix _
  -- 🎉 no goals
#align list.rtake_while_suffix List.rtakeWhile_suffix

variable {p} {l}

@[simp]
theorem rtakeWhile_eq_self_iff : rtakeWhile p l = l ↔ ∀ x ∈ l, p x := by
  simp [rtakeWhile, reverse_eq_iff]
  -- 🎉 no goals
#align list.rtake_while_eq_self_iff List.rtakeWhile_eq_self_iff

-- Porting note: This needed a lot of rewriting.
@[simp]
theorem rtakeWhile_eq_nil_iff : rtakeWhile p l = [] ↔ ∀ hl : l ≠ [], ¬p (l.getLast hl) := by
  induction' l using List.reverseRecOn with l a
  -- ⊢ rtakeWhile p [] = [] ↔ ∀ (hl : [] ≠ []), ¬p (getLast [] hl) = true
  · simp only [rtakeWhile, takeWhile, reverse_nil, true_iff]
    -- ⊢ ∀ (hl : [] ≠ []), ¬p (getLast [] hl) = true
    intro f; contradiction
    -- ⊢ ¬p (getLast [] f) = true
             -- 🎉 no goals
  · simp only [rtakeWhile, reverse_append, takeWhile, reverse_eq_nil, getLast_append, ne_eq,
  append_eq_nil, and_false, forall_true_left]
    refine' ⟨fun h => _ , fun h => _⟩
    · intro pa; simp only [pa] at h
      -- ⊢ False
                -- 🎉 no goals
    · simp only [h]
      -- 🎉 no goals
#align list.rtake_while_eq_nil_iff List.rtakeWhile_eq_nil_iff

theorem mem_rtakeWhile_imp {x : α} (hx : x ∈ rtakeWhile p l) : p x := by
  rw [rtakeWhile, mem_reverse] at hx
  -- ⊢ p x = true
  exact mem_takeWhile_imp hx
  -- 🎉 no goals
#align list.mem_rtake_while_imp List.mem_rtakeWhile_imp

variable (p) (l)

theorem rtakeWhile_idempotent : rtakeWhile p (rtakeWhile p l) = rtakeWhile p l :=
  rtakeWhile_eq_self_iff.mpr fun _ => mem_rtakeWhile_imp
#align list.rtake_while_idempotent List.rtakeWhile_idempotent

end List
