/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Parity
import Mathlib.Data.List.Chain

#align_import data.bool.count from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# List of booleans

In this file we prove lemmas about the number of `false`s and `true`s in a list of booleans. First
we prove that the number of `false`s plus the number of `true` equals the length of the list. Then
we prove that in a list with alternating `true`s and `false`s, the number of `true`s differs from
the number of `false`s by at most one. We provide several versions of these statements.
-/


namespace List

@[simp]
theorem count_not_add_count (l : List Bool) (b : Bool) : count (!b) l + count b l = length l := by
  -- Porting note: Proof re-written
  -- Old proof: simp only [length_eq_countP_add_countP (Eq (!b)), Bool.not_not_eq, count]
  simp only [length_eq_countP_add_countP (· == !b), count, add_right_inj]
  -- ⊢ countP (fun x => x == b) l = countP (fun a => decide ¬(a == !b) = true) l
  suffices : (fun x => x == b) = (fun a => decide ¬(a == !b) = true); rw [this]
  -- ⊢ countP (fun x => x == b) l = countP (fun a => decide ¬(a == !b) = true) l
                                                                      -- ⊢ (fun x => x == b) = fun a => decide ¬(a == !b) = true
  ext x; cases x <;> cases b <;> rfl
  -- ⊢ (x == b) = decide ¬(x == !b) = true
         -- ⊢ (false == b) = decide ¬(false == !b) = true
                     -- ⊢ (false == false) = decide ¬(false == !false) = true
                     -- ⊢ (true == false) = decide ¬(true == !false) = true
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align list.count_bnot_add_count List.count_not_add_count

@[simp]
theorem count_add_count_not (l : List Bool) (b : Bool) : count b l + count (!b) l = length l := by
  rw [add_comm, count_not_add_count]
  -- 🎉 no goals
#align list.count_add_count_bnot List.count_add_count_not

@[simp]
theorem count_false_add_count_true (l : List Bool) : count false l + count true l = length l :=
  count_not_add_count l true
#align list.count_ff_add_count_tt List.count_false_add_count_true

@[simp]
theorem count_true_add_count_false (l : List Bool) : count true l + count false l = length l :=
  count_not_add_count l false
#align list.count_tt_add_count_ff List.count_true_add_count_false

theorem Chain.count_not :
    ∀ {b : Bool} {l : List Bool}, Chain (· ≠ ·) b l → count (!b) l = count b l + length l % 2
  | b, [], _h => rfl
  | b, x :: l, h => by
    obtain rfl : b = !x := Bool.eq_not_iff.2 (rel_of_chain_cons h)
    -- ⊢ count (!!x) (x :: l) = count (!x) (x :: l) + length (x :: l) % 2
    rw [Bool.not_not, count_cons_self, count_cons_of_ne x.not_ne_self,
      Chain.count_not (chain_of_chain_cons h), length, add_assoc, Nat.mod_two_add_succ_mod_two]
#align list.chain.count_bnot List.Chain.count_not

namespace Chain'

variable {l : List Bool}

theorem count_not_eq_count (hl : Chain' (· ≠ ·) l) (h2 : Even (length l)) (b : Bool) :
    count (!b) l = count b l := by
  cases' l with x l
  -- ⊢ count (!b) [] = count b []
  · rfl
    -- 🎉 no goals
  rw [length_cons, Nat.even_add_one, Nat.not_even_iff] at h2
  -- ⊢ count (!b) (x :: l) = count b (x :: l)
  suffices count (!x) (x :: l) = count x (x :: l) by
    -- Porting note: old proof is
    -- cases b <;> cases x <;> try exact this;
    cases b <;> cases x <;>
    revert this <;> simp only [Bool.not_false, Bool.not_true] <;> intro this <;>
    (try exact this) <;> exact this.symm
  rw [count_cons_of_ne x.not_ne_self, hl.count_not, h2, count_cons_self]
  -- 🎉 no goals
#align list.chain'.count_bnot_eq_count List.Chain'.count_not_eq_count

theorem count_false_eq_count_true (hl : Chain' (· ≠ ·) l) (h2 : Even (length l)) :
    count false l = count true l :=
  hl.count_not_eq_count h2 true
#align list.chain'.count_ff_eq_count_tt List.Chain'.count_false_eq_count_true

theorem count_not_le_count_add_one (hl : Chain' (· ≠ ·) l) (b : Bool) :
    count (!b) l ≤ count b l + 1 := by
  cases' l with x l
  -- ⊢ count (!b) [] ≤ count b [] + 1
  · exact zero_le _
    -- 🎉 no goals
  obtain rfl | rfl : b = x ∨ b = !x := by simp only [Bool.eq_not_iff, em]
  -- ⊢ count (!b) (b :: l) ≤ count b (b :: l) + 1
  · rw [count_cons_of_ne b.not_ne_self, count_cons_self, hl.count_not, add_assoc]
    -- ⊢ count b l + length l % 2 ≤ count b l + (1 + 1)
    exact add_le_add_left (Nat.mod_lt _ two_pos).le _
    -- 🎉 no goals
  · rw [Bool.not_not, count_cons_self, count_cons_of_ne x.not_ne_self, hl.count_not]
    -- ⊢ count x l + 1 ≤ count x l + length l % 2 + 1
    exact add_le_add_right (le_add_right le_rfl) _
    -- 🎉 no goals
#align list.chain'.count_bnot_le_count_add_one List.Chain'.count_not_le_count_add_one

theorem count_false_le_count_true_add_one (hl : Chain' (· ≠ ·) l) :
    count false l ≤ count true l + 1 :=
  hl.count_not_le_count_add_one true
#align list.chain'.count_ff_le_count_tt_add_one List.Chain'.count_false_le_count_true_add_one

theorem count_true_le_count_false_add_one (hl : Chain' (· ≠ ·) l) :
    count true l ≤ count false l + 1 :=
  hl.count_not_le_count_add_one false
#align list.chain'.count_tt_le_count_ff_add_one List.Chain'.count_true_le_count_false_add_one

theorem two_mul_count_bool_of_even (hl : Chain' (· ≠ ·) l) (h2 : Even (length l)) (b : Bool) :
    2 * count b l = length l := by
  rw [← count_not_add_count l b, hl.count_not_eq_count h2, two_mul]
  -- 🎉 no goals
#align list.chain'.two_mul_count_bool_of_even List.Chain'.two_mul_count_bool_of_even

theorem two_mul_count_bool_eq_ite (hl : Chain' (· ≠ ·) l) (b : Bool) :
    2 * count b l =
      if Even (length l) then length l else
      if Option.some b == l.head? then length l + 1 else length l - 1 := by
  by_cases h2 : Even (length l)
  -- ⊢ 2 * count b l = if Even (length l) then length l else if (some b == head? l) …
  · rw [if_pos h2, hl.two_mul_count_bool_of_even h2]
    -- 🎉 no goals
  · cases' l with x l
    -- ⊢ 2 * count b [] = if Even (length []) then length [] else if (some b == head? …
    · exact (h2 even_zero).elim
      -- 🎉 no goals
    simp only [if_neg h2, count_cons, mul_add, head?, Option.mem_some_iff, @eq_comm _ x]
    -- ⊢ (2 * count b l + 2 * if b = x then 1 else 0) = if (some b == some x) = true  …
    rw [length_cons, Nat.even_add_one, not_not] at h2
    -- ⊢ (2 * count b l + 2 * if b = x then 1 else 0) = if (some b == some x) = true  …
    replace hl : l.Chain' (· ≠ ·) := hl.tail
    -- ⊢ (2 * count b l + 2 * if b = x then 1 else 0) = if (some b == some x) = true  …
    rw [hl.two_mul_count_bool_of_even h2]
    -- ⊢ (length l + 2 * if b = x then 1 else 0) = if (some b == some x) = true then  …
    cases b <;> cases x <;> split_ifs <;> simp <;> contradiction
    -- ⊢ (length l + 2 * if false = x then 1 else 0) = if (some false == some x) = tr …
                -- ⊢ (length l + 2 * if false = false then 1 else 0) = if (some false == some fal …
                -- ⊢ (length l + 2 * if true = false then 1 else 0) = if (some true == some false …
                                          -- 🎉 no goals
                                          -- ⊢ False
                                          -- ⊢ length l = Nat.succ (length l) + 1
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- ⊢ False
                                          -- ⊢ length l = Nat.succ (length l) + 1
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- ⊢ False
                                          -- ⊢ length l = Nat.succ (length l) + 1
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- ⊢ False
                                          -- ⊢ length l = Nat.succ (length l) + 1
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- ⊢ False
                                          -- ⊢ length l = Nat.succ (length l) + 1
                                          -- 🎉 no goals
                                          -- 🎉 no goals
                                          -- ⊢ False
                                          -- ⊢ length l = Nat.succ (length l) + 1
                                          -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
                                                   -- 🎉 no goals
#align list.chain'.two_mul_count_bool_eq_ite List.Chain'.two_mul_count_bool_eq_ite

theorem length_sub_one_le_two_mul_count_bool (hl : Chain' (· ≠ ·) l) (b : Bool) :
    length l - 1 ≤ 2 * count b l := by
  rw [hl.two_mul_count_bool_eq_ite]
  -- ⊢ length l - 1 ≤ if Even (length l) then length l else if (some b == head? l)  …
  split_ifs <;> simp [le_tsub_add, Nat.le_succ_of_le]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align list.chain'.length_sub_one_le_two_mul_count_bool List.Chain'.length_sub_one_le_two_mul_count_bool

theorem length_div_two_le_count_bool (hl : Chain' (· ≠ ·) l) (b : Bool) :
    length l / 2 ≤ count b l := by
  rw [Nat.div_le_iff_le_mul_add_pred two_pos, ← tsub_le_iff_right]
  -- ⊢ length l - (2 - 1) ≤ 2 * count b l
  exact length_sub_one_le_two_mul_count_bool hl b
  -- 🎉 no goals
#align list.chain'.length_div_two_le_count_bool List.Chain'.length_div_two_le_count_bool

theorem two_mul_count_bool_le_length_add_one (hl : Chain' (· ≠ ·) l) (b : Bool) :
    2 * count b l ≤ length l + 1 := by
  rw [hl.two_mul_count_bool_eq_ite]
  -- ⊢ (if Even (length l) then length l else if (some b == head? l) = true then le …
  split_ifs <;> simp [Nat.le_succ_of_le]
                -- 🎉 no goals
                -- 🎉 no goals
                -- 🎉 no goals
#align list.chain'.two_mul_count_bool_le_length_add_one List.Chain'.two_mul_count_bool_le_length_add_one

end Chain'

end List
