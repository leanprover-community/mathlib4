/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.List.Chain

/-!
# List of Booleans

In this file we prove lemmas about the number of `false`s and `true`s in a list of Booleans. First
we prove that the number of `false`s plus the number of `true` equals the length of the list. Then
we prove that in a list with alternating `true`s and `false`s, the number of `true`s differs from
the number of `false`s by at most one. We provide several versions of these statements.
-/


namespace List

@[simp]
theorem count_not_add_count (l : List Bool) (b : Bool) : count (!b) l + count b l = length l := by
  have := length_eq_countP_add_countP (l := l) (· == !b)
  aesop (add simp this)

grind_pattern count_not_add_count => count (!b) l

@[simp]
theorem count_add_count_not (l : List Bool) (b : Bool) : count b l + count (!b) l = length l := by
  grind

@[simp]
theorem count_false_add_count_true (l : List Bool) : count false l + count true l = length l :=
  count_not_add_count l true

grind_pattern count_false_add_count_true => count false l
grind_pattern count_false_add_count_true => count true l

@[simp]
theorem count_true_add_count_false (l : List Bool) : count true l + count false l = length l :=
  count_not_add_count l false

theorem Chain.count_not :
    ∀ {b : Bool} {l : List Bool}, Chain (· ≠ ·) b l → count (!b) l = count b l + length l % 2
  | _, [], _h => rfl
  | b, x :: l, h => by
    obtain rfl : b = !x := Bool.eq_not_iff.2 (rel_of_chain_cons h)
    rw [Bool.not_not, count_cons_self, count_cons_of_ne x.not_ne_self.symm,
      Chain.count_not (chain_of_chain_cons h), length, add_assoc, Nat.mod_two_add_succ_mod_two]

namespace Chain'

variable {l : List Bool}

theorem count_not_eq_count (hl : Chain' (· ≠ ·) l) (h2 : Even (length l)) (b : Bool) :
    count (!b) l = count b l := by
  rcases l with - | ⟨x, l⟩
  · rfl
  rw [length_cons, Nat.even_add_one, Nat.not_even_iff] at h2
  suffices count (!x) (x :: l) = count x (x :: l) by grind
  rw [count_cons_of_ne x.not_ne_self.symm, hl.count_not, h2, count_cons_self]

theorem count_false_eq_count_true (hl : Chain' (· ≠ ·) l) (h2 : Even (length l)) :
    count false l = count true l :=
  hl.count_not_eq_count h2 true

theorem count_not_le_count_add_one (hl : Chain' (· ≠ ·) l) (b : Bool) :
    count (!b) l ≤ count b l + 1 := by
  rcases l with - | ⟨x, l⟩
  · exact zero_le _
  obtain rfl | rfl : b = x ∨ b = !x := by simp only [Bool.eq_not_iff, em]
  · rw [count_cons_of_ne b.not_ne_self.symm, count_cons_self, hl.count_not, add_assoc]
    cutsat
  · rw [Bool.not_not, count_cons_self, count_cons_of_ne x.not_ne_self.symm, hl.count_not]
    cutsat

theorem count_false_le_count_true_add_one (hl : Chain' (· ≠ ·) l) :
    count false l ≤ count true l + 1 :=
  hl.count_not_le_count_add_one true

theorem count_true_le_count_false_add_one (hl : Chain' (· ≠ ·) l) :
    count true l ≤ count false l + 1 :=
  hl.count_not_le_count_add_one false

theorem two_mul_count_bool_of_even (hl : Chain' (· ≠ ·) l) (h2 : Even (length l)) (b : Bool) :
    2 * count b l = length l := by
  rw [← count_not_add_count l b, hl.count_not_eq_count h2, two_mul]

theorem two_mul_count_bool_eq_ite (hl : Chain' (· ≠ ·) l) (b : Bool) :
    2 * count b l =
      if Even (length l) then length l else
      if Option.some b == l.head? then length l + 1 else length l - 1 := by
  by_cases h2 : Even (length l)
  · rw [if_pos h2, hl.two_mul_count_bool_of_even h2]
  · rcases l with - | ⟨x, l⟩
    · exact (h2 .zero).elim
    simp only [if_neg h2, count_cons, mul_add, head?]
    rw [length_cons, Nat.even_add_one, not_not] at h2
    replace hl : l.Chain' (· ≠ ·) := hl.tail
    rw [hl.two_mul_count_bool_of_even h2]
    cases b <;> cases x <;> split_ifs <;> simp <;> contradiction

theorem length_sub_one_le_two_mul_count_bool (hl : Chain' (· ≠ ·) l) (b : Bool) :
    length l - 1 ≤ 2 * count b l := by
  rw [hl.two_mul_count_bool_eq_ite]
  split_ifs <;> simp [Nat.le_succ_of_le]

theorem length_div_two_le_count_bool (hl : Chain' (· ≠ ·) l) (b : Bool) :
    length l / 2 ≤ count b l := by
  rw [Nat.div_le_iff_le_mul_add_pred two_pos, ← tsub_le_iff_right]
  exact length_sub_one_le_two_mul_count_bool hl b

theorem two_mul_count_bool_le_length_add_one (hl : Chain' (· ≠ ·) l) (b : Bool) :
    2 * count b l ≤ length l + 1 := by
  rw [hl.two_mul_count_bool_eq_ite]
  split_ifs <;> simp [Nat.le_succ_of_le]

end Chain'

end List
