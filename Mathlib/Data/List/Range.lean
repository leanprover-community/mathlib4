/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Kim Morrison
-/
import Mathlib.Data.List.Chain

/-!
# Ranges of naturals as lists

This file shows basic results about `List.iota`, `List.range`, `List.range'`
and defines `List.finRange`.
`finRange n` is the list of elements of `Fin n`.
`iota n = [n, n - 1, ..., 1]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

universe u

open Nat

namespace List

variable {α : Type u}

theorem getElem_range'_1 {n m} (i) (H : i < (range' n m).length) :
    (range' n m)[i] = n + i := by simp

theorem chain'_range_succ (r : ℕ → ℕ → Prop) (n : ℕ) :
    Chain' r (range n.succ) ↔ ∀ m < n, r m m.succ := by
  rw [range_succ]
  induction' n with n hn
  · simp
  · rw [range_succ]
    simp only [append_assoc, singleton_append, chain'_append_cons_cons, chain'_singleton, and_true]
    rw [hn, forall_lt_succ]

theorem chain_range_succ (r : ℕ → ℕ → Prop) (n a : ℕ) :
    Chain r a (range n.succ) ↔ r a 0 ∧ ∀ m < n, r m m.succ := by
  rw [range_succ_eq_map, chain_cons, and_congr_right_iff, ← chain'_range_succ, range_succ_eq_map]
  exact fun _ => Iff.rfl

@[deprecated (since := "2024-08-19")] alias nthLe_range' := get_range'
@[deprecated (since := "2024-08-19")] alias nthLe_range'_1 := getElem_range'_1
@[deprecated (since := "2024-08-19")] alias nthLe_range := get_range


section Ranges

/-- From `l : List ℕ`, construct `l.ranges : List (List ℕ)` such that
  `l.ranges.map List.length = l` and `l.ranges.join = range l.sum`
* Example: `[1,2,3].ranges = [[0],[1,2],[3,4,5]]` -/
def ranges : List ℕ → List (List ℕ)
  | [] => nil
  | a::l => range a::(ranges l).map (map (a + ·))

/-- The members of `l.ranges` are pairwise disjoint -/
theorem ranges_disjoint (l : List ℕ) :
    Pairwise Disjoint (ranges l) := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l hl =>
    simp only [ranges, pairwise_cons]
    constructor
    · intro s hs
      obtain ⟨s', _, rfl⟩ := mem_map.mp hs
      intro u hu
      rw [mem_map]
      rintro ⟨v, _, rfl⟩
      rw [mem_range] at hu
      omega
    · rw [pairwise_map]
      apply Pairwise.imp _ hl
      intro u v
      apply disjoint_map
      exact fun u v => Nat.add_left_cancel

/-- The lengths of the members of `l.ranges` are those given by `l` -/
theorem ranges_length (l : List ℕ) :
    l.ranges.map length = l := by
  induction l with
  | nil => simp only [ranges, map_nil]
  | cons a l hl => -- (a :: l)
    simp only [map, length_range, map_map, cons.injEq, true_and]
    conv_rhs => rw [← hl]
    apply map_congr_left
    intro s _
    simp only [Function.comp_apply, length_map]

set_option linter.deprecated false in
/-- See `List.ranges_flatten` for the version about `List.sum`. -/
@[deprecated "Use `List.ranges_flatten`." (since := "2024-10-17")]
lemma ranges_flatten' : ∀ l : List ℕ, l.ranges.flatten = range (Nat.sum l)
  | [] => rfl
  | a :: l => by simp only [Nat.sum_cons, flatten, ← map_flatten, ranges_flatten', range_add]

@[deprecated (since := "2024-10-15")] alias ranges_join' := ranges_flatten'

set_option linter.deprecated false in
/-- Any entry of any member of `l.ranges` is strictly smaller than `Nat.sum l`.
See `List.mem_mem_ranges_iff_lt_sum` for the version about `List.sum`. -/
@[deprecated "Use `List.mem_mem_ranges_iff_lt_sum`." (since := "2024-11-18")]
lemma mem_mem_ranges_iff_lt_natSum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ l.ranges, n ∈ s) ↔ n < Nat.sum l := by
  rw [← mem_range, ← ranges_flatten', mem_flatten]

end Ranges

end List
