/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Order.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Chain

/-!
# Ranges of naturals as lists

This file shows basic results about `List.iota`, `List.range`, `List.range'` (all defined in
`Std.Data.List.Basic`) and defines `List.finRange`.
`finRange n` is the list of elements of `fin n`.
`iota n = [1, ..., n]` and `range n = [0, ..., n - 1]` are basic list constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

namespace List

open Nat

@[simp]
theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n
  | s, 0 => by simp
  | s, succ n =>
    have : m = s → m < s + n + 1 := fun e => e ▸ lt_succ_of_le (Nat.le_add_right _ _)
    have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m := by
      simpa only [eq_comm] using (@Decidable.le_iff_eq_or_lt _ _ _ s m).symm
    mem_cons.trans <| by
      simp only [mem_range', or_and_left, or_iff_right_of_imp this, l, Nat.add_right_comm]
        <;> rfl

theorem rangeAux_range' : ∀ s n : ℕ, rangeAux s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by
    rw [show n + (s + 1) = n + 1 + s from Nat.add_right_comm n s 1]
    exact rangeAux_range' s (n + 1)

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
  (rangeAux_range' n 0).trans <| by rw [Nat.zero_add]

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range', Nat.zero_le, true_and, Nat.zero_add]
  rfl

theorem chain_succ_range' : ∀ s n : ℕ, Chain (fun a b => b = succ a) s (range' (s + 1) n)
  | _, 0 => Chain.nil
  | s, n + 1 => (chain_succ_range' (s + 1) n).cons rfl

theorem chain_lt_range' (s n : ℕ) : Chain (· < ·) s (range' (s + 1) n) :=
  (chain_succ_range' s n).imp fun _ _ e => e.symm ▸ lt_succ_self _

theorem pairwise_lt_range' : ∀ s n : ℕ, Pairwise (· < ·) (range' s n)
  | _, 0 => Pairwise.nil
  | s, n + 1 => chain_iff_pairwise.1 (chain_lt_range' s n)

theorem nodup_range' (s n : ℕ) : Nodup (range' s n) :=
  (pairwise_lt_range' s n).imp Nat.ne_of_lt

theorem nodup_range (n : ℕ) : Nodup (range n) := by
  simp only [range_eq_range', nodup_range']

/-- All elements of `fin n`, from `0` to `n-1`. The corresponding finset is `finset.univ`. -/
def finRange (n : ℕ) : List (Fin n) := (range n).pmap Fin.mk fun _ => mem_range.1

@[simp] theorem fin_range_zero : finRange 0 = [] := rfl

@[simp]
theorem mem_fin_range {n : ℕ} (a : Fin n) : a ∈ finRange n :=
  mem_pmap.2 ⟨a.1, mem_range.2 a.2, Fin.eta _ _⟩

theorem nodup_fin_range (n : ℕ) : (finRange n).Nodup :=
  (nodup_range _).pmap fun _ _ _ _ => Fin.val_eq_of_eq
