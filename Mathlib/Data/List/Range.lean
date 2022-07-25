/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison
-/
import Mathlib.Data.List.Chain

/-!
# Ranges of naturals as lists
This file shows basic results about `List.iota`, `List.range`, `List.range'` (all deFined in
`data.List.defs`) and deFines `List.finRange`.
`finRange n` is the List of elements of `Fin n`.
`iota n = [1, ..., n]` and `range n = [0, ..., n - 1]` are basic List constructions used for
tactics. `range' a b = [a, ..., a + b - 1]` is there to help prove properties about them.
Actual maths should use `List.Ico` instead.
-/

universe u

open Nat

namespace List
variable {α : Type u}
#check List.range
@[simp] theorem mem_range' {m : ℕ} : ∀ {s n : ℕ}, m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by sorry
-- | s 0     := (false_iff _).2 $ λ ⟨H1, H2⟩, not_le_of_lt H2 H1
-- | s (succ n) :=
--   have m = s → m < s + n + 1,
--     from λ e, e ▸ lt_succ_of_le (nat.le_add_right _ _),
--   have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m,
--     by simpa only [eq_comm] using (@decidable.le_iff_eq_or_lt _ _ _ s m).symm,
--   (mem_cons_iff _ _ _).trans $ by simp only [mem_range',
--     or_and_distrib_left, or_iff_right_of_imp this, l, add_right_comm]; refl

theorem Pairwise_lt_range' : ∀ s n : ℕ, Pairwise (·<·) (range' s n)
| s, 0   => Pairwise.nil
| s, n+1 => Chain_iff_Pairwise.1 sorry -- (chain_lt_range' s n)

theorem nodup_range' (s n : ℕ) : Nodup (range' s n) := sorry
-- (Pairwise_lt_range' s n).imp (λ a b => ne_of_lt)

theorem rangeAux_range' : ∀ s n : ℕ, rangeAux s (range' s n) = range' 0 (n + s)
| 0,   n => rfl
| s+1, n => by rw [show n+(s+1) = n+1+s from Nat.add_right_comm n s 1];
               exact rangeAux_range' s (n+1)

theorem range_eq_range' (n : ℕ) : range n = range' 0 n :=
(rangeAux_range' n 0).trans $ by rw [Nat.zero_add]

theorem nodup_range (n : ℕ) : Nodup (range n) :=
by simp [range_eq_range', nodup_range']

@[simp] theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
by simp only [range_eq_range', mem_range', Nat.zero_le, true_and, Nat.zero_add]; rfl

/-- All elements of `Fin n`, from `0` to `n-1`. -/
def finRange (n : ℕ) : List (Fin n) :=
(range n).pmap Fin.mk (λ _ => List.mem_range.1)

@[simp] lemma finRange_zero : finRange 0 = [] := rfl

@[simp] lemma mem_finRange {n : ℕ} (a : Fin n) : a ∈ finRange n :=
mem_pmap.2 ⟨a.1, mem_range.2 a.2, rfl⟩

lemma Nodup_finRange (n : ℕ) : (finRange n).Nodup :=
sorry -- (nodup_range _).pmap $ λ _ _ _ _ => fin.veq_of_eq
