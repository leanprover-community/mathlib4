module

import Mathlib.Data.Nat.Fib.Basic

/-!
The examples below are ported from the [Rocq supplementary material](https://zenodo.org/records/13855491)
accompanying Olivier Danvy's "[Nested Summations](https://doi.org/10.1145/3694848.3694858)".
-/

open Nat Finset

def fibf (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | 1 => f 1
  | n + 2 => fibf f (n + 1) + fibf f n

example {f : ℕ → ℕ} {n : ℕ} : fibf f (n + 1) = f 1 * fib (n + 1) + f 0 * fib n := by
  induction n using stepInduction 2 with
  | base n hn =>
    obtain rfl | rfl : n = 0 ∨ n = 1 := by lia
    all_goals simp [fibf]
  | step n ih => grind [fibf, fib_add_two, ih 0 (by decide)]

def a6356 : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | n + 3 => 2 * a6356 (n + 2) + a6356 (n + 1) - a6356 n

def a6356Sum (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => f (2 - i)
  | n + 1, i => ∑ j ∈ range (3 - i), a6356Sum f n j

lemma strictMono_a6356 : StrictMono a6356 := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  induction n using stepInduction 3 with
  | base n hn => decide +revert
  | step n ih => grind [a6356]

example {n : ℕ} : a6356Sum (· - 1) (n + 1) 0 = a6356 n := by
  induction n using stepInduction 3 with
  | base n hn => decide +revert
  | step n ih =>
    have := strictMono_a6356 (lt_add_one n)
    rw [← add_left_inj (a6356 n), a6356, Nat.sub_add_cancel (by lia)]
    grind [sum_range_succ, sum_range_one, a6356Sum, ih 0 (by decide)]
