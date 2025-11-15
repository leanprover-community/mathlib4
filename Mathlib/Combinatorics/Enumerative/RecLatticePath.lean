/-
Copyright (c) 2025 YiranWang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wang Yiran
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Monotone lattice paths and a ballot-style subdiagonal condition

This file defines and studies monotone lattice paths.  It introduces:
* `pathCount`, `pathCountFrom` and their closed forms,
* a Dyck/ballot-style subdiagonal condition on words (`SubdiagProp`) and the corresponding set.

## Main statements
* `pathCount_eq_closed : pathCount m n = (m + n).choose m`
* `pathCountFrom_eq_closed`
-/

open Nat

universe u

/--
Number of monotone lattice paths from `(0, 0)` to `(m, n)` using only
right `(1, 0)` and up `(0, 1)` steps.
-/
def pathCount : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _, 0 => 1
  | m + 1, n + 1 => pathCount (m + 1) n + pathCount m (n + 1)

/--
Closed form for `pathCount`: the number of lattice paths from `(0, 0)` to `(m, n)`
equals `(m + n).choose m`.
-/
theorem pathCount_eq_closed : ∀ m n, pathCount m n = (m + n).choose m := by
  intro m
  induction m with
  | zero =>
    intro n
    simp [pathCount, Nat.choose_zero_right]
  | succ m ih =>
    intro n
    induction n with
    | zero =>
      simp [pathCount]
    | succ n ih' =>
      simp only [pathCount]
      rw [ih', ih]
      have h : (m + 1 + (n + 1)) = (m + n + 2) := by ring
      rw [h]
      rw [Nat.choose_succ_succ, Nat.add_comm]
      congr! 1
      simp
      rw [Nat.add_right_comm]

/-- Diagonal specialization of `pathCount_eq_closed`. -/
theorem pathCount_eq_closed_n_n : ∀ n, pathCount n n = (2 * n).choose n := by
  intro n
  simpa [two_mul] using (pathCount_eq_closed n n)
