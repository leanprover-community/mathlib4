/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Group.Int.Defs

/-!
# Distance between elements of Finset range

## Implementation

Separate from `Data.Finset.Range` to avoid additional imports
-/

open Finset

lemma abs_sub_lt_of_mem_finset_range (N n m : ℕ) (hn : n ∈ range N) (hm : m ∈ range N) :
    |n - (m : ℤ)| < N := by
  simp_all only [mem_range]
  rcases (Nat.lt_or_ge n m) with (h1 | h2)
  · have e1 : 0 < m-(n : ℤ) := by
      simp_all only [sub_pos, Int.ofNat_lt]
    rw [abs_sub_comm]
    rw [abs_of_pos e1]
    rw [← Int.add_lt_add_iff_right n]
    rw [sub_add_cancel]
    norm_cast
    exact Nat.lt_add_right n hm
  · have e1 : 0 ≤ n-(m : ℤ) := by
      simp_all only [sub_nonneg, Int.ofNat_le]
    rw [abs_of_nonneg e1]
    rw [← Int.add_lt_add_iff_right m]
    rw [sub_add_cancel]
    norm_cast
    exact Nat.lt_add_right m hn
