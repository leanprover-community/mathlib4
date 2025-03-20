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

lemma abs_sub_lt_of_mem_finset_range {N n m : ℕ} (hn : n ∈ range N) (hm : m ∈ range N) :
    |n - (m : ℤ)| < N := by
  rcases (Nat.lt_or_ge n m) with (h1 | h2)
  · rw [← Int.ofNat_lt, ← sub_pos] at h1
    rw [abs_sub_comm, abs_of_pos h1, ← Int.add_lt_add_iff_right n, sub_add_cancel]
    norm_cast
    exact Nat.lt_add_right n (mem_range.mp hm)
  · rw [ge_iff_le, ← Int.ofNat_le, ← sub_nonneg] at h2
    rw [abs_of_nonneg h2, ← Int.add_lt_add_iff_right m, sub_add_cancel]
    norm_cast
    exact Nat.lt_add_right m (mem_range.mp hn)
