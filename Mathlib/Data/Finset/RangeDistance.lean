/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Distance between elements of Finset range

## Implementation

Separate from `Data.Finset.Range` to avoid additional imports
-/

@[expose] public section

open Finset

lemma abs_sub_lt_of_mem_finset_range {N n m : ℕ} (hn : n ∈ range N) (hm : m ∈ range N) :
    |n - (m : ℤ)| < N := by
  rw [← max_sub_min_eq_abs']
  rw [mem_range] at hn hm
  omega
