/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring.RingNF

/-!
# Hermite's identity for the floor function

This file proves the classical Hermite identity for the floor function: for every
element `x` of a linearly ordered floor field and every natural number `n`,
$$ \sum_{i=0}^{n-1} \left\lfloor x + \frac{i}{n} \right\rfloor = \lfloor n x \rfloor. $$


## Main statements

* `Int.sum_floor_add_div`: Hermite's identity, `∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋`.

## Implementation notes

The proof reduces the real statement to a purely integer one.  Writing `m = ⌊n * x⌋`,
each summand satisfies `⌊x + i / n⌋ = (m + i) / n` (integer/Euclidean division).
The integer identity `∑ i ∈ range n, (m + i) / n = m` (`Int.sum_range_add_ediv`) is then proven and
used in the main statement.
-/

public section

namespace Int

variable {α : Type*} [Field α] [LinearOrder α] [IsOrderedRing α] [FloorRing α]

/-- The discrete (integer) form of Hermite's identity: the sum of `(m + i) / n` over a
complete block `0 ≤ i < n` of consecutive shifts equals `m`, where `/` is Euclidean
(`Int.ediv`) division. -/
theorem sum_range_add_ediv (m : ℤ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (m + i) / n = m := by
  rw [← Int.natCast_pos] at hn
  lift m % n to ℕ using Int.emod_nonneg m (by grind) with t ht
  calc
    _ = ∑ i ∈ Finset.range n, (m / n + if n - t ≤ i then 1 else 0) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Int.add_ediv_of_pos hn]
        grind [Nat.div_eq_zero_iff, Nat.mod_eq_of_lt]
    _ = n * (m / n) + (Finset.Ico (n - t) n).card := by
      simp [Finset.sum_add_distrib, -tsub_le_iff_right, -Nat.sub_le_iff_le_add,
        ← Nat.Ico_zero_eq_range]
    _ = m := by
      have : m % n < n := Int.emod_lt_of_pos _ hn
      grind [Int.mul_ediv_add_emod, Nat.card_Ico]

/-- **Hermite's identity** for the floor function: for every `x` in a linearly ordered
floor field and every `n : ℕ`, `∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋`. -/
theorem sum_floor_add_div (x : α) (n : ℕ) : ∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · calc
      _ = ∑ i ∈ Finset.range n, (⌊(n : α) * x⌋ + (i : ℤ)) / (n : ℤ) :=
          Finset.sum_congr rfl fun i _ ↦
            (by rw [← Int.floor_add_natCast, ← Int.floor_div_natCast]; field_simp)
      _ = ⌊(n : α) * x⌋ := sum_range_add_ediv _ hn

end Int
