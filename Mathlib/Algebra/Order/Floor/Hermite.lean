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
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
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
each summand satisfies `⌊x + i / n⌋ = (m + i) / n` (integer/Euclidean division), see
`Int.floor_add_natCast_div`.  The integer identity `∑ i ∈ range n, (m + i) / n = m`
(`Int.sum_range_add_ediv`) is then proven by induction on `m`, the key step being that
shifting `m` by one shifts the sum by one.
-/

public section

namespace Int

variable {α : Type*} [Field α] [LinearOrder α] [IsOrderedRing α] [FloorRing α]

/-- The discrete (integer) form of Hermite's identity: the sum of `(m + i) / n` over a
complete block `0 ≤ i < n` of consecutive shifts equals `m`, where `/` is Euclidean
(`Int.ediv`) division. -/
theorem sum_range_add_ediv (m : ℤ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (m + i) / n = m := by
  -- key step: replacing `m` by `m + 1` increases the sum by exactly one.
  have key : ∀ k : ℤ,
      ∑ i ∈ Finset.range n, (k + 1 + i) / n = (∑ i ∈ Finset.range n, (k + i) / n) + 1 := by
    intro k
    -- View the summands as `f` evaluated at `i` and at `i + 1`.
    set f : ℕ → ℤ := fun i ↦ (k + i) / n with hf
    have hshift : ∑ i ∈ Finset.range n, (k + 1 + i) / n = ∑ i ∈ Finset.range n, f (i + 1) := by
      simp [hf, add_comm, add_left_comm]
    rw [hshift]
    have hfn : f n = f 0 + 1 := by
      simp only [hf, Nat.cast_zero, add_zero]
      rw [show k + n = k + 1 * n by ring, Int.add_mul_ediv_right _ _ (by exact_mod_cast hn.ne')]
    have hsum : (∑ i ∈ Finset.range n, f (i + 1)) + f 0 = (∑ i ∈ Finset.range n, f i) + f n := by
      rw [← Finset.sum_range_succ', ← Finset.sum_range_succ]
    rw [hfn] at hsum
    linarith [hsum]
  -- Induct on `m`, using `key` in both directions.
  induction m using Int.induction_on with
  | zero =>
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [zero_add]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast Finset.mem_range.mp hi)
  | succ k ih => exact (key k).trans (congrArg (· + 1) ih)
  | pred k ih => grind [key (-k - 1)]

/-- Reduction of a real floor to an integer (Euclidean) division:
`⌊x + i / n⌋ = (⌊n * x⌋ + i) / n`. -/
theorem floor_add_natCast_div (x : α) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    ⌊x + (i : α) / n⌋ = (⌊(n : α) * x⌋ + i) / n := by
  have hn0 : (n : α) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show x + (i : α) / n = ((n : α) * x + i) / n by field_simp,
    Int.floor_div_natCast, Int.floor_add_natCast]

/-- **Hermite's identity** for the floor function: for every `x` in a linearly ordered
floor field and every `n : ℕ`, `∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋`. -/
theorem sum_floor_add_div (x : α) (n : ℕ) : ∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · calc
      _ = ∑ i ∈ Finset.range n, (⌊(n : α) * x⌋ + (i : ℤ)) / (n : ℤ) :=
          Finset.sum_congr rfl fun i _ ↦ floor_add_natCast_div x hn i
      _ = ⌊(n : α) * x⌋ := sum_range_add_ediv _ hn

end Int
