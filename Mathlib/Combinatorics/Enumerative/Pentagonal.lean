/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.SuccPred

/-!
# Pentagonal number

This file introduces (generalized) pentagonal numbers $3k(k-1)/2$ for integer $k$.

Some source, such as A001318 in the OEIS, orders generalized pentagonal numbers by indices
$k = 0, 1, -1, 2, -2, \cdots$ to form a strictly monotone sequence. This file doesn't follow this
convention, but implicitly shows the monotonicity by `pentagonal_lt_pentagonal_neg` and
`pentagonal_neg_lt_pentagonal_add_one`.

## Main definitions
* `pentagonal`: pentagonal numbers as a function `ℤ → ℤ`.
* `pentagonalNat`: pentagonal numbers as a function `ℤ → ℕ`, bundling in the fact that pentagonal
  numbers are all non-negative.

## TODO

Show the relation between pentagonal numbers and partitions, including pentagonal number theorem.

## References

* https://en.wikipedia.org/wiki/Pentagonal_number
-/

public section

/-- Pentagonal numbers $3k(k-1)/2$ for integer $k$. -/
@[expose]
def pentagonal (k : ℤ) : ℤ := k * (3 * k - 1) / 2

theorem pentagonal_neg (k : ℤ) : pentagonal (-k) = k * (3 * k + 1) / 2 := by
  grind [pentagonal]

theorem two_pentagonal (k : ℤ) : 2 * pentagonal k = k * (3 * k - 1) :=
  Int.two_mul_ediv_two_of_even (by grind)

theorem two_pentagonal_neg (k : ℤ) : 2 * pentagonal (-k) = k * (3 * k + 1) := by
  grind [two_pentagonal]

theorem pentagonal_nonneg (k : ℤ) : 0 ≤ pentagonal k := by
  simp only [pentagonal, Nat.ofNat_pos, Int.ediv_nonneg_iff_of_pos]
  rcases lt_or_ge 0 k with h | h <;> nlinarith

theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h := congr(2 * $h)
  simp_rw [two_pentagonal] at h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h with h | h <;> grind

@[simp]
theorem pentagonal_inj {x y : ℤ} : pentagonal x = pentagonal y ↔ x = y :=
  pentagonal_injective.eq_iff

theorem pentagonal_lt_pentagonal_neg {k : ℤ} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  grind [pentagonal]

theorem pentagonal_neg_lt_pentagonal_add_one {k : ℤ} (h : 0 ≤ k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  grind [pentagonal]

theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [pentagonal]

theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [pentagonal]

/-- Pentagonal numbers $3k(k-1)/2$ as `Nat` for integer $k$. -/
@[expose]
def pentagonalNat (k : ℤ) : ℕ := (pentagonal k).toNat

@[simp]
theorem natCast_pentagonalNat (k : ℤ) : ↑(pentagonalNat k) = pentagonal k := by
  simp [pentagonalNat, pentagonal_nonneg]

theorem pentagonalNat_injective : Function.Injective pentagonalNat := by
  intro x y h
  zify at h
  simpa using h

@[simp]
theorem pentagonalNat_inj {x y : ℤ} : pentagonalNat x = pentagonalNat y ↔ x = y :=
  pentagonalNat_injective.eq_iff
