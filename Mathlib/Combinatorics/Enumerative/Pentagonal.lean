/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Int.SuccPred
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.LinearCombination

/-!
# Pentagonal number

This file introduces (generalized) pentagonal numbers $k(3k-1)/2$ for integer $k$.

Some source, such as A001318 in the OEIS, orders generalized pentagonal numbers by indices
$k = 0, 1, -1, 2, -2, \cdots$ to form a strictly monotone sequence. This file doesn't follow this
convention, but implicitly shows the monotonicity by `pentagonal_lt_pentagonal_neg` and
`pentagonal_neg_lt_pentagonal_add_one`.

## Main definitions
* `pentagonal`: pentagonal numbers as a function `ℤ → ℕ`.

## TODO

Show the relation between pentagonal numbers and partitions, including pentagonal number theorem.

## References

* https://en.wikipedia.org/wiki/Pentagonal_number
-/

public section

/-- Pentagonal numbers $k(3k-1)/2$ for integer $k$. -/
def pentagonal (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

theorem pentagonal_def (k : ℤ) : pentagonal k = (k * (3 * k - 1) / 2).toNat := by rfl

theorem pentagonal_neg (k : ℤ) : pentagonal (-k) = (k * (3 * k + 1) / 2).toNat := by
  grind [pentagonal_def]

theorem natCast_pentagonal (k : ℤ) : (pentagonal k : ℤ) = k * (3 * k - 1) / 2 := by
  simp only [pentagonal_def, Int.ofNat_toNat, sup_eq_left, Nat.ofNat_pos,
    Int.ediv_nonneg_iff_of_pos]
  rcases lt_or_ge 0 k with h | h <;> nlinarith

theorem two_mul_natCast_pentagonal (k : ℤ) : 2 * (pentagonal k : ℤ) = k * (3 * k - 1) := by
  rw [natCast_pentagonal]
  exact Int.two_mul_ediv_two_of_even (by grind)

theorem two_mul_natCast_pentagonal_neg (k : ℤ) : 2 * (pentagonal (-k) : ℤ) = k * (3 * k + 1) := by
  grind [two_mul_natCast_pentagonal]

theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h := congr(2 * ($h : ℤ))
  simp_rw [two_mul_natCast_pentagonal] at h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h with h | h <;> grind

@[simp]
theorem pentagonal_inj {x y : ℤ} : pentagonal x = pentagonal y ↔ x = y :=
  pentagonal_injective.eq_iff

theorem pentagonal_lt_pentagonal_neg {k : ℤ} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  zify
  grind [natCast_pentagonal]

theorem pentagonal_neg_lt_pentagonal_add_one {k : ℤ} (h : 0 ≤ k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  zify
  grind [natCast_pentagonal]

theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  zify
  grind [natCast_pentagonal]

theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  zify
  grind [natCast_pentagonal]
