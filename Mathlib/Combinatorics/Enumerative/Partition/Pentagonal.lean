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

-/

public section

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
  obtain h | h := lt_or_ge 0 k
  · exact mul_nonneg h.le (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)

theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h := congr(2 * $h)
  simp_rw [two_pentagonal] at h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h with h | h <;> grind

@[simp]
theorem pentagonal_inj {x y : ℤ} : pentagonal x = pentagonal y ↔ x = y :=
  ⟨fun h ↦ pentagonal_injective h, fun h ↦ congrArg _ h⟩

theorem pentagonal_lt_pentagonal_neg {k : ℤ} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  grind [pentagonal]

theorem pentagonal_neg_lt_pentagonal_add_one {k : ℤ} (h : 0 ≤ k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  grind [pentagonal]

theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  refine strictMonoOn_of_lt_add_one Set.ordConnected_Ici fun k hm h h' ↦ ?_
  grind [pentagonal]

theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  refine strictAntiOn_of_add_one_lt Set.ordConnected_Iic fun k hm h h' ↦ ?_
  grind [pentagonal]

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
  ⟨fun h ↦ pentagonalNat_injective h, fun h ↦ congrArg _ h⟩
