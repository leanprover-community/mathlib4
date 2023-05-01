/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Data.Int.Parity

namespace CochainComplex

def ε (n : ℤ) : ℤ := (-1 : Units ℤ) ^ n

lemma ε_add (n₁ n₂ : ℤ) : ε (n₁ + n₂) = ε n₁ * ε n₂ := by
  simp only [ε, ← Units.val_mul, ← Units.ext_iff, zpow_add]

@[simp]
lemma ε_0 : ε 0 = 1 := rfl

@[simp]
lemma ε_1 : ε 1 = -1 := rfl

lemma ε_succ (n : ℤ) : ε (n + 1) = - ε n := by
  simp only [ε_add, ε_1, mul_neg, mul_one]

lemma ε_even (n : ℤ) (hn : Even n) : ε n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  simp only [ε, ← Units.ext_iff, zpow_add, ← mul_zpow, mul_neg, mul_one, neg_neg, one_zpow]

lemma ε_odd (n : ℤ) (hn : Odd n) : ε n = -1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [ε_add, ε_even (2 * k) ⟨k, two_mul k⟩, one_mul, ε_1]

lemma ε_eq_one_iff (n : ℤ) : ε n = 1 ↔ Even n := by
  constructor
  . intro h
    rw [Int.even_iff_not_odd]
    intro h'
    rw [ε_odd _ h'] at h
    simp only at h
  . exact ε_even n

lemma ε_eq_neg_one_iff (n : ℤ) : ε n = -1 ↔ Odd n := by
  constructor
  . intro h
    rw [Int.odd_iff_not_even]
    intro h'
    rw [ε_even _ h'] at h
    simp only at h
  . exact ε_odd n

lemma ε_neg (n : ℤ) : ε (-n) = ε n := by
  dsimp [ε]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

lemma ε_sub (n₁ n₂ : ℤ) : ε (n₁ - n₂) = ε n₁ * ε n₂ := by
  simp only [sub_eq_add_neg, ε_add, ε_neg]

lemma ε_eq_iff (n₁ n₂ : ℤ) : ε n₁ = ε n₂ ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  . rw [ε_even _ h₂, Int.even_sub, ε_eq_one_iff]
    tauto
  . rw [← Int.odd_iff_not_even] at h₂
    rw [ε_odd _ h₂, Int.even_sub, ε_eq_neg_one_iff,
      Int.even_iff_not_odd, Int.even_iff_not_odd]
    tauto

@[simp]
lemma mul_ε_self (n : ℤ) : ε n * ε n = 1 := by
  simpa only [← ε_add] using ε_even _ (even_add_self n)

@[simp]
lemma ε_mul_self (n : ℤ) : ε (n * n) = ε n := by
  by_cases hn : Even n
  . rw [ε_even _ hn, ε_even]
    rw [Int.even_mul]
    tauto
  . rw [← Int.odd_iff_not_even] at hn
    rw [ε_odd _ hn, ε_odd]
    rw [Int.odd_mul]
    tauto

end CochainComplex
