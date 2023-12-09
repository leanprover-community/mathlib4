/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
import Mathlib.Data.Int.Parity
import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Integer powers of (-1)

This file defines the map `negOnePow : ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.

The definition of `negOnePow` and some lemmas first appeared in contributions by
Johan Commelin to the Liquid Tensor Experiment.

-/

namespace Int

/-- The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`. -/
@[pp_dot]
def negOnePow (n : ℤ) : ℤˣ := (-1 : ℤˣ) ^ n

lemma negOnePow_def (n : ℤ) : n.negOnePow = (-1 : ℤˣ) ^ n := rfl

lemma negOnePow_add (n₁ n₂ : ℤ) :
    (n₁ + n₂).negOnePow =  n₁.negOnePow * n₂.negOnePow :=
  zpow_add _ _ _

@[simp]
lemma negOnePow_zero : negOnePow 0 = 1 := rfl

@[simp]
lemma negOnePow_one : negOnePow 1 = -1 := rfl

lemma negOnePow_succ (n : ℤ) : (n + 1).negOnePow = - n.negOnePow := by
  rw [negOnePow_add, negOnePow_one, mul_neg, mul_one]

lemma negOnePow_even (n : ℤ) (hn : Even n) : n.negOnePow = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [negOnePow_add, units_mul_self]

@[simp]
lemma negOnePow_two_mul (n : ℤ) : (2 * n).negOnePow = 1 :=
  negOnePow_even _ ⟨n, two_mul n⟩

lemma negOnePow_odd (n : ℤ) (hn : Odd n) : n.negOnePow = -1 := by
  obtain ⟨k, rfl⟩ := hn
  simp only [negOnePow_add, negOnePow_two_mul, negOnePow_one, mul_neg, mul_one]

lemma negOnePow_eq_one_iff (n : ℤ) : n.negOnePow = 1 ↔ Even n := by
  constructor
  · intro h
    rw [Int.even_iff_not_odd]
    intro h'
    simp only [negOnePow_odd _ h'] at h
    contradiction
  · exact negOnePow_even n

lemma negOnePow_eq_neg_one_iff (n : ℤ) : n.negOnePow = -1 ↔ Odd n := by
  constructor
  · intro h
    rw [Int.odd_iff_not_even]
    intro h'
    rw [negOnePow_even _ h'] at h
    contradiction
  · exact negOnePow_odd n

@[simp]
lemma negOnePow_neg (n : ℤ) : (-n).negOnePow = n.negOnePow := by
  dsimp [negOnePow]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

lemma negOnePow_sub (n₁ n₂ : ℤ) :
    (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow := by
  simp only [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

lemma negOnePow_eq_iff (n₁ n₂ : ℤ) :
    n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  · rw [negOnePow_even _ h₂, Int.even_sub, negOnePow_eq_one_iff]
    tauto
  · rw [← Int.odd_iff_not_even] at h₂
    rw [negOnePow_odd _ h₂, Int.even_sub, negOnePow_eq_neg_one_iff,
      Int.even_iff_not_odd, Int.even_iff_not_odd]
    tauto

end Int
