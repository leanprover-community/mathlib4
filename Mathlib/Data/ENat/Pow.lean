/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Data.ENat.Basic

/-!
# Powers of extended natural numbers

We define the power of an extended natural `x : ℕ∞` by another extended natural `y : ℕ∞`. The
definition is chosen such that `x ^ y` is the cardinality of `α → β`, when `β` has cardinality `x`
and `α` has cardinality `y`:

* When `y` is finite, it coincides with the exponentiation by natural numbers (e.g. `⊤ ^ 0 = 1`).
* We set `0 ^ ⊤ = 0`, `1 ^ ⊤ = 1` and `x ^ ⊤ = ⊤` for `x > 1`.

## Naming convention

The quantity `x ^ y` for `x`, `y : ℕ∞` is defined as a `Pow` instance. It is called `epow` in
lemmas' names.
-/

@[expose] public section

namespace ENat

variable {x y z : ℕ∞}

instance : Pow ℕ∞ ℕ∞ where
  pow
    | x, some y => x ^ y
    | x, ⊤ => if x = 0 then 0 else if x = 1 then 1 else ⊤

lemma epow_def {x y : ℕ∞} :
    x ^ y = if y < ⊤ then x ^ y.toNat else if x = 0 then 0 else if x = 1 then 1 else ⊤ := by
  cases y with
  | top => simp only [lt_self_iff_false, ↓reduceIte]; rfl
  | coe n => simp only [natCast_lt_top, ↓reduceIte, toNat_natCast]; rfl

@[simp, norm_cast]
lemma epow_natCast {y : ℕ} : x ^ (y : ℕ∞) = x ^ y := rfl

@[simp]
lemma zero_epow_top : (0 : ℕ∞) ^ (⊤ : ℕ∞) = 0 := rfl

lemma zero_epow (h : y ≠ 0) : (0 : ℕ∞) ^ y = 0 := by
  induction y with
  | top => exact zero_epow_top
  | coe y => rwa [epow_natCast, pow_eq_zero_iff', eq_self 0, true_and, ← y.cast_ne_zero (R := ℕ∞)]

@[simp]
lemma one_epow : (1 : ℕ∞) ^ y = 1 := by
  induction y with
  | top => rfl
  | coe y => rw [epow_natCast, one_pow]

@[simp]
lemma top_epow_top : (⊤ : ℕ∞) ^ (⊤ : ℕ∞) = ⊤ := rfl

lemma top_epow (h : y ≠ 0) : (⊤ : ℕ∞) ^ y = ⊤ := by
  induction y with
  | top => exact top_epow_top
  | coe y => rwa [epow_natCast, pow_eq_top_iff, eq_self ⊤, true_and, ← y.cast_ne_zero (R := ℕ∞)]

@[simp]
lemma epow_zero : x ^ (0 : ℕ∞) = 1 := by
  rw [← natCast_zero, epow_natCast, pow_zero]

@[simp]
lemma epow_one : x ^ (1 : ℕ∞) = x := by
  rw [← natCast_one, epow_natCast, pow_one]

lemma epow_top (h : 1 < x) : x ^ (⊤ : ℕ∞) = ⊤ := by
  have : (0 : ℕ∞) ≤ 1 := zero_le_one
  rw [epow_def, if_neg, if_neg, if_neg] <;> grind

lemma epow_right_mono (h : x ≠ 0) : Monotone (fun y : ℕ∞ ↦ x ^ y) := by
  intro y z y_z
  induction y
  · rw [top_le_iff.1 y_z]
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · exact (h (Order.lt_one_iff.1 x_0)).rec
    · simp only [one_epow, le_refl]
    · simp only [epow_top x_2, le_top]
  · exact pow_right_mono₀ (Order.one_le_iff_ne_zero.2 h) (Nat.cast_le.1 y_z)

lemma one_le_epow (h : x ≠ 0) : 1 ≤ x ^ y := by
  simpa using epow_right_mono h zero_le

lemma epow_pos (h : x ≠ 0) : 0 < x ^ y := by
  rw [← Order.one_le_iff_pos]; exact one_le_epow h

lemma epow_left_mono : Monotone (fun x : ℕ∞ ↦ x ^ y) := by
  intro x z x_z
  simp only
  induction y
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · rw [Order.lt_one_iff.1 x_0, zero_epow_top]; exact bot_le
    · rw [one_epow]; exact one_le_epow (Order.one_le_iff_ne_zero.1 x_z)
    · rw [epow_top (x_2.trans_le x_z)]; exact le_top
  · simp only [epow_natCast, (pow_left_mono _) x_z]

lemma epow_eq_zero_iff : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  refine ⟨fun h ↦ ⟨?_, fun y_0 ↦ ?_⟩, fun h ↦ h.1.symm ▸ zero_epow h.2⟩
  · contrapose! h
    exact (epow_pos h).ne'
  · rw [y_0, epow_zero] at h; contradiction

lemma epow_eq_one_iff : x ^ y = 1 ↔ x = 1 ∨ y = 0 := by
  refine ⟨fun h ↦ or_iff_not_imp_right.2 fun y_0 ↦ ?_, fun h ↦ by rcases h with h | h <;> simp [h]⟩
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0] at h; contradiction
  · rfl
  · have := epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0)
    simp only [epow_one, h] at this
    exact (not_lt_of_ge this x_2).rec

lemma epow_add : x ^ (y + z) = x ^ y * x ^ z := by
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0]
    rcases eq_zero_or_pos y with rfl | y_0
    · simp only [zero_add, epow_zero, one_mul]
    · rw [zero_epow y_0.ne.symm, zero_mul]
      exact zero_epow (add_pos_of_pos_of_nonneg y_0 bot_le).ne.symm
  · simp only [one_epow, mul_one]
  · induction y
    · rw [top_add, epow_top x_2, top_mul]
      exact (epow_pos x_2.ne_zero).ne'
    induction z
    · rw [add_top, epow_top x_2, mul_top]
      exact (epow_pos x_2.ne_zero).ne'
    simp only [← Nat.cast_add, epow_natCast, pow_add x]

lemma mul_epow : (x * y) ^ z = x ^ z * y ^ z := by
  induction z
  · rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · simp only [Order.lt_one_iff.1 x_0, zero_mul, zero_epow_top]
    · simp only [one_mul, one_epow]
    · rcases lt_trichotomy y 1 with y_0 | rfl | y_2
      · simp only [Order.lt_one_iff.1 y_0, mul_zero, zero_epow_top]
      · simp
      · rw [epow_top x_2, epow_top y_2, mul_top top_ne_zero]
        exact epow_top (one_lt_mul x_2.le y_2)
  · simp only [epow_natCast, mul_pow x y]

lemma epow_mul : x ^ (y * z) = (x ^ y) ^ z := by
  rcases eq_or_ne y 0 with y_0 | y_0
  · simp [y_0]
  rcases eq_or_ne z 0 with z_0 | z_0
  · simp [z_0]
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [Order.lt_one_iff.1 x_0, zero_epow y_0, zero_epow z_0, zero_epow (mul_ne_zero y_0 z_0)]
  · simp only [one_epow]
  · induction y
    · rw [top_mul z_0, epow_top x_2, top_epow z_0]
    induction z
    · rw [mul_top y_0, epow_top x_2, epow_top]
      apply (epow_right_mono x_2.ne_zero (Order.one_le_iff_ne_zero.2 y_0)).trans_lt'
      simp [x_2]
    · simp only [← Nat.cast_mul, epow_natCast, pow_mul x]

end ENat
