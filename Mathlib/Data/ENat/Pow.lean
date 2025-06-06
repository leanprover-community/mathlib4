/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Data.ENat.Basic

/-!
# Powers of extended natural numbers

We define the power of an extended natural `x : ℕ∞` by another extended natural `y : ℕ∞`.
When `y` is finite, it extends the exponentiation by natural numbers. When `y = ⊤`, this definition
is compatible with cardinality `ENat.card`.

## TODO

`ℝ≥0∞` powers of `ℝ≥0∞` numbers and coercion from `ℕ∞`.
-/

namespace ENat

variable {x y z : ℕ∞}

instance : Subsingleton ℕ∞ˣ := by
  refine subsingleton_of_forall_eq 1 fun x ↦ ?_
  have := x.val_inv
  have x_top : x.val ≠ ⊤ := by
    intro h
    simp only [h, x.inv_eq_val_inv, ne_eq, (x⁻¹).ne_zero, not_false_eq_true, top_mul, top_ne_one]
      at this
  have x_inv_top : x.inv ≠ ⊤ := by
    intro h
    simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
  obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
  obtain ⟨z, x_z⟩ := ne_top_iff_exists.1 x_inv_top
  replace x_y := x_y.symm
  rw [x_y, ← x_z, ← coe_mul, ← coe_one, coe_inj, _root_.mul_eq_one] at this
  rwa [this.1, Nat.cast_one, Units.val_eq_one] at x_y

instance : Pow ℕ∞ ℕ∞ where
  pow
    | x, some y => x ^ y
    | x, ⊤ => if x = 0 then 0 else if x = 1 then 1 else ⊤

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
  rw [← coe_zero, epow_natCast, _root_.pow_zero]

@[simp]
lemma epow_one : x ^ (1 : ℕ∞) = x := by
  rw [← coe_one, epow_natCast, _root_.pow_one]

lemma epow_top (h : 1 < x) : x ^ (⊤ : ℕ∞) = ⊤ := by
  simp only [instHPow, instPow, (zero_le_one.trans_lt h).ne.symm, ↓reduceIte, h.ne.symm]

lemma epow_eq_zero_iff : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.1.symm ▸ zero_epow h.2⟩
  induction y with
  | top =>
    simp only [ne_eq, top_ne_zero, not_false_eq_true, and_true]
    rcases lt_trichotomy x 1 with x_0 | rfl | x_2
    · exact lt_one_iff_eq_zero.1 x_0
    · rw [one_epow] at h; contradiction
    · rw [epow_top x_2] at h; contradiction
  | coe y =>
    rw [epow_natCast, pow_eq_zero_iff'] at h
    exact ⟨h.1, y.cast_ne_zero.2 h.2⟩

lemma epow_add : x ^ (y + z) = (x ^ y) * x ^ z := by
  rcases lt_trichotomy x 1 with x_0 | rfl | x_2
  · rw [lt_one_iff_eq_zero] at x_0
    rw [x_0]
    rcases eq_zero_or_pos (y + z) with yz_0 | yz_1
    · rw [add_eq_zero] at yz_0
      simp only [yz_0, add_zero, epow_zero, mul_one]
    · rw [zero_epow yz_1.ne.symm]
      simp only [add_pos_iff, zero_eq_mul] at yz_1 ⊢
      exact Or.imp (fun h ↦ zero_epow h.ne.symm) (fun h ↦ zero_epow h.ne.symm) yz_1
  · simp only [one_epow, mul_one]
  · induction y
    · rw [top_add, epow_top x_2]
      refine (WithTop.top_mul ?_).symm
      rw [ne_eq, epow_eq_zero_iff, not_and]
      intro h; rw [h] at x_2; contradiction
    · induction z
      · rw [add_top, epow_top x_2]
        refine (WithTop.mul_top ?_).symm
        rw [ne_eq, epow_eq_zero_iff, not_and]
        intro h; rw [h] at x_2; contradiction
      · exact pow_add x _ _

lemma mul_epow : (x * y) ^ z = (x ^ z) * y ^ z := by
  induction z
  · rcases lt_trichotomy (x * y) 1 with xy_0 | xy_1 | xy_2
    · rw [lt_one_iff_eq_zero] at xy_0
      rw [xy_0, zero_epow_top]
      simp only [mul_eq_zero, zero_eq_mul] at *
      apply Or.imp _ _ xy_0 <;> exact fun h ↦ h ▸ zero_epow_top
    · rw [xy_1, (mul_eq_one.1 xy_1).1, (mul_eq_one.1 xy_1).2, one_epow, one_mul]
    · rw [epow_top xy_2]
      rcases eq_or_ne x 0 with rfl | x_0
      · simp only [zero_mul, not_lt_zero] at xy_2
      rcases eq_or_ne x 1 with rfl | x_1
      · rw [one_mul] at xy_2; simp only [one_epow, epow_top xy_2, one_mul]
      rw [epow_top (x_1.lt_of_le' (one_le_iff_ne_zero.2 x_0))]
      refine (WithTop.top_mul ?_).symm
      rw [ne_eq, epow_eq_zero_iff, not_and]
      intro h
      simp only [h, mul_zero, not_lt_zero] at xy_2
  · simp only [epow_natCast]
    exact _root_.mul_pow x y _

end ENat
