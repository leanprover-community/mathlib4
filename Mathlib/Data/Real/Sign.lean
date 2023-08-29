/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
import Mathlib.Data.Real.Basic

#align_import data.real.sign from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Real sign function

This file introduces and contains some results about `Real.sign` which maps negative
real numbers to -1, positive real numbers to 1, and 0 to 0.

## Main definitions

 * `Real.sign r` is $\begin{cases} -1 & \text{if } r < 0, \\
                               ~~\, 0 & \text{if } r = 0, \\
                               ~~\, 1 & \text{if } r > 0. \end{cases}$

## Tags

sign function
-/


namespace Real

/-- The sign function that maps negative real numbers to -1, positive numbers to 1, and 0
otherwise. -/
noncomputable def sign (r : ℝ) : ℝ :=
  if r < 0 then -1 else if 0 < r then 1 else 0
#align real.sign Real.sign

theorem sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 := by rw [sign, if_pos hr]
                                                             -- 🎉 no goals
#align real.sign_of_neg Real.sign_of_neg

theorem sign_of_pos {r : ℝ} (hr : 0 < r) : sign r = 1 := by rw [sign, if_pos hr, if_neg hr.not_lt]
                                                            -- 🎉 no goals
#align real.sign_of_pos Real.sign_of_pos

@[simp]
theorem sign_zero : sign 0 = 0 := by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
                                     -- 🎉 no goals
#align real.sign_zero Real.sign_zero

@[simp]
theorem sign_one : sign 1 = 1 :=
  sign_of_pos <| by norm_num
                    -- 🎉 no goals
#align real.sign_one Real.sign_one

theorem sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1 := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · exact Or.inl <| sign_of_neg hn
    -- 🎉 no goals
  · exact Or.inr <| Or.inl <| sign_zero
    -- 🎉 no goals
  · exact Or.inr <| Or.inr <| sign_of_pos hp
    -- 🎉 no goals
#align real.sign_apply_eq Real.sign_apply_eq

/-- This lemma is useful for working with `ℝˣ` -/
theorem sign_apply_eq_of_ne_zero (r : ℝ) (h : r ≠ 0) : sign r = -1 ∨ sign r = 1 :=
  h.lt_or_lt.imp sign_of_neg sign_of_pos
#align real.sign_apply_eq_of_ne_zero Real.sign_apply_eq_of_ne_zero

@[simp]
theorem sign_eq_zero_iff {r : ℝ} : sign r = 0 ↔ r = 0 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ sign_zero⟩
  -- ⊢ r = 0
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    -- ⊢ r = 0
    exact (one_ne_zero h).elim
    -- 🎉 no goals
  · rfl
    -- 🎉 no goals
  · rw [sign_of_pos hp] at h
    -- ⊢ r = 0
    exact (one_ne_zero h).elim
    -- 🎉 no goals
#align real.sign_eq_zero_iff Real.sign_eq_zero_iff

theorem sign_int_cast (z : ℤ) : sign (z : ℝ) = ↑(Int.sign z) := by
  obtain hn | rfl | hp := lt_trichotomy z (0 : ℤ)
  · rw [sign_of_neg (Int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
    -- 🎉 no goals
  · rw [sign_of_pos (Int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]
    -- 🎉 no goals
#align real.sign_int_cast Real.sign_int_cast

theorem sign_neg {r : ℝ} : sign (-r) = -sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
    -- 🎉 no goals
  · rw [sign_zero, neg_zero, sign_zero]
    -- 🎉 no goals
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]
    -- 🎉 no goals
#align real.sign_neg Real.sign_neg

theorem sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn]
    -- ⊢ 0 ≤ -1 * r
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) hn.le
    -- 🎉 no goals
  · rw [mul_zero]
    -- 🎉 no goals
  · rw [sign_of_pos hp, one_mul]
    -- ⊢ 0 ≤ r
    exact hp.le
    -- 🎉 no goals
#align real.sign_mul_nonneg Real.sign_mul_nonneg

theorem sign_mul_pos_of_ne_zero (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r := by
  refine' lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr _
  -- ⊢ r = 0
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  -- ⊢ r = 0
  exact sign_eq_zero_iff.mp hs0
  -- 🎉 no goals
#align real.sign_mul_pos_of_ne_zero Real.sign_mul_pos_of_ne_zero

@[simp]
theorem inv_sign (r : ℝ) : (sign r)⁻¹ = sign r := by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    -- ⊢ (-1)⁻¹ = -1
    norm_num
    -- 🎉 no goals
  · rw [hz]
    -- ⊢ 0⁻¹ = 0
    exact inv_zero
    -- 🎉 no goals
  · rw [hp]
    -- ⊢ 1⁻¹ = 1
    exact inv_one
    -- 🎉 no goals
#align real.inv_sign Real.inv_sign

@[simp]
theorem sign_inv (r : ℝ) : sign r⁻¹ = sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
    -- 🎉 no goals
  · rw [sign_zero, inv_zero, sign_zero]
    -- 🎉 no goals
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]
    -- 🎉 no goals
#align real.sign_inv Real.sign_inv

end Real
