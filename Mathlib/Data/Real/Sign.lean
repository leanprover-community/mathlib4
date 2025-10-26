/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
import Mathlib.Data.Real.Basic

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

theorem sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 := by rw [sign, if_pos hr]

theorem sign_of_pos {r : ℝ} (hr : 0 < r) : sign r = 1 := by rw [sign, if_pos hr, if_neg hr.not_gt]

@[simp]
theorem sign_zero : sign 0 = 0 := by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

@[simp]
theorem sign_one : sign 1 = 1 :=
  sign_of_pos <| by simp

theorem sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1 := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · exact Or.inl <| sign_of_neg hn
  · exact Or.inr <| Or.inl <| sign_zero
  · exact Or.inr <| Or.inr <| sign_of_pos hp

/-- This lemma is useful for working with `ℝˣ` -/
theorem sign_apply_eq_of_ne_zero (r : ℝ) (h : r ≠ 0) : sign r = -1 ∨ sign r = 1 :=
  h.lt_or_gt.imp sign_of_neg sign_of_pos

@[simp]
theorem sign_eq_zero_iff {r : ℝ} : sign r = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    exact (one_ne_zero h).elim
  · rfl
  · rw [sign_of_pos hp] at h
    exact (one_ne_zero h).elim

theorem sign_intCast (z : ℤ) : sign (z : ℝ) = ↑(Int.sign z) := by
  obtain hn | rfl | hp := lt_trichotomy z (0 : ℤ)
  · rw [sign_of_neg (Int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
  · rw [sign_of_pos (Int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]

theorem sign_neg {r : ℝ} : sign (-r) = -sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
  · rw [sign_zero, neg_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]

theorem sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn]
    exact mul_nonneg_of_nonpos_of_nonpos (by simp) hn.le
  · rw [mul_zero]
  · rw [sign_of_pos hp, one_mul]
    exact hp.le

theorem sign_mul_pos_of_ne_zero (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r := by
  refine lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr ?_
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  exact sign_eq_zero_iff.mp hs0

@[simp]
theorem inv_sign (r : ℝ) : (sign r)⁻¹ = sign r := by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    simp
  · rw [hz]
    exact inv_zero
  · rw [hp]
    exact inv_one

@[simp]
theorem sign_inv (r : ℝ) : sign r⁻¹ = sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
  · rw [sign_zero, inv_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]

end Real
