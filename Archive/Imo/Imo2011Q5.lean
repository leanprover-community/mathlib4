/-
Copyright (c) 2021 Alain Verberkmoes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Verberkmoes
-/
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Int.Defs

/-!
# IMO 2011 Q5

Let `f` be a function from the set of integers to the set
of positive integers.  Suppose that, for any two integers
`m` and `n`, the difference `f m - f n` is divisible by
`f (m - n)`.  Prove that, for all integers `m` and `n` with
`f m ≤ f n`, the number `f n` is divisible by `f m`.
-/


open Int

theorem imo2011_q5 (f : ℤ → ℤ) (hpos : ∀ n : ℤ, 0 < f n) (hdvd : ∀ m n : ℤ, f (m - n) ∣ f m - f n) :
    ∀ m n : ℤ, f m ≤ f n → f m ∣ f n := by
  intro m n h_fm_le_fn
  rcases lt_or_eq_of_le h_fm_le_fn with h_fm_lt_fn | h_fm_eq_fn
  · -- m < n
    let d := f m - f (m - n)
    have h_fn_dvd_d : f n ∣ d := by
      rw [← sub_sub_self m n]
      exact hdvd m (m - n)
    have h_d_lt_fn : d < f n := calc
      d < f m := sub_lt_self _ (hpos (m - n))
      _ < f n := h_fm_lt_fn
    have h_neg_d_lt_fn : -d < f n := by
      calc
        -d = f (m - n) - f m := neg_sub _ _
        _ < f (m - n) := sub_lt_self _ (hpos m)
        _ ≤ f n - f m := le_of_dvd (sub_pos.mpr h_fm_lt_fn) ?_
        _ < f n := sub_lt_self _ (hpos m)
      -- ⊢ f (m - n) ∣ f n - f m
      rw [← Int.dvd_neg, neg_sub]
      exact hdvd m n
    have h_d_eq_zero : d = 0 := by
      obtain hd | hd | hd : d > 0 ∨ d = 0 ∨ d < 0 := trichotomous d 0
      · -- d > 0
        have h₁ : f n ≤ d := le_of_dvd hd h_fn_dvd_d
        have h₂ : ¬f n ≤ d := not_le.mpr h_d_lt_fn
        contradiction
      · -- d = 0
        exact hd
      · -- d < 0
        have h₁ : f n ≤ -d := le_of_dvd (neg_pos.mpr hd) h_fn_dvd_d.neg_right
        have h₂ : ¬f n ≤ -d := not_le.mpr h_neg_d_lt_fn
        contradiction
    have h₁ : f m = f (m - n) := sub_eq_zero.mp h_d_eq_zero
    have h₂ : f (m - n) ∣ f m - f n := hdvd m n
    rw [← h₁] at h₂
    exact (dvd_iff_dvd_of_dvd_sub h₂).mp dvd_rfl
  · -- m = n
    rw [h_fm_eq_fn]
