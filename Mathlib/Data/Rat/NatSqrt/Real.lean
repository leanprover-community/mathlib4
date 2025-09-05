/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Rat.NatSqrt.Defs
import Mathlib.Data.Real.Sqrt

/-!
Comparisons between rational approximations to the square root of a natural number
and the real square root.
-/

namespace Nat

theorem ratSqrt_le_realSqrt (x : ℕ) {prec : ℕ} (h : 0 < prec) : ratSqrt x prec ≤ √x := by
  have := ratSqrt_sq_le (x := x) h
  have : (x.ratSqrt prec ^ 2 : ℝ) ≤ ↑x := by norm_cast
  have := Real.sqrt_monotone this
  rwa [Real.sqrt_sq] at this
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg _ _

theorem realSqrt_lt_ratSqrt_add_inv_prec (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x < ratSqrt x prec + 1 / prec := by
  have := lt_ratSqrt_add_inv_prec_sq (x := x) h
  have : (x : ℝ) < ↑((x.ratSqrt prec + 1 / prec) ^ 2 : ℚ) := by norm_cast
  have := Real.sqrt_lt_sqrt (by simp) this
  rw [Rat.cast_pow, Real.sqrt_sq] at this
  · push_cast at this
    exact this
  · push_cast
    exact add_nonneg (by simpa using ratSqrt_nonneg _ _) (by simp)

theorem realSqrt_mem_Ico (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    √x ∈ Set.Ico (ratSqrt x prec : ℝ) (ratSqrt x prec + 1 / prec : ℝ) := by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

theorem ratSqrt_mem_Ioc (x : ℕ) {prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec : ℝ) ∈ Set.Ioc (√x - 1 / prec) √x := by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

end Nat
