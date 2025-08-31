/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Mitchell Lee, Yuval Filmus
-/
import Mathlib.RingTheory.Polynomial.Chebyshev.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Chebyshev polynomials

## Main statements

* Trigonometric identities satisfied by Chebyshev polynomials:
  `Polynomial.Chebyshev.T_cos`, `Polynomial.Chebyshev.U_cos`
* T is bounded in [-1, 1]: `Polynomial.Chebyshev.T_bounded`

## TODO

* Compute zeroes and extrema of Chebyshev polynomials.
* Prove orthonormality with respect to appropriate inner product.
* Prove minimax properties of Chebyshev polynomials.
-/

namespace Polynomial.Chebyshev

open Polynomial
open Real

theorem T_cos (n : ℤ) (θ : ℝ) : (T ℝ n).eval (cos θ) = cos (n * θ) := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    rw [T_add_two, eval_sub, eval_mul, eval_mul, eval_ofNat, eval_X, ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [Real.cos_add_cos, mul_assoc, mul_comm θ.cos, ←mul_assoc]
    push_cast; congr 3 <;> ring
  | neg n ih => simp [T_neg, ih]

theorem T_cosh (n : ℤ) (θ : ℝ) : (T ℝ n).eval (cosh θ) = cosh (n * θ) := by
  induction n using Chebyshev.induct' with
  | zero => simp
  | one => simp
  | add_two n ih1 ih2 =>
    rw [T_add_two, eval_sub, eval_mul, eval_mul, eval_ofNat, eval_X, ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    trans cosh ((n + 1) * θ + θ) + cosh ((n + 1) * θ - θ)
    · rw [cosh_add, cosh_sub]; push_cast; ring
    · congr <;> (push_cast; ring)
  | neg n ih => simp [T_neg, ih]

theorem T_bounded_of_bounded (n : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
  (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc] at hx
  rw [←cos_arccos hx.1 hx.2, T_cos]
  apply cos_mem_Icc

theorem T_bounded_of_bounded' (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
  |(T ℝ n).eval x| ≤ 1 := by
  apply abs_le.mpr
  rw [←Set.mem_Icc]
  apply T_bounded_of_bounded n
  rw [Set.mem_Icc]
  exact abs_le.mp hx

noncomputable def arccosh (x : ℝ) : ℝ := log (x + sqrt (x^2 - 1))

@[simp]
theorem cosh_arccosh {x : ℝ} (hx : 1 ≤ x) : cosh (arccosh x) = x := by
  unfold arccosh
  have : 0 < x + sqrt (x^2 - 1) := by positivity
  rw [cosh_eq, exp_neg, exp_log this]
  field_simp; ring_nf
  rw [sq_sqrt]
  · ring
  · linarith [show 1 ≤ x^2 from one_le_pow₀ hx]

theorem T_ge_of_ge_one (n : ℤ) {x : ℝ} (hx : x ≥ 1) :
  (T ℝ n).eval x ≥ 1 := by
  rw [←cosh_arccosh hx, T_cosh]
  apply one_le_cosh

theorem T_gt_of_gt_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x > 1) :
  (T ℝ n).eval x > 1 := by
  rw [←cosh_arccosh (le_of_lt hx), T_cosh]
  apply one_lt_cosh.mpr
  apply mul_ne_zero_iff.mpr
  constructor
  · norm_cast
  by_contra! h
  have : x = 1 := by rw [←cosh_arccosh (le_of_lt hx), h, cosh_zero]
  subst this
  exact (lt_self_iff_false 1).mp hx

theorem T_ge_of_le_neg_one (n : ℤ) {x : ℝ} (hx : x ≤ -1) :
  n.negOnePow * (T ℝ n).eval x ≥ 1 := by
  rw [←neg_neg x, T_eval_neg, ←mul_assoc]
  norm_cast
  rw [←Int.negOnePow_add, ←two_mul, Int.negOnePow_two_mul]
  norm_cast; rw [one_mul]
  apply T_ge_of_ge_one n
  linarith

theorem T_gt_of_lt_neg_one {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : x < -1) :
  n.negOnePow * (T ℝ n).eval x > 1 := by
  rw [←neg_neg x, T_eval_neg, ←mul_assoc]
  norm_cast
  rw [←Int.negOnePow_add, ←two_mul, Int.negOnePow_two_mul]
  norm_cast; rw [one_mul]
  apply T_gt_of_gt_one hn
  linarith

theorem T_abs_ge_of_abs_ge (n : ℤ) {x : ℝ} (hx : |x| ≥ 1) :
  |(T ℝ n).eval x| ≥ 1 := by
  apply le_abs.mpr
  cases le_abs.mp hx with
  | inl hx =>
    left
    exact T_ge_of_ge_one n hx
  | inr hx =>
    have : x ≤ -1 := by linarith
    have := T_ge_of_le_neg_one n this
    cases n.even_or_odd with
    | inl hn =>
      left
      rw [Int.negOnePow_even n hn] at this
      push_cast at this
      rw [one_mul] at this
      exact this
    | inr hn =>
      right
      rw [Int.negOnePow_odd n hn] at this
      push_cast at this
      rw [neg_one_mul] at this
      exact this

theorem T_abs_gt_of_abs_gt {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : |x| > 1) :
  |(T ℝ n).eval x| > 1 := by
  apply lt_abs.mpr
  cases lt_abs.mp hx with
  | inl hx =>
    left
    exact T_gt_of_gt_one hn hx
  | inr hx =>
    have : x < -1 := by linarith
    have := T_gt_of_lt_neg_one hn this
    cases n.even_or_odd with
    | inl hn =>
      left
      rw [Int.negOnePow_even n hn] at this
      push_cast at this
      rw [one_mul] at this
      exact this
    | inr hn =>
      right
      rw [Int.negOnePow_odd n hn] at this
      push_cast at this
      rw [neg_one_mul] at this
      exact this

theorem T_bounded_iff_bounded {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  |x| ≤ 1 ↔ |(T ℝ n).eval x| ≤ 1 := by
  constructor
  · intro hx; exact T_bounded_of_bounded' n hx
  · intro hx; contrapose! hx; exact T_abs_gt_of_abs_gt hn hx

theorem U_cos (n : ℤ) (θ : ℝ) : (U ℝ n).eval (cos θ) * sin θ = sin ((n+1) * θ) := by
  induction n using Chebyshev.induct with
  | zero => simp
  | one => norm_num; rw [sin_two_mul]; ring
  | add_two n ih1 ih2 =>
    norm_num
    rw [sub_mul]
    trans 2 * θ.cos * ((U ℝ (n+1)).eval θ.cos * θ.sin) - (U ℝ n).eval θ.cos * θ.sin
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [Real.sin_add_sin, mul_assoc, mul_comm θ.cos, ←mul_assoc]
    push_cast; congr 3 <;> ring
  | neg_add_one n ih1 ih2 =>
    rw [U_sub_one]
    norm_num
    rw [sub_mul]
    trans 2 * θ.cos * ((U ℝ (-n)).eval θ.cos * θ.sin) - (U ℝ (-n+1)).eval θ.cos * θ.sin
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [←sin_neg, ←cos_neg, sin_add_sin, mul_assoc, mul_comm (-θ).cos, ←mul_assoc]
    push_cast; congr 3 <;> ring

theorem U_cosh (n : ℤ) (θ : ℝ) : (U ℝ n).eval (cosh θ) * sinh θ = sinh ((n+1) * θ) := by
  induction n using Chebyshev.induct with
  | zero => simp
  | one => norm_num; rw [sinh_two_mul]; ring
  | add_two n ih1 ih2 =>
    norm_num
    rw [sub_mul]
    trans 2 * θ.cosh * ((U ℝ (n+1)).eval θ.cosh * θ.sinh) - (U ℝ n).eval θ.cosh * θ.sinh
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    trans sinh ((n + 2) * θ + θ) + sinh ((n + 2) * θ - θ)
    · rw [sinh_add, sinh_sub]; push_cast; ring_nf
    · congr <;> (push_cast; ring)
  | neg_add_one n ih1 ih2 =>
    rw [U_sub_one]
    norm_num
    rw [sub_mul]
    trans 2 * θ.cosh * ((U ℝ (-n)).eval θ.cosh * θ.sinh) - (U ℝ (-n+1)).eval θ.cosh * θ.sinh
    · ring
    rw [ih1, ih2]
    apply sub_eq_iff_eq_add.mpr
    rw [←sinh_neg]
    trans sinh ((-n + 1) * θ - θ) + sinh ((-n + 1) * θ + θ)
    · rw [sinh_add, sinh_sub]; push_cast; ring
    · congr <;> (push_cast; ring)

end Polynomial.Chebyshev
