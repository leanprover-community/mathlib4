/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth, Mitchell Lee, Yuval Filmus
-/
import Mathlib.RingTheory.Polynomial.Chebyshev.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Chebyshev polynomials

## Main statements

* Trigonometric identities satisfied by Chebyshev polynomials:
  `Polynomial.Chebyshev.T_cos`, `Polynomial.Chebyshev.U_cos`
* T is bounded in [-1, 1]: `Polynomial.Chebyshev.T_bounded`

## TODO

* Compute zeroes and extrema of Chebyshev polynomials.
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

-- The converse also holds (for n ≠ 0) but is more difficult to prove
theorem T_bounded (n : ℤ) (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
  (T ℝ n).eval x ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc] at hx
  rw [←cos_arccos hx.1 hx.2, T_cos]
  apply cos_mem_Icc

theorem U_cos (n : ℤ) (θ : ℝ) : (U ℝ n).eval (cos θ) * sin θ = sin ((n+1) * θ) := by
  induction n using Chebyshev.induct with
  | zero => simp
  | one => norm_num; rw [Real.sin_two_mul]; ring
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
    rw [←Real.sin_neg, ←Real.cos_neg, Real.sin_add_sin, mul_assoc, mul_comm (-θ).cos, ←mul_assoc]
    push_cast; congr 3 <;> ring

end Polynomial.Chebyshev
