/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Module
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.RingTheory.Polynomial.Chebyshev

#align_import analysis.special_functions.trigonometric.chebyshev from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

/-!
# Multiple angle formulas in terms of Chebyshev polynomials

This file gives the trigonometric characterizations of Chebyshev polynomials, for both the real
(`Real.cos`) and complex (`Complex.cos`) cosine.
-/

set_option linter.uppercaseLean3 false

namespace Polynomial.Chebyshev

open Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

@[simp]
theorem aeval_T (x : A) (n : ℕ) : aeval x (T R n) = (T A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_T]
  -- 🎉 no goals
#align polynomial.chebyshev.aeval_T Polynomial.Chebyshev.aeval_T

@[simp]
theorem aeval_U (x : A) (n : ℕ) : aeval x (U R n) = (U A n).eval x := by
  rw [aeval_def, eval₂_eq_eval_map, map_U]
  -- 🎉 no goals
#align polynomial.chebyshev.aeval_U Polynomial.Chebyshev.aeval_U

@[simp]
theorem algebraMap_eval_T (x : R) (n : ℕ) :
    algebraMap R A ((T R n).eval x) = (T A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_T]
  -- 🎉 no goals
#align polynomial.chebyshev.algebra_map_eval_T Polynomial.Chebyshev.algebraMap_eval_T

@[simp]
theorem algebraMap_eval_U (x : R) (n : ℕ) :
    algebraMap R A ((U R n).eval x) = (U A n).eval (algebraMap R A x) := by
  rw [← aeval_algebraMap_apply_eq_algebraMap_eval, aeval_U]
  -- 🎉 no goals
#align polynomial.chebyshev.algebra_map_eval_U Polynomial.Chebyshev.algebraMap_eval_U

-- Porting note: added type ascriptions to the statement
@[simp, norm_cast]
theorem complex_ofReal_eval_T : ∀ (x : ℝ) n, (((T ℝ n).eval x : ℝ) : ℂ) = (T ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_T ℝ ℂ _ _ _
#align polynomial.chebyshev.complex_of_real_eval_T Polynomial.Chebyshev.complex_ofReal_eval_T

-- Porting note: added type ascriptions to the statement
@[simp, norm_cast]
theorem complex_ofReal_eval_U : ∀ (x : ℝ) n, (((U ℝ n).eval x : ℝ) : ℂ) = (U ℂ n).eval (x : ℂ) :=
  @algebraMap_eval_U ℝ ℂ _ _ _
#align polynomial.chebyshev.complex_of_real_eval_U Polynomial.Chebyshev.complex_ofReal_eval_U

/-! ### Complex versions -/


section Complex

open Complex

variable (θ : ℂ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_complex_cos : ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
  | 0 => by simp only [T_zero, eval_one, Nat.cast_zero, zero_mul, cos_zero]
            -- 🎉 no goals
  | 1 => by simp only [eval_X, one_mul, T_one, Nat.cast_one]
            -- 🎉 no goals
  | n + 2 => by
    -- Porting note: partially rewrote proof for lean4 numerals.
    have : (2 : ℂ[X]) = (2 : ℕ) := by norm_num
    -- ⊢ eval (cos θ) (T ℂ (n + 2)) = cos (↑(n + 2) * θ)
    simp only [this, eval_X, eval_one, T_add_two, eval_sub, eval_mul, eval_nat_cast]
    -- ⊢ ↑2 * cos θ * eval (cos θ) (T ℂ (n + 1)) - eval (cos θ) (T ℂ n) = cos (↑(n +  …
    simp only [Nat.cast_ofNat, Nat.cast_add]
    -- ⊢ 2 * cos θ * eval (cos θ) (T ℂ (n + 1)) - eval (cos θ) (T ℂ n) = cos ((↑n + 2 …
    rw [T_complex_cos (n + 1), T_complex_cos n]
    -- ⊢ 2 * cos θ * cos (↑(n + 1) * θ) - cos (↑n * θ) = cos ((↑n + 2) * θ)
    simp only [Nat.cast_add, Nat.cast_one, add_mul, cos_add, one_mul, mul_assoc, sin_two_mul,
      cos_two_mul]
    ring
    -- 🎉 no goals
#align polynomial.chebyshev.T_complex_cos Polynomial.Chebyshev.T_complex_cos

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_complex_cos (n : ℕ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  induction' n with d hd
  -- ⊢ eval (cos θ) (U ℂ Nat.zero) * sin θ = sin ((↑Nat.zero + 1) * θ)
  · simp [U_zero, eval_one, zero_add, one_mul, Nat.zero_eq, CharP.cast_eq_zero]
    -- 🎉 no goals
  · rw [U_eq_X_mul_U_add_T]
    -- ⊢ eval (cos θ) (X * U ℂ d + T ℂ (d + 1)) * sin θ = sin ((↑(Nat.succ d) + 1) * θ)
    simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mul, mul_assoc, hd, one_mul]
    -- ⊢ cos θ * sin (↑d * θ + θ) + cos (↑(d + 1) * θ) * sin θ = sin (↑(Nat.succ d) * …
    -- Porting note: added `trans` to prevent `rw` from going on a wild goose chase applying `rfl`
    trans cos θ * sin (↑(d.succ) * θ) + cos (↑(d.succ) * θ) * sin θ
    -- ⊢ cos θ * sin (↑d * θ + θ) + cos (↑(d + 1) * θ) * sin θ = cos θ * sin (↑(Nat.s …
    swap
    -- ⊢ cos θ * sin (↑(Nat.succ d) * θ) + cos (↑(Nat.succ d) * θ) * sin θ = sin (↑(N …
    · conv_rhs => rw [sin_add, mul_comm]
      -- 🎉 no goals
    push_cast
    -- ⊢ cos θ * sin (↑d * θ + θ) + cos ((↑d + 1) * θ) * sin θ = cos θ * sin ((↑d + 1 …
    simp only [add_mul, one_mul]
    -- 🎉 no goals
#align polynomial.chebyshev.U_complex_cos Polynomial.Chebyshev.U_complex_cos

end Complex

-- ### Real versions
section Real

open Real

variable (θ : ℝ) (n : ℕ)

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
@[simp]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ) := by exact_mod_cast T_complex_cos θ n
                                                              -- 🎉 no goals
#align polynomial.chebyshev.T_real_cos Polynomial.Chebyshev.T_real_cos

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n + 1) * θ) / sin θ`. -/
@[simp]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  exact_mod_cast U_complex_cos θ n
  -- 🎉 no goals
#align polynomial.chebyshev.U_real_cos Polynomial.Chebyshev.U_real_cos

end Real

end Polynomial.Chebyshev
