/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.mul_p
! leanprover-community/mathlib commit 7abfbc92eec87190fba3ed3d5ec58e7c167e7144
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.IsPoly

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mul_n_is_poly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type _} [hp : Fact p.Prime] [CommRing R]

-- mathport name: expr𝕎
local notation "𝕎" => WittVector p

-- type as `\bbW`
open MvPolynomial

noncomputable section

include hp

variable (p)

/-- `witt_mul_n p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
noncomputable def wittMulN : ℕ → ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![witt_mul_n n, X]) (wittAdd p k)
#align witt_vector.witt_mul_n WittVector.wittMulN

variable {p}

theorem mul_n_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) : (x * n).coeff k = aeval x.coeff (wittMulN p n k) :=
  by
  induction' n with n ih generalizing k
  ·
    simp only [Nat.zero_eq, Nat.cast_zero, MulZeroClass.mul_zero, zero_coeff, witt_mul_n,
      AlgHom.map_zero, Pi.zero_apply]
  · rw [witt_mul_n, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_add, mul_one, aeval_bind₁,
      add_coeff]
    apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl
    ext1 ⟨b, i⟩
    fin_cases b
    · simp only [Function.uncurry, Matrix.cons_val_zero, ih]
    · simp only [Function.uncurry, Matrix.cons_val_one, Matrix.head_cons, aeval_X]
#align witt_vector.mul_n_coeff WittVector.mul_n_coeff

variable (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly]
theorem mulNIsPoly (n : ℕ) : IsPoly p fun R _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mul_n_coeff n x k⟩⟩
#align witt_vector.mul_n_is_poly WittVector.mulNIsPoly

@[simp]
theorem bind₁_wittMulN_wittPolynomial (n k : ℕ) :
    bind₁ (wittMulN p n) (wittPolynomial p ℤ k) = n * wittPolynomial p ℤ k :=
  by
  induction' n with n ih
  · simp only [witt_mul_n, Nat.cast_zero, MulZeroClass.zero_mul, bind₁_zero_witt_polynomial]
  · rw [witt_mul_n, ← bind₁_bind₁, witt_add, wittStructureInt_prop]
    simp only [AlgHom.map_add, Nat.cast_succ, bind₁_X_right]
    rw [add_mul, one_mul, bind₁_rename, bind₁_rename]
    simp only [ih, Function.uncurry, Function.comp, bind₁_X_left, AlgHom.id_apply,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
#align witt_vector.bind₁_witt_mul_n_witt_polynomial WittVector.bind₁_wittMulN_wittPolynomial

end WittVector

