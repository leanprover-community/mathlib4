/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.WittVector.IsPoly

#align_import ring_theory.witt_vector.mul_p from "leanprover-community/mathlib"@"7abfbc92eec87190fba3ed3d5ec58e7c167e7144"

/-!
## Multiplication by `n` in the ring of Witt vectors

In this file we show that multiplication by `n` in the ring of Witt vectors
is a polynomial function. We then use this fact to show that the composition of Frobenius
and Verschiebung is equal to multiplication by `p`.

### Main declarations

* `mulN_isPoly`: multiplication by `n` is a polynomial function

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type*} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p -- type as `\bbW`

open MvPolynomial

noncomputable section

variable (p)

/-- `wittMulN p n` is the family of polynomials that computes
the coefficients of `x * n` in terms of the coefficients of the Witt vector `x`. -/
noncomputable def wittMulN : ℕ → ℕ → MvPolynomial ℕ ℤ
  | 0 => 0
  | n + 1 => fun k => bind₁ (Function.uncurry <| ![wittMulN n, X]) (wittAdd p k)
#align witt_vector.witt_mul_n WittVector.wittMulN

variable {p}

theorem mulN_coeff (n : ℕ) (x : 𝕎 R) (k : ℕ) :
    (x * n).coeff k = aeval x.coeff (wittMulN p n k) := by
  induction' n with n ih generalizing k
  -- ⊢ coeff (x * ↑Nat.zero) k = ↑(aeval x.coeff) (wittMulN p Nat.zero k)
  · simp only [Nat.zero_eq, Nat.cast_zero, mul_zero, zero_coeff, wittMulN,
      AlgHom.map_zero, Pi.zero_apply]
  · rw [wittMulN, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_add, mul_one, aeval_bind₁,
      add_coeff]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    -- ⊢ Function.uncurry ![(x * ↑n).coeff, x.coeff] = fun i => ↑(aeval x.coeff) (Fun …
    ext1 ⟨b, i⟩
    -- ⊢ Function.uncurry ![(x * ↑n).coeff, x.coeff] (b, i) = ↑(aeval x.coeff) (Funct …
    fin_cases b
    -- ⊢ Function.uncurry ![(x * ↑n).coeff, x.coeff] ({ val := 0, isLt := (_ : 0 < 2) …
    · simp [Function.uncurry, Matrix.cons_val_zero, ih]
      -- 🎉 no goals
    · simp [Function.uncurry, Matrix.cons_val_one, Matrix.head_cons, aeval_X]
      -- 🎉 no goals
#align witt_vector.mul_n_coeff WittVector.mulN_coeff

variable (p)

/-- Multiplication by `n` is a polynomial function. -/
@[is_poly]
theorem mulN_isPoly (n : ℕ) : IsPoly p fun R _Rcr x => x * n :=
  ⟨⟨wittMulN p n, fun R _Rcr x => by funext k; exact mulN_coeff n x k⟩⟩
                                     -- ⊢ coeff (x * ↑n) k = ↑(aeval x.coeff) (wittMulN p n k)
                                               -- 🎉 no goals
#align witt_vector.mul_n_is_poly WittVector.mulN_isPoly

@[simp]
theorem bind₁_wittMulN_wittPolynomial (n k : ℕ) :
    bind₁ (wittMulN p n) (wittPolynomial p ℤ k) = n * wittPolynomial p ℤ k := by
  induction' n with n ih
  -- ⊢ ↑(bind₁ (wittMulN p Nat.zero)) (wittPolynomial p ℤ k) = ↑Nat.zero * wittPoly …
  · simp [wittMulN, Nat.cast_zero, zero_mul, bind₁_zero_wittPolynomial]
    -- 🎉 no goals
  · rw [wittMulN, ← bind₁_bind₁, wittAdd, wittStructureInt_prop]
    -- ⊢ ↑(bind₁ (Function.uncurry ![wittMulN p n, X])) (↑(bind₁ fun i => ↑(rename (P …
    simp only [AlgHom.map_add, Nat.cast_succ, bind₁_X_right]
    -- ⊢ ↑(bind₁ (Function.uncurry ![wittMulN p n, X])) (↑(rename (Prod.mk 0)) (wittP …
    rw [add_mul, one_mul, bind₁_rename, bind₁_rename]
    -- ⊢ ↑(bind₁ (Function.uncurry ![wittMulN p n, X] ∘ Prod.mk 0)) (wittPolynomial p …
    simp only [ih, Function.uncurry, Function.comp, bind₁_X_left, AlgHom.id_apply,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
#align witt_vector.bind₁_witt_mul_n_witt_polynomial WittVector.bind₁_wittMulN_wittPolynomial

end

end WittVector
