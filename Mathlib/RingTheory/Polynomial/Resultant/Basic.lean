/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Resultant of polynomials

This file contains basic facts about resultant of polynomials over commutative rings.

## Main definitions

* `Polynomial.resultant`: The resultant of two polynomials `p` and `q` is defined as the determinant
  of the Sylvester matrix of `p` and `q`.

-/


universe u

namespace Polynomial

section sylvester

variable {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively is a
`(n+m) × (n+m)` matrix with the coefficients of `f` and `g` arranged in a specific way. Here, `m`
and `n` are free variables, not fixed to the actual degrees of the polynomials `f` and `g`. -/
def sylvester : Matrix (Fin (n+m)) (Fin (n+m)) R :=
  fun i j ↦ j.addCases
    (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+m) then f.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i:ℕ) ∈ Set.Icc (j₁:ℕ) (j₁+n) then g.coeff (i - j₁) else 0)

theorem sylvester_C (a : R) :
    sylvester f (C a) m 0 = Matrix.diagonal (fun _ ↦ a) := by
  ext i j
  cases j using Fin.addCases with
  | left j => fin_cases j
  | right j =>
    rw [sylvester, Fin.addCases_right, Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff]

end sylvester


section resultant

variable {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)

/-- A version of `resultant` where the degrees of the polynomials `f` and `g` are free variables.
This is useful for proving theorems, and comparing `resultant` across rings, where the ring
homomorphism might map some coefficient to `0`. -/
def resultantAux : R :=
(sylvester f g m n : Matrix _ _ R).det

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix of `f`
and `g`. -/
def resultant : R :=
resultantAux f g f.natDegree g.natDegree

lemma resultant_eq_resultantAux : resultant f g = resultantAux f g f.natDegree g.natDegree := rfl

lemma resultant_def : resultant f g = (sylvester f g f.natDegree g.natDegree).det := rfl

/-- For polynomial `f` and constant `a`, `Res(f,a) = a ^ m`. -/
theorem resultantAux_C (a : R) : resultantAux f (C a) m 0 = a ^ m := by
  rw [resultantAux, sylvester_C, Matrix.det_diagonal, Fin.prod_const, zero_add]

/-- For polynomial `f` and constant `a`, `Res(f,a) = a ^ n`, where `n = f.natDegree`. -/
theorem resultant_C (a : R) : resultant f (C a) = a ^ f.natDegree := by
  rw [resultant, natDegree_C, resultantAux_C]

end resultant

end Polynomial
