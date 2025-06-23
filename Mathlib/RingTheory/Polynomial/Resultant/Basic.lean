/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Resultant of two polynomials

This file contains basic facts about resultant of two polynomials over commutative rings.

## Main definitions

* `Polynomial.resultant`: The resultant of two polynomials `p` and `q` is defined as the determinant
  of the Sylvester matrix of `p` and `q`.

## TODO

* The eventual goal is to prove the following property:
  `resultant (∏ a ∈ s, (X - C a)) f = ∏ a ∈ s, f.eval a`.
  This allows us to write the `resultant f g` as the product of terms of the form `a - b` where `a`
  is a root of `f` and `b` is a root of `g`.
* A smaller intermediate goal is to show that the Sylvester matrix corresponds to the linear map
  that we will call the Sylvester map, which is `R[X]_n × R[X]_m →ₗ[R] R[X]_(n + m)` given by
  `(p, q) ↦ f * p + g * q`, where `R[X]_n` is
  `Polynomial.degreeLT` in `Mathlib.RingTheory.Polynomial.Basic`.

-/


universe u

namespace Polynomial

section sylvester

variable {R : Type u} [Semiring R]

/-- The Sylvester matrix of two polynomials `f` and `g` of degrees `m` and `n` respectively is a
`(n+m) × (n+m)` matrix with the coefficients of `f` and `g` arranged in a specific way. Here, `m`
and `n` are free variables, not necessarily equal to the actual degrees of the polynomials `f` and
`g`. -/
def sylvester (f g : R[X]) (m n : ℕ) : Matrix (Fin (n + m)) (Fin (n + m)) R :=
  fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)

variable (f g : R[X]) (m n : ℕ)

theorem sylvester_C (a : R) : sylvester f (C a) m 0 = Matrix.diagonal (fun _ ↦ a) := by
  ext i j
  refine j.addCases (Fin.elim0 ·) (fun j ↦ ?_)
  rw [sylvester, Fin.addCases_right, Matrix.diagonal_apply]
  split_ifs <;> simp_all [Fin.ext_iff]

end sylvester


section resultant

variable {R : Type u} [CommRing R]

/-- A version of `resultant` where the degrees of the polynomials `f` and `g` are free variables.
This is useful for proving theorems, and comparing `resultant` across rings, where the ring
homomorphism might map the leading coefficients to `0`. -/
def resultantAux (f g : R[X]) (m n : ℕ) : R :=
  (sylvester f g m n).det

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix of `f`
and `g`. -/
def resultant (f g : R[X]) : R :=
  resultantAux f g f.natDegree g.natDegree

variable (f g : R[X]) (m n : ℕ)

lemma resultant_eq_resultantAux : resultant f g = resultantAux f g f.natDegree g.natDegree := rfl

lemma resultant_def : resultant f g = (sylvester f g f.natDegree g.natDegree).det := rfl

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
theorem resultantAux_C (a : R) : resultantAux f (C a) m 0 = a ^ m := by
  rw [resultantAux, sylvester_C, Matrix.det_diagonal, Fin.prod_const, zero_add]

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`, where `m = f.natDegree`. -/
theorem resultant_C (a : R) : resultant f (C a) = a ^ f.natDegree := by
  rw [resultant, natDegree_C, resultantAux_C]

end resultant

end Polynomial
