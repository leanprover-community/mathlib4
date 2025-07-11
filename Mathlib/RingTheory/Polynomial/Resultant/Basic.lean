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
* Resultant of two binary forms (i.e. homogeneous polynomials in two variables), after binary forms
  are implemented.

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
  .of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + m) then f.coeff (i - j₁) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + n) then g.coeff (i - j₁) else 0)

variable (f g : R[X]) (m n : ℕ)

@[simp] theorem sylvester_C_right (a : R) :
    sylvester f (C a) m 0 = Matrix.diagonal (fun _ ↦ a) :=
  Matrix.ext fun i j ↦ j.addCases nofun fun j ↦ by
    rw [sylvester, Matrix.of_apply, Fin.addCases_right, Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff]

end sylvester


section resultant

variable {R : Type u} [CommRing R]

/-- The resultant of two polynomials `f` and `g` is the determinant of the Sylvester matrix of `f`
and `g`. The size arguments `m` and `n` are implemented as `optParam`, meaning that the default
values are `f.natDegree` and `g.natDegree` respectively, but they can also be specified to be
other values. -/
def resultant (f g : R[X]) (m : ℕ := f.natDegree) (n : ℕ := g.natDegree) : R :=
  (sylvester f g m n).det

variable (f g : R[X]) (m n : ℕ)

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
@[simp]
theorem resultant_C_zero_right (a : R) : resultant f (C a) m 0 = a ^ m := by simp [resultant]

/-- For polynomial `f` and constant `a`, `Res(f, a) = a ^ m`. -/
theorem resultant_C_right (a : R) : resultant f (C a) m = a ^ m := by simp

end resultant

end Polynomial
