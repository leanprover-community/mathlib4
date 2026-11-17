/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Ring-theoretic properties of quadratic algebras

This file collects ring-theoretic properties of `QuadraticAlgebra R a b` as an `R`-algebra.

## Main results

* `QuadraticAlgebra.polynomial_discr_eq_discr`: the discriminant of the polynomial
  `X ^ 2 - C b * X - C a` equals `discr a b`.
* `Algebra.trace_quadraticAlgebra_apply` and `Algebra.norm_quadraticAlgebra_apply`:
  `Algebra.trace` and `Algebra.norm` on `QuadraticAlgebra R a b` agree with
  `QuadraticAlgebra.trace` and `QuadraticAlgebra.norm`.
* `Algebra.discr_quadraticAlgebra`: `Algebra.discr R (basis a b)` equals `discr a b`.
-/

@[expose] public section

open QuadraticAlgebra

variable {R : Type*} [CommRing R] (a b : R)

open Polynomial in
/-- The discriminant of the polynomial `X ^ 2 - C b * X - C a` is the discriminant `discr a b` of
the quadratic algebra `QuadraticAlgebra R a b`. -/
theorem QuadraticAlgebra.polynomial_discr_eq_discr :
    (X ^ 2 - C b * X - C a).discr = discr a b := by
  nontriviality R
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [discr_def]

variable {a b}

/-- The matrix of left multiplication by `z` in the basis `{1, ω}`. -/
theorem Algebra.leftMulMatrix_quadraticAlgebra (z : QuadraticAlgebra R a b) :
    Algebra.leftMulMatrix (basis a b) z = !![z.re, a * z.im; z.im, z.re + b * z.im] := by
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  simp [Algebra.leftMulMatrix_eq_repr_mul]

/-- The algebra trace of `QuadraticAlgebra R a b` is the elementary trace. -/
@[simp]
theorem Algebra.trace_quadraticAlgebra_apply (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  rw [Algebra.trace_eq_matrix_trace (basis a b), Algebra.leftMulMatrix_quadraticAlgebra,
    Matrix.trace_fin_two_of, trace_def]
  ring

/-- The algebra norm of `QuadraticAlgebra R a b` is the elementary norm. -/
@[simp]
theorem Algebra.norm_quadraticAlgebra_apply (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = QuadraticAlgebra.norm z :=
  det_toLinearMap_eq_norm z

/-- The `Algebra.discr` of the standard basis `{1, ω}` is the elementary discriminant. -/
@[simp]
theorem Algebra.discr_quadraticAlgebra :
    Algebra.discr R (basis a b) = QuadraticAlgebra.discr a b := by
  rw [Algebra.discr_def, Matrix.det_fin_two, QuadraticAlgebra.discr_def]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    Algebra.trace_quadraticAlgebra_apply, basis_apply_zero, basis_apply_one, one_mul, mul_one,
    omega_mul_omega_eq_mk, QuadraticAlgebra.trace_def, re_one, im_one, re_omega, im_omega]
  ring
