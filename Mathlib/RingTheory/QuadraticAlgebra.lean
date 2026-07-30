/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discr
public import Mathlib.RingTheory.Discriminant

/-!
# Ring-theoretic properties of quadratic algebras

This file collects ring-theoretic properties of `QuadraticAlgebra R a b` as an `R`-algebra.

## Main results

* `Algebra.trace_quadraticAlgebra_apply` and `Algebra.norm_quadraticAlgebra_apply`:
  `Algebra.trace` and `Algebra.norm` on `QuadraticAlgebra R a b` agree with
  `QuadraticAlgebra.trace` and `QuadraticAlgebra.norm`.
* `Algebra.discr_quadraticAlgebra`: `Algebra.discr R (basis a b)` equals `discr a b`.
-/

@[expose] public section

open QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The algebra trace of `QuadraticAlgebra R a b` is the elementary trace. -/
@[simp]
theorem Algebra.trace_quadraticAlgebra_apply (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  simp [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two,
    QuadraticAlgebra.trace_apply, Algebra.leftMulMatrix_eq_repr_mul, basis_repr_apply,
    basis_apply_zero, basis_apply_one]
  ring

/-- The algebra norm of `QuadraticAlgebra R a b` is the elementary norm. -/
@[simp]
theorem Algebra.norm_quadraticAlgebra_apply (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = QuadraticAlgebra.norm z := by
  simp [Algebra.norm_eq_matrix_det (basis a b), Matrix.det_fin_two, QuadraticAlgebra.norm_def,
    Algebra.leftMulMatrix_eq_repr_mul, basis_repr_apply, basis_apply_zero, basis_apply_one]
  ring

/-- The `Algebra.discr` of the standard basis `{1, ω}` is the elementary discriminant. -/
@[simp]
theorem Algebra.discr_quadraticAlgebra :
    Algebra.discr R (basis a b) = QuadraticAlgebra.discr a b := by
  rw [Algebra.discr_def, Matrix.det_fin_two, QuadraticAlgebra.discr_def]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    Algebra.trace_quadraticAlgebra_apply, basis_apply_zero, basis_apply_one, one_mul, mul_one,
    omega_mul_omega_eq_mk, QuadraticAlgebra.trace_apply, re_one, im_one, omega_re, omega_im]
  ring
