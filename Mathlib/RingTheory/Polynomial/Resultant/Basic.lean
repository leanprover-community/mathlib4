/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/

import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Resultant of two polynomials

This file contains basic facts about resultant of two polynomials over commutative rings.

## Main definitions

* `Polynomial.resultant`: The resultant of two polynomials `p` and `q` is defined as the determinant
  of the Sylvester matrix of `p` and `q`.
* `Polynomial.disc`: The discriminant of a polynomial `f` is defined as the resultant of `f` and
  `f.derivative`, modified by factoring out a sign and a power of the leading term.

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

open Set

namespace Polynomial

section sylvester

variable {R : Type*} [Semiring R]

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

/--
The Sylvester matrix for `f` and `f.derivative`, modified by dividing the bottom row by
the leading coefficient of `f`. Important because its determinant is (up to a sign) the
discriminant of `f`.
-/
noncomputable def
sylvester_deriv (f : R[X]) : Matrix (Fin (2 * f.natDegree - 1)) (Fin (2 * f.natDegree - 1)) R :=
  letI n := f.natDegree
  .of fun i j ↦
    if i < 2 * n - 2 then
      f.sylvester f.derivative n (n - 1) ⟨i, by omega⟩ ⟨j, by omega⟩
    else (if ↑j = n - 2 then 1 else (if ↑j = 2 * n - 2 then n else 0))

end sylvester

section resultant

variable {R : Type*} [CommRing R]

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

section disc

variable {R : Type*} [CommRing R]

/-- The discriminant of a polynomial, defined as the determinant of `f.sylvester_deriv` modified
by a sign. The sign is chosen so polynomials over `ℝ` with all roots real have non-negative
discriminant. -/
noncomputable def disc (f : R[X]) : R :=
  f.sylvester_deriv.det * (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)

/-- The discriminant of a constant polynomial is `1`. -/
lemma disc_const (r : R) : disc (C r) = 1 := by
  let e : Fin (2 * (C r).natDegree - 1) ≃ Fin 0 := finCongr (by simp)
  simp [disc, ← Matrix.det_reindex_self e]

/-- The discriminant of a linear polynomial is `1`. -/
lemma disc_linear {f : R[X]} (hf : f.natDegree = 1) : disc f = 1 := by
  let e : Fin (2 * f.natDegree - 1) ≃ Fin 1 := finCongr (by rw [hf])
  have : f.sylvester_deriv.reindex e e = !![1] := by
    ext i j
    simp [e, sylvester_deriv, mul_comm, hf]
  simp [disc, ← Matrix.det_reindex_self e,  this, hf]

/-- Standard formula for the discriminant of a quadratic polynomial. -/
lemma disc_quadratic {f : R[X]} (hf : f.natDegree = 2) :
    disc f = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2 := by
  let e : Fin (2 * f.natDegree - 1) ≃ Fin 3 := finCongr (by rw [hf])
  rw [disc, ← Matrix.det_reindex_self e]
  have : f.sylvester_deriv.reindex e e =
      !![f.coeff 0,     f.coeff 1,         0;
         f.coeff 1, 2 * f.coeff 2, f.coeff 1;
         1,                     0,         2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, sylvester_deriv, sylvester, coeff_derivative, mul_comm, Fin.addCases,
        one_add_one_eq_two, hf]
  simp only [this, hf, Matrix.det_fin_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val]
  ring_nf

set_option maxHeartbeats 300000 in -- times out otherwise!
/-- Standard formula for the discriminant of a cubic polynomial. -/
lemma disc_cubic {f : R[X]} (hf : f.natDegree = 3) :
    disc f = f.coeff 2 ^ 2 * f.coeff 1 ^ 2
              - 4 * f.coeff 3 * f.coeff 1 ^ 3
              - 4 * f.coeff 2 ^ 3 * f.coeff 0
              - 27 * f.coeff 3 ^ 2 * f.coeff 0 ^ 2
              + 18 * f.coeff 3 * f.coeff 2 * f.coeff 1 * f.coeff 0 := by
  let e : Fin (2 * f.natDegree - 1) ≃ Fin 5 := finCongr (by rw [hf])
  rw [disc, ← Matrix.det_reindex_self e]
  have : f.sylvester_deriv.reindex e e =
      !![f.coeff 0,         0, 1 * f.coeff 1,             0,             0;
         f.coeff 1, f.coeff 0, 2 * f.coeff 2, 1 * f.coeff 1,             0;
         f.coeff 2, f.coeff 1, 3 * f.coeff 3, 2 * f.coeff 2, 1 * f.coeff 1;
         f.coeff 3, f.coeff 2,             0, 3 * f.coeff 3, 2 * f.coeff 2;
                 0,         1,             0,             0,             3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [e, hf, sylvester_deriv, sylvester, coeff_derivative, mul_comm, Fin.addCases,
        one_add_one_eq_two, (by norm_num : (2 : R) + 1 = 3)]
  simp [this, Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hf]
  ring_nf

end disc

end Polynomial
