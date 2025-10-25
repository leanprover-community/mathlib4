/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

* `Matrix.mem_spectrum_iff_isRoot_charpoly`: the roots of the characteristic polynomial are exactly
  the spectrum of the matrix.
* `Matrix.det_eq_prod_roots_charpoly_of_splits`: the determinant (in the field of the matrix)
  is the product of the roots of the characteristic polynomial if the polynomial splits in the field
  of the matrix.
* `Matrix.trace_eq_sum_roots_charpoly_of_splits`: the trace is the sum of the roots of the
  characteristic polynomial if the polynomial splits in the field of the matrix.

In an algebraically closed field we show that:

* `Matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
  characteristic polynomial.
* `Matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the
  characteristic polynomial.

Note that over other fields such as `ℝ`, these results can be used by using
`A.map (algebraMap ℝ ℂ)` as the matrix, and then applying `RingHom.map_det`.

The two lemmas `Matrix.det_eq_prod_roots_charpoly` and `Matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `LinearAlgebra.Eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.

## TODO

The proofs of `det_eq_prod_roots_charpoly_of_splits` and
`trace_eq_sum_roots_charpoly_of_splits` closely resemble
`norm_gen_eq_prod_roots` and `trace_gen_eq_sum_roots` respectively, but the
dependencies are not general enough to unify them. We should refactor
`Polynomial.coeff_zero_eq_prod_roots_of_monic_of_split` and
`Polynomial.nextCoeff_eq_neg_sum_roots_of_monic_of_splits` to assume splitting over an
arbitrary map.
-/


variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R K : Type*} [CommRing R] [Field K]
variable {A : Matrix n n K} {B : Matrix n n R}

open Matrix Polynomial

open scoped Matrix

namespace Matrix

/-- The roots of the characteristic polynomial are in the spectrum of the matrix. -/
theorem mem_spectrum_of_isRoot_charpoly [Nontrivial R]
    {r : R} (hr : IsRoot B.charpoly r) : r ∈ spectrum R B := by
  simp_all [eval_charpoly, spectrum.mem_iff, isUnit_iff_isUnit_det, algebraMap_eq_diagonal,
    Pi.algebraMap_def]

/--
In fields, the roots of the characteristic polynomial are exactly the spectrum of the matrix.
The weaker direction is true in nontrivial rings (see `Matrix.mem_spectrum_of_isRoot_charpoly`).
-/
theorem mem_spectrum_iff_isRoot_charpoly {r : K} : r ∈ spectrum K A ↔ IsRoot A.charpoly r := by
  simp [eval_charpoly, spectrum.mem_iff, isUnit_iff_isUnit_det, algebraMap_eq_diagonal,
    Pi.algebraMap_def]

theorem det_eq_prod_roots_charpoly_of_factors (hAps : A.charpoly.Factors) :
    A.det = (Matrix.charpoly A).roots.prod := by
  rw [det_eq_sign_charpoly_coeff, ← charpoly_natDegree_eq_dim A,
    Polynomial.coeff_zero_eq_prod_roots_of_monic_of_factors A.charpoly_monic hAps, ← mul_assoc,
    ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]

@[deprecated (since := "2025-10-24")]
alias det_eq_prod_roots_charpoly_of_splits := det_eq_prod_roots_charpoly_of_factors

theorem trace_eq_sum_roots_charpoly_of_factors (hAps : A.charpoly.Factors) :
    A.trace = (Matrix.charpoly A).roots.sum := by
  rcases isEmpty_or_nonempty n with h | _
  · rw [Matrix.trace, Fintype.sum_empty, Matrix.charpoly,
      det_eq_one_of_card_eq_zero (Fintype.card_eq_zero_iff.2 h), Polynomial.roots_one,
      Multiset.empty_eq_zero, Multiset.sum_zero]
  · rw [trace_eq_neg_charpoly_nextCoeff, neg_eq_iff_eq_neg,
      ← Polynomial.nextCoeff_eq_neg_sum_roots_of_monic_of_factors A.charpoly_monic hAps]

@[deprecated (since := "2025-10-24")]
alias trace_eq_sum_roots_charpoly_of_splits := trace_eq_sum_roots_charpoly_of_factors

variable (A)

theorem det_eq_prod_roots_charpoly [IsAlgClosed K] : A.det = (Matrix.charpoly A).roots.prod :=
  det_eq_prod_roots_charpoly_of_factors (IsAlgClosed.factors A.charpoly)

theorem trace_eq_sum_roots_charpoly [IsAlgClosed K] : A.trace = (Matrix.charpoly A).roots.sum :=
  trace_eq_sum_roots_charpoly_of_factors (IsAlgClosed.factors A.charpoly)

end Matrix
