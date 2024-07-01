/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

#align_import linear_algebra.matrix.charpoly.eigs from "leanprover-community/mathlib"@"48dc6abe71248bd6f4bffc9703dc87bdd4e37d0b"

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

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
`Polynomial.prod_roots_eq_coeff_zero_of_monic_of_split` and
`Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split` to assume splitting over an arbitrary map.
-/


variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [Field R]
variable {A : Matrix n n R}

open Matrix Polynomial

open scoped Matrix

namespace Matrix

theorem det_eq_prod_roots_charpoly_of_splits (hAps : A.charpoly.Splits (RingHom.id R)) :
    A.det = (Matrix.charpoly A).roots.prod := by
  rw [det_eq_sign_charpoly_coeff, ← charpoly_natDegree_eq_dim A,
    Polynomial.prod_roots_eq_coeff_zero_of_monic_of_split A.charpoly_monic hAps, ← mul_assoc,
    ← pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]
#align matrix.det_eq_prod_roots_charpoly_of_splits Matrix.det_eq_prod_roots_charpoly_of_splits

theorem trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.Splits (RingHom.id R)) :
    A.trace = (Matrix.charpoly A).roots.sum := by
  cases' isEmpty_or_nonempty n with h
  · rw [Matrix.trace, Fintype.sum_empty, Matrix.charpoly,
      det_eq_one_of_card_eq_zero (Fintype.card_eq_zero_iff.2 h), Polynomial.roots_one,
      Multiset.empty_eq_zero, Multiset.sum_zero]
  · rw [trace_eq_neg_charpoly_coeff, neg_eq_iff_eq_neg,
      ← Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split A.charpoly_monic hAps, nextCoeff,
      charpoly_natDegree_eq_dim, if_neg (Fintype.card_ne_zero : Fintype.card n ≠ 0)]
#align matrix.trace_eq_sum_roots_charpoly_of_splits Matrix.trace_eq_sum_roots_charpoly_of_splits

variable (A)

theorem det_eq_prod_roots_charpoly [IsAlgClosed R] : A.det = (Matrix.charpoly A).roots.prod :=
  det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)
#align matrix.det_eq_prod_roots_charpoly Matrix.det_eq_prod_roots_charpoly

theorem trace_eq_sum_roots_charpoly [IsAlgClosed R] : A.trace = (Matrix.charpoly A).roots.sum :=
  trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)
#align matrix.trace_eq_sum_roots_charpoly Matrix.trace_eq_sum_roots_charpoly

end Matrix
