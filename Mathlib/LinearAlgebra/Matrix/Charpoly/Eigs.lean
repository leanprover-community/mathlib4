/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed

! This file was ported from Lean 3 source module linear_algebra.matrix.charpoly.eigs
! leanprover-community/mathlib commit 48dc6abe71248bd6f4bffc9703dc87bdd4e37d0b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Basic
import Mathbin.FieldTheory.IsAlgClosed.Basic

/-!
# Eigenvalues are characteristic polynomial roots.

In fields we show that:

* `matrix.det_eq_prod_roots_charpoly_of_splits`: the determinant (in the field of the matrix)
  is the product of the roots of the characteristic polynomial if the polynomial splits in the field
  of the matrix.
* `matrix.trace_eq_sum_roots_charpoly_of_splits`: the trace is the sum of the roots of the
  characteristic polynomial if the polynomial splits in the field of the matrix.

In an algebraically closed field we show that:

* `matrix.det_eq_prod_roots_charpoly`: the determinant is the product of the roots of the
  characteristic polynomial.
* `matrix.trace_eq_sum_roots_charpoly`: the trace is the sum of the roots of the
  characteristic polynomial.

Note that over other fields such as `ℝ`, these results can be used by using
`A.map (algebra_map ℝ ℂ)` as the matrix, and then applying `ring_hom.map_det`.

The two lemmas `matrix.det_eq_prod_roots_charpoly` and `matrix.trace_eq_sum_roots_charpoly` are more
commonly stated as trace is the sum of eigenvalues and determinant is the product of eigenvalues.
Mathlib has already defined eigenvalues in `linear_algebra.eigenspace` as the roots of the minimal
polynomial of a linear endomorphism. These do not have correct multiplicity and cannot be used in
the theorems above. Hence we express these theorems in terms of the roots of the characteristic
polynomial directly.

## TODO

The proofs of `det_eq_prod_roots_charpoly_of_splits` and
`trace_eq_sum_roots_charpoly_of_splits` closely resemble
`norm_gen_eq_prod_roots` and `trace_gen_eq_sum_roots` respectively, but the
dependencies are not general enough to unify them. We should refactor
`polynomial.prod_roots_eq_coeff_zero_of_monic_of_split` and
`polynomial.sum_roots_eq_next_coeff_of_monic_of_split` to assume splitting over an arbitrary map.
-/


variable {n : Type _} [Fintype n] [DecidableEq n]

variable {R : Type _} [Field R]

variable {A : Matrix n n R}

open Matrix Polynomial

open scoped Matrix BigOperators

namespace Matrix

theorem det_eq_prod_roots_charpoly_of_splits (hAps : A.charpoly.Splits (RingHom.id R)) :
    A.det = (Matrix.charpoly A).roots.Prod := by
  rw [det_eq_sign_charpoly_coeff, ← charpoly_nat_degree_eq_dim A,
    Polynomial.prod_roots_eq_coeff_zero_of_monic_of_split A.charpoly_monic hAps, ← mul_assoc, ←
    pow_two, pow_right_comm, neg_one_sq, one_pow, one_mul]
#align matrix.det_eq_prod_roots_charpoly_of_splits Matrix.det_eq_prod_roots_charpoly_of_splits

theorem trace_eq_sum_roots_charpoly_of_splits (hAps : A.charpoly.Splits (RingHom.id R)) :
    A.trace = (Matrix.charpoly A).roots.Sum :=
  by
  cases isEmpty_or_nonempty n
  ·
    rw [Matrix.trace, Fintype.sum_empty, Matrix.charpoly,
      det_eq_one_of_card_eq_zero (Fintype.card_eq_zero_iff.2 h), Polynomial.roots_one,
      Multiset.empty_eq_zero, Multiset.sum_zero]
  ·
    rw [trace_eq_neg_charpoly_coeff, neg_eq_iff_eq_neg, ←
      Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split A.charpoly_monic hAps, next_coeff,
      charpoly_nat_degree_eq_dim, if_neg (Fintype.card_ne_zero : Fintype.card n ≠ 0)]
#align matrix.trace_eq_sum_roots_charpoly_of_splits Matrix.trace_eq_sum_roots_charpoly_of_splits

variable (A)

theorem det_eq_prod_roots_charpoly [IsAlgClosed R] : A.det = (Matrix.charpoly A).roots.Prod :=
  det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)
#align matrix.det_eq_prod_roots_charpoly Matrix.det_eq_prod_roots_charpoly

theorem trace_eq_sum_roots_charpoly [IsAlgClosed R] : A.trace = (Matrix.charpoly A).roots.Sum :=
  trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits A.charpoly)
#align matrix.trace_eq_sum_roots_charpoly Matrix.trace_eq_sum_roots_charpoly

end Matrix

