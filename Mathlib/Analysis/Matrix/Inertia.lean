/-
Copyright (c) 2026 Richie Caputo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richie Caputo
-/
module

public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Inertia of a real symmetric matrix

This file defines the inertia indices of a real symmetric matrix: the numbers of positive and
negative eigenvalues counted with multiplicity, and the signature (their difference).

It also proves that the characteristic polynomial of `A + c • 1` splits over the eigenvalues of
`A` shifted by `c`, which identifies the root multiset of `charpoly (A + c • 1)` with the
multiset of shifted eigenvalues.  This is a convenient tool for transferring eigenvalue counts
along identities of characteristic polynomials, such as the `AB` vs `BA` identity
`Matrix.charpoly_mul_comm'`.

## Main definitions

* `Matrix.IsHermitian.posInertia`: the number of positive eigenvalues, with multiplicity.
* `Matrix.IsHermitian.negInertia`: the number of negative eigenvalues, with multiplicity.
* `Matrix.IsHermitian.signature`: `posInertia - negInertia`, as an integer.

## Main results

* `Matrix.IsHermitian.charpoly_add_smul_one`: `charpoly (A + c • 1)` splits as
  `∏ i, (X - C (eigenvalues i + c))`.
* `Matrix.IsHermitian.roots_charpoly_add_smul_one`: the root multiset of
  `charpoly (A + c • 1)` is the multiset of eigenvalues of `A` shifted by `c`.

## Tags

inertia, signature, eigenvalues, Sylvester's law of inertia
-/

@[expose] public section

open Finset Matrix Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The positive index of inertia of a real symmetric matrix: the number of positive
eigenvalues, counted with multiplicity. -/
noncomputable def IsHermitian.posInertia (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The negative index of inertia of a real symmetric matrix: the number of negative
eigenvalues, counted with multiplicity. -/
noncomputable def IsHermitian.negInertia (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i < 0).card

/-- The signature of a real symmetric matrix: the number of positive eigenvalues minus the
number of negative eigenvalues, counted with multiplicity. -/
noncomputable def IsHermitian.signature (hA : A.IsHermitian) : ℤ :=
  (hA.posInertia : ℤ) - hA.negInertia

/-- The characteristic polynomial of `A + c • 1` for a real symmetric matrix `A` splits over
the shifted eigenvalues of `A`. -/
theorem IsHermitian.charpoly_add_smul_one (hA : A.IsHermitian) (c : ℝ) :
    (A + c • 1).charpoly = ∏ i, (X - C (hA.eigenvalues i + c)) := by
  have huu : (hA.eigenvectorUnitary : Matrix n n ℝ) *
      star (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hsu : star (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hA' : A = (hA.eigenvectorUnitary : Matrix n n ℝ) * diagonal hA.eigenvalues *
      (star hA.eigenvectorUnitary : Matrix n n ℝ) := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [RCLike.ofReal_real_eq_id, Function.id_comp]
  have key : A + c • 1 = (hA.eigenvectorUnitary : Matrix n n ℝ) *
      (diagonal hA.eigenvalues + c • 1) * (star hA.eigenvectorUnitary : Matrix n n ℝ) := by
    rw [mul_add, add_mul, ← hA', mul_smul_comm, mul_one, smul_mul_assoc, huu]
  rw [key, charpoly_mul_comm, ← mul_assoc, hsu, one_mul,
    smul_one_eq_diagonal, diagonal_add, charpoly_diagonal]

/-- The root multiset of `charpoly (A + c • 1)` for a real symmetric matrix `A` is the multiset
of eigenvalues of `A`, shifted by `c`. -/
theorem IsHermitian.roots_charpoly_add_smul_one (hA : A.IsHermitian) (c : ℝ) :
    (A + c • 1).charpoly.roots = Finset.univ.val.map fun i => hA.eigenvalues i + c := by
  rw [hA.charpoly_add_smul_one c, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · simp only [Finset.prod_ne_zero_iff]
    exact fun i _ => Polynomial.X_sub_C_ne_zero _

end Matrix
