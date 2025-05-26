/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/

import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with degree less than `n`

This file contains the properties of the submodule of polynomials of degree less than `n` in a
commutative ring `R`, denoted `R[X]_n`.

## Main definitions/lemmas

* `degreeLT.basis R n`: a basis for `R[X]_n` the submodule of polynomials with degree `< n`,
given by the monomials `X^i` for `i < n`.

* `degreeLT.basisProd R m n`: a basis for `(R[X]_m) × (R[X]_n)` as above, which is the sum
of the two bases.

* `degreeLT.addLinearEquiv R m n`: an isomorphism between `(R[X]_(m+n))` and `(R[X]_m) × (R[X]_n)`
given by the fact that the bases are both indexed by `Fin (m+n)`. This is used for the Sylvester
matrix, which is the matrix representing the Sylvester map between these two spaces, in a future
file.

* `taylorLinear r n`: The linear automorphism induced by `taylor r` on `R[X]_n`.

-/


namespace Polynomial

/-- R[X]_n is notation for the submodule of polynomials of degree strictly less than n. -/
scoped notation:9000 R "[X]_" n => Polynomial.degreeLT R n

namespace degreeLT

variable {R : Type*} [Semiring R] {m n : ℕ} (i : Fin n) (P : R[X]_n)

variable (R) in
/-- Basis for R[X]_n given by the `X^i` with `i < n`. -/
noncomputable def basis (n : ℕ) : Basis (Fin n) R R[X]_n :=
  .ofEquivFun (Polynomial.degreeLTEquiv R n)

instance : Module.Finite R R[X]_n :=
  .of_basis <| basis ..

instance : Module.Free R R[X]_n :=
  .of_basis <| basis ..

lemma X_pow_mem_degreeLT (i : Fin n) : X ^ i.val ∈ R[X]_n := by
  nontriviality R using mem_degreeLT, WithBot.bot_lt_iff_ne_bot
  simp only [Polynomial.mem_degreeLT, Polynomial.degree_X_pow, Nat.cast_lt, Fin.is_lt]

variable (R) in
/-- The element `X^i` in `R[X]_n`. This is equal to `basis R n i`. -/
noncomputable def xPow (n : ℕ) (i : Fin n) : R[X]_n :=
  ⟨X ^ (i : ℕ), X_pow_mem_degreeLT i⟩

@[simp] lemma xPow_val : (xPow R n i : R[X]) = X ^ (i : ℕ) :=
  rfl

@[simp] lemma basis_repr : (basis R n).repr P i = (P : R[X]).coeff i :=
  rfl

@[simp] lemma basis_apply (i : Fin n) :
    basis R n i = xPow R n i := by
  rw [Basis.apply_eq_iff]
  ext j
  simp only [basis_repr, xPow_val, coeff_X_pow, eq_comm, Finsupp.single_apply, Fin.ext_iff]

lemma basis_val (i : Fin n) : (basis R n i : R[X]) = X ^ (i : ℕ) := by
  rw [basis_apply, xPow_val]

variable (R m n) in
/-- Basis for `(R[X]_m) × (R[X]_n)`. -/
noncomputable def basisProd : Basis (Fin (m + n)) R ((R[X]_m) × (R[X]_n)) :=
  ((basis R m).prod (basis R n)).reindex finSumFinEquiv

@[simp] lemma basisProd_castAdd (m n : ℕ) (i : Fin m) :
    basisProd R m n (i.castAdd n) = (xPow R m i, 0) := by
  rw [basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Basis.prod_apply,
    Sum.elim_inl, LinearMap.coe_inl, Function.comp_apply, basis_apply]

@[simp] lemma basisProd_natAdd (m n : ℕ) (i : Fin n) :
    basisProd R m n (i.natAdd m) = (0, xPow R n i) := by
  rw [basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd, Basis.prod_apply,
    Sum.elim_inr, LinearMap.coe_inr, Function.comp_apply, basis_apply]

variable (R m n) in
/-- An isomorphism between `(R[X]_(m+n))` and `(R[X]_m) × (R[X]_n)` given by the fact that
the bases are both indexed by `Fin (m+n)`. -/
noncomputable def addLinearEquiv :
    (R[X]_(m + n)) ≃ₗ[R] (R[X]_m) × (R[X]_n) :=
  Basis.equiv (basis ..) (basisProd ..) (Equiv.refl _)

lemma addLinearEquiv_castAdd (i : Fin m) :
    addLinearEquiv R m n (xPow R (m+n) (i.castAdd n)) = (xPow R m i, 0) := by
  rw [addLinearEquiv, ← basis_apply, Basis.equiv_apply, Equiv.refl_apply, basisProd_castAdd]

lemma addLinearEquiv_natAdd (i : Fin n) :
    addLinearEquiv R m n (xPow R (m+n) (i.natAdd m)) = (0, xPow R n i) := by
  rw [addLinearEquiv, ← basis_apply, Basis.equiv_apply, Equiv.refl_apply, basisProd_natAdd]

lemma addLinearEquiv_symm_apply_xPow_left (i : Fin m) :
    (addLinearEquiv R m n).symm (LinearMap.inl R _ _ (xPow R m i)) = xPow R (m+n) (i.castAdd n) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_castAdd i).symm

lemma addLinearEquiv_symm_apply_xPow_right (j : Fin n) :
    (addLinearEquiv R m n).symm (LinearMap.inr R _ _ (xPow R n j)) = xPow R (m+n) (j.natAdd m) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_natAdd j).symm

lemma addLinearEquiv_symm_apply_left (P : R[X]_m) :
    ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ P) : R[X]) = (P : R[X]) := by
  rw [← (basis ..).sum_repr P]
  simp [-LinearMap.coe_inl, addLinearEquiv_symm_apply_xPow_left]

lemma addLinearEquiv_symm_apply_right (Q : R[X]_n) :
    ((addLinearEquiv R m n).symm (LinearMap.inr R _ _ Q) : R[X]) = (Q : R[X]) * X ^ (m : ℕ) := by
  rw [← (basis ..).sum_repr Q]
  simp [-LinearMap.coe_inr, Finset.sum_mul, addLinearEquiv_symm_apply_xPow_right,
    smul_eq_C_mul, mul_assoc, ← pow_add, add_comm]

lemma addLinearEquiv_symm_apply (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + (PQ.2 : R[X]) * X ^ (m : ℕ) := calc
  _ = ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ PQ.1 + LinearMap.inr R _ _ PQ.2) : R[X]) :=
      by rw [LinearMap.inl_apply, LinearMap.inr_apply, Prod.add_def, add_zero, zero_add]
  _ = _ := by rw [map_add, Submodule.coe_add,
        addLinearEquiv_symm_apply_left, addLinearEquiv_symm_apply_right]

lemma addLinearEquiv_symm_apply' (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + X ^ (m : ℕ) * (PQ.2 : R[X]) := by
  rw [X_pow_mul, addLinearEquiv_symm_apply]

lemma addLinearEquiv_apply' {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) ∧
      ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m) := by
  rw [and_comm, eq_comm, eq_comm (b := _ %ₘ _)]
  nontriviality R; refine div_modByMonic_unique _ _ (monic_X_pow _) ⟨?_, ?_⟩
  · rw [← addLinearEquiv_symm_apply', LinearEquiv.symm_apply_apply]
  · rw [degree_X_pow, ← mem_degreeLT]; exact Subtype.prop _

lemma addLinearEquiv_apply_fst {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).1 : R[X]) = f %ₘ (X ^ m) :=
  (addLinearEquiv_apply' f).1

lemma addLinearEquiv_apply_snd {R : Type*} [Ring R] (f) :
    ((addLinearEquiv R m n f).2 : R[X]) = f /ₘ (X ^ m) :=
  (addLinearEquiv_apply' f).2

lemma addLinearEquiv_apply {R : Type*} [Ring R] (f) :
    addLinearEquiv R m n f =
      (⟨f %ₘ (X ^ m), addLinearEquiv_apply_fst f ▸ Subtype.prop _⟩,
      ⟨f /ₘ (X ^ m), addLinearEquiv_apply_snd f ▸ Subtype.prop _⟩) :=
  Prod.ext (Subtype.ext <| addLinearEquiv_apply_fst f) (Subtype.ext <| addLinearEquiv_apply_snd f)

end degreeLT

section taylor

variable {R : Type*} [CommRing R] {r : R} {m n : ℕ} {s : R} {f g : R[X]}

lemma map_taylorEquiv_degreeLT : (R[X]_n).map (taylorEquiv r) = R[X]_n :=
  le_antisymm (Submodule.map_le_iff_le_comap.2
      fun _ hf ↦ mem_degreeLT.2 <| (degree_taylor ..).trans_lt <| mem_degreeLT.1 hf)
    (fun f hf ↦ (taylorEquiv r).apply_symm_apply f ▸ Submodule.mem_map_of_mem
      (mem_degreeLT.2 <| (degree_taylor ..).trans_lt <| mem_degreeLT.1 hf))

/-- The map `taylor r` induces an automorphism of the module `R[X]_n` of polynomials of
degree `< n`. -/
noncomputable def taylorLinear (r : R) (n : ℕ) : (R[X]_n) ≃ₗ[R] (R[X]_n) :=
  (taylorEquiv r : R[X] ≃ₗ[R] R[X]).ofSubmodules _ _ map_taylorEquiv_degreeLT

@[simp] lemma taylorLinear_apply (P : R[X]_n) :
    (taylorLinear r n P : R[X]) = (P : R[X]).taylor r :=
  rfl

@[simp] theorem det_taylor_toLinearMap :
    (taylorLinear r n).toLinearMap.det = 1 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n),
    Matrix.det_of_upperTriangular, Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply, degreeLT.basis_repr, ← natDegree_X_pow (R:=R) (i:ℕ),
      LinearEquiv.coe_coe, taylorLinear_apply, degreeLT.basis_val, taylor_coeff_natDegree,
      leadingCoeff_X_pow]
  · intro i j hji
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, degreeLT.basis_repr, taylorLinear_apply,
      degreeLT.basis_val, coeff_eq_zero_of_degree_lt]
    · rwa [degree_taylor, degree_X_pow, Nat.cast_lt, Fin.val_fin_lt]

@[simp] theorem det_taylor :
    (taylorLinear r n).det = 1 :=
  Units.ext <| by rw [LinearEquiv.coe_det, det_taylor_toLinearMap, Units.val_one]

end taylor

end Polynomial
