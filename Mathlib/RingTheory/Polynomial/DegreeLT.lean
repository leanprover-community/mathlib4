/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kenny Lau
-/

import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials with degree strictly less than `n`

This file contains the properties of the submodule of polynomials of degree less than `n` in a
(semi)ring `R`, denoted `R[X]_n`.

## Main definitions/lemmas

* `degreeLT.basis R n`: a basis for `R[X]_n` the submodule of polynomials with degree `< n`,
  given by the monomials `X^i` for `i < n`.

* `degreeLT.basisProd R m n`: a basis for `R[X]_m × R[X]_n`, which is the sum of two instances of
  the basis given above.

* `degreeLT.addLinearEquiv R m n`: an isomorphism between `R[X]_(m + n)` and `R[X]_m × R[X]_n`,
  given by the fact that the bases are both indexed by `Fin (m + n)`. This is used for the Sylvester
  matrix, which is the matrix representing the Sylvester map between these two spaces, in a future
  file.

* `taylorLinear r n`: The linear automorphism induced by `taylor r` on `R[X]_n` which sends `X` to
  `X + r` and preserves degrees.

-/

open Module

namespace Polynomial

@[inherit_doc] scoped notation:9000 R "[X]_" n:arg => Polynomial.degreeLT R n

namespace degreeLT

variable {R : Type*} [Semiring R] {m n : ℕ} (i : Fin n) (P : R[X]_n)

variable (R) in
/-- Basis for `R[X]_n` given by `X^i` with `i < n`. -/
noncomputable def basis (n : ℕ) : Basis (Fin n) R R[X]_n :=
  .ofEquivFun (degreeLTEquiv R n)

instance : Module.Finite R R[X]_n := .of_basis <| basis ..
instance : Module.Free R R[X]_n := .of_basis <| basis ..

@[simp] lemma basis_repr : (basis R n).repr P i = (P : R[X]).coeff i :=
  rfl

@[simp] lemma basis_val : (basis R n i : R[X]) = X ^ (i : ℕ) := by
  change _ = ((⟨X ^ (i : ℕ), mem_degreeLT.2 <| (degree_X_pow_le i).trans_lt <|
      Nat.cast_lt.2 i.is_lt⟩ : R[X]_n) : R[X])
  refine congr_arg _ (Basis.apply_eq_iff.2 <| Finsupp.ext fun j ↦ ?_)
  simp only [basis_repr, coeff_X_pow, eq_comm, Finsupp.single_apply, Fin.ext_iff]

variable (R m n) in
/-- Basis for `R[X]_m × R[X]_n`. -/
noncomputable def basisProd : Basis (Fin (m + n)) R (R[X]_m × R[X]_n) :=
  ((basis R m).prod (basis R n)).reindex finSumFinEquiv

@[simp] lemma basisProd_castAdd (m n : ℕ) (i : Fin m) :
    basisProd R m n (i.castAdd n) = (basis R m i, 0) := by
  rw [basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd, Basis.prod_apply,
    Sum.elim_inl, LinearMap.coe_inl, Function.comp_apply]

@[simp] lemma basisProd_natAdd (m n : ℕ) (i : Fin n) :
    basisProd R m n (i.natAdd m) = (0, basis R n i) := by
  rw [basisProd, Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd, Basis.prod_apply,
    Sum.elim_inr, LinearMap.coe_inr, Function.comp_apply]

variable (R m n) in
/-- An isomorphism between `R[X]_(m + n)` and `R[X]_m × R[X]_n` given by the fact that the bases are
both indexed by `Fin (m + n)`. -/
noncomputable def addLinearEquiv :
    R[X]_(m + n) ≃ₗ[R] R[X]_m × R[X]_n :=
  Basis.equiv (basis ..) (basisProd ..) (Equiv.refl _)

lemma addLinearEquiv_castAdd (i : Fin m) :
    addLinearEquiv R m n (basis R (m + n) (i.castAdd n)) = (basis R m i, 0) := by
  rw [addLinearEquiv, Basis.equiv_apply, Equiv.refl_apply, basisProd_castAdd]

lemma addLinearEquiv_natAdd (i : Fin n) :
    addLinearEquiv R m n (basis R (m + n) (i.natAdd m)) = (0, basis R n i) := by
  rw [addLinearEquiv, Basis.equiv_apply, Equiv.refl_apply, basisProd_natAdd]

lemma addLinearEquiv_symm_apply_inl_basis (i : Fin m) :
    (addLinearEquiv R m n).symm (LinearMap.inl R _ _ (basis R m i)) =
      basis R (m + n) (i.castAdd n) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_castAdd i).symm

lemma addLinearEquiv_symm_apply_inr_basis (j : Fin n) :
    (addLinearEquiv R m n).symm (LinearMap.inr R _ _ (basis R n j)) =
      basis R (m + n) (j.natAdd m) :=
  (LinearEquiv.symm_apply_eq _).2 (addLinearEquiv_natAdd j).symm

lemma addLinearEquiv_symm_apply_inl (P : R[X]_m) :
    ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ P) : R[X]) = (P : R[X]) := by
  rw [← (basis ..).sum_repr P]
  simp [-LinearMap.coe_inl, addLinearEquiv_symm_apply_inl_basis]

lemma addLinearEquiv_symm_apply_inr (Q : R[X]_n) :
    ((addLinearEquiv R m n).symm (LinearMap.inr R _ _ Q) : R[X]) = (Q : R[X]) * X ^ (m : ℕ) := by
  rw [← (basis ..).sum_repr Q]
  simp [-LinearMap.coe_inr, Finset.sum_mul, addLinearEquiv_symm_apply_inr_basis,
    smul_eq_C_mul, mul_assoc, ← pow_add, add_comm]

lemma addLinearEquiv_symm_apply (PQ) :
    ((addLinearEquiv R m n).symm PQ : R[X]) = (PQ.1 : R[X]) + (PQ.2 : R[X]) * X ^ (m : ℕ) := calc
  _ = ((addLinearEquiv R m n).symm (LinearMap.inl R _ _ PQ.1 + LinearMap.inr R _ _ PQ.2) : R[X]) :=
      by rw [LinearMap.inl_apply, LinearMap.inr_apply, Prod.add_def, add_zero, zero_add]
  _ = _ := by rw [map_add, Submodule.coe_add,
        addLinearEquiv_symm_apply_inl, addLinearEquiv_symm_apply_inr]

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

@[simp]
lemma taylor_mem_degreeLT : taylor r f ∈ R[X]_n ↔ f ∈ R[X]_n := by simp [mem_degreeLT]

lemma comap_taylorEquiv_degreeLT : (R[X]_n).comap (taylorEquiv r) = R[X]_n := by
  ext; simp [taylorEquiv]

lemma map_taylorEquiv_degreeLT : (R[X]_n).map (taylorEquiv r) = R[X]_n := by
  nth_rw 1 [← comap_taylorEquiv_degreeLT (r := r),
    Submodule.map_comap_eq_of_surjective (taylorEquiv r).surjective]

/-- The map `taylor r` induces an automorphism of the module `R[X]_n` of polynomials of
degree `< n`. -/
@[simps! apply_coe]
noncomputable def taylorLinearEquiv (r : R) (n : ℕ) : R[X]_n ≃ₗ[R] R[X]_n :=
  (taylorEquiv r : R[X] ≃ₗ[R] R[X]).ofSubmodules _ _ map_taylorEquiv_degreeLT

@[simp] lemma taylorLinearEquiv_symm (r : R) :
    (taylorLinearEquiv r n).symm = taylorLinearEquiv (-r) n :=
  LinearEquiv.ext <| fun _ ↦ rfl

@[simp] theorem det_taylorLinearEquiv_toLinearMap :
    (taylorLinearEquiv r n).toLinearMap.det = 1 := by
  nontriviality R
  rw [← LinearMap.det_toMatrix (degreeLT.basis R n),
    Matrix.det_of_upperTriangular, Fintype.prod_eq_one]
  · intro i
    rw [LinearMap.toMatrix_apply, degreeLT.basis_repr, ← natDegree_X_pow (R := R) (i : ℕ)]
    change (taylor r (degreeLT.basis R n i)).coeff _ = 1
    rw [degreeLT.basis_val, coeff_taylor_natDegree, leadingCoeff_X_pow]
  · intro i j hji
    rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, degreeLT.basis_repr]
    change (taylor r (degreeLT.basis R n j)).coeff i = 0
    rw [degreeLT.basis_val, coeff_eq_zero_of_degree_lt (by simpa [-taylor_X_pow, -taylor_pow])]

@[simp] theorem det_taylorLinearEquiv :
    (taylorLinearEquiv r n).det = 1 :=
  Units.ext <| by rw [LinearEquiv.coe_det, det_taylorLinearEquiv_toLinearMap, Units.val_one]

end taylor

end Polynomial
