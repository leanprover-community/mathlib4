/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Connections between `TensorProduct` and `Matrix`

This file contains results about the matrices corresponding to maps between tensor product types,
where the correspondence is induced by `Basis.tensorProduct`

Notably, `TensorProduct.toMatrix_map` shows that taking the tensor product of linear maps is
equivalent to taking the Kronecker product of their matrix representations.
-/

open Matrix Module LinearMap
open scoped Kronecker

variable {R : Type*} {M N P M' N' : Type*} {ι κ τ ι' κ' : Type*}
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]
variable [Fintype ι] [Fintype κ] [Fintype τ] [Finite ι'] [Finite κ']
variable [CommRing R]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [AddCommGroup M'] [AddCommGroup N']
variable [Module R M] [Module R N] [Module R P] [Module R M'] [Module R N']
variable (bM : Basis ι R M) (bN : Basis κ R N) (bP : Basis τ R P)
variable (bM' : Basis ι' R M') (bN' : Basis κ' R N')

/-- The linear map built from `TensorProduct.map` corresponds to the matrix built from
`Matrix.kronecker`. -/
theorem TensorProduct.toMatrix_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    toMatrix (bM.tensorProduct bN) (bM'.tensorProduct bN') (TensorProduct.map f g) =
      toMatrix bM bM' f ⊗ₖ toMatrix bN bN' g := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp_rw [Matrix.kroneckerMap_apply, toMatrix_apply, Basis.tensorProduct_apply,
    TensorProduct.map_tmul, Basis.tensorProduct_repr_tmul_apply]
  exact mul_comm _ _

/-- The matrix built from `Matrix.kronecker` corresponds to the linear map built from
`TensorProduct.map`. -/
theorem Matrix.toLin_kronecker (A : Matrix ι' ι R) (B : Matrix κ' κ R) :
    toLin (bM.tensorProduct bN) (bM'.tensorProduct bN') (A ⊗ₖ B) =
      TensorProduct.map (toLin bM bM' A) (toLin bN bN' B) := by
  rw [← LinearEquiv.eq_symm_apply, toLin_symm, TensorProduct.toMatrix_map, toMatrix_toLin,
    toMatrix_toLin]

/-- `TensorProduct.comm` corresponds to a permutation of the identity matrix. -/
theorem TensorProduct.toMatrix_comm :
    toMatrix (bM.tensorProduct bN) (bN.tensorProduct bM) (TensorProduct.comm R M N) =
      (1 : Matrix (ι × κ) (ι × κ) R).submatrix Prod.swap _root_.id := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [toMatrix_apply, Basis.tensorProduct_apply, LinearEquiv.coe_coe, comm_tmul,
    Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply, @eq_comm _ i',
    @eq_comm _ j', smul_eq_mul, mul_ite, mul_one, mul_zero, ← ite_and, and_comm, submatrix_apply,
    Matrix.one_apply, Prod.swap_prod_mk, id_eq, Prod.mk.injEq]

/-- `TensorProduct.assoc` corresponds to a permutation of the identity matrix. -/
theorem TensorProduct.toMatrix_assoc :
    toMatrix ((bM.tensorProduct bN).tensorProduct bP) (bM.tensorProduct (bN.tensorProduct bP))
        (TensorProduct.assoc R M N P) =
      (1 : Matrix (ι × κ × τ) (ι × κ × τ) R).submatrix _root_.id (Equiv.prodAssoc _ _ _) := by
  ext ⟨i, j, k⟩ ⟨⟨i', j'⟩, k'⟩
  simp only [toMatrix_apply, Basis.tensorProduct_apply, LinearEquiv.coe_coe, assoc_tmul,
    Basis.tensorProduct_repr_tmul_apply, Basis.repr_self, Finsupp.single_apply, @eq_comm _ k',
    @eq_comm _ j', smul_eq_mul, mul_ite, mul_one, mul_zero, ← ite_and, @eq_comm _ i',
    submatrix_apply, Matrix.one_apply, id_eq, Equiv.prodAssoc_apply, Prod.mk.injEq]
