/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.tensor_product.matrix
! leanprover-community/mathlib commit f784cc6142443d9ee623a20788c282112c322081
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Kronecker
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.TensorProductBasis

/-!
# Connections between `tensor_product` and `matrix`

This file contains results about the matrices corresponding to maps between tensor product types,
where the correspondance is induced by `basis.tensor_product`

Notably, `tensor_product.to_matrix_map` shows that taking  the tensor product of linear maps is
equivalent to taking the kronecker product of their matrix representations.
-/


variable {R : Type _} {M N P M' N' : Type _} {ι κ τ ι' κ' : Type _}

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

variable [Fintype ι] [Fintype κ] [Fintype τ] [Fintype ι'] [Fintype κ']

variable [CommRing R]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [AddCommGroup M'] [AddCommGroup N']

variable [Module R M] [Module R N] [Module R P] [Module R M'] [Module R N']

variable (bM : Basis ι R M) (bN : Basis κ R N) (bP : Basis τ R P)

variable (bM' : Basis ι' R M') (bN' : Basis κ' R N')

open Kronecker

open Matrix LinearMap

/-- The linear map built from `tensor_product.map` corresponds to the matrix built from
`matrix.kronecker`. -/
theorem TensorProduct.toMatrix_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    toMatrix (bM.TensorProduct bN) (bM'.TensorProduct bN') (TensorProduct.map f g) =
      toMatrix bM bM' f ⊗ₖ toMatrix bN bN' g :=
  by
  ext (⟨i, j⟩⟨i', j'⟩)
  simp_rw [Matrix.kroneckerMap_apply, to_matrix_apply, Basis.tensorProduct_apply,
    TensorProduct.map_tmul, Basis.tensorProduct_repr_tmul_apply]
#align tensor_product.to_matrix_map TensorProduct.toMatrix_map

/-- The matrix built from `matrix.kronecker` corresponds to the linear map built from
`tensor_product.map`. -/
theorem Matrix.toLin_kronecker (A : Matrix ι' ι R) (B : Matrix κ' κ R) :
    toLin (bM.TensorProduct bN) (bM'.TensorProduct bN') (A ⊗ₖ B) =
      TensorProduct.map (toLin bM bM' A) (toLin bN bN' B) :=
  by
  rw [← LinearEquiv.eq_symm_apply, to_lin_symm, TensorProduct.toMatrix_map, to_matrix_to_lin,
    to_matrix_to_lin]
#align matrix.to_lin_kronecker Matrix.toLin_kronecker

/-- `tensor_product.comm` corresponds to a permutation of the identity matrix. -/
theorem TensorProduct.toMatrix_comm :
    toMatrix (bM.TensorProduct bN) (bN.TensorProduct bM) (TensorProduct.comm R M N) =
      (1 : Matrix (ι × κ) (ι × κ) R).submatrix Prod.swap id :=
  by
  ext (⟨i, j⟩⟨i', j'⟩)
  simp_rw [to_matrix_apply, Basis.tensorProduct_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    Basis.tensorProduct_repr_tmul_apply, Matrix.submatrix_apply, Prod.swap_prod_mk, id.def,
    Basis.repr_self_apply, Matrix.one_apply, Prod.ext_iff, ite_and, @eq_comm _ i', @eq_comm _ j']
  split_ifs <;> simp
#align tensor_product.to_matrix_comm TensorProduct.toMatrix_comm

/-- `tensor_product.assoc` corresponds to a permutation of the identity matrix. -/
theorem TensorProduct.toMatrix_assoc :
    toMatrix ((bM.TensorProduct bN).TensorProduct bP) (bM.TensorProduct (bN.TensorProduct bP))
        (TensorProduct.assoc R M N P) =
      (1 : Matrix (ι × κ × τ) (ι × κ × τ) R).submatrix id (Equiv.prodAssoc _ _ _) :=
  by
  ext (⟨i, j, k⟩⟨⟨i', j'⟩, k'⟩)
  simp_rw [to_matrix_apply, Basis.tensorProduct_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, Basis.tensorProduct_repr_tmul_apply, Matrix.submatrix_apply,
    Equiv.prodAssoc_apply, id.def, Basis.repr_self_apply, Matrix.one_apply, Prod.ext_iff, ite_and,
    @eq_comm _ i', @eq_comm _ j', @eq_comm _ k']
  split_ifs <;> simp
#align tensor_product.to_matrix_assoc TensorProduct.toMatrix_assoc

