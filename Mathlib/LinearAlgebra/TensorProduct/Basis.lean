/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FinsuppVectorSpace

#align_import linear_algebra.tensor_product_basis from "leanprover-community/mathlib"@"f784cc6142443d9ee623a20788c282112c322081"

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `LinearAlgebra.TensorProduct` since they depend on
`LinearAlgebra.FinsuppVectorSpace` which in turn imports `LinearAlgebra.TensorProduct`.
-/


noncomputable section

open Set LinearMap Submodule

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

/-- If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`. -/
def Basis.tensorProduct (b : Basis ι S M) (c : Basis κ R N) :
    Basis (ι × κ) S (TensorProduct R M N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
        (finsuppTensorFinsupp R S _ _ _ _).trans <|
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm
#align basis.tensor_product Basis.tensorProduct

@[simp]
theorem Basis.tensorProduct_apply (b : Basis ι R M) (c : Basis κ R N) (i : ι) (j : κ) :
    Basis.tensorProduct b c (i, j) = b i ⊗ₜ c j := by
  simp [Basis.tensorProduct]
#align basis.tensor_product_apply Basis.tensorProduct_apply

theorem Basis.tensorProduct_apply' (b : Basis ι R M) (c : Basis κ R N) (i : ι × κ) :
    Basis.tensorProduct b c i = b i.1 ⊗ₜ c i.2 := by
  simp [Basis.tensorProduct]
#align basis.tensor_product_apply' Basis.tensorProduct_apply'

@[simp]
theorem Basis.tensorProduct_repr_tmul_apply (b : Basis ι R M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (Basis.tensorProduct b c).repr (m ⊗ₜ n) (i, j) = b.repr m i * c.repr n j := by
  simp [Basis.tensorProduct, mul_comm]
#align basis.tensor_product_repr_tmul_apply Basis.tensorProduct_repr_tmul_apply

end CommSemiring
end
