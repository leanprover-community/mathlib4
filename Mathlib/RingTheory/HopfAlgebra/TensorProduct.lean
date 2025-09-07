/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Tensor products of Hopf algebras

We define the Hopf algebra instance on the tensor product of two Hopf algebras.

-/

open Coalgebra TensorProduct HopfAlgebra

namespace TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [HopfAlgebra R A] [HopfAlgebra S B] [Algebra R B]
    [IsScalarTower R S B]

noncomputable
instance : HopfAlgebra S (B ⊗[R] A) where
  antipode := AlgebraTensorModule.map (HopfAlgebra.antipode S) (HopfAlgebra.antipode R)
  mul_antipode_rTensor_comul := by
    ext x y
    convert congr($(mul_antipode_rTensor_comul_apply (R := S) x) ⊗ₜ[R]
      $(mul_antipode_rTensor_comul_apply (R := R) y)) using 1
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      simp
    · dsimp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul']
  mul_antipode_lTensor_comul := by
    ext x y
    convert congr($(mul_antipode_lTensor_comul_apply (R := S) x) ⊗ₜ[R]
      $(mul_antipode_lTensor_comul_apply (R := R) y)) using 1
    · dsimp [Algebra.TensorProduct.one_def]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      simp
    · dsimp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul']

@[simp]
theorem antipode_def :
    antipode S (A := B ⊗[R] A) = AlgebraTensorModule.map (antipode S) (antipode R) := rfl

end TensorProduct
