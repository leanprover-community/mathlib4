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

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [HopfAlgebra R A]
    [HopfAlgebra R B]

noncomputable
instance : HopfAlgebra R (B ⊗[R] A) where
  antipode := AlgebraTensorModule.map HopfAlgebra.antipode HopfAlgebra.antipode
  mul_antipode_rTensor_comul := by
    ext x y
    convert congr($(mul_antipode_rTensor_comul_apply (R := R) x) ⊗ₜ[R]
      $(mul_antipode_rTensor_comul_apply (R := R) y)) using 1
    · dsimp
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      simp
    · dsimp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul', mul_smul]
  mul_antipode_lTensor_comul := by
    ext x y
    convert congr($(mul_antipode_lTensor_comul_apply (R := R) x) ⊗ₜ[R]
      $(mul_antipode_lTensor_comul_apply (R := R) y)) using 1
    · dsimp [Algebra.TensorProduct.one_def]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      simp
    · dsimp [Algebra.TensorProduct.one_def]
      simp [Algebra.algebraMap_eq_smul_one, smul_tmul', mul_smul]

@[simp]
theorem antipode_def :
    antipode (R := R) (A := B ⊗[R] A) = AlgebraTensorModule.map antipode antipode := rfl

end TensorProduct
