/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Bilinear maps on a Tensor Product

## Main definitions

* `LinearMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear map on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`.

## Implementation notes

Bilinear map versions of some results in `LinearAlgebra.BilinearForm.TensorProduct`.
-/

suppress_compilation

universe u v w uι uR uA uM₁ uM₂

variable {ι : Type uι} {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂}

open TensorProduct

namespace LinearMap

variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Algebra R A] [Module R M₁] [Module A M₁]
variable [SMulCommClass R A M₁] [SMulCommClass A R M₁] [IsScalarTower R A M₁]
variable [Module R M₂]

variable (R A) in
/-- The tensor product of two bilinear maps injects into bilinear maps on tensor products.

Note this is heterobasic; the bilinear map on the left can take values in an (commutative) algebra
over the ring in which the right bilinear map is valued. -/
def tensorDistrib : (M₁ →ₗ[A] M₁ →ₗ[A] A) ⊗[R] (M₂ →ₗ[R] M₂ →ₗ[R] R) →ₗ[A]
    ((M₁ ⊗[R] M₂) →ₗ[A] (M₁ ⊗[R] M₂) →ₗ[A] A) :=
  ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R A M₁ M₂ M₁ M₂).dualMap
    ≪≫ₗ (TensorProduct.lift.equiv A (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) A).symm).toLinearMap
  ∘ₗ TensorProduct.AlgebraTensorModule.dualDistrib R _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv A M₁ M₁ A)
    (TensorProduct.lift.equiv R _ _ _)).toLinearMap

@[simp]
theorem tensorDistrib_tmul (B₁ : M₁ →ₗ[A] M₁ →ₗ[A] A) (B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R)
    (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
    LinearMap.tensorDistrib R A (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₂ m₂ m₂' • B₁ m₁ m₁' :=
  rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : M₁ →ₗ[A] M₁ →ₗ[A] A) (B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R) :
    (M₁ ⊗[R] M₂) →ₗ[A] (M₁ ⊗[R] M₂) →ₗ[A] A :=
  LinearMap.tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

variable (A) in
/-- The base change of a bilinear form. -/
protected def baseChange₂ (B : M₂ →ₗ[R] M₂ →ₗ[R] R) :
    ((A ⊗[R] M₂) →ₗ[A] (A ⊗[R] M₂) →ₗ[A] A) :=
  LinearMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
theorem baseChange_tmul₂ (B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange₂ A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl


attribute [ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear forms is symmetric. -/
lemma IsSymm.tmul {B₁ : M₁ →ₗ[A] M₁ →ₗ[A] A} {B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R}
    (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) : (B₁.tmul B₂).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂ x₂ y₂) (hB₁ x₁ y₁)

end LinearMap
