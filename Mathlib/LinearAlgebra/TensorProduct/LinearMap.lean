/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Christopher Hoskin
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Bilinear maps on a Tensor Product

## Main definitions

* `LinearMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear map on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`.
* `LinearMap.tensorDistribEquiv`: `LinearMap.tensorDistrib` as an equivalence on finite free
  modules.

## TODO

Move results to bilinear map namespace #10424

-/

suppress_compilation

universe u v w uι uR uA uM₁ uM₂

variable {ι : Type uι} {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂}

open TensorProduct

namespace LinearMap

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Algebra R A] [Module R M₁] [Module A M₁]
variable [IsScalarTower R A M₁]
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

-- TODO: make the RHS `MulOpposite.op (B₂ m₂ m₂') • B₁ m₁ m₁'` so that this has a nicer defeq for
-- `R = A` of `B₁ m₁ m₁' * B₂ m₂ m₂'`, as it did before the generalization in #6306.
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

attribute [ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear forms is symmetric. -/
lemma IsSymm.tmul {B₁ : M₁ →ₗ[A] M₁ →ₗ[A] A} {B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R}
    (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) : (B₁.tmul B₂).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂ x₂ y₂) (hB₁ x₁ y₁)

variable (A) in
/-- The base change of a bilinear form. -/
protected def baseChange₂ (B : M₂ →ₗ[R] M₂ →ₗ[R] R) :
    ((A ⊗[R] M₂) →ₗ[A] (A ⊗[R] M₂) →ₗ[A] A) :=
  LinearMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
theorem baseChange₂_tmul (B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange₂ A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl

variable (A) in
/-- The base change of a symmetric bilinear form is symmetric. -/
lemma IsSymm.baseChange {B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R} (hB₂ : B₂.IsSymm) : (B₂.baseChange₂ A).IsSymm :=
  IsSymm.tmul mul_comm hB₂

end CommSemiring

section CommRing

variable [CommRing R]

variable [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Module.Free R M₁] [Module.Finite R M₁]

variable [Module.Free R M₂] [Module.Finite R M₂]

variable [Nontrivial R]

variable (R) in
/-- `tensorDistrib` as an equivalence. -/
noncomputable def tensorDistribEquiv :
    (M₁ →ₗ[R] M₁ →ₗ[R] R) ⊗[R] (M₂ →ₗ[R] M₂ →ₗ[R] R) ≃ₗ[R]
    (M₁ ⊗[R] M₂) →ₗ[R] (M₁ ⊗[R] M₂) →ₗ[R] R :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr (TensorProduct.lift.equiv R _ _ _)
    (TensorProduct.lift.equiv R _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv R _ _ _).symm

-- this is a dsimp lemma
@[simp, nolint simpNF]
theorem tensorDistribEquiv_tmul (B₁ : M₁ →ₗ[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ[R] M₂ →ₗ[R] R)
    (m₁ : M₁) (m₂ : M₂) (m₁' : M₁) (m₂' : M₂) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) (B₁ ⊗ₜ[R] B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₁ m₁ m₁' * B₂ m₂ m₂' :=
  rfl

variable (R M₁ M₂) in
-- TODO: make this `rfl`
@[simp]
theorem tensorDistribEquiv_toLinearMap :
    (tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂)).toLinearMap = tensorDistrib R R := by
  ext B₁ B₂ : 3
  ext
  exact mul_comm _ _

@[simp]
theorem tensorDistribEquiv_apply (B : (M₁ →ₗ[R] M₁ →ₗ[R] R) ⊗ (M₂ →ₗ[R] M₂ →ₗ[R] R)) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) B = tensorDistrib R R B :=
  DFunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B

end CommRing

end LinearMap
