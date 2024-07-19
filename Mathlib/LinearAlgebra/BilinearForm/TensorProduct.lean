/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The bilinear form on a tensor product

## Main definitions

* `LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by
  applying `B₁` on `M₁` and `B₂` on `M₂`.
* `LinearMap.BilinMap.tensorDistribEquiv`: `BilinForm.tensorDistrib` as an equivalence on finite
  free modules.

-/

suppress_compilation

universe u v w uι uR uA uM₁ uM₂

variable {ι : Type uι} {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂}

open TensorProduct

namespace LinearMap

namespace BilinMap

open LinearMap (BilinMap)
open LinearMap (BilinForm)

section CommSemiring
variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Algebra R A] [Module R M₁] [Module A M₁]
variable [SMulCommClass R A M₁] [SMulCommClass A R M₁] [IsScalarTower R A M₁]
variable [Module R M₂]

variable (R A) in
/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products.

Note this is heterobasic; the bilinear form on the left can take values in an (commutative) algebra
over the ring in which the right bilinear form is valued. -/
def tensorDistrib : BilinForm A M₁ ⊗[R] BilinForm R M₂ →ₗ[A] BilinForm A (M₁ ⊗[R] M₂) :=
  ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R A M₁ M₂ M₁ M₂).dualMap
    ≪≫ₗ (TensorProduct.lift.equiv A (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) A).symm).toLinearMap
  ∘ₗ TensorProduct.AlgebraTensorModule.dualDistrib R _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv A M₁ M₁ A)
    (TensorProduct.lift.equiv R _ _ _)).toLinearMap

-- TODO: make the RHS `MulOpposite.op (B₂ m₂ m₂') • B₁ m₁ m₁'` so that this has a nicer defeq for
-- `R = A` of `B₁ m₁ m₁' * B₂ m₂ m₂'`, as it did before the generalization in #6306.
@[simp]
theorem tensorDistrib_tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₂ m₂ m₂' • B₁ m₁ m₁' :=
  rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
protected abbrev tmul (B₁ : BilinMap A M₁ A) (B₂ : BilinMap  R M₂ R) : BilinMap A (M₁ ⊗[R] M₂) A :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear forms is symmetric. -/
lemma _root_.LinearMap.IsSymm.tmul {B₁ : BilinMap A M₁ A} {B₂ : BilinMap R M₂ R}
    (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) : (B₁.tmul B₂).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂ x₂ y₂) (hB₁ x₁ y₁)

variable (A) in
/-- The base change of a bilinear form. -/
protected def baseChange (B : BilinMap R M₂ R) : BilinForm A (A ⊗[R] M₂) :=
  BilinMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
theorem baseChange_tmul (B₂ : BilinMap R M₂ R) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl

variable (A) in
/-- The base change of a symmetric bilinear form is symmetric. -/
lemma IsSymm.baseChange {B₂ : BilinForm R M₂} (hB₂ : B₂.IsSymm) : (B₂.baseChange A).IsSymm :=
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
    BilinForm R M₁ ⊗[R] BilinForm R M₂ ≃ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr (TensorProduct.lift.equiv R _ _ _) (TensorProduct.lift.equiv R _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv R _ _ _).symm

@[simp]
theorem tensorDistribEquiv_tmul (B₁ : BilinForm R M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
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
theorem tensorDistribEquiv_apply (B : BilinForm R M₁ ⊗ BilinForm R M₂) :
    tensorDistribEquiv R (M₁ := M₁) (M₂ := M₂) B = tensorDistrib R R B :=
  DFunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B

end CommRing

end BilinMap

end LinearMap
