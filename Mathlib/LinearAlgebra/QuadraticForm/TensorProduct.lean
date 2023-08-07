/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The quadratic form on a tensor product

## Main definitions

* `QuadraticForm.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`.
* `QuadraticForm.tensorDistribEquiv`: `QuadraticForm.tensorDistrib` as an equivalence on finite free
  modules.

-/


universe u v w uι uR uA uM₁ uM₂

variable {ι : Type _} {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂}

open TensorProduct

namespace QuadraticForm

section CommSemiring
variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Algebra R A] [Module R M₁] [Module A M₁]
variable [SMulCommClass R A M₁] [SMulCommClass A R M₁] [IsScalarTower R A M₁]
variable [Module R M₂] [Invertible (2 : R)]

instance :   SMulCommClass R A (QuadraticForm A M₁) := QuadraticForm.smulComm

instance : Module A (QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂) :=
  TensorProduct.leftModule
/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products.

Note this is heterobasic; the bilinear form on the left can take values in a larger ring than
the one on the right. -/
def tensorDistrib : QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂ →ₗ[A] QuadraticForm A (M₁ ⊗[R] M₂) :=
_ ∘ₗ BilinForm.tensorDistrib ∘ₗ AlgebraTensorModule.map _ _


#exit
-- TODO: make the RHS `MulOpposite.op (B₂ m₂ m₂') • B₁ m₁ m₁'` so that this has a nicer defeq for
-- `R = A` of `B₁ m₁ m₁' * B₂ m₂ m₂'`, as it did before the generalization in #6306.
@[simp]
theorem tensorDistrib_tmul (B₁ : QuadraticForm A M₁) (B₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib (A := A) (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₂ m₂ m₂' • B₁ m₁ m₁' :=
  rfl
#align bilin_form.tensor_distrib_tmul QuadraticForm.tensorDistrib_tmulₓ

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : QuadraticForm A M₁) (B₂ : QuadraticForm R M₂) : QuadraticForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib (A := A) (B₁ ⊗ₜ[R] B₂)
#align bilin_form.tmul QuadraticForm.tmul

/-- The base change of a bilinear form. -/
protected def baseChange (B : QuadraticForm R M₂) : QuadraticForm A (A ⊗[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.toBilin <| LinearMap.mul A A) B

@[simp]
theorem baseChange_tmul (B₂ : QuadraticForm R M₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl

end CommSemiring

section CommRing

variable [CommRing R]

variable [AddCommGroup M₁] [AddCommGroup M₂]

variable [Module R M₁] [Module R M₂]

variable [Module.Free R M₁] [Module.Finite R M₁]

variable [Module.Free R M₂] [Module.Finite R M₂]

variable [Nontrivial R]

/-- `tensorDistrib` as an equivalence. -/
noncomputable def tensorDistribEquiv :
    QuadraticForm R M₁ ⊗[R] QuadraticForm R M₂ ≃ₗ[R] QuadraticForm R (M₁ ⊗[R] M₂) :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr (QuadraticForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _)
    (QuadraticForm.toLin ≪≫ₗ TensorProduct.lift.equiv R _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv R _ _ _).symm ≪≫ₗ LinearMap.toBilin
#align bilin_form.tensor_distrib_equiv QuadraticForm.tensorDistribEquiv


@[simp]
theorem tensorDistribEquiv_tmul (B₁ : QuadraticForm R M₁) (B₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistribEquiv (R := R) (M₁ := M₁) (M₂ := M₂) (B₁ ⊗ₜ[R] B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₁ m₁ m₁' * B₂ m₂ m₂' :=
  rfl

variable (R M₁ M₂) in
-- TODO: make this `rfl`
@[simp]
theorem tensorDistribEquiv_toLinearMap :
    (tensorDistribEquiv (R := R) (M₁ := M₁) (M₂ := M₂)).toLinearMap = tensorDistrib (A := R) := by
  ext B₁ B₂ : 3
  apply toLin.injective
  ext
  exact mul_comm _ _

@[simp]
theorem tensorDistribEquiv_apply (B : QuadraticForm R M₁ ⊗ QuadraticForm R M₂) :
    tensorDistribEquiv (R := R) (M₁ := M₁) (M₂ := M₂) B = tensorDistrib (A := R) B :=
  FunLike.congr_fun (tensorDistribEquiv_toLinearMap R M₁ M₂) B
#align bilin_form.tensor_distrib_equiv_apply QuadraticForm.tensorDistribEquiv_apply

end CommRing

end QuadraticForm
