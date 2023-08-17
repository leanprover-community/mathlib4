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

* `QuadraticForm.tensorDistrib (B₁ ⊗ₜ B₂)`: the quadratic form on `M₁ ⊗ M₂` constructed by applying
  `B₁` on `M₁` and `B₂` on `M₂`. This construction is not available in characteristic two.
* `QuadraticForm.tensorDistribEquiv`: `QuadraticForm.tensorDistrib` as an equivalence on finite free
  modules.

-/


universe u v w uι uR uA uM₁ uM₂

variable {ι : Type _} {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂}

open TensorProduct

namespace QuadraticForm

section CommRing
variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂]
variable [Algebra R A] [Module R M₁] [Module A M₁]
variable [SMulCommClass R A M₁] [SMulCommClass A R M₁] [IsScalarTower R A M₁]
variable [Module R M₂] [Invertible (2 : R)]

instance : Module A (QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂) :=
  TensorProduct.leftModule


variable (R A) in
/-- The tensor product of two quadratic forms injects into quadratic forms on tensor products.

Note this is heterobasic; the quadratic form on the left can take values in a larger ring than
the one on the right. -/
def tensorDistrib : QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂ →ₗ[A] QuadraticForm A (M₁ ⊗[R] M₂) :=
  BilinForm.toQuadraticFormLinearMap A A (M₁ ⊗[R] M₂)
    ∘ₗ BilinForm.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
    ∘ₗ AlgebraTensorModule.map
      (QuadraticForm.associatedHom A : QuadraticForm A M₁ →ₗ[A] BilinForm A M₁)
      (QuadraticForm.associatedHom R : QuadraticForm R M₁ →ₗ[R] BilinForm R M₁)


-- TODO: make the RHS `MulOpposite.op (Q₂ m₂) • Q₁ m₁` so that this has a nicer defeq for
-- `R = A` of `Q₁ m₁ * Q₂ m₂`.
@[simp]
theorem tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib (A := A) (Q₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = Q₂ m₂ • Q₁ m₁ :=
  rfl
#align bilin_form.tensor_distrib_tmul QuadraticForm.tensorDistrib_tmulₓ

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (B₁ : QuadraticForm A M₁) (B₂ : QuadraticForm R M₂) : QuadraticForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib (A := A) (B₁ ⊗ₜ[R] B₂)
#align bilin_form.tmul QuadraticForm.tmul

/-- The base change of a bilinear form. -/
protected def baseChange (Q : QuadraticForm R M₂) : QuadraticForm A (A ⊗[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticForm.sq) Q

@[simp]
theorem baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) :
    Q.baseChange (a ⊗ₜ m₂) = Q m₂ • a :=
  rfl

end CommSemiring

end QuadraticForm
