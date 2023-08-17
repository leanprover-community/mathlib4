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

* `QuadraticForm.tensorDistrib (Q₁ ⊗ₜ Q₂)`: the quadratic form on `M₁ ⊗ M₂` constructed by applying
  `Q₁` on `M₁` and `Q₂` on `M₂`. This construction is not available in characteristic two.

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


variable (R A) in
/-- The tensor product of two quadratic forms injects into quadratic forms on tensor products.

Note this is heterobasic; the quadratic form on the left can take values in a larger ring than
the one on the right. -/
def tensorDistrib : QuadraticForm A M₁ ⊗[R] QuadraticForm R M₂ →ₗ[A] QuadraticForm A (M₁ ⊗[R] M₂) :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  let toQ := BilinForm.toQuadraticFormLinearMap A A (M₁ ⊗[R] M₂)
  let tmulB := BilinForm.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticForm.associatedHom A : QuadraticForm A M₁ →ₗ[A] BilinForm A M₁)
      (QuadraticForm.associatedHom R : QuadraticForm R M₂ →ₗ[R] BilinForm R M₂)
  toQ ∘ₗ tmulB ∘ₗ toB

-- TODO: make the RHS `MulOpposite.op (Q₂ m₂) • Q₁ m₁` so that this has a nicer defeq for
-- `R = A` of `Q₁ m₁ * Q₂ m₂`.
@[simp]
theorem tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) :
    tensorDistrib R A (Q₁ ⊗ₜ Q₂) (m₁ ⊗ₜ m₂) = Q₂ m₂ • Q₁ m₁ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  (BilinForm.tensorDistrib_tmul _ _ _ _ _ _).trans <| congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/-- The tensor product of two quadratic forms, a shorthand for dot notation. -/
@[reducible]
protected def tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    QuadraticForm A (M₁ ⊗[R] M₂) :=
  tensorDistrib (A := A) (Q₁ ⊗ₜ[R] Q₂)

/-- The base change of a quadratic form. -/
protected def baseChange (Q : QuadraticForm R M₂) : QuadraticForm A (A ⊗[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticForm.sq) Q

@[simp]
theorem baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) :
    Q.baseChange (a ⊗ₜ m₂) = Q m₂ • a :=
  tensorDistrib_tmul _ _

end CommSemiring

end QuadraticForm
