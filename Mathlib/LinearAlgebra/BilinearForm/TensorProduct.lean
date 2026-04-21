/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The bilinear form on a tensor product

## Main definitions

* `LinearMap.BilinMap.tensorDistrib (B₁ ⊗ₜ B₂)`: the bilinear form on `M₁ ⊗ M₂` constructed by
  applying `B₁` on `M₁` and `B₂` on `M₂`.
* `LinearMap.BilinMap.tensorDistribEquiv`: `BilinForm.tensorDistrib` as an equivalence on finite
  free modules.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v w uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open TensorProduct

namespace LinearMap

open LinearMap (BilinMap BilinForm)

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁]
variable [SMulCommClass R A N₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

namespace BilinMap

variable (R A) in
/-- The tensor product of two bilinear maps injects into bilinear maps on tensor products.

Note this is heterobasic; the bilinear map on the left can take values in a module over a
(commutative) algebra over the ring of the module in which the right bilinear map is valued. -/
def tensorDistrib :
    (BilinMap A M₁ N₁ ⊗[R] BilinMap R M₂ N₂) →ₗ[A] BilinMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  (TensorProduct.lift.equiv (.id A) (M₁ ⊗[R] M₂) (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂)).symm.toLinearMap ∘ₗ
  ((LinearMap.llcomp A _ _ _).flip
    (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A M₁ M₂ M₁ M₂).toLinearMap)
  ∘ₗ TensorProduct.AlgebraTensorModule.homTensorHomMap R _ _ _ _ _ _
  ∘ₗ (TensorProduct.AlgebraTensorModule.congr
    (TensorProduct.lift.equiv (.id A) M₁ M₁ N₁)
    (TensorProduct.lift.equiv (.id R) _ _ _)).toLinearMap

@[simp]
theorem tensorDistrib_tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₁ m₁ m₁' ⊗ₜ B₂ m₂ m₂' :=
  rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
protected abbrev tmul (B₁ : BilinMap A M₁ N₁) (B₂ : BilinMap R M₂ N₂) :
    BilinMap A (M₁ ⊗[R] M₂) (N₁ ⊗[R] N₂) :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear maps is symmetric. -/
lemma tmul_isSymm {B₁ : BilinMap A M₁ N₁} {B₂ : BilinMap R M₂ N₂}
    (hB₁ : ∀ x y, B₁ x y = B₁ y x) (hB₂ : ∀ x y, B₂ x y = B₂ y x)
    (x y : M₁ ⊗[R] M₂) :
    B₁.tmul B₂ x y = B₁.tmul B₂ y x := by
  revert x y
  rw [isSymm_iff_eq_flip]
  aesop

variable (A) in
/-- The base change of a bilinear map (also known as "extension of scalars"). -/
protected def baseChange (B : BilinMap R M₂ N₂) : BilinMap A (A ⊗[R] M₂) (A ⊗[R] N₂) :=
  BilinMap.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
theorem baseChange_tmul (B₂ : BilinMap R M₂ N₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (a * a') ⊗ₜ (B₂ m₂ m₂') :=
  rfl

lemma baseChange_isSymm {B₂ : BilinMap R M₂ N₂} (hB₂ : ∀ x y, B₂ x y = B₂ y x) (x y : A ⊗[R] M₂) :
    B₂.baseChange A x y = B₂.baseChange A y x :=
  tmul_isSymm mul_comm hB₂ x y

end BilinMap

namespace BilinForm

variable (R A) in
/-- The tensor product of two bilinear forms injects into bilinear forms on tensor products.

Note this is heterobasic; the bilinear form on the left can take values in an (commutative) algebra
over the ring in which the right bilinear form is valued. -/
def tensorDistrib : BilinForm A M₁ ⊗[R] BilinForm R M₂ →ₗ[A] BilinForm A (M₁ ⊗[R] M₂) :=
  (AlgebraTensorModule.rid R A A).congrRight₂.toLinearMap ∘ₗ (BilinMap.tensorDistrib R A)

variable (R A) in
-- TODO: make the RHS `MulOpposite.op (B₂ m₂ m₂') • B₁ m₁ m₁'` so that this has a nicer defeq for
-- `R = A` of `B₁ m₁ m₁' * B₂ m₂ m₂'`, as it did before the generalization in https://github.com/leanprover-community/mathlib4/pull/6306.
@[simp]
theorem tensorDistrib_tmul (B₁ : BilinForm A M₁) (B₂ : BilinForm R M₂) (m₁ : M₁) (m₂ : M₂)
    (m₁' : M₁) (m₂' : M₂) :
    tensorDistrib R A (B₁ ⊗ₜ B₂) (m₁ ⊗ₜ m₂) (m₁' ⊗ₜ m₂')
      = B₂ m₂ m₂' • B₁ m₁ m₁' :=
  rfl

/-- The tensor product of two bilinear forms, a shorthand for dot notation. -/
protected abbrev tmul (B₁ : BilinForm A M₁) (B₂ : BilinMap R M₂ R) : BilinMap A (M₁ ⊗[R] M₂) A :=
  tensorDistrib R A (B₁ ⊗ₜ[R] B₂)

attribute [local ext] TensorProduct.ext in
/-- A tensor product of symmetric bilinear forms is symmetric. -/
lemma _root_.LinearMap.IsSymm.tmul {B₁ : BilinForm A M₁} {B₂ : BilinForm R M₂}
    (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) : (B₁.tmul B₂).IsSymm := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext x₁ x₂ y₁ y₂
  exact congr_arg₂ (HSMul.hSMul) (hB₂.eq x₂ y₂) (hB₁.eq x₁ y₁)

variable (A) in
/-- The base change of a bilinear form. -/
protected def baseChange (B : BilinForm R M₂) : BilinForm A (A ⊗[R] M₂) :=
  BilinForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (LinearMap.mul A A) B

@[simp]
theorem baseChange_tmul (B₂ : BilinForm R M₂) (a : A) (m₂ : M₂)
    (a' : A) (m₂' : M₂) :
    B₂.baseChange A (a ⊗ₜ m₂) (a' ⊗ₜ m₂') = (B₂ m₂ m₂') • (a * a') :=
  rfl

variable (A) in
/-- The base change of a symmetric bilinear form is symmetric. -/
lemma IsSymm.baseChange {B₂ : BilinForm R M₂} (hB₂ : B₂.IsSymm) : (B₂.baseChange A).IsSymm :=
  IsSymm.tmul ⟨mul_comm⟩ hB₂

end BilinForm

end CommSemiring

section CommRing

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Module.Free R M₁] [Module.Finite R M₁]
variable [Module.Free R M₂] [Module.Finite R M₂]

namespace BilinForm

variable (R) in
/-- `tensorDistrib` as an equivalence. -/
noncomputable def tensorDistribEquiv :
    BilinForm R M₁ ⊗[R] BilinForm R M₂ ≃ₗ[R] BilinForm R (M₁ ⊗[R] M₂) :=
  -- the same `LinearEquiv`s as from `tensorDistrib`,
  -- but with the inner linear map also as an equiv
  TensorProduct.congr
    (TensorProduct.lift.equiv (.id R) _ _ _) (TensorProduct.lift.equiv (.id R) _ _ _) ≪≫ₗ
  TensorProduct.dualDistribEquiv R (M₁ ⊗ M₁) (M₂ ⊗ M₂) ≪≫ₗ
  (TensorProduct.tensorTensorTensorComm R _ _ _ _).dualMap ≪≫ₗ
  (TensorProduct.lift.equiv (.id R) _ _ _).symm

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

end BilinForm

end CommRing

end LinearMap
