/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Linear equivalences of tensor products as isometries

These results are separate from the definition of `QuadraticForm.tmul` as that file is very slow.

## Main definitions

* `QuadraticForm.tensorComm`: `TensorProduct.comm` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorAssoc`: `TensorProduct.assoc` as a `QuadraticForm.IsometryEquiv`
-/

universe uR uM₁ uM₂ uM₃
variable {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃}

open scoped TensorProduct

namespace QuadraticForm

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Invertible (2 : R)]

section tensorComm

@[simp]
theorem tmul_comp_tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₂.tmul Q₁).comp (TensorProduct.comm R M₁ M₂) = Q₁.tmul Q₂ := by
  refine (QuadraticForm.associated_rightInverse R).injective ?_
  apply BilinForm.toLin.injective
  ext m₁ m₂ m₁' m₂'
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticForm.associated_comp]
  exact mul_comm _ _

@[simp]
theorem tmul_tensorComm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (x : M₁ ⊗[R] M₂) :
    Q₂.tmul Q₁ (TensorProduct.comm R M₁ M₂ x) = Q₁.tmul Q₂ x :=
  FunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

/-- `TensorProduct.comm` preserves tensor products of quadratic forms. -/
def tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).IsometryEquiv (Q₂.tmul Q₁) where
  toLinearEquiv := TensorProduct.comm R M₁ M₂
  map_app' := tmul_tensorComm_apply Q₁ Q₂

@[simp] lemma tensorComm_apply (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (x : M₁ ⊗[R] M₂) :
    tensorComm Q₁ Q₂ x = TensorProduct.comm R M₁ M₂ x :=
  rfl

@[simp] lemma tensorComm_symm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (tensorComm Q₁ Q₂).symm = tensorComm Q₂ Q₁ :=
  rfl

end tensorComm

section tensorAssoc

@[simp]
theorem tmul_comp_tensorAssoc
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    (Q₁.tmul (Q₂.tmul Q₃)).comp (TensorProduct.assoc R M₁ M₂ M₃) = (Q₁.tmul Q₂).tmul Q₃ := by
  refine (QuadraticForm.associated_rightInverse R).injective ?_
  apply BilinForm.toLin.injective
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticForm.associated_comp]
  exact mul_assoc _ _ _

@[simp]
theorem tmul_tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃):
    Q₁.tmul (Q₂.tmul Q₃) (TensorProduct.assoc R M₁ M₂ M₃ x) = (Q₁.tmul Q₂).tmul Q₃ x :=
  FunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

/-- `TensorProduct.assoc` preserves tensor products of quadratic forms. -/
def tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    ((Q₁.tmul Q₂).tmul Q₃).IsometryEquiv (Q₁.tmul (Q₂.tmul Q₃)) where
  toLinearEquiv := TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_comp_tensorAssoc Q₁ Q₂ Q₃

@[simp] lemma tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃) :
    tensorAssoc Q₁ Q₂ x = TensorProduct.assoc R M₁ M₂ M₃ x :=
  rfl

@[simp] lemma tensorAssoc_symm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (tensorAssoc Q₁ Q₂ Q₃).symm x = (TensorProduct.assoc R M₁ M₂ M₃).symm x).symm x :=
  rfl

end tensorAssoc

end QuadraticForm
