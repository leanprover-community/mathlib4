/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Linear equivalences of tensor products as isometries

These results are separate from the definition of `QuadraticForm.tmul` as that file is very slow.

## Main definitions

* `QuadraticForm.Isometry.tmul`: `TensorProduct.map` as a `QuadraticForm.Isometry`
* `QuadraticForm.tensorComm`: `TensorProduct.comm` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorAssoc`: `TensorProduct.assoc` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorRId`: `TensorProduct.rid` as a `QuadraticForm.IsometryEquiv`
* `QuadraticForm.tensorLId`: `TensorProduct.lid` as a `QuadraticForm.IsometryEquiv`
-/

@[expose] public section

universe uR uM₁ uM₂ uM₃ uM₄
variable {R : Type uR} {M₁ : Type uM₁} {M₂ : Type uM₂} {M₃ : Type uM₃} {M₄ : Type uM₄}

open scoped TensorProduct

open QuadraticMap

namespace QuadraticForm

variable [CommRing R]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Invertible (2 : R)]

@[simp]
theorem tmul_comp_tensorMap
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) :
    (Q₂.tmul Q₄).comp (TensorProduct.map f.toLinearMap g.toLinearMap) = Q₁.tmul Q₃ := by
  have h₁ : Q₁ = Q₂.comp f.toLinearMap := QuadraticMap.ext fun x => (f.map_app x).symm
  have h₃ : Q₃ = Q₄.comp g.toLinearMap := QuadraticMap.ext fun x => (g.map_app x).symm
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₃ m₁' m₃'
  simp [-associated_apply, h₁, h₃, associated_tmul]

@[simp]
theorem tmul_tensorMap_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) (x : M₁ ⊗[R] M₃) :
    Q₂.tmul Q₄ (TensorProduct.map f.toLinearMap g.toLinearMap x) = Q₁.tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorMap f g) x

namespace Isometry

/-- `TensorProduct.map` for `QuadraticForm.Isometry`s -/
def _root_.QuadraticMap.Isometry.tmul
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) : (Q₁.tmul Q₃) →qᵢ (Q₂.tmul Q₄) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  map_app' := tmul_tensorMap_apply f g

@[simp]
theorem _root_.QuadraticMap.Isometry.tmul_apply
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₃ : QuadraticForm R M₃} {Q₄ : QuadraticForm R M₄}
    (f : Q₁ →qᵢ Q₂) (g : Q₃ →qᵢ Q₄) (x : M₁ ⊗[R] M₃) :
    f.tmul g x = TensorProduct.map f.toLinearMap g.toLinearMap x :=
  rfl

end Isometry

section tensorComm

@[simp]
theorem tmul_comp_tensorComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₂.tmul Q₁).comp (TensorProduct.comm R M₁ M₂) = Q₁.tmul Q₂ := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂'
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_comm _ _

@[simp]
theorem tmul_tensorComm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (x : M₁ ⊗[R] M₂) :
    Q₂.tmul Q₁ (TensorProduct.comm R M₁ M₂ x) = Q₁.tmul Q₂ x :=
  DFunLike.congr_fun (tmul_comp_tensorComm Q₁ Q₂) x

/-- `TensorProduct.comm` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
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
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₂ m₁' m₂' m₁'' m₂''
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  exact mul_assoc _ _ _

@[simp]
theorem tmul_tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃) :
    Q₁.tmul (Q₂.tmul Q₃) (TensorProduct.assoc R M₁ M₂ M₃ x) = (Q₁.tmul Q₂).tmul Q₃ x :=
  DFunLike.congr_fun (tmul_comp_tensorAssoc Q₁ Q₂ Q₃) x

/-- `TensorProduct.assoc` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
def tensorAssoc (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃) :
    ((Q₁.tmul Q₂).tmul Q₃).IsometryEquiv (Q₁.tmul (Q₂.tmul Q₃)) where
  toLinearEquiv := TensorProduct.assoc R M₁ M₂ M₃
  map_app' := tmul_tensorAssoc_apply Q₁ Q₂ Q₃

@[simp] lemma tensorAssoc_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : (M₁ ⊗[R] M₂) ⊗[R] M₃) :
    tensorAssoc Q₁ Q₂ Q₃ x = TensorProduct.assoc R M₁ M₂ M₃ x :=
  rfl

@[simp] lemma tensorAssoc_symm_apply
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) (Q₃ : QuadraticForm R M₃)
    (x : M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (tensorAssoc Q₁ Q₂ Q₃).symm x = (TensorProduct.assoc R M₁ M₂ M₃).symm x :=
  rfl

end tensorAssoc

section tensorRId

theorem comp_tensorRId_eq (Q₁ : QuadraticForm R M₁) :
    Q₁.comp (TensorProduct.rid R M₁) = Q₁.tmul (sq (R := R)) := by
  refine (QuadraticMap.associated_rightInverse R).injective ?_
  ext m₁ m₁'
  dsimp [-associated_apply]
  simp only [associated_tmul, QuadraticMap.associated_comp]
  simp [-associated_apply, one_mul]

@[simp]
theorem tmul_tensorRId_apply
    (Q₁ : QuadraticForm R M₁) (x : M₁ ⊗[R] R) :
    Q₁ (TensorProduct.rid R M₁ x) = Q₁.tmul (sq (R := R)) x :=
  DFunLike.congr_fun (comp_tensorRId_eq Q₁) x

/-- `TensorProduct.rid` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
def tensorRId (Q₁ : QuadraticForm R M₁) :
    (Q₁.tmul (sq (R := R))).IsometryEquiv Q₁ where
  toLinearEquiv := TensorProduct.rid R M₁
  map_app' := tmul_tensorRId_apply Q₁

@[simp] lemma tensorRId_apply (Q₁ : QuadraticForm R M₁) (x : M₁ ⊗[R] R) :
    tensorRId Q₁ x = TensorProduct.rid R M₁ x :=
  rfl

@[simp] lemma tensorRId_symm_apply (Q₁ : QuadraticForm R M₁) (x : M₁) :
    (tensorRId Q₁).symm x = (TensorProduct.rid R M₁).symm x :=
  rfl

end tensorRId

section tensorLId

theorem comp_tensorLId_eq (Q₂ : QuadraticForm R M₂) :
    Q₂.comp (TensorProduct.lid R M₂) = QuadraticForm.tmul (sq (R := R)) Q₂ := by
  ext
  simp

@[simp]
theorem tmul_tensorLId_apply
    (Q₂ : QuadraticForm R M₂) (x : R ⊗[R] M₂) :
    Q₂ (TensorProduct.lid R M₂ x) = QuadraticForm.tmul (sq (R := R)) Q₂ x :=
  DFunLike.congr_fun (comp_tensorLId_eq Q₂) x

/-- `TensorProduct.lid` preserves tensor products of quadratic forms. -/
@[simps toLinearEquiv]
def tensorLId (Q₂ : QuadraticForm R M₂) :
    (QuadraticForm.tmul (sq (R := R)) Q₂).IsometryEquiv Q₂ where
  toLinearEquiv := TensorProduct.lid R M₂
  map_app' := tmul_tensorLId_apply Q₂

@[simp] lemma tensorLId_apply (Q₂ : QuadraticForm R M₂) (x : R ⊗[R] M₂) :
    tensorLId Q₂ x = TensorProduct.lid R M₂ x :=
  rfl

@[simp] lemma tensorLId_symm_apply (Q₂ : QuadraticForm R M₂) (x : M₂) :
    (tensorLId Q₂).symm x = (TensorProduct.lid R M₂).symm x :=
  rfl

end tensorLId

end QuadraticForm
