/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor product and products of algebras

In this file we examine the behaviour of the tensor product with (finite) products. This
is a direct application of `Mathlib/LinearAlgebra/TensorProduct/Pi.lean` to the algebra case.

-/

open TensorProduct

namespace Algebra.TensorProduct

variable (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring A]
  [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {ι : Type*} (B : ι → Type*) [∀ i, Semiring (B i)] [∀ i, Algebra R (B i)]

@[simp]
lemma piRightHom_one : piRightHom R S A B 1 = 1 := rfl

variable {R S A B} in
@[simp]
lemma piRightHom_mul (x y : A ⊗[R] ∀ i, B i) :
    piRightHom R S A B (x * y) = piRightHom R S A B x * piRightHom R S A B y := by
  induction x
  · simp
  · induction y
    · simp
    · ext j
      simp
    · simp_all [mul_add]
  · simp_all [add_mul]

/-- The canonical map `A ⊗[R] (∀ i, B i) →ₐ[S] ∀ i, A ⊗[R] B i`. This is an isomorphism
if `ι` is finite (see `Algebra.TensorProduct.piRight`). -/
def piRightHom : A ⊗[R] (∀ i, B i) →ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgHom.ofLinearMap (_root_.TensorProduct.piRightHom R S A B) (by simp) (by simp)

variable [Fintype ι] [DecidableEq ι]

/-- Tensor product of rings commutes with finite products on the right. -/
def piRight : A ⊗[R] (∀ i, B i) ≃ₐ[S] ∀ i, A ⊗[R] B i :=
  AlgEquiv.ofLinearEquiv (_root_.TensorProduct.piRight R S A B) (by simp) (by simp)

@[simp]
lemma piRight_tmul (x : A) (f : ∀ i, B i) :
    piRight R S A B (x ⊗ₜ f) = (fun j ↦ x ⊗ₜ f j) := rfl

variable (ι) in
/-- Variant of `Algebra.TensorProduct.piRight` with constant factors. -/
def piScalarRight : A ⊗[R] (ι → R) ≃ₐ[S] ι → A :=
  (piRight R S A (fun _ : ι ↦ R)).trans <|
    AlgEquiv.piCongrRight (fun _ ↦ Algebra.TensorProduct.rid R S A)

lemma piScalarRight_tmul (x : A) (y : ι → R) :
    piScalarRight R S A ι (x ⊗ₜ y) = fun i ↦ y i • x :=
  rfl

@[simp]
lemma piScalarRight_tmul_apply (x : A) (y : ι → R) (i : ι) :
    piScalarRight R S A ι (x ⊗ₜ y) i = y i • x :=
  rfl

section

variable (B C : Type*) [Semiring B] [Semiring C] [Algebra R B] [Algebra R C]

/-- Tensor product of rings commutes with binary products on the right. -/
nonrec def prodRight : A ⊗[R] (B × C) ≃ₐ[S] A ⊗[R] B × A ⊗[R] C :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodRight R S A B C)
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

lemma prodRight_tmul (a : A) (x : B × C) : prodRight R S A B C (a ⊗ₜ x) = (a ⊗ₜ x.1, a ⊗ₜ x.2) :=
  rfl

@[simp]
lemma prodRight_tmul_fst (a : A) (x : B × C) : (prodRight R S A B C (a ⊗ₜ x)).fst = a ⊗ₜ x.1 :=
  rfl

@[simp]
lemma prodRight_tmul_snd (a : A) (x : B × C) : (prodRight R S A B C (a ⊗ₜ x)).snd = a ⊗ₜ x.2 :=
  rfl

@[simp]
lemma prodRight_symm_tmul (a : A) (b : B) (c : C) :
    (prodRight R S A B C).symm (a ⊗ₜ b, a ⊗ₜ c) = a ⊗ₜ (b, c) := by
  apply (prodRight R S A B C).injective
  simp [prodRight_tmul]

end

end Algebra.TensorProduct
