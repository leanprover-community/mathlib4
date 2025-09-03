/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Convolution product on linear maps from a coalgebra to an algebra

This file constructs the ring structure on linear maps `C → A` where `C` is a coalgebra and `A` an
algebra, where multiplication is given by `(f * g)(x) = ∑ f x₍₁₎ * g x₍₂₎` in Sweedler notation or
```
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.

## Implementation notes

Note that in the case `C = A` this convolution product conflicts with the (unfortunately global!)
group instance on `Module.End R A` with multiplication defined as composition.
As a result, the convolution product is scoped to `ConvolutionProduct`.
-/

suppress_compilation

open Coalgebra TensorProduct
open scoped RingTheory.LinearMap

variable {R A B C : Type*} [CommSemiring R]

namespace LinearMap
section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [CoalgebraStruct R C]

/-- Convolution product on linear maps from a coalgebra to an algebra. -/
abbrev convMul : Mul (C →ₗ[R] A) where mul f g := mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul

scoped[ConvolutionProduct] attribute [instance] LinearMap.convMul

open scoped ConvolutionProduct

lemma convMul_def (f g : C →ₗ[R] A) : f * g = mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul := rfl

@[simp]
lemma convMul_apply (f g : C →ₗ[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

lemma _root_.Coalgebra.Repr.convMul_apply {a : C} (𝓡 : Coalgebra.Repr R a) (f g : C →ₗ[R] A) :
    (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [convMul_def, ← 𝓡.eq]

/-- Non-unital and non-associative convolution semiring structure on linear maps from a
coalgebra to a non-unital non-associative algebra. -/
abbrev convNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (C →ₗ[R] A) where
  left_distrib f g h := by ext; simp [map_add_right]
  right_distrib f g h := by ext; simp [map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp

scoped[ConvolutionProduct] attribute [instance] LinearMap.convNonUnitalNonAssocSemiring

@[simp] lemma toSpanSingleton_convMul_toSpanSingleton (x y : A) :
    toSpanSingleton R A x * toSpanSingleton R A y = toSpanSingleton R A (x * y) := by ext; simp

end NonUnitalNonAssocSemiring

open scoped ConvolutionProduct

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [CoalgebraStruct R C]

/-- Non-unital and non-associative convolution ring structure on linear maps from a
coalgebra to a non-unital and non-associative algebra. -/
abbrev convNonUnitalNonAssocRing : NonUnitalNonAssocRing (C →ₗ[R] A) where

scoped[ConvolutionProduct] attribute [instance] LinearMap.convNonUnitalNonAssocRing

end NonUnitalNonAssocRing

section NonUnitalSemiring
variable [NonUnitalSemiring A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [Coalgebra R C]

private lemma convMul_assoc (f g h : C →ₗ[R] A) : f * g * h = f * (g * h) := calc
      μ ∘ₗ (μ ∘ₗ (f ⊗ₘ g) ∘ₗ δ ⊗ₘ h) ∘ₗ δ
  _ = (μ ∘ₗ .rTensor _ μ) ∘ₗ ((f ⊗ₘ g) ⊗ₘ h) ∘ₗ (.rTensor _ δ ∘ₗ δ) := by
    rw [comp_assoc, ← comp_assoc _ _ (rTensor _ _), rTensor_comp_map,
      ← comp_assoc _ (rTensor _ _), map_comp_rTensor, comp_assoc]
  _ = (μ ∘ₗ rTensor _ μ)
      ∘ₗ (((f ⊗ₘ g) ⊗ₘ h) ∘ₗ (TensorProduct.assoc R C C C).symm) ∘ₗ lTensor C δ ∘ₗ δ := by
    simp only [comp_assoc, coassoc_symm]
  _ = (μ ∘ₗ rTensor A μ ∘ₗ ↑(TensorProduct.assoc R A A A).symm)
      ∘ₗ (f ⊗ₘ (g ⊗ₘ h)) ∘ₗ lTensor C δ ∘ₗ δ := by
    simp only [map_map_comp_assoc_symm_eq, comp_assoc]
  _ = (μ ∘ₗ .lTensor _ μ) ∘ₗ (f ⊗ₘ (g ⊗ₘ h)) ∘ₗ (lTensor C δ ∘ₗ δ) := by
    congr 1
    ext
    simp [mul_assoc]
  _ = μ ∘ₗ (f ⊗ₘ μ ∘ₗ (g ⊗ₘ h) ∘ₗ δ) ∘ₗ δ := by
    rw [comp_assoc, ← comp_assoc _ _ (lTensor _ _), lTensor_comp_map,
      ← comp_assoc _ (lTensor _ _), map_comp_lTensor, comp_assoc]

/-- Non-unital convolution semiring structure on linear maps from a coalgebra to a
non-unital algebra. -/
abbrev convNonUnitalSemiring : NonUnitalSemiring (C →ₗ[R] A) where
  mul_assoc := convMul_assoc

scoped[ConvolutionProduct] attribute [instance] LinearMap.convNonUnitalSemiring

end NonUnitalSemiring

section NonUnitalRing
variable [NonUnitalRing A] [AddCommMonoid C] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [Module R C] [Coalgebra R C]

/-- Non-unital convolution ring structure on linear maps from a coalgebra to a
non-unital algebra. -/
abbrev convNonUnitalRing : NonUnitalRing (C →ₗ[R] A) where

scoped[ConvolutionProduct] attribute [instance] LinearMap.convNonUnitalRing

end NonUnitalRing

section Semiring
variable [Semiring A] [Semiring B] [AddCommMonoid C] [Algebra R A] [Algebra R B] [Module R C]
  [Coalgebra R C]

/-- Convolution unit on linear maps from a coalgebra to an algebra. -/
abbrev convOne : One (C →ₗ[R] A) where one := Algebra.linearMap R A ∘ₗ counit

scoped[ConvolutionProduct] attribute [instance] LinearMap.convOne LinearMap.convMul

lemma convOne_def : (1 : C →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := rfl

@[simp] lemma convOne_apply (c : C) : (1 : C →ₗ[R] A) c = algebraMap R A (counit c) := rfl

private lemma convOne_convMul (f : C →ₗ[R] A) : 1 * f = f := by
  ext; simp [convOne_def, ← map_comp_rTensor]

private lemma convMul_convOne (f : C →ₗ[R] A) : f * 1 = f := by
  ext; simp [convOne_def, ← map_comp_lTensor]

/-- Convolution semiring structure on linear maps from a coalgebra to an algebra. -/
abbrev convSemiring : Semiring (C →ₗ[R] A) where
  one_mul := convOne_convMul
  mul_one := convMul_convOne

scoped[ConvolutionProduct] attribute [instance] LinearMap.convSemiring

lemma nonUnitalAlgHom_comp_convMul_distrib (h : A →ₙₐ[R] B) (f g : C →ₗ[R] A) :
    (h : A →ₗ[R] B).comp (f * g) = .comp h f * .comp h g := by
  simp [convMul_def, map_comp, ← comp_assoc, NonUnitalAlgHom.comp_mul']

lemma algHom_comp_convMul_distrib (h : A →ₐ B) (f g : C →ₗ[R] A) :
    h.toLinearMap.comp (f * g) = h.toLinearMap.comp f * h.toLinearMap.comp g := by
  simp [convMul_def, map_comp, ← comp_assoc, AlgHom.comp_mul']

end Semiring

section Ring
variable [Ring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]

/-- Convolution ring structure on linear maps from a coalgebra to an algebra. -/
instance convRing : Ring (C →ₗ[R] A) where

scoped[ConvolutionProduct] attribute [instance] LinearMap.convRing

end Ring
end LinearMap
