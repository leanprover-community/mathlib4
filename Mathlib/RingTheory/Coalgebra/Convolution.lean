/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała, Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała, Yunzhou Xie
-/
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

variable {R A B C : Type*} [CommSemiring R]

open scoped RingTheory.LinearMap

namespace LinearMap

section Semiring
variable [Semiring A] [Semiring B] [AddCommMonoid C] [Algebra R A] [Algebra R B] [Module R C]
  [Coalgebra R C]

/-- Convolution unit on linear maps from a coalgebra to an algebra. -/
abbrev convOne : One (C →ₗ[R] A) where one := Algebra.linearMap R A ∘ₗ counit

/-- Convolution product on linear maps from a coalgebra to an algebra. -/
abbrev convMul : Mul (C →ₗ[R] A) where mul f g := mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul

scoped[ConvolutionProduct] attribute [instance] LinearMap.convOne LinearMap.convMul

open scoped ConvolutionProduct

lemma one_def : (1 : C →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := rfl
lemma mul_def (f g : C →ₗ[R] A) : f * g = mul' R A ∘ₗ TensorProduct.map f g ∘ₗ comul := rfl

@[simp] lemma one_apply (c : C) : (1 : C →ₗ[R] A) c = algebraMap R A (counit c) := rfl
@[simp] lemma mul_apply (f g : C →ₗ[R] A) (c : C) : (f * g) c = mul' R A (.map f g (comul c)) := rfl

lemma _root_.Coalgebra.Repr.mul_apply {a : C} (𝓡 : Coalgebra.Repr R a) (f g : C →ₗ[R] A) :
    (f * g) a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [mul_def, ← 𝓡.eq]

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

private lemma one_convMul (f : C →ₗ[R] A) : 1 * f = f := calc
      μ ∘ₗ ((η ∘ₗ ε) ⊗ₘ f) ∘ₗ δ
  _ = μ ∘ₗ ((η ⊗ₘ f) ∘ₗ rTensor C ε) ∘ₗ δ  := by simp only [map_comp_rTensor]
  _ = μ ∘ₗ (η ⊗ₘ f) ∘ₗ (rTensor C ε) ∘ₗ δ := by rw [comp_assoc]
  _ = μ ∘ₗ (rTensor A η ∘ₗ lTensor R f) ∘ₗ rTensor C ε ∘ₗ δ := by simp
  _ = (μ ∘ₗ rTensor A η) ∘ₗ lTensor R f ∘ₗ (rTensor C ε ∘ₗ δ) := by simp only [comp_assoc]
  _ = (μ ∘ₗ rTensor A η) ∘ₗ lTensor R f ∘ₗ ((TensorProduct.mk R R C) 1) := by
    rw [rTensor_counit_comp_comul]
  _ = f := by ext; simp

private lemma convMul_one (f : C →ₗ[R] A) : f * 1 = f := calc
      μ ∘ₗ (f ⊗ₘ (η ∘ₗ ε)) ∘ₗ δ
  _ = μ ∘ₗ ((f ⊗ₘ η) ∘ₗ lTensor C ε) ∘ₗ δ  := by simp only [map_comp_lTensor]
  _ = μ ∘ₗ (f ⊗ₘ η) ∘ₗ lTensor C ε ∘ₗ δ := by rw [comp_assoc]
  _ = μ ∘ₗ (lTensor A η ∘ₗ rTensor R f) ∘ₗ lTensor C ε ∘ₗ δ := by simp
  _ = (μ ∘ₗ lTensor A η) ∘ₗ rTensor R f ∘ₗ (lTensor C ε ∘ₗ δ) := by simp only [comp_assoc]
  _ = (μ ∘ₗ lTensor A η) ∘ₗ rTensor R f ∘ₗ ((TensorProduct.mk R C R).flip 1) := by
    rw [lTensor_counit_comp_comul]
  _ = f := by ext; simp

/-- Convolution semiring structure on linear maps from a coalgebra to an algebra. -/
abbrev convSemiring : Semiring (C →ₗ[R] A) where
  left_distrib f g h := by ext; simp [TensorProduct.map_add_right]
  right_distrib f g h := by ext; simp [TensorProduct.map_add_left]
  zero_mul f := by ext; simp
  mul_zero f := by ext; simp
  mul_assoc := convMul_assoc
  one_mul := one_convMul
  mul_one := convMul_one

scoped[ConvolutionProduct] attribute [instance] LinearMap.convSemiring

lemma _root_.AlgHom.map_comp_mul (h : A →ₐ B) :
    h.toLinearMap ∘ₗ μ = mul' R B ∘ₗ (h.toLinearMap ⊗ₘ h.toLinearMap) := by ext; simp

lemma comp_mul_distrib (f g : C →ₗ[R] A) (h : A →ₐ[R] B) :
    h.toLinearMap.comp (f * g) = (.comp h.toLinearMap f) * (.comp h.toLinearMap g) := by
  simp only [mul_def, map_comp, ← comp_assoc, AlgHom.map_comp_mul]

end Semiring

section Ring
variable [Ring A] [AddCommMonoid C] [Algebra R A] [Module R C] [Coalgebra R C]

open scoped ConvolutionProduct

/-- Convolution ring structure on linear maps from a coalgebra to an algebra. -/
instance convRing : Ring (C →ₗ[R] A) where

scoped[ConvolutionProduct] attribute [instance] LinearMap.convRing

end Ring
end LinearMap
