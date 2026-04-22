import Mathlib.RingTheory.Coalgebra.CoassocSimps

open TensorProduct

open LinearMap (id)

namespace Coalgebra

variable {R A M N P M' N' P' Q Q' : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommMonoid M₁]
    [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "λ" => (TensorProduct.lid R _).toLinearMap
local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation3 "ρ" => (TensorProduct.rid R _).toLinearMap
local notation3 "ρ⁻¹" => (TensorProduct.rid R _).symm.toLinearMap
local notation3 "β" => (TensorProduct.comm R _ _).toLinearMap
local infix:90 " ⊗ₘ " => TensorProduct.map
local notation3 "δ" => comul (R := R)
local notation3 "ε" => counit (R := R)

example (f₃' : N →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (f₁₂ ⊗ₘ (f₃ ∘ₗ f₃')) = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ f₃') := by
  simp only [coassoc_simps]

example (f₃' : N →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] N₃)
    (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) (f : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ (f₁₂ ⊗ₘ (f₃ ∘ₗ f₃')) ∘ₗ f = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ f₃') ∘ₗ f := by
  simp only [coassoc_simps]

example (f₁ : M₁ →ₗ[R] N₁) (f₁' : N →ₗ[R] M₁) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ ((f₁ ∘ₗ f₁') ⊗ₘ f₂₃) = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (f₁' ⊗ₘ f₂₃) := by
  simp only [coassoc_simps]

example (f₁ : M₁ →ₗ[R] N₁) (f₁' : N →ₗ[R] M₁)
    (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) (f : P →ₗ[R] N ⊗[R] M) :
    α⁻¹ ∘ₗ ((f₁ ∘ₗ f₁') ⊗ₘ f₂₃) ∘ₗ f = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (f₁' ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [coassoc_simps]

example (f₁ : M₁ →ₗ[R] N₁) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) := by
  simp only [coassoc_simps]

example (f₁ : M₁ →ₗ[R] N₁)
    (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) (f : P →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) ∘ₗ f = ((f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [coassoc_simps]

example (g : N →ₗ[R] M') :
    λ ∘ₗ (id ⊗ₘ g) = g ∘ₗ λ := by
  simp only [coassoc_simps]

example (g : N →ₗ[R] M') (h : P →ₗ[R] R ⊗[R] N) :
    λ ∘ₗ (id ⊗ₘ g) ∘ₗ h = g ∘ₗ λ ∘ₗ h := by
  simp only [coassoc_simps]
