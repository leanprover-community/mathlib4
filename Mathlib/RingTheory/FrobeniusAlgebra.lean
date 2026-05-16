/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic

import Mathlib.RingTheory.Coalgebra.CoassocSimps

/-!
# Frobenius algebras

This file defines `FrobeniusAlgebra` and shows some elementary results.

A Frobenius algebra `A` over a commutative semiring `R` is a semiring with both `Algebra R A` and
`Coalgebra R A` structures such that
`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`
(the Frobenius equation).

This file shows that it suffices to have
`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)` in order to have the
Frobenius equations. So we call this one the Frobenius equation too.
-/

public section

open TensorProduct LinearMap Coalgebra
open scoped RingTheory.LinearMap

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "λ" => (TensorProduct.lid R _).toLinearMap
local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation "rT" => rTensor
local notation "lT" => lTensor

omit [Coalgebra R A] in
theorem LinearMap.mul'_comp_map_lid_comp {M N : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] R ⊗[R] A) (g : N →ₗ[R] _) :
    μ[R] ∘ₗ ((λ ∘ₗ f) ⊗ₘ g) = λ ∘ₗ lT R μ ∘ₗ α ∘ₗ (f ⊗ₘ g) := by
  trans μ[R] ∘ₗ (rT _ λ) ∘ₗ (f ⊗ₘ g)
  · ext; simp
  simp only [← comp_assoc]
  congr 1; ext; simp

/-- If `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
then `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul`. -/
theorem LinearMap.lTensor_mul'_comp_assoc_comp_rTensor_comul_of
    (h : lT A μ ∘ₗ α ∘ₗ rT A δ = rT A μ ∘ₗ α⁻¹ ∘ₗ lT A δ) :
    lT A μ ∘ₗ α ∘ₗ rT A δ = δ ∘ₗ μ := by
  simp only [lTensor, rTensor] at h ⊢
  calc
    _ = rT A μ ∘ₗ α⁻¹ ∘ₗ ((λ ∘ₗ rT A ε ∘ₗ δ) ⊗ₘ δ) := by
      simp only [h, CoassocSimps.map_counit_comp_comul_left, coassoc_simps]
    _ = λ ∘ₗ rT (A ⊗[R] A) ε ∘ₗ α ∘ₗ rT A (rT A μ ∘ₗ α⁻¹ ∘ₗ lT A δ) ∘ₗ α⁻¹ ∘ₗ lT A δ := by
      simp only [rTensor, lTensor, ← h, lid_tensor]
      simp only [coassoc_simps, mul'_comp_map_lid_comp]
    _ = λ ∘ₗ (ε ⊗ₘ δ) ∘ₗ lT A μ ∘ₗ α ∘ₗ rT A δ := by simp only [assoc_tensor, h, coassoc_simps]
    _ = λ ∘ₗ lT R (δ ∘ₗ μ) ∘ₗ α ∘ₗ rT A (rT A ε ∘ₗ δ) := by simp only [coassoc_simps]
    _ = δ ∘ₗ μ := by simp only [coassoc_simps, CoassocSimps.map_counit_comp_comul_left]

variable (R A) in
/-- A semiring with both algebra and coalgebra structures is a Frobenius algebra when
the Frobenius equation is satisfied:

`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`. -/
class FrobeniusAlgebra : Prop where
  /-- The Frobenius equation. -/
  lTensor_mul'_comp_assoc_comp_rTensor_comul : lT A μ[R] ∘ₗ α ∘ₗ rT A δ = rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ

namespace FrobeniusAlgebra
variable [FrobeniusAlgebra R A]

theorem lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul' :
    lT A μ[R] ∘ₗ α ∘ₗ rT A δ = δ ∘ₗ μ[R] :=
  lTensor_mul'_comp_assoc_comp_rTensor_comul_of lTensor_mul'_comp_assoc_comp_rTensor_comul

theorem rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul :
    rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ = δ ∘ₗ μ[R] :=
  lTensor_mul'_comp_assoc_comp_rTensor_comul (R := R) (A := A) ▸
    lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul'

section Algebra
variable {A : Type*} [Semiring A] [Algebra R A] [Coalgebra R A] [FrobeniusAlgebra R A]

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`. -/
theorem rTensor_counit_comp_mul'_assoc_symm_comp_lTensor_comul_comp_algebraLinearMap :
    rT A (ε ∘ₗ μ[R]) ∘ₗ α⁻¹ ∘ₗ lT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [lTensor_comp, ← comp_assoc (lT A η), rTensor_comp, comp_assoc _ (rT _ _),
    rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul, ← comp_assoc,
    rTensor_counit_comp_comul]
  ext; simp

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`. -/
theorem lTensor_counit_comp_mul_comp_assoc_comp_rTensor_comul_comp_algebraLinearMap :
    lT A (ε ∘ₗ μ[R]) ∘ₗ α ∘ₗ rT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [rTensor_comp, ← comp_assoc (rT A η), lTensor_comp, comp_assoc _ (lT _ _),
    lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul', ← comp_assoc,
    lTensor_counit_comp_comul]
  ext; simp

end Algebra

end FrobeniusAlgebra
