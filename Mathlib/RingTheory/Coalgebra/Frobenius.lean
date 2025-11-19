/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic

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

/-- If `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
then `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul`. -/
theorem LinearMap.lTensor_mul'_comp_assoc_comp_rTensor_comul_of
    (h : lT A μ ∘ₗ α ∘ₗ rT A δ = rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ) :
    lT A μ ∘ₗ α ∘ₗ rT A δ = δ ∘ₗ μ[R] :=
  calc _ = rT A μ ∘ₗ α⁻¹ ∘ₗ lT A δ := h
    _ = rT _ μ ∘ₗ α⁻¹ ∘ₗ ((λ ∘ₗ rT _ ε ∘ₗ δ) ⊗ₘ δ) := by ext; simp
    _ = rT _ μ ∘ₗ α⁻¹ ∘ₗ rT _ λ ∘ₗ rT _ (rT _ ε) ∘ₗ (δ ⊗ₘ δ) := by simp only [rTensor_comp_map]
    _ = rT _ (μ[R] ∘ₗ λ ∘ₗ rTensor _ ε ∘ₗ α) ∘ₗ α⁻¹ ∘ₗ (δ ⊗ₘ δ) := by
      simp_rw [← LinearMap.comp_assoc]
      congr 1; ext; simp [smul_mul_assoc]
    _ = rT _ (λ ∘ₗ (lT _ μ[R] ∘ₗ rT _ ε) ∘ₗ α) ∘ₗ α⁻¹ ∘ₗ (δ ⊗ₘ δ) := by
      simp_rw [← LinearMap.comp_assoc]
      congr 5; ext; simp
    _ = rT _ (λ ∘ₗ (rT _ ε ∘ₗ lT _ μ[R]) ∘ₗ α) ∘ₗ α⁻¹ ∘ₗ (δ ⊗ₘ δ) := by
      congr; ext; simp
    _ = rT _ (λ ∘ₗ (rT _ ε ∘ₗ lT _ μ[R]) ∘ₗ α) ∘ₗ (α⁻¹ ∘ₗ rT _ δ) ∘ₗ lT _ δ := by
      simp only [comp_assoc]
      congr; ext; simp
    _ = rT _ (λ ∘ₗ (rT _ ε ∘ₗ lT _ μ[R]) ∘ₗ α) ∘ₗ rT _ (rT _ δ) ∘ₗ α⁻¹ ∘ₗ lT _ δ := by
      simp only [rTensor_tensor, comp_assoc]
      simp only [← comp_assoc _ _ α⁻¹, LinearEquiv.symm_comp, id_comp]
    _ = (λ ∘ₗ rT _ ε) ∘ₗ α ∘ₗ (rT _ (rT _ μ[R] ∘ₗ α⁻¹ ∘ₗ lT _ δ) ∘ₗ α⁻¹) ∘ₗ lT A δ := by
      simp_rw [← h, ← comp_assoc]
      congr 2
      simp_rw [← rTensor_comp, lid_tensor, ← LinearEquiv.comp_coe, LinearEquiv.coe_rTensor]
      symm
      nth_rw 3 [comp_assoc]
      simp only [rTensor_tensor, ← comp_assoc _ _ α⁻¹, LinearEquiv.symm_comp, id_comp]
      simp only [LinearEquiv.symm_comp, comp_id, ← rTensor_comp, comp_assoc]
    _ = λ ∘ₗ rT _ ε ∘ₗ α ∘ₗ rT _ (rT _ μ[R]) ∘ₗ rT A α⁻¹ ∘ₗ α⁻¹ ∘ₗ lT _ (rT A δ ∘ₗ δ) := by
      simp_rw [comp_assoc]
      congr 3
      simp_rw [← comp_assoc, ← rTensor_comp]
      nth_rw 1 [rTensor_comp]
      simp_rw [comp_assoc]
      congr 1
      rw [← comp_assoc, rTensor_lTensor_comp_assoc_symm, comp_assoc, ← lTensor_comp]
    _ = λ ∘ₗ rT _ ε ∘ₗ α ∘ₗ rT _ (rT _ μ[R]) ∘ₗ rT A α⁻¹ ∘ₗ α⁻¹ ∘ₗ lT _ (α⁻¹ ∘ₗ lT A δ ∘ₗ δ) := by
      rw [Coalgebra.coassoc_symm]
    _ = λ ∘ₗ rT _ ε ∘ₗ α ∘ₗ rT _ (rT _ μ[R]) ∘ₗ rT A α⁻¹ ∘ₗ α⁻¹ ∘ₗ
        lT _ α⁻¹ ∘ₗ lT _ (lT A δ) ∘ₗ lT _ δ := by
      simp_rw [← lTensor_comp]
    _ = λ ∘ₗ rT _ ε ∘ₗ (rT _ μ[R] ∘ₗ α) ∘ₗ rT A α⁻¹ ∘ₗ α⁻¹ ∘ₗ lT _ α⁻¹ ∘ₗ
        lT _ (lT A δ) ∘ₗ lT _ δ := by
      simp_rw [rTensor_tensor, comp_assoc]
      simp only [← comp_assoc _ _ α⁻¹, LinearEquiv.symm_comp, id_comp]
    _ = λ ∘ₗ rT _ ε ∘ₗ rT _ μ[R] ∘ₗ (α⁻¹ ∘ₗ lT _ (lT A δ)) ∘ₗ lT _ δ := by
      simp_rw [assoc_tensor'', LinearEquiv.trans_symm, ← LinearEquiv.comp_coe,
        LinearEquiv.symm_symm, comp_assoc]
      rfl
    _ = λ ∘ₗ rT _ ε ∘ₗ (rT _ μ[R] ∘ₗ lT _ δ) ∘ₗ α⁻¹ ∘ₗ lT _ δ := by
      simp_rw [lTensor_tensor, comp_assoc]
      simp only [← comp_assoc _ _ α, LinearEquiv.comp_symm, id_comp]
    _ = λ ∘ₗ rT _ ε ∘ₗ lT _ δ ∘ₗ (lT _ μ[R] ∘ₗ α ∘ₗ rT _ δ) := by
      simp_rw [rTensor_comp_lTensor, ← lTensor_comp_rTensor, h, comp_assoc]
    _ = λ ∘ₗ (lT _ (δ ∘ₗ μ[R]) ∘ₗ rT _ ε) ∘ₗ α ∘ₗ rT _ δ := by
      simp_rw [lTensor_comp_rTensor, ← rTensor_comp_lTensor, lTensor_comp, comp_assoc]
    _ = λ ∘ₗ lT _ (δ ∘ₗ μ[R]) ∘ₗ (rT _ ε ∘ₗ α) ∘ₗ rT _ δ := by
      simp_rw [comp_assoc]
    _ = λ ∘ₗ lT _ (δ ∘ₗ μ[R]) ∘ₗ (α ∘ₗ rT _ (rT _ ε)) ∘ₗ rT _ δ := by
      simp_rw [rTensor_tensor, comp_assoc]
      simp only [← comp_assoc _ _ α⁻¹, LinearEquiv.symm_comp, id_comp]
    _ = λ ∘ₗ lT _ (δ ∘ₗ μ[R]) ∘ₗ α ∘ₗ rT _ λ⁻¹ := by
      rw [(by rfl : λ⁻¹ = TensorProduct.mk R R A 1), ← rTensor_counit_comp_comul, rTensor_comp]
      simp_rw [comp_assoc]
    _ = δ ∘ₗ μ[R] := ext' fun _ _ => by
      simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul,
        TensorProduct.lid_symm_apply, TensorProduct.assoc_tmul, lTensor_tmul, mul'_apply,
        TensorProduct.lid_tmul, one_smul]

/-- A semiring with both algebra and coalgebra structures is a Frobenius algebra when
the Frobenius equation is satisfied:

`(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`. -/
class FrobeniusAlgebra (R A : Type*) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] [Coalgebra R A] : Prop where
  /-- The Frobenius equation. -/
  lTensor_mul'_comp_assoc_comp_rTensor_comul :
    lT A μ[R] ∘ₗ (TensorProduct.assoc R A A A) ∘ₗ rT A δ =
      rT A μ[R] ∘ₗ (TensorProduct.assoc R A A A).symm ∘ₗ lT A δ

namespace FrobeniusAlgebra
variable [FrobeniusAlgebra R A]

theorem lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul' :
    lT A μ[R] ∘ₗ α ∘ₗ rT A δ = δ ∘ₗ μ[R] :=
  lTensor_mul'_comp_assoc_comp_rTensor_comul_of
    lTensor_mul'_comp_assoc_comp_rTensor_comul

theorem rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul :
    rT A μ[R] ∘ₗ α⁻¹ ∘ₗ lT A δ = δ ∘ₗ μ[R] :=
  lTensor_mul'_comp_assoc_comp_rTensor_comul (R := R) (A := A) ▸
    lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul'

section Algebra
variable {A : Type*} [Semiring A] [Algebra R A] [Coalgebra R A] [FrobeniusAlgebra R A]

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`. -/
theorem rTensor_counit_comp_mul'_assoc_symm_comp_lTensor_comul_comp_algebraLinearMap :
    rT A (ε ∘ₗ μ[R]) ∘ₗ α⁻¹ ∘ₗ lT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [lTensor_comp, ← comp_assoc (lTensor A (Algebra.linearMap R A)),
    rTensor_comp, LinearMap.comp_assoc _ (rTensor _ _),
    rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul,
    ← LinearMap.comp_assoc, rTensor_counit_comp_comul]
  ext
  simp

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`. -/
theorem lTensor_counit_comp_mul_comp_assoc_comp_rTensor_comul_comp_algebraLinearMap :
    lT A (ε ∘ₗ μ[R]) ∘ₗ α ∘ₗ rT A (δ ∘ₗ η[R]) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [rTensor_comp, ← comp_assoc (rTensor A (Algebra.linearMap R A)),
    lTensor_comp, comp_assoc _ (lTensor _ _),
    lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul',
    ← comp_assoc, lTensor_counit_comp_comul]
  ext
  simp

end Algebra

end FrobeniusAlgebra
