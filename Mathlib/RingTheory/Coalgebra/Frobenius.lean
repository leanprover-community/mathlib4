/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Coalgebra.Basic

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

variable {R A : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Coalgebra R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

local notation "ϰ" => TensorProduct.assoc R
local notation "τ" => TensorProduct.lid R

/-- If `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = (mul ⊗ id) ∘ assoc.symm ∘ (id ⊗ comul)`,
then `(id ⊗ mul) ∘ assoc ∘ (comul ⊗ id) = comul ∘ mul`. -/
theorem LinearMap.lTensor_mul'_comp_assoc_comp_rTensor_comul_of
    (h : lTensor A (mul' R A) ∘ₗ ϰ A A A ∘ₗ rTensor A comul =
      rTensor A (mul' R A) ∘ₗ (ϰ A A A).symm ∘ₗ lTensor A comul) :
    lTensor A (mul' R A) ∘ₗ ϰ A A A ∘ₗ rTensor A comul = comul ∘ₗ mul' R A :=
  calc _ = rTensor A (mul' R A) ∘ₗ (ϰ A A A).symm ∘ₗ lTensor A comul := h
    _ = rTensor _ (mul' R A) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ
      map ((τ _).toLinearMap ∘ₗ rTensor _ counit ∘ₗ comul) comul := by ext; simp
    _ = rTensor _ (mul' R A) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ rTensor _ (τ _).toLinearMap ∘ₗ
      rTensor _ (rTensor _ counit) ∘ₗ map comul comul := by simp only [rTensor_comp_map]
    _ = rTensor _ (mul' R _ ∘ₗ (τ _).toLinearMap ∘ₗ rTensor _ counit ∘ₗ (ϰ A A A).toLinearMap) ∘ₗ
      (ϰ _ _ _).symm.toLinearMap ∘ₗ map comul comul := by
        simp_rw [← LinearMap.comp_assoc]
        congr 1; ext; simp [smul_mul_assoc]
    _ = rTensor _ ((τ _).toLinearMap ∘ₗ (lTensor _ (mul' R A) ∘ₗ rTensor _ counit) ∘ₗ
      (ϰ _ _ _).toLinearMap) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ map comul comul := by
        simp_rw [← LinearMap.comp_assoc]
        congr 5; ext; simp
    _ = rTensor _ ((τ _).toLinearMap ∘ₗ (rTensor _ counit ∘ₗ lTensor _ (mul' R A)) ∘ₗ
      (ϰ _ _ _).toLinearMap) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ map comul comul := by
        congr; ext; simp
    _ = rTensor _ ((τ _).toLinearMap ∘ₗ (rTensor _ counit ∘ₗ lTensor _ (mul' R A)) ∘ₗ
        (ϰ _ _ _).toLinearMap) ∘ₗ
      ((ϰ _ _ _).symm.toLinearMap ∘ₗ rTensor _ comul) ∘ₗ lTensor _ comul := by
        simp only [comp_assoc]
        congr; ext; simp
    _ = rTensor _ ((τ _).toLinearMap ∘ₗ (rTensor _ counit ∘ₗ lTensor _ (mul' R A)) ∘ₗ
      (ϰ _ _ _).toLinearMap) ∘ₗ rTensor _ (rTensor _ comul) ∘ₗ
      (ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ comul := by
        simp only [rTensor_tensor, comp_assoc]
        simp only [← comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap, LinearEquiv.symm_comp, id_comp]
    _ = ((τ _).toLinearMap ∘ₗ rTensor _ counit) ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ
      (rTensor _ (rTensor _ (mul' R A) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ
      lTensor _ comul) ∘ₗ (ϰ _ _ _).symm.toLinearMap) ∘ₗ lTensor A comul := by
        rw [← h]
        simp_rw [← comp_assoc]
        congr 2
        simp_rw [← rTensor_comp, lid_tensor, ← LinearEquiv.comp_coe,
          LinearEquiv.coe_rTensor]
        symm
        nth_rw 3 [comp_assoc]
        simp only [rTensor_tensor, ← comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap,
          LinearEquiv.symm_comp, id_comp]
        simp_rw [← comp_assoc, ← rTensor_comp]
        nth_rw 2 [comp_assoc]
        simp only [LinearEquiv.symm_comp, comp_id]
        simp_rw [← rTensor_comp, comp_assoc]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ
      rTensor _ (rTensor _ (mul' R A)) ∘ₗ rTensor A (ϰ A A A).symm.toLinearMap ∘ₗ
      (ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ (rTensor A comul ∘ₗ comul) := by
        simp_rw [comp_assoc]
        congr 3
        simp_rw [← comp_assoc]
        rw [← rTensor_comp]
        nth_rw 1 [rTensor_comp]
        simp_rw [comp_assoc]
        congr 1
        rw [← comp_assoc, rTensor_lTensor_comp_assoc_symm, comp_assoc, ← lTensor_comp]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ
      rTensor _ (rTensor _ (mul' R A)) ∘ₗ rTensor A (ϰ A A A).symm.toLinearMap ∘ₗ
      (ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ ((ϰ _ _ _).symm.toLinearMap ∘ₗ
      lTensor A comul ∘ₗ comul) := by
        rw [Coalgebra.coassoc_symm]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ
      rTensor _ (rTensor _ (mul' R A)) ∘ₗ rTensor A (ϰ A A A).symm.toLinearMap ∘ₗ
      (ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ (ϰ _ _ _).symm.toLinearMap ∘ₗ
      lTensor _ (lTensor A comul) ∘ₗ lTensor _ comul := by
        simp_rw [← lTensor_comp]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ (rTensor _ (mul' R A) ∘ₗ
      (ϰ _ _ _).toLinearMap) ∘ₗ rTensor A (ϰ A A A).symm.toLinearMap ∘ₗ
      (ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ (ϰ _ _ _).symm.toLinearMap ∘ₗ
      lTensor _ (lTensor A comul) ∘ₗ lTensor _ comul := by
        simp_rw [rTensor_tensor, comp_assoc]
        simp only [← comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap, LinearEquiv.symm_comp, id_comp]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ rTensor _ (mul' R A) ∘ₗ
      ((ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ (lTensor A comul)) ∘ₗ lTensor _ comul := by
        rw [assoc_tensor'']
        simp_rw [LinearEquiv.trans_symm, ← LinearEquiv.comp_coe, LinearEquiv.symm_symm, comp_assoc]
        rfl
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ (rTensor _ (mul' R A) ∘ₗ
      lTensor _ comul) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ lTensor _ comul := by
        simp_rw [lTensor_tensor, comp_assoc]
        simp only [← comp_assoc _ _ (ϰ _ _ _).toLinearMap, LinearEquiv.comp_symm, id_comp]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ rTensor _ counit ∘ₗ lTensor _ comul ∘ₗ
      (lTensor _ (mul' R A) ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ rTensor _ comul) := by
        rw [rTensor_comp_lTensor, ← lTensor_comp_rTensor, h]
        simp_rw [comp_assoc]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ (lTensor _ (comul ∘ₗ (mul' R A)) ∘ₗ rTensor _ counit) ∘ₗ
      (ϰ _ _ _).toLinearMap ∘ₗ rTensor _ comul := by
        rw [lTensor_comp_rTensor, ← rTensor_comp_lTensor, lTensor_comp]
        simp_rw [comp_assoc]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ lTensor _ (comul ∘ₗ (mul' R A)) ∘ₗ (rTensor _ counit ∘ₗ
      (ϰ _ _ _).toLinearMap) ∘ₗ rTensor _ comul := by
        simp_rw [comp_assoc]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ lTensor _ (comul ∘ₗ (mul' R A)) ∘ₗ ((ϰ _ _ _).toLinearMap ∘ₗ
      rTensor _ (rTensor _ counit)) ∘ₗ rTensor _ comul := by
        simp_rw [rTensor_tensor, comp_assoc]
        simp only [← comp_assoc _ _ (ϰ _ _ _).symm.toLinearMap, LinearEquiv.symm_comp, id_comp]
    _ = (τ (A ⊗[R] A)).toLinearMap ∘ₗ lTensor _ (comul ∘ₗ (mul' R A)) ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ
      rTensor _ (τ A).symm.toLinearMap := by
        rw [(by rfl : (τ A).symm.toLinearMap = (TensorProduct.mk R R A) 1),
          ← rTensor_counit_comp_comul, rTensor_comp]
        simp_rw [comp_assoc]
    _ = comul ∘ₗ mul' R A := ext' fun _ _ => by
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
    lTensor A (mul' R A) ∘ₗ (TensorProduct.assoc R A A A) ∘ₗ rTensor A comul =
      rTensor A (mul' R A) ∘ₗ (TensorProduct.assoc R A A A).symm ∘ₗ lTensor A comul

namespace FrobeniusAlgebra
variable [FrobeniusAlgebra R A]

theorem lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul' :
    lTensor A (mul' R A) ∘ₗ ϰ A A A ∘ₗ rTensor A comul = comul ∘ₗ mul' R A :=
  lTensor_mul'_comp_assoc_comp_rTensor_comul_of
    FrobeniusAlgebra.lTensor_mul'_comp_assoc_comp_rTensor_comul

theorem rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul :
    rTensor A (mul' R A) ∘ₗ (ϰ A A A).symm ∘ₗ lTensor A comul = comul ∘ₗ mul' R A :=
  lTensor_mul'_comp_assoc_comp_rTensor_comul (R := R) (A := A)
    ▸ lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul'

section Algebra
variable {A : Type*} [Semiring A] [Algebra R A] [Coalgebra R A] [FrobeniusAlgebra R A]

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`. -/
theorem rTensor_counit_comp_mul'_assoc_symm_comp_lTensor_comul_comp_algebraLinearMap :
    rTensor A (counit ∘ₗ mul' R A) ∘ₗ (ϰ _ _ _).symm.toLinearMap ∘ₗ
      lTensor A (comul ∘ₗ Algebra.linearMap R A) =
      (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [lTensor_comp, ← comp_assoc (lTensor A (Algebra.linearMap R A)),
    rTensor_comp, LinearMap.comp_assoc _ (rTensor _ _),
    rTensor_mul'_comp_assoc_symm_comp_lTensor_comul_eq_comul_comp_mul,
    ← LinearMap.comp_assoc, rTensor_counit_comp_comul]
  ext
  simp

/-- Composing the Frobenius equations with `Coalgebra.counit` and `Algebra.linearMap`. -/
theorem lTensor_counit_comp_mul_comp_assoc_comp_rTensor_comul_comp_algebraLinearMap :
    lTensor A (counit ∘ₗ mul' R A) ∘ₗ (ϰ _ _ _).toLinearMap ∘ₗ
      rTensor A (comul ∘ₗ Algebra.linearMap R A) = (TensorProduct.comm _ _ _).toLinearMap := by
  simp_rw [rTensor_comp, ← comp_assoc (rTensor A (Algebra.linearMap R A)),
    lTensor_comp, comp_assoc _ (lTensor _ _),
    lTensor_mul'_comp_assoc_comp_rTensor_comul_eq_comul_comp_mul',
    ← comp_assoc, lTensor_counit_comp_comul]
  ext
  simp

end Algebra

end FrobeniusAlgebra
