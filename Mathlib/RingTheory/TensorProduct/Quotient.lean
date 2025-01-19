/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Interaction between quotients and tensor products for algebras

This files proves algebra analogs of the isomorphisms in
`Mathlib.LinearAlgebra.TensorProduct.Quotient`.

## Main results

- `Algebra.TensorProduct.tensorQuotEquivQuotIdealMap`:
  `B ⊗[A] (A ⧸ I) ≃ₐ[A] B ⧸ (I.map <| algebraMap A B)`
-/

open TensorProduct

section

variable {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

private noncomputable def tensorQuotEquivQuotIdealMapAux (I : Ideal A) :
    B ⊗[A] (A ⧸ I) ≃ₗ[A] B ⧸ (I.map <| algebraMap A B) :=
  TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)

private lemma tensorQuotEquivQuotIdealMapAux_apply (b : B) (a : A) :
    tensorQuotEquivQuotIdealMapAux B I (b ⊗ₜ[A] a) =
      Submodule.Quotient.mk (a • b) :=
  rfl

private lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMapAux_symm_mk (b : B) :
    (tensorQuotEquivQuotIdealMapAux B I).symm
      (Ideal.Quotient.mk (I.map <| algebraMap A B) b) = b ⊗ₜ[A] 1 :=
  rfl

/-- `B ⊗[A] (A ⧸ I)` is isomorphic as an `A`-algebra to `B ⧸ I B`. -/
noncomputable def Algebra.TensorProduct.tensorQuotEquivQuotIdealMap :
    B ⊗[A] (A ⧸ I) ≃ₐ[A] B ⧸ (I.map <| algebraMap A B) :=
  AlgEquiv.ofLinearEquiv (tensorQuotEquivQuotIdealMapAux B I)
    (by
      rw [one_def, ← map_one (Ideal.Quotient.mk _), tensorQuotEquivQuotIdealMapAux_apply]
      simp)
    (fun x y ↦ (tensorQuotEquivQuotIdealMapAux B I).symm.injective <| by
      conv_lhs => rw [← (tensorQuotEquivQuotIdealMapAux B I).symm_apply_apply x,
        ← (tensorQuotEquivQuotIdealMapAux B I).symm_apply_apply y]
      induction' (tensorQuotEquivQuotIdealMapAux B I) x using Submodule.Quotient.induction_on with u
      induction' (tensorQuotEquivQuotIdealMapAux B I) y using Submodule.Quotient.induction_on with v
      simp only [LinearEquiv.symm_apply_apply, Ideal.Quotient.mk_eq_mk, ← map_mul,
        tensorQuotEquivQuotIdealMapAux_symm_mk, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one])

@[simp]
lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMap_apply (b : B) (a : A) :
    tensorQuotEquivQuotIdealMap B I (b ⊗ₜ[A] a) = Submodule.Quotient.mk (a • b) :=
  rfl

@[simp]
lemma Algebra.TensorProduct.tensorQuotEquivQuotIdealMap_symm_mk (b : B) :
    (tensorQuotEquivQuotIdealMap B I).symm b = b ⊗ₜ[A] 1 :=
  rfl

end
