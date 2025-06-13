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
`Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.

## Main results

- `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`:
  `B ⧸ (I.map <| algebraMap A B) ≃ₐ[B] B ⊗[A] (A ⧸ I)`
-/

open TensorProduct

namespace Algebra.TensorProduct

variable {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

private noncomputable def quotIdealMapEquivTensorQuotAux :
      (B ⧸ (I.map <| algebraMap A B)) ≃ₗ[B] B ⊗[A] (A ⧸ I) :=
  AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

private lemma quotIdealMapEquivTensorQuotAux_mk (b : B) :
    (quotIdealMapEquivTensorQuotAux B I) b = b ⊗ₜ[A] 1 :=
  rfl

/-- `B ⊗[A] (A ⧸ I)` is isomorphic as an `A`-algebra to `B ⧸ I B`. -/
noncomputable def quotIdealMapEquivTensorQuot :
    (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[B] B ⊗[A] (A ⧸ I) :=
  AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y ↦ by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)

@[simp]
lemma quotIdealMapEquivTensorQuot_mk (b : B) :
    quotIdealMapEquivTensorQuot B I b = b ⊗ₜ[A] 1 :=
  rfl

@[simp]
lemma quotIdealMapEquivTensorQuot_symm_tmul (b : B) (a : A) :
    (quotIdealMapEquivTensorQuot B I).symm (b ⊗ₜ[A] a) = Submodule.Quotient.mk (a • b) :=
  rfl

end Algebra.TensorProduct
