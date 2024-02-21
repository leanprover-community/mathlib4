/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct
/-!

# Tensor Product of polynomial rings

-/


universe u v w

noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (σ : Type u) [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

noncomputable def MvPolynomial.rTensor' :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) :=
  TensorProduct.finsuppLeft'

noncomputable def MvPolynomial.rTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N := by
  exact (MvPolynomial.rTensor' σ (S := R) (N := N) (R := R)).trans
    (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))

end


-- DOES NOT WORK YET
#exit

section MonoidAlgebra

open TensorProduct
variable (α : Type*) [Monoid α] [DecidableEq α]
  (R : Type*) [CommSemiring R]
  (N : Type*) [Semiring N] [Algebra R N]

noncomputable example : Semiring (MonoidAlgebra R α) := inferInstance

noncomputable example : Algebra R (MonoidAlgebra R α) := inferInstance

noncomputable example : Semiring ((MonoidAlgebra R α) ⊗[R] N) := inferInstance

noncomputable example : Algebra R ((MonoidAlgebra R α) ⊗[R] N) := inferInstance

#check Finsupp.rTensor (R := R) (ι := α) (M := R) (N := N)

variable {α R N}

noncomputable def MonoidAlgebra.AlgEquiv
  {N' : Type*} [Semiring N'] [Algebra R N'] (e : N ≃ₐ[R] N') :
    MonoidAlgebra N α ≃ₐ[R] MonoidAlgebra N' α := {
  Finsupp.mapRange.linearEquiv e.toLinearEquiv with
  map_mul' := sorry
  commutes' := sorry  }

noncomputable def MonoidAlgebra.rTensorEquiv :
    (MonoidAlgebra R α) ⊗[R] N ≃ₗ[R] MonoidAlgebra N α :=
  (Finsupp.rTensor (R := R) (ι := α) (M := R) (N := N)).trans
    (MonoidAlgebra.AlgEquiv (α := α) (Algebra.TensorProduct.lid R N)).toLinearEquiv

example (f g : (MonoidAlgebra R α) ⊗[R] N) :
    MonoidAlgebra.rTensorEquiv (N := N) (R := R) (f * g) =
      MonoidAlgebra.rTensorEquiv f * MonoidAlgebra.rTensorEquiv g := by
  induction f using TensorProduct.induction_on with
  | zero => simp only [zero_mul, LinearEquiv.map_zero]
  | tmul f n => sorry
  | add => sorry

noncomputable example : (MonoidAlgebra R α) ⊗[R] N ≃ₐ[R] MonoidAlgebra N α := {
  MonoidAlgebra.rTensorEquiv with
  map_mul' := fun f g ↦ by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply]
    apply MonoidAlgebra.induction_on
    · intro a
      apply MonoidAlgebra.induction_on
      · intro b
        simp only [MonoidAlgebra.of_apply]
        sorry
      · sorry
      · sorry
    · sorry -- add
    · sorry -- hsmul
  commutes' := sorry }
