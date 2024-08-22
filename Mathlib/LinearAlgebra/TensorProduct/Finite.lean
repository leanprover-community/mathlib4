/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!

# Tensor products with finite free modules

This file contains variants of results in `Mathlib.LinearAlgebra.DirectSum.Finsupp`
where `m →₀ R` is replaced by `m → R` under the hypothesis `[Finite m]`.

-/

namespace TensorProduct

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] {ι : Type*} [DecidableEq ι] [Finite ι]

noncomputable def finiteLeft : (ι → M) ⊗[R] N ≃ₗ[R] ι → M ⊗[R] N :=
  (LinearEquiv.rTensor N (Finsupp.linearEquivFunOnFinite R M ι).symm :
    (ι → M) ⊗[R] N ≃ₗ[R] ((ι →₀ M) ⊗[R] N)) ≪≫ₗ
  (TensorProduct.finsuppLeft R M N ι :
    (ι →₀ M) ⊗[R] N ≃ₗ[R] ι →₀ (M ⊗[R] N)) ≪≫ₗ
  (Finsupp.linearEquivFunOnFinite R (M ⊗[R] N) ι :
    (ι →₀ M ⊗[R] N) ≃ₗ[R] ι → M ⊗[R] N)

noncomputable def isom'' {R : Type*} [CommRing R] {m n : Type*} [Finite m] [DecidableEq m] :
    (m → R) ⊗[R] (n → R) ≃ₗ[R] (m × n → R) :=
  (LinearEquiv.rTensor (n → R) (Finsupp.linearEquivFunOnFinite R R m).symm :
    (m → R) ⊗[R] (n → R) ≃ₗ[R] ((m →₀ R) ⊗[R] (n → R))) ≪≫ₗ
  (TensorProduct.finsuppScalarLeft R (n → R) m :
    (m →₀ R) ⊗[R] (n → R) ≃ₗ[R] (m →₀ (n → R))) ≪≫ₗ
  ((Finsupp.linearEquivFunOnFinite R (n → R) m :
    (m →₀ (n → R)) ≃ₗ[R] m → n → R)) ≪≫ₗ
  ((LinearEquiv.curry R m n).symm :
    (m → n → R) ≃ₗ[R] (m × n → R))
