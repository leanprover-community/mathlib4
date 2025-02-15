/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jiedong Jiang
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Operations

/-!
# The quotient map from `R ⧸ I ^ m` to `R ⧸ I ^ n` where `m ≥ n`
In this file we define the canonical quotient linear map from
`M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` and canonical quotient ring map from
`R ⧸ I ^ m` to `R ⧸ I ^ n`. These definitions will be used in theorems
related to `IsAdicComplete` to find a lift element from compatible sequences in the quotients.
We also include results about the relation between quotients of submodules and quotients of
ideals here. Since `Mathlib.LinearAlgebra.Quotient.Basic` and
`Mathlib.RingTheory.Ideal.Quotient.Defs` do not import each other, and the first file
that imports both of them is `Mathlib.RingTheory.Ideal.Quotient.Operations`
which has already established the first isomophism theorem and Chinese remainder theorem,
we put these pure
technical lemmas that involves both `Submodule.mapQ` and `Ideal.Quotient.factor` in this file.
## Main definitions
- `Submodule.mapQPow`: the linear map from `M ⧸ I ^ (n + 1) • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ (n + 1) • ⊤`.
- `Ideal.Quotient.factorPow`: the ring homomorphism from `R ⧸ I ^ (n + 1)`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ (n + 1)`.
## Main results
-/

open Submodule Ideal Quotient

variable {R : Type*} [Ring R] {I J : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]

namespace Submodule

section

variable [I.IsTwoSided] [J.IsTwoSided] (h : I ≤ J)

@[simp]
theorem mapQ_eq_factor (x : R ⧸ I) :
    mapQ I J LinearMap.id h x = factor I J h x := rfl

end

variable (I M) in
/--
The linear map from `M ⧸ I ^ (n + 1) • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ (n + 1) • ⊤`.
-/
def mapQPow {m n : ℕ} (le : n ≤ m):
    M ⧸ (I ^ m • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  mapQ _ _ LinearMap.id (comap_id (I ^ n • ⊤ : Submodule R M) ▸
      smul_mono_left (pow_le_pow_right le))

@[simp]
theorem mapQPow_mk {m n : ℕ} (le : n ≤ m) (x : M) :
    mapQPow I M le (Quotient.mk x) = (Quotient.mk x : M ⧸ I ^ n • ⊤) := by
  simp [mapQPow]

@[simp]
theorem mk_out_eq_mapQPowSucc {m n : ℕ} (le : n ≤ m) (x : M ⧸ (I ^ m • ⊤ : Submodule R M)) :
    Quotient.mk x.out = mapQPow I M le x := by
  nth_rw 2 [← Quotient.out_eq x]
  rfl

lemma mapQPow_surjective {m n : ℕ} (le : n ≤ m): Function.Surjective (mapQPow I M le) := by
  intro x
  use Quotient.mk x.out
  rw [mapQPow, Submodule.mapQ_apply, LinearMap.id_coe, id_eq]
  exact Quotient.out_eq x

end Submodule

namespace Ideal

namespace Quotient

variable [I.IsTwoSided]

variable (I) in
/--
The ring homomorphism from `R ⧸ I ^ m`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ (n + 1)`.
-/
def factorPow {m n : ℕ} (le : n ≤ m) : R ⧸ I ^ m →+* R ⧸ I ^ n :=
  factor _ _ (pow_le_pow_right le)

@[simp]
theorem factorPow_mk {m n : ℕ} (le : n ≤ m) (x : R) :
    factorPow I le (mk (I ^ m) x) = mk (I ^ n) x := by
  simp only [factorPow, factor_mk]

@[simp]
theorem mk_out_eq_mapQPow {m n : ℕ} (le : n ≤ m) (x : R ⧸ I ^ m) :
    mk (I ^ n) x.out = factorPow I le x := by
  nth_rw 2 [← Quotient.out_eq x]
  rfl

lemma factorPow_surjective {m n : ℕ} (le : n ≤ m): Function.Surjective (factorPow I le) :=
  factor_surjective (I ^ m) (I ^ n) (pow_le_pow_right le)

end Quotient

end Ideal
