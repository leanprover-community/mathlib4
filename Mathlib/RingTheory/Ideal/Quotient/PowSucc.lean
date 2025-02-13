/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Ideal.Operations

/-!
# The quotient map from `R ⧸ I ^ (n + 1)` to `R ⧸ I ^ n`

In this file we define the canonical quotient linear map from
`M ⧸ I ^ (n + 1) • ⊤` to `M ⧸ I ^ n • ⊤` and canonical quotient ring map from
`R ⧸ I ^ (n + 1)` to `R ⧸ I ^ n`. These definitions will be used in theorems
related to `IsAdicComplete` to find a lift element from compatible sequences in the quotients.

We also include results about the relation between quotients of submodules and quotients of
ideals here. Since `Mathlib.LinearAlgebra.Quotient.Basic` and
`Mathlib.RingTheory.Ideal.Quotient.Defs` do not import each other, and the first file
that imports both of them is `Mathlib.RingTheory.Ideal.Quotient.Operations`
which has already established the first isomophism theorem and Chinese remainder theorem,
we put these pure
technical lemmas that involves both `Submodule.mapQ` and `Ideal.Quotient.factor` in this file.

## Main definitions

- `Submodule.mapQPowSucc`: the linear map from `M ⧸ I ^ (n + 1) • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ (n + 1) • ⊤`.
- `Ideal.Quotient.factorPowSucc`: the ring homomorphism from `R ⧸ I ^ (n + 1)`
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
def mapQPowSucc (n : ℕ) :
    M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  mapQ _ _ LinearMap.id (comap_id (I ^ n • ⊤ : Submodule R M) ▸
      smul_mono_left (pow_le_pow_right n.le_succ))

@[simp]
theorem mapQPowSucc_mk (n : ℕ) (x : M) :
    mapQPowSucc I M n (Quotient.mk x) =
    (Quotient.mk x : M ⧸ I ^ n • ⊤) := by
  simp [mapQPowSucc]

@[simp]
theorem mk_out_eq_mapQPowSucc (n : ℕ) (x : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) :
    Quotient.mk x.out = mapQPowSucc I M n x := by
  nth_rw 2 [← Submodule.Quotient.mk_out x]
  simp only [mapQPowSucc_mk]

end Submodule

namespace Ideal

namespace Quotient

variable [I.IsTwoSided]

variable (I) in
/--
The ring homomorphism from `R ⧸ I ^ (n + 1)`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ (n + 1)`.
-/
def factorPowSucc (n : ℕ) :
    R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n :=
  factor _ _ (pow_le_pow_right n.le_succ)

@[simp]
theorem factorPowSucc_mk (n : ℕ) (x : R) :
    factorPowSucc I n (mk (I ^ (n + 1)) x) = mk (I ^ n) x := by
  simp only [factorPowSucc, factor_mk]

@[simp]
theorem mk_out_eq_mapQPowSucc (n : ℕ) (x : R ⧸ I ^ (n + 1)) :
    mk (I ^ n) x.out = factorPowSucc I n x := by
  nth_rw 2 [← mk_out x]
  simp only [factorPowSucc_mk]

end Quotient

end Ideal
