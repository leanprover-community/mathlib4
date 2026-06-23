/-
Copyright (c) 2026 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# The Yang–Baxter equation

This file defines the Yang–Baxter equation for an `R`-linear endomorphism
`B : M ⊗[R] M →ₗ[R] M ⊗[R] M`.

Writing `B₁` for `B` acting on the first two tensor factors of `M ⊗[R] M ⊗[R] M` and `B₂` for `B`
acting on the last two factors, the Yang-Baxter equation is `B₁ ∘ B₂ ∘ B₁ = B₂ ∘ B₁ ∘ B₂`.

A module `M` equipped with such a `B` satisfying this equation is called
a *braided vector space*. (Braided vector spaces are the basic input to constructions such as
quantum shuffle algebras and Nichols algebras.)

## Main definitions

* `LinearMap.rTensorMid B` / `LinearMap.lTensorMid B`: `B` acting on the first two, resp. last two,
  tensor factors of `M ⊗[R] M ⊗[R] M`.
* `LinearMap.YangBaxterEquation B`: the proposition that `B` satisfies the Yang–Baxter equation.
* `BraidedVectorSpace R M`: an `R`-module `M` together with a chosen solution of the Yang–Baxter
  equation on `M ⊗[R] M`, called its braiding.

## Main results

* `LinearMap.yangBaxterEquation_comm`: the symmetry `TensorProduct.comm`, the trivial braiding,
  satisfies the Yang–Baxter equation.
* `BraidedVectorSpace.trivial`: the braided vector space structure on `M` given by the symmetry
  `TensorProduct.comm`.

## Tags

Yang-Baxter, braided vector space, braiding, R-matrix
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (B : M ⊗[R] M →ₗ[R] M ⊗[R] M)

/-- `B` acting on the first two tensor factors of `M ⊗[R] M ⊗[R] M`. -/
def rTensorMid : M ⊗[R] M ⊗[R] M →ₗ[R] M ⊗[R] M ⊗[R] M := B.rTensor M

/-- `B` acting on the last two tensor factors of `M ⊗[R] M ⊗[R] M`. -/
def lTensorMid : M ⊗[R] M ⊗[R] M →ₗ[R] M ⊗[R] M ⊗[R] M :=
  (TensorProduct.assoc R M M M).symm.toLinearMap ∘ₗ B.lTensor M ∘ₗ
    (TensorProduct.assoc R M M M).toLinearMap

@[simp]
theorem rTensorMid_tmul (a b c : M) : B.rTensorMid (a ⊗ₜ[R] b ⊗ₜ[R] c) = B (a ⊗ₜ[R] b) ⊗ₜ[R] c :=
  rTensor_tmul ..

@[simp]
theorem lTensorMid_tmul (a b c : M) :
    B.lTensorMid (a ⊗ₜ[R] b ⊗ₜ[R] c) =
      (TensorProduct.assoc R M M M).symm (a ⊗ₜ[R] B (b ⊗ₜ[R] c)) := by
  simp [lTensorMid]

/-- The Yang–Baxter equation for an `R`-linear endomorphism `B` of `M ⊗[R] M`.
Denoting `B₁` and `B₂` for `B` acting on the first two, resp. last two, tensor factors of
`M ⊗[R] M ⊗[R] M`, the Yang–Baxter equation states `B₁ ∘ B₂ ∘ B₁ = B₂ ∘ B₁ ∘ B₂`. -/
def YangBaxterEquation : Prop :=
  B.rTensorMid ∘ₗ B.lTensorMid ∘ₗ B.rTensorMid = B.lTensorMid ∘ₗ B.rTensorMid ∘ₗ B.lTensorMid

theorem yangBaxterEquation_iff :
    B.YangBaxterEquation ↔
      ∀ a b c : M,
        B.rTensorMid (B.lTensorMid (B.rTensorMid (a ⊗ₜ[R] b ⊗ₜ[R] c))) =
          B.lTensorMid (B.rTensorMid (B.lTensorMid (a ⊗ₜ[R] b ⊗ₜ[R] c))) := by
  refine ⟨fun h a b c => by
      simpa only [comp_apply] using LinearMap.congr_fun h (a ⊗ₜ[R] b ⊗ₜ[R] c), fun h => ?_⟩
  refine TensorProduct.ext_threefold fun a b c => ?_
  simpa using h a b c

/-- `TensorProduct.comm`, i.e. the trivial braiding on `M`, satisfies the Yang–Baxter
equation. -/
theorem yangBaxterEquation_comm :
    YangBaxterEquation (TensorProduct.comm R M M).toLinearMap := by
  rw [yangBaxterEquation_iff]
  intro a b c
  simp

end LinearMap

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A braided vector space over `R` is an `R`-module `M` equipped with a chosen `R`-linear
endomorphism of `M ⊗[R] M`, its braiding, satisfying the Yang–Baxter equation. -/
structure BraidedVectorSpace where
  /-- The braiding of the braided vector space. -/
  braiding : M ⊗[R] M →ₗ[R] M ⊗[R] M
  /-- The braiding satisfies the Yang–Baxter equation. -/
  yangBaxterEquation : braiding.YangBaxterEquation

namespace BraidedVectorSpace

variable {R M}

/-- The trivial braided vector space structure on `M`, whose braiding is just
`TensorProduct.comm`. -/
def trivial : BraidedVectorSpace R M where
  braiding := (TensorProduct.comm R M M).toLinearMap
  yangBaxterEquation := LinearMap.yangBaxterEquation_comm

@[simp]
theorem trivial_braiding_tmul (a b : M) :
    (trivial : BraidedVectorSpace R M).braiding (a ⊗ₜ[R] b) = b ⊗ₜ[R] a :=
  rfl

end BraidedVectorSpace
