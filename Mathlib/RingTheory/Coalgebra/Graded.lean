/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Graded comultiplication

This file defines `SetLike.GradedComul 𝒜`: the comultiplication of `A` carries each `𝒜 n` into
`TensorProduct.grade 𝒜 𝒜 n`, for a family of submodules `𝒜 : ι → Submodule R A`.
-/

public section

open scoped TensorProduct

variable {ι R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [CoalgebraStruct R A] [Add ι]

/-- The comultiplication carries `𝒜 n` into the degree-`n` part of `A ⊗[R] A`. -/
class SetLike.GradedComul (𝒜 : ι → Submodule R A) : Prop where
  /-- Comultiplication is homogeneous -/
  comul_mem : ∀ ⦃n : ι⦄ {x : A}, x ∈ 𝒜 n → Coalgebra.comul x ∈ TensorProduct.grade 𝒜 𝒜 n

variable {𝒜 : ι → Submodule R A} [SetLike.GradedComul 𝒜] {M : Type*} [AddCommMonoid M]
  [Module R M] {n : ι} {x : A}

/-- To show a linear map sends `comul x` into `S` for `x` of degree `n`, it suffices to check it
sends every pure tensor of total degree `n` into `S`. -/
theorem SetLike.map_comul_mem (f : A ⊗[R] A →ₗ[R] M) {S : Submodule R M} (hx : x ∈ 𝒜 n)
    (h : ∀ i j, i + j = n → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, f (a ⊗ₜ[R] b) ∈ S) :
    f (Coalgebra.comul x) ∈ S :=
  (TensorProduct.grade_le (S := S.comap f)).2 h (GradedComul.comul_mem hx)
