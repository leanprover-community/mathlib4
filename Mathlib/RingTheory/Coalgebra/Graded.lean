/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# Graded coalgebras

This file defines the typeclass `GradedCoalgebra 𝒜`, for working with a coalgebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → Submodule R A`.

## Main definitions

* `SetLike.GradedComul 𝒜`: `comul` carries `𝒜 n` into `TensorProduct.grade 𝒜 𝒜 n`.
* `SetLike.GradedCounit 𝒜`: `counit` vanishes on homogeneous elements of nonzero degree.
* `GradedCoalgebra 𝒜`: an internally graded coalgebra.
-/

public section

open scoped TensorProduct

variable {ι R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]

section RespectsGrading

variable [CoalgebraStruct R A] (𝒜 : ι → Submodule R A)

/-- The comultiplication carries `𝒜 n` into the degree-`n` part of `A ⊗[R] A`. -/
class SetLike.GradedComul [Add ι] : Prop where
  /-- Comultiplication is homogeneous -/
  comul_mem : ∀ ⦃n : ι⦄ {x : A}, x ∈ 𝒜 n → Coalgebra.comul x ∈ TensorProduct.grade 𝒜 𝒜 n

/-- The counit is concentrated in degree zero. -/
class SetLike.GradedCounit [Zero ι] : Prop where
  /-- The counit vanishes on homogeneous elements of nonzero degree -/
  counit_eq_zero : ∀ ⦃n : ι⦄ {x : A}, x ∈ 𝒜 n → n ≠ 0 → Coalgebra.counit (R := R) x = 0

variable {𝒜}

/-- To show a linear map sends `comul x` into `S` for `x` of degree `n`, it suffices to check it
sends every pure tensor of total degree `n` into `S`. -/
theorem SetLike.map_comul_mem [Add ι] [SetLike.GradedComul 𝒜] {M : Type*} [AddCommMonoid M]
    [Module R M] (f : A ⊗[R] A →ₗ[R] M) {S : Submodule R M} {n : ι}
    (h : ∀ i j, i + j = n → ∀ a ∈ 𝒜 i, ∀ b ∈ 𝒜 j, f (a ⊗ₜ[R] b) ∈ S) {x : A} (hx : x ∈ 𝒜 n) :
    f (Coalgebra.comul x) ∈ S :=
  Submodule.mem_comap.1 <| TensorProduct.grade_le.2 h (GradedComul.comul_mem hx)

/-- To show two linear maps agree on `comul x` for `x` of degree `n`, it suffices to check they
agree on pure tensors of total degree `n`. -/
theorem SetLike.map_comul_congr [Add ι] [SetLike.GradedComul 𝒜] {M : Type*} [AddCommMonoid M]
    [Module R M] {f g : A ⊗[R] A →ₗ[R] M} {n : ι} {x : A} (hx : x ∈ 𝒜 n)
    (h : ∀ p q, p + q = n → ∀ a ∈ 𝒜 p, ∀ b ∈ 𝒜 q, f (a ⊗ₜ[R] b) = g (a ⊗ₜ[R] b)) :
    f (Coalgebra.comul x) = g (Coalgebra.comul x) :=
  SetLike.map_comul_mem LinearMap.id (S := LinearMap.eqLocus f g)
    (fun p q hpq a ha b hb ↦ LinearMap.mem_eqLocus.mpr (h p q hpq a ha b hb)) hx

end RespectsGrading

/-- An internally graded coalgebra is a decomposition of `A` whose comultiplication and counit
respect the grading. -/
class GradedCoalgebra [DecidableEq ι] [AddMonoid ι] [Coalgebra R A] (𝒜 : ι → Submodule R A) extends
  SetLike.GradedComul 𝒜, SetLike.GradedCounit 𝒜, DirectSum.Decomposition 𝒜
