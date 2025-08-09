/-
Copyright (c) 2025 Jason Reed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Reed
-/
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Restriction of linear isometries (and equivalences) to `Submodule`s.

## Main declarations

* `LinearIsometry.submoduleMap`: A linear isometry restricted to a submodule
* `LinearIsometryEquiv.submoduleMap`: A linear isometry equivalence restricted to a submodule

## Tags

submodule, subspace, linear map, isometry, equivalence
-/

variable {R : Type*} {R₁ : Type*} {R₂ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*}

namespace LinearIsometry

variable [Ring R] [SeminormedAddCommGroup M] [SeminormedAddCommGroup M₁]
variable [Module R M] [Module R M₁]

/-- A linear isometry between two modules restricts to a linear isometry from any submodule p of the
domain onto the image of that submodule.

This is a version of `LinearMap.submoduleMap` extended to linear isometries -/
@[simps!]
def submoduleMap (p : Submodule R M) (e : M →ₗᵢ[R] M₁) :
    p →ₗᵢ[R] (Submodule.map e p) :=
  { e.toLinearMap.submoduleMap p with norm_map' x := e.norm_map' x }

end LinearIsometry

namespace LinearIsometryEquiv

variable [Ring R] [Ring R₂] [SeminormedAddCommGroup M] [SeminormedAddCommGroup M₂]
variable [Module R M] [Module R₂ M₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}

/-- A linear isometry equivalence between two modules restricts to a linear isometry equivalence
from any submodule p of the domain onto the image of that submodule.

This is a version of `LinearEquiv.submoduleMap` extended to linear isometry equivalences -/
@[simps!]
def submoduleMap (p : Submodule R M) (e : M ≃ₛₗᵢ[σ₁₂] M₂) :
    p ≃ₛₗᵢ[σ₁₂] (Submodule.map e p) :=
  { e.toLinearEquiv.submoduleMap p with norm_map' x := e.norm_map' x }

end LinearIsometryEquiv
