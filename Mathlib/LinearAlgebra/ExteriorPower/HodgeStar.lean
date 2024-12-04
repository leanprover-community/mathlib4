/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorPower.InducedForm

/-!
Documentation
-/
/-
Hodge star operator or Hodge star is a linear map defined on the exterior algebra of a
finite-dimensional oriented vector space endowed with a nondegenerate symmetric bilinear form.

α = ⋀ α_i , β = ⋀ β_i ∈ ⋀ᵏ V
⟨α , β⟩ = det( ⟨α_i , β_j⟩ )

{e_i} orthonormal basis for V
ω = ⋀ e_i
α ∧ ⋆β = ⟨α , β⟩ ω
-/

open ExteriorAlgebra BigOperators

namespace exteriorPower

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (k : ℕ)
variable (B : LinearMap.BilinForm K M)
variable {I : Type*} [LinearOrder I] (b : Basis I K M)














#check Submodule.span_induction
#check Submodule.closure_induction

theorem bilin_symm_of_symm (h : B.IsSymm) : (exteriorPower.BilinForm k B).IsSymm := by
  intro v w
  rw [RingHom.id_apply]

  sorry

end exteriorPower
