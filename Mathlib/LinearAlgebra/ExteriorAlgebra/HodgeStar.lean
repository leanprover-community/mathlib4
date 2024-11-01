/-
Copyright (c) 2024 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/

import Mathlib.LinearAlgebra.ExteriorAlgebra.InducedForm

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

/-
TODO:
✓  Split into separate files
✓  Rewrite as separate bases on left and right entries
3. Prove independence of bases
4. Show definition on simple tensors
5. Use dual basis for nondegenerate forms
6. Construct dual basis on exterior power
-/

open ExteriorAlgebra BigOperators

namespace exteriorPower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {I : Type*} [LinearOrder I] [Fintype I]
variable (B : LinearMap.BilinForm K V) (b : Basis I K V)
variable {k : ℕ}

local notation "⟪" x ", " y "⟫" => @inducedForm _ _ _ _ _ _ _ _ k B b x y

section nondegenerate

#check B.dualBasis

theorem induced_dualBasis (hB : B.Nondegenerate) (s t : {a : Finset I // a.card = k}) :
  ⟪(B.dualBasis hB b).exteriorPower s, b.exteriorPower t⟫ = if s=t then 1 else 0 := by
  unfold inducedForm

  sorry

theorem induced_nondegenerate (hB : B.Nondegenerate) :
  ∀ (v : ⋀[K]^k V), (∀ (w : ⋀[K]^k V), ⟪v, w⟫ = 0) → v = 0 := by
  intro v h'
  rw [← @Basis.forall_coord_eq_zero_iff _ K (⋀[K]^k V) _ _ _ (b.exteriorPower)]
  intro s
  sorry

theorem inducedBilin_nondegenerate (hB : B.Nondegenerate) :
  (@inducedBilinForm _ _ _ _ _ _ _ _ k B b).Nondegenerate := induced_nondegenerate B b hB

end nondegenerate

section hodgeStar



end hodgeStar

end exteriorPower
