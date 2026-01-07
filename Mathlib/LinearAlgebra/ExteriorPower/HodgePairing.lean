/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Constructs the Hodge pairing on the exterior product
-/

@[expose] public section

open BigOperators Module

namespace exteriorPower

noncomputable section volume

variable {R M : Type*} {n : ℕ}
  [CommRing R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I] (b : Basis I R M)

/-- The induced element of maximal rank by the basis `b` on `M`. -/
def _root_.Module.Basis.vol : ⋀[R]^(finrank R M) M :=
  ιMulti_family R (finrank R M) (fun i => b i)
  ⟨Finset.univ, by rw [finrank_eq_card_basis b, Finset.card_univ]⟩

def volEquiv : ⋀[R]^(finrank R M) M ≃ₗ[R] R where
  toFun x := (Basis.exteriorPower R (finrank R M) b
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry

lemma volEquiv_vol : volEquiv b b.vol = 1 := by
  rw [volEquiv]
  sorry

end volume

end exteriorPower
