/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.Valuation.IntegrallyClosed
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Valued fields have integrally closed valuation rings

-/


namespace Valued

variable (K : Type*) [Field K] {Γ₀ : outParam Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [vK : Valued K Γ₀]

instance : IsIntegrallyClosed 𝒪[K] := inferInstance
instance : IsIntegrallyClosed 𝒪[K] := vK.v.isIntegrallyClosed_integers

end Valued
