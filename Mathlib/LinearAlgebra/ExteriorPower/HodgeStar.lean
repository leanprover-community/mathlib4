/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Hodge star on exterior powers

We construct the Hodge star associated to a bijective bilinear form and a bijective linear form
on the top exterior power.
-/

@[expose] public section

namespace exteriorPower

open Function Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The Hodge star associated to `B` and `vol`, in complementary degrees. -/
@[simps!]
noncomputable def hodgeStar (B : LinearMap.BilinForm K V) (hB : Bijective B)
    (vol : Dual K (⋀[K]^(finrank K V) V)) (hvol : Bijective vol) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^k V ≃ₗ[K] ⋀[K]^l V :=
  (LinearEquiv.ofBijective (B.exteriorPower k) (B.bijective_exteriorPower k hB)).flip.trans
    (wedgePairingEquiv vol hvol k l hkl).symm

end exteriorPower
