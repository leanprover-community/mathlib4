/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.LinearAlgebra.ExteriorPower.Orientation
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Hodge star on exterior powers

This file contains a definition of the Hodge star on exterior powers.

## Main definitions / results:
 * `exteriorPower.hodgeStar`: the Hodge star on exterior powers associated to a choice of bilinear
   form and volume element.
 * `exteriorPower.hodgeStarOfOrientation`: the Hodge star associated to a bilinear form and a
   positive orientation.

## TODO

* Prove
  + `Δ * B.exteriorPower l (hodgeStar B hB vol hkl x) (hodgeStar B hB vol hkl y) =
      B.exteriorPower k x y`
  + `Δ • hodgeStar B hB vol hlk (hodgeStar B hB vol hkl x) = (-1 : R) ^ (k * l) • x`
  where `Δ := B.exteriorPower (finrank R M) (vol.symm 1) (vol.symm 1)`
* Develop further theory in the common case that the determinant identity:
  `B.exteriorPower (finrank R M) (vol.symm 1) (vol.symm 1) = 1`
  holds.

-/

noncomputable section

namespace exteriorPower

open Function Module

variable {R M : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
  (B : LinearMap.BilinForm R M) (hB : Bijective B)
  (vol : ⋀[R]^(finrank R M) M ≃ₗ[R] R)
  {k l : ℕ} (hkl : k + l = finrank R M)

/-- The Hodge star associated to `B` and `vol`. -/
@[expose, simps!]
public def hodgeStar :
    ⋀[R]^k M ≃ₗ[R] ⋀[R]^l M :=
  letI e : ⋀[R]^l M ≃ₗ[R] Dual R (⋀[R]^l M) := .ofBijective _ (B.bijective_exteriorPower l hB)
  (wedgePairing vol hkl).toPerfPair.trans e.symm

lemma exteriorPower_hodgeStar_eq_wedgePairing (x : ⋀[R]^k M) :
    B.exteriorPower l (hodgeStar B hB vol hkl x) = wedgePairing vol hkl x := by
  simp

variable [LinearOrder R] [IsStrictOrderedRing R] [Module.Oriented R M (Fin (finrank R M))]

/-- The Hodge star associated to a bijective bilinear form on an oriented module. -/
abbrev hodgeStarOfOrientation :
    ⋀[R]^k M ≃ₗ[R] ⋀[R]^l M :=
  hodgeStar B hB volOfOrientation hkl

end exteriorPower
