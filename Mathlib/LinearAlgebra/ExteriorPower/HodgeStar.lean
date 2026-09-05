/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Hodge star on exterior powers

We construct the Hodge star associated to a bijective bilinear form and a nonzero top-degree
element.
-/

@[expose] public section

namespace exteriorPower

open Function Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The Hodge star associated to `B` and `vol`, in complementary degrees. -/
@[simps!]
noncomputable def hodgeStar (B : LinearMap.BilinForm K V) (hB : Bijective B)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^k V ≃ₗ[K] ⋀[K]^l V := by
  let Bk := B.exteriorPower k
  have hBkbij : Bijective Bk := B.bijective_exteriorPower k hB
  exact (LinearEquiv.ofBijective Bk.flip
      ((LinearMap.flip_bijective_iff₁ (B := Bk)).mpr hBkbij)).trans
    (wedgePairingEquiv vol hvol k l hkl).symm

end exteriorPower
