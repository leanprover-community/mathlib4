/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Hodge star on exterior powers

We construct the Hodge star associated to a nondegenerate bilinear form and a nonzero top-degree
element.
-/

@[expose] public section

namespace exteriorPower

open Function Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The Hodge star associated to `B` and `vol`, in complementary degrees. -/
noncomputable def hodgeStar (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k : ℕ)
    (l : ℕ) (hkl : k + l = finrank K V) :
    ⋀[K]^k V ≃ₗ[K] ⋀[K]^l V := by
  let Bk := B.exteriorPower k
  have hBkbij : Bijective Bk := B.bijective_exteriorPower k (B.toDual hB).bijective
  have hBkflipbij : Bijective Bk.flip := LinearMap.flip_bijective_iff₁.mpr hBkbij
  have hBk : Bk.flip.Nondegenerate := by
    exact ⟨
      LinearMap.separatingLeft_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hBkflipbij.1),
      LinearMap.separatingRight_iff_flip_ker_eq_bot.mpr (by
        change LinearMap.ker Bk = ⊥
        exact LinearMap.ker_eq_bot.mpr hBkbij.1)⟩
  exact (Bk.flip.toDual hBk).trans (wedgePairingEquiv vol hvol k l hkl).symm

end exteriorPower
