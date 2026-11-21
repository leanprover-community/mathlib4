/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

import Mathlib.LinearAlgebra.ExteriorPower.Orientation

/-!
# Hodge star on exterior powers

This file contains a definition of the Hodge star on exterior powers.

## Main definitions / results:
 * `exteriorPower.hodgeStar`: the Hodge star on exterior powers associated to a choice of bilinear
   form and volume element.
 * `exteriorPower.hodgeStarOfOrientation`: the Hodge star associated to a bilinear form and a
   positive orientation.
 * `exteriorPower.discr_mul_exteriorPower_hodgeStar_hodgeStar`: the Hodge star preserves the
   bilinear form on exterior powers up to multiplication by `B.discr vol`.

## TODO

* For symmetric `B`, prove
  `B.discr vol • hodgeStar B hB vol hlk (hodgeStar B hB vol hkl x) = (-1 : R) ^ (k * l) • x`.
* Develop further theory in the common case `B.discr vol = 1`.
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

/-- Up to multiplication by the discriminant, the Hodge star preserves the bilinear form. -/
@[simp↓] public lemma discr_mul_exteriorPower_hodgeStar_hodgeStar (x y : ⋀[R]^k M) :
    letI star := hodgeStar B hB vol hkl
    B.discr vol * B.exteriorPower l (star x) (star y) = B.exteriorPower k x y := by
  nontriviality R
  rw [exteriorPower_hodgeStar_eq_wedgePairing]
  suffices B.discr vol • (wedgePairing vol hkl).compl₂ (hodgeStar B hB vol hkl).toLinearMap =
      B.exteriorPower k from LinearMap.congr_fun₂ this x y
  let b := finBasis R M
  let c := b.dualBasis.map (LinearEquiv.ofBijective B hB).symm
  have hdual n := B.exteriorPower_apply_basis_exteriorPower n b c (by simp [c])
  have hvol : B.discr vol * (vol b.topVector * vol c.topVector) = 1 := by
    rw [mul_comm (vol b.topVector), B.discr_mul_vol_mul_vol]
    simp only [← Basis.topVector_eq_exteriorPower _ ⟨Finset.univ, Finset.card_fin _⟩, hdual,
      Basis.dualBasis_apply_self, ↓reduceIte]
  rw [wedgePairing_eq_apply_topVector_smul vol hkl c]
  refine LinearMap.ext_basis (c.exteriorPower k) (b.exteriorPower k) fun I J ↦ ?_
  simp +contextual [-Basis.coe_dualBasis, -coe_basis, Basis.groupSMul_apply,
    wedgePairing_eq_apply_topVector_smul vol hkl b, ← hdual l, hdual k, Basis.dualBasis_apply_self,
    smul_smul, hvol]

variable [LinearOrder R] [IsStrictOrderedRing R] [Module.Oriented R M (Fin (finrank R M))]

/-- The Hodge star associated to a bijective bilinear form on an oriented module. -/
abbrev hodgeStarOfOrientation :
    ⋀[R]^k M ≃ₗ[R] ⋀[R]^l M :=
  hodgeStar B hB volOfOrientation hkl

end exteriorPower
