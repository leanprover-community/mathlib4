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
 * `exteriorPower.mul_exteriorPower_hodgeStar_hodgeStar`: the Hodge star preserves the bilinear
   form on exterior powers up to a scalar, namely the self-pairing of the volume element.

## TODO

* Prove `Δ • hodgeStar B hB vol hlk (hodgeStar B hB vol hkl x) = (-1 : R) ^ (k * l) • x`
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

/-- Up to multiplication by the discriminant, the Hodge star preserves the bilinear form. -/
@[simp] public lemma discr_mul_exteriorPower_hodgeStar_hodgeStar (x y : ⋀[R]^k M) :
    letI star := hodgeStar B hB vol hkl
    B.discr vol * B.exteriorPower l (star x) (star y) = B.exteriorPower k x y := by
  intro Δ
  nontriviality R
  let b := finBasis R M
  let c := b.dualBasis.map (LinearEquiv.ofBijective B hB).symm
  have hdual n := B.exteriorPower_apply_basis_exteriorPower n b c (by simp [c])
  have hΔ : Δ * (vol b.topVector * vol c.topVector) = 1 := by
    calc
      _ = B.exteriorPower _ (vol c.topVector • vol.symm 1) (vol b.topVector • vol.symm 1) := by
        simp [Δ, mul_assoc, mul_comm]
      _ = B.exteriorPower _ c.topVector b.topVector := by simp [← map_smul]
      _ = 1 := by
        let s : Set.powersetCard (Fin (finrank R M)) (finrank R M) := ⟨Finset.univ, by simp⟩
        simp only [← Basis.topVector_eq_exteriorPower _ s, hdual, Basis.dualBasis_apply_self,
          ↓reduceIte]
  rw [exteriorPower_hodgeStar_eq_wedgePairing]
  suffices Δ • (wedgePairing vol hkl).compl₂ (hodgeStar B hB vol hkl).toLinearMap =
      B.exteriorPower k from congr($this x y)
  rw [wedgePairing_eq_apply_topVector_smul vol hkl c]
  refine LinearMap.ext_basis (c.exteriorPower k) (b.exteriorPower k) fun I J ↦ ?_
  simp +contextual [-Basis.coe_dualBasis, -coe_basis, Basis.groupSMul_apply,
    wedgePairing_eq_apply_topVector_smul vol hkl b, ← hdual l, hdual k, Basis.dualBasis_apply_self,
    smul_smul, hΔ]

variable [LinearOrder R] [IsStrictOrderedRing R] [Module.Oriented R M (Fin (finrank R M))]

/-- The Hodge star associated to a bijective bilinear form on an oriented module. -/
abbrev hodgeStarOfOrientation :
    ⋀[R]^k M ≃ₗ[R] ⋀[R]^l M :=
  hodgeStar B hB volOfOrientation hkl

end exteriorPower
