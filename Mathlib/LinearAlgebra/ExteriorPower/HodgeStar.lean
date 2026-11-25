/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.BilinForm

import Mathlib.LinearAlgebra.ExteriorPower.Orientation

/-!
# Hodge star on exterior powers

This file contains a definition of the Hodge star on exterior powers.

## Main definitions and statements

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

open Function Module Set

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

/-- If `bᵢ` and `cᵢ` are two bases for `M`, in duality wrt `B`, and `I` is a subset of the type
indexing the bases, then:
  `★ ∧_{i ∈ I} bᵢ = ± D ∧_{j ∈ Iᶜ} cⱼ`
where `★` is the Hodge star and `D` is the volume of the basis `b`.

In the case that `b` is orthonormal wrt `B` we have `c = b`, `D = ±1` and the lemma takes a familiar
form. -/
public lemma hodgeStar_basis_exteriorPower [Nontrivial R] {ι : Type*} [LinearOrder ι] [Fintype ι]
    (b c : Basis ι R M) (hc : ∀ i, B (c i) = b.dualBasis i)
    (I : powersetCard ι k) (J : powersetCard ι l) (hIJ : (J : Finset ι)ᶜ = I) :
    hodgeStar B hB vol hkl (b.exteriorPower k I) =
      powersetCard.sign I • vol b.topVector • c.exteriorPower l J := by
  apply (B.bijective_exteriorPower l hB).injective
  refine (b.exteriorPower l).ext fun J' ↦ ?_
  have : Disjoint I.val J'.val ↔ J' = J := by
    rw [← hIJ, disjoint_compl_left_iff, powersetCard.eq_iff_subset]
  rw [exteriorPower_hodgeStar_eq_wedgePairing, wedgePairing_basis_exteriorPower]
  simp [-coe_basis, B.exteriorPower_apply_basis_exteriorPower l b c hc, Finsupp.single_apply, this,
    eq_comm]

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
  have hc i : B (c i) = b.dualBasis i := by simp [c]
  have hkl' : l + k = Fintype.card (Fin (finrank R M)) := by simp [hkl, add_comm]
  refine LinearMap.ext_basis (c.exteriorPower k) (b.exteriorPower k) fun I J ↦ ?_
  have : Disjoint I.val J.valᶜ ↔ J = I := by
    rw [disjoint_compl_right_iff, ← powersetCard.eq_iff_subset, eq_comm]
  simp only [LinearMap.smul_apply, LinearMap.compl₂_apply, LinearEquiv.coe_toLinearMap]
  rw [hodgeStar_basis_exteriorPower B hB vol hkl b c hc J (powersetCard.compl hkl' J) (by simp),
    map_zsmul_unit, map_smul, wedgePairing_basis_exteriorPower]
  simp only [B.exteriorPower_apply_basis_exteriorPower k b c hc, Basis.dualBasis_apply_self,
    powersetCard.coe_compl, this]
  split_ifs with hIJ
  · subst hIJ
    simp [← mul_smul_comm, smul_smul, B.discr_mul_vol_topVector_mul_vol_topVector vol b c hc]
  · simp

variable [LinearOrder R] [IsStrictOrderedRing R] [Module.Oriented R M (Fin (finrank R M))]

/-- The Hodge star associated to a bijective bilinear form on an oriented module. -/
abbrev hodgeStarOfOrientation :
    ⋀[R]^k M ≃ₗ[R] ⋀[R]^l M :=
  hodgeStar B hB volOfOrientation hkl

end exteriorPower
