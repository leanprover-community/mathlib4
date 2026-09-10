/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Wedge pairing on exterior powers

Given a trivialisation of the top exterior power, the wedge pairing in complementary degrees
is a scalar-valued bilinear map. We construct this here and prove that it is a perfect pairing.

## Main definitions / results:
 * `exteriorPower.wedge`: the bilinear map `∧^k × ∧^l → ∧^(k + l)`
 * `exteriorPower.wedgePairing`: the bilinear map `∧^k × ∧^l → R` when `k + l` = top degree
 * `exteriorPower.instIsPerfPairWedgePairing`: the proof that `exteriorPower.wedgePairing` is
   perfect.

-/

public noncomputable section

open Function Module Set

namespace exteriorPower

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (k l : ℕ)

/-- The wedge product as an operation on exterior powers. -/
abbrev wedge :
    ⋀[R]^k M →ₗ[R] ⋀[R]^l M →ₗ[R] ⋀[R]^(k + l) M :=
  DirectSum.gMulLHom R <| fun d ↦ ⋀[R]^d M

variable {R M k l} (vol : ⋀[R]^(finrank R M) M ≃ₗ[R] R) (hkl : k + l = finrank R M)

/-- The wedge product in complementary degrees as a scalar-valued bilinear map (for a choice of
trivialisation of the top exterior power). -/
abbrev wedgePairing :
    ⋀[R]^k M →ₗ[R] ⋀[R]^l M →ₗ[R] R :=
  (wedge R M k l).compr₂ (hkl ▸ vol)

section Basis

variable [Nontrivial R] {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Basis ι R M)

/-- The wedge product of all the elements of the basis `b`, in increasing order. -/
def _root_.Module.Basis.topVector : ⋀[R]^(finrank R M) M :=
  b.exteriorPower (finrank R M) ⟨Finset.univ, by simp [finrank_eq_card_basis b]⟩

lemma isUnit_apply_topVector : IsUnit (vol b.topVector) := by
  have : Unique (powersetCard ι (finrank R M)) :=
    { default := ⟨Finset.univ, by simp [finrank_eq_card_basis b]⟩
      uniq s := Subtype.ext <| Finset.eq_univ_of_card _ <| by simp [finrank_eq_card_basis b] }
  obtain ⟨x, hx⟩ := vol.surjective 1
  suffices ((b.exteriorPower (finrank R M)).repr x default) * vol b.topVector = 1 from
    IsUnit.of_mul_eq_one_right _ this
  suffices (b.exteriorPower (finrank R M)).repr x default • b.topVector = x by
    rw [← smul_eq_mul, ← map_smul, ← hx, this]
  have : b.exteriorPower (finrank R M) default = b.topVector := by
    congr; exact Subsingleton.elim _ _
  simpa only [Fintype.sum_unique, this] using (b.exteriorPower <| finrank R M).sum_repr x

lemma wedgePairing_eq_apply_topVector_smul :
    haveI hkl' : k + l = Fintype.card ι := by rw [hkl, Module.finrank_eq_card_basis b]
    letI bk : Basis (powersetCard ι k) R (⋀[R]^k M) := b.exteriorPower k
    letI bl : Basis (powersetCard ι k) R (Dual R (⋀[R]^l M)) :=
      (b.exteriorPower l).dualBasis.reindex (powersetCard.compl hkl') |>.groupSMul powersetCard.sign
    wedgePairing vol hkl = vol b.topVector • (bk.repr.trans bl.repr.symm) := by
  sorry

end Basis

instance instIsPerfPairWedgePairing [Module.Finite R M] [Module.Free R M] :
    (wedgePairing vol hkl).IsPerfPair := by
  nontriviality R
  suffices Bijective (wedgePairing vol hkl) from
    LinearMap.IsPerfPair.of_bijective (wedgePairing vol hkl) this
  let ι := Module.Free.ChooseBasisIndex R M
  let b : Basis ι R M := Module.Free.chooseBasis R M
  have : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  rw [wedgePairing_eq_apply_topVector_smul vol hkl b]
  let e : Dual R (⋀[R]^l M) ≃ₗ[R] Dual R (⋀[R]^l M) :=
    .smulOfUnit (isUnit_apply_topVector vol b).unit
  exact (LinearEquiv.trans _ e).bijective

end exteriorPower
