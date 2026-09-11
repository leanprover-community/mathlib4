/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov, Oliver Nash
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
  classical
  have hkl' : k + l = Fintype.card ι := by rw [hkl, finrank_eq_card_basis b]
  let topWedge : ⋀[R]^(k + l) M :=
    b.exteriorPower (k + l) ⟨Finset.univ, by simp [hkl']⟩
  have htopWedge (degree : ℕ) (hdegree : degree = finrank R M) :
      (hdegree ▸ vol : ⋀[R]^degree M →ₗ[R] R) (b.exteriorPower degree
        ⟨Finset.univ, by simp [hdegree, finrank_eq_card_basis b]⟩) = vol b.topVector := by
    subst degree
    rfl
  refine (b.exteriorPower k).ext fun leftSet ↦ (b.exteriorPower l).ext fun rightSet ↦ ?_
  simp only [wedgePairing, LinearMap.compr₂_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, Basis.repr_self, Basis.repr_symm_single_one,
    Basis.groupSMul_apply, Pi.smul_apply', Basis.reindex_apply, Basis.dualBasis_apply_self]
  by_cases hdisjoint : Disjoint leftSet.val rightSet.val
  · have hcompl : leftSet = powersetCard.compl hkl' rightSet :=
      (powersetCard.disjoint_iff_eq_compl hkl').mp hdisjoint
    suffices wedge R M k l (b.exteriorPower k leftSet) (b.exteriorPower l rightSet) =
        powersetCard.sign leftSet • topWedge by
      rw [this]; simpa [hcompl, topWedge] using htopWedge (k + l) hkl
    apply Subtype.ext
    rw [powersetCard.sign_eq_permOfDisjoint_sign hkl' leftSet rightSet hdisjoint]
    simpa [-coe_basis, topWedge, ← ExteriorAlgebra.basis_eq_coe_basis, hcompl,
      Finset.disjUnion_eq_union, Finset.union_comm] using
      ExteriorAlgebra.basis_mul_of_disjoint b leftSet rightSet hdisjoint
  · have hcompl : leftSet ≠ powersetCard.compl hkl' rightSet :=
      (powersetCard.disjoint_iff_eq_compl hkl').not.mp hdisjoint
    suffices wedge R M k l (b.exteriorPower k leftSet) (b.exteriorPower l rightSet) = 0 by
      rw [this]; simp [Equiv.eq_symm_apply, ne_comm, hcompl]
    apply Subtype.ext
    simpa [-coe_basis, ← ExteriorAlgebra.basis_eq_coe_basis] using
      ExteriorAlgebra.basis_mul_of_not_disjoint b leftSet rightSet hdisjoint

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
