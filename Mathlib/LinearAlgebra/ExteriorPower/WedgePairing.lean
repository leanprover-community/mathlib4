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

/-- An auxiliary lemma for `exteriorPower.wedgePairing_eq_apply_topVector_smul`. -/
private lemma apply_eqRec {N : Type*} [AddCommGroup N] [Module R N]
    (h : k = l) (f : ⋀[R]^l M →ₗ[R] N)
    {x : ⋀[R]^k M} {y : ⋀[R]^l M} (hxy : (x : ExteriorAlgebra R M) = y) :
    (h ▸ f) x = f y := by
  subst h
  exact congrArg f (Subtype.ext hxy)

section Basis

variable {ι : Type*} [LinearOrder ι] (b : Basis ι R M)

lemma wedge_apply_of_not_disjoint
    {I : powersetCard ι k} {J : powersetCard ι l} (h : ¬ Disjoint I.val J.val) :
    wedge R M k l (b.exteriorPower k I) (b.exteriorPower l J) = 0 := by
  ext
  simp_rw [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ← ExteriorAlgebra.basis_eq_coe_basis,
    ZeroMemClass.coe_zero, ExteriorAlgebra.basis_mul_of_not_disjoint b I J h]

variable [Fintype ι]

lemma wedge_apply_of_disjoint (hkl : k + l = Fintype.card ι)
    {I : powersetCard ι k} {J : powersetCard ι l} (h : Disjoint I.val J.val) :
    wedge R M k l (b.exteriorPower k I) (b.exteriorPower l J) =
      powersetCard.sign I • b.ExteriorAlgebra (I.val ∪ J.val) := by
  simp_rw [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ← ExteriorAlgebra.basis_eq_coe_basis,
    ExteriorAlgebra.basis_mul_of_disjoint b I J h, powersetCard.coe_disjUnion,
      Finset.disjUnion_eq_union, powersetCard.sign_eq_permOfDisjoint_sign hkl I J h]

variable [Nontrivial R]

/-- The wedge product of all the elements of the basis `b`, in increasing order. -/
def _root_.Module.Basis.topVector : ⋀[R]^(finrank R M) M :=
  b.exteriorPower (finrank R M) ⟨Finset.univ, by simp [finrank_eq_card_basis b]⟩

@[simp]
lemma _root_.Module.Basis.coe_topVector :
    (b.topVector : ExteriorAlgebra R M) = b.ExteriorAlgebra .univ :=
  (ExteriorAlgebra.basis_eq_coe_basis b ⟨Finset.univ, by simp [finrank_eq_card_basis b]⟩).symm

@[simp]
lemma _root_.Module.Basis.topVector_eq_exteriorPower (s : powersetCard ι (finrank R M)) :
    b.exteriorPower (finrank R M) s = b.topVector := by
  have : (s : Finset ι) = .univ := Finset.eq_univ_of_card _ <| by simp [finrank_eq_card_basis b]
  simp_rw [Module.Basis.topVector, ← this]

lemma isUnit_apply_topVector : IsUnit (vol b.topVector) := by
  have : Unique (powersetCard ι (finrank R M)) :=
    { default := ⟨Finset.univ, by simp [finrank_eq_card_basis b]⟩
      uniq s := Subtype.ext <| Finset.eq_univ_of_card _ <| by simp [finrank_eq_card_basis b] }
  obtain ⟨x, hx⟩ := vol.surjective 1
  suffices ((b.exteriorPower (finrank R M)).repr x default) * vol b.topVector = 1 from
    IsUnit.of_mul_eq_one_right _ this
  suffices (b.exteriorPower (finrank R M)).repr x default • b.topVector = x by
    rw [← smul_eq_mul, ← map_smul, ← hx, this]
  simpa using (b.exteriorPower _).sum_repr x

lemma wedgePairing_eq_apply_topVector_smul :
    haveI hkl' : k + l = Fintype.card ι := by rw [hkl, finrank_eq_card_basis b]
    letI bk : Basis (powersetCard ι k) R (⋀[R]^k M) := b.exteriorPower k
    letI bl : Basis (powersetCard ι k) R (Dual R (⋀[R]^l M)) :=
      (b.exteriorPower l).dualBasis.reindex (powersetCard.compl hkl') |>.groupSMul powersetCard.sign
    wedgePairing vol hkl = vol b.topVector • (bk.repr.trans bl.repr.symm) := by
  have hkl' : k + l = Fintype.card ι := by rw [hkl, finrank_eq_card_basis b]
  suffices ∀ (I : powersetCard ι k) (J : powersetCard ι l),
      (wedgePairing vol hkl) (b.exteriorPower k I) (b.exteriorPower l J) =
        powersetCard.sign I • vol b.topVector • if Disjoint I.val J.val then 1 else 0 by
    refine (b.exteriorPower k).ext fun I ↦ (b.exteriorPower l).ext fun J ↦ ?_
    simp [-Basis.coe_dualBasis, -coe_basis, Basis.groupSMul_apply, Basis.dualBasis_apply_self,
      Equiv.eq_symm_apply, eq_comm (b := I), powersetCard.disjoint_iff_eq_compl hkl', this I J]
  intro I J
  by_cases hdisjoint : Disjoint I.val J.val
  · have hIJ : (I : Finset ι) ∪ (J : Finset ι) = Finset.univ :=
      Finset.eq_univ_of_card _ <| by simp [hdisjoint, hkl']
    have : (wedge R M k l (b.exteriorPower k I) (b.exteriorPower l J) : ExteriorAlgebra R M) =
        (powersetCard.sign I • b.topVector : ⋀[R]^(finrank R M) M) := by
      rw [wedge_apply_of_disjoint b hkl' hdisjoint, hIJ, SetLike.val_smul_of_tower, b.coe_topVector]
    simp_rw [wedgePairing, LinearMap.compr₂_apply, apply_eqRec hkl _ this, map_zsmul_unit,
      LinearEquiv.coe_coe, hdisjoint, reduceIte, smul_eq_mul, mul_one]
  · rw [wedgePairing, LinearMap.compr₂_apply, wedge_apply_of_not_disjoint b hdisjoint, map_zero]
    simp [hdisjoint]

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
