/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Wedge pairing on exterior powers
-/

open Function Module Set Set.powersetCard

variable {K V : Type*}

noncomputable section private_defs

namespace exteriorPower

section Basis

variable [CommRing K] [AddCommGroup V] [Module K V]
variable {ι : Type} [Fintype ι] [LinearOrder ι] (b : Basis ι K V)
variable {k l : ℕ} (hkl : k + l = Fintype.card ι)
variable (I : powersetCard ι l) (J : powersetCard ι k)

lemma disjoint_compl :
    Disjoint (powersetCard.compl (by simpa using hkl) I).val I.val := by
  simpa only [coe_compl] using
    (disjoint_compl_right : Disjoint I.val I.valᶜ).symm

lemma disjoint_iff_eq_compl :
    Disjoint J.val I.val ↔ J = powersetCard.compl (by simpa using hkl) I := by
  simpa only [powersetCard.eq_iff_subset, coe_compl] using
    (Finset.subset_compl_iff_disjoint_right :
      J.val ⊆ I.valᶜ ↔ Disjoint J.val I.val).symm

def topVector : ⋀[K]^(k + l) V :=
  b.exteriorPower (k + l) ⟨Finset.univ, by simpa using hkl.symm⟩

lemma basis_mul_of_complement (hdisjoint : Disjoint J.val I.val) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k J)
        (b.exteriorPower l I) =
      (permOfDisjoint hdisjoint).sign • topVector b hkl := by
  obtain rfl := (disjoint_iff_eq_compl hkl I J).mp hdisjoint
  apply Subtype.ext
  simpa only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    topVector, Submodule.coe_smul_of_tower, ← ExteriorAlgebra.basis_eq_coe_basis, coe_compl,
    coe_disjUnion, Finset.disjUnion_eq_union, Finset.union_comm, Finset.union_compl] using
    ExteriorAlgebra.basis_mul_of_disjoint b _ I (disjoint_compl hkl I)

omit [Fintype ι] in
lemma basis_mul_of_not_disjoint (hdisjoint : ¬Disjoint J.val I.val) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k J)
        (b.exteriorPower l I) = 0 := by
  apply Subtype.ext
  simpa only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    ← ExteriorAlgebra.basis_eq_coe_basis, Submodule.coe_zero] using
    ExteriorAlgebra.basis_mul_of_not_disjoint b J I hdisjoint

end Basis

section FiniteDimensional

variable [Field K] [AddCommGroup V] [Module K V]
variable {k l : ℕ} (vol : Dual K (⋀[K]^(k + l) V)) (hvol : Bijective vol)
variable (hkl : k + l = finrank K V)

def wedgePairing :
    ⋀[K]^l V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  (LinearMap.flip (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V))).compr₂ vol

def wedgePairingBasis (b : Basis (Fin (finrank K V)) K V) :
    Basis (powersetCard (Fin (finrank K V)) l) K (⋀[K]^k V →ₗ[K] K) :=
  (((b.exteriorPower k).dualBasis.reindex
      (powersetCard.compl (by simpa using hkl)).symm).isUnitSMul
    (fun _ ↦ isUnit_iff_ne_zero.mpr (show vol (topVector b (by simpa using hkl)) ≠ 0 by
      rw [ne_eq, vol.map_eq_zero_iff hvol.injective]
      exact (b.exteriorPower _).ne_zero _))).groupSMul (fun I ↦
      (permOfDisjoint (disjoint_compl (k := k) (l := l)
        (hkl := by simpa using hkl) I)).sign)

lemma wedgePairingBasis_apply (b : Basis (Fin (finrank K V)) K V)
    (I : powersetCard (Fin (finrank K V)) l)
    (J : powersetCard (Fin (finrank K V)) k) :
    wedgePairingBasis vol hvol hkl b I (b.exteriorPower k J) =
      wedgePairing vol (b.exteriorPower l I) (b.exteriorPower k J) := by
  change wedgePairingBasis vol hvol hkl b I (b.exteriorPower k J) =
    vol (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V)
      (b.exteriorPower k J) (b.exteriorPower l I))
  have hdisjoint_iff :=
    disjoint_iff_eq_compl (k := k) (l := l) (hkl := by simpa using hkl) I J
  by_cases htarget : J = powersetCard.compl (by simpa using hkl) I
  · rw [basis_mul_of_complement b (k := k) (l := l)
      (hkl := by simpa using hkl) I J
      (hdisjoint_iff.mpr htarget)]
    simp [wedgePairingBasis, htarget, Module.Basis.isUnitSMul_apply,
      Basis.reindex_apply, Basis.groupSMul_apply]
  · rw [basis_mul_of_not_disjoint b I J (hdisjoint_iff.not.mpr htarget)]
    simp [wedgePairingBasis, htarget, Module.Basis.isUnitSMul_apply,
      Basis.reindex_apply, Basis.groupSMul_apply]

include hvol hkl in
lemma bijective_wedgePairing [FiniteDimensional K V] : Bijective (wedgePairing vol) := by
  let basis := finBasis K V
  let basisEquiv :=
    (basis.exteriorPower l).equiv
      (wedgePairingBasis vol hvol hkl basis) (Equiv.refl _)
  suffices basisEquiv.toLinearMap = wedgePairing vol by
    rw [← this]
    exact basisEquiv.bijective
  apply LinearMap.ext_basis (basis.exteriorPower l) (basis.exteriorPower k)
  intro I J
  simpa only [basisEquiv, LinearEquiv.coe_toLinearMap, Basis.equiv_apply, Equiv.refl_apply] using
    wedgePairingBasis_apply vol hvol hkl basis I J

end FiniteDimensional
end exteriorPower
end private_defs

namespace exteriorPower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (vol : Dual K (⋀[K]^(finrank K V) V)) (hvol : Bijective vol)
variable (k l : ℕ) (hkl : k + l = finrank K V)

/-- The linear equivalence obtained by applying `vol` to wedge products in complementary degrees. -/
public noncomputable def wedgePairingEquiv :
    ⋀[K]^l V ≃ₗ[K] Dual K (⋀[K]^k V) :=
  let e := LinearEquiv.cast (R := K) (M := fun n : ℕ ↦ ⋀[K]^n V) hkl
  LinearEquiv.ofBijective (wedgePairing (vol.comp e.toLinearMap))
    (bijective_wedgePairing _ (hvol.comp e.bijective) hkl)

@[simp]
public lemma wedgePairingEquiv_apply (x : ⋀[K]^l V) (y : ⋀[K]^k V) :
    wedgePairingEquiv vol hvol k l hkl x y =
      vol (LinearEquiv.cast (R := K) (M := fun n : ℕ ↦ ⋀[K]^n V) hkl
        (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) y x)) := by
  simp [wedgePairingEquiv, wedgePairing]

end exteriorPower
