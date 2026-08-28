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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable section private_defs

namespace exteriorPower

def complementEquiv (k l : ℕ) (hkl : k + l = finrank K V) :
    powersetCard (Fin (finrank K V)) l ≃ powersetCard (Fin (finrank K V)) k :=
  powersetCard.compl (by simpa using hkl)

section Basis

variable (b : Basis (Fin (finrank K V)) K V)
variable (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
variable {k l : ℕ} (hkl : k + l = finrank K V)
variable (sourceIndex : powersetCard (Fin (finrank K V)) l)
  (targetIndex : powersetCard (Fin (finrank K V)) k)

lemma disjoint_compl :
    Disjoint (complementEquiv k l hkl sourceIndex).val sourceIndex.val := by
  simpa only [complementEquiv, coe_compl] using
    (disjoint_compl_right : Disjoint sourceIndex.val sourceIndex.valᶜ).symm

lemma disjoint_iff_eq_compl :
    Disjoint targetIndex.val sourceIndex.val ↔
      targetIndex = complementEquiv k l hkl sourceIndex := by
  simpa only [complementEquiv, powersetCard.eq_iff_subset, coe_compl] using
    (Finset.subset_compl_iff_disjoint_right :
      targetIndex.val ⊆ sourceIndex.valᶜ ↔
        Disjoint targetIndex.val sourceIndex.val).symm

def topVector : ⋀[K]^(k + l) V :=
  ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
    rw [hkl, ExteriorAlgebra.basis_eq_coe_basis b
      (⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V))]
    exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩

lemma basis_mul_of_complement (hdisjoint : Disjoint targetIndex.val sourceIndex.val) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex) =
      (permOfDisjoint hdisjoint).sign • topVector b hkl := by
  obtain rfl := (disjoint_iff_eq_compl hkl sourceIndex targetIndex).mp hdisjoint
  apply Subtype.ext
  simpa only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    ← ExteriorAlgebra.basis_eq_coe_basis, topVector, complementEquiv, coe_compl,
    SetLike.mk_smul_of_tower_mk, coe_disjUnion, Finset.disjUnion_eq_union,
    Finset.union_comm, Finset.union_compl] using
    ExteriorAlgebra.basis_mul_of_disjoint b _ sourceIndex
      (disjoint_compl hkl sourceIndex)

lemma basis_mul_of_not_disjoint
    (hdisjoint : ¬Disjoint targetIndex.val sourceIndex.val) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex) = 0 := by
  apply Subtype.ext
  simpa only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    ← ExteriorAlgebra.basis_eq_coe_basis, Submodule.coe_zero] using
    ExteriorAlgebra.basis_mul_of_not_disjoint b targetIndex sourceIndex hdisjoint

section FiniteDimensional

variable [FiniteDimensional K V]

def volumeBasis :
    Basis Unit K (⋀[K]^(finrank K V) V) :=
  FiniteDimensional.basisSingleton Unit (by simp) vol hvol

def volumeCoordinate : ⋀[K]^(k + l) V →ₗ[K] K :=
  (hkl ▸ volumeBasis vol hvol).coord default

def wedgePairing :
    ⋀[K]^l V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  (LinearMap.flip (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V))).compr₂
    (volumeCoordinate vol hvol hkl)

lemma volumeCoordinate_topVector_ne_zero :
    volumeCoordinate vol hvol hkl (topVector b hkl) ≠ 0 := by
  intro hzero
  apply (b.ExteriorAlgebra).ne_zero (Finset.univ : Finset (Fin (finrank K V)))
  change (topVector b hkl : ExteriorAlgebra K V) = 0
  rw [Submodule.coe_eq_zero]
  exact ((hkl ▸ volumeBasis vol hvol).forall_coord_eq_zero_iff).mp fun _ ↦ by
    simpa [volumeCoordinate] using hzero

def wedgePairingBasis :
    Basis (powersetCard (Fin (finrank K V)) l) K (⋀[K]^k V →ₗ[K] K) :=
  (((b.exteriorPower k).dualBasis.reindex (complementEquiv k l hkl).symm).isUnitSMul
      (fun _ ↦ isUnit_iff_ne_zero.mpr
        (volumeCoordinate_topVector_ne_zero b vol hvol hkl))).groupSMul
    (fun sourceIndex ↦ (permOfDisjoint (disjoint_compl hkl sourceIndex)).sign)

lemma wedgePairingBasis_apply :
    wedgePairingBasis b vol hvol hkl sourceIndex (b.exteriorPower k targetIndex) =
      wedgePairing vol hvol hkl (b.exteriorPower l sourceIndex)
        (b.exteriorPower k targetIndex) := by
  change wedgePairingBasis b vol hvol hkl sourceIndex (b.exteriorPower k targetIndex) =
    volumeCoordinate vol hvol hkl
      (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V)
        (b.exteriorPower k targetIndex) (b.exteriorPower l sourceIndex))
  have hdisjoint_iff := disjoint_iff_eq_compl hkl sourceIndex targetIndex
  by_cases htarget : targetIndex = complementEquiv k l hkl sourceIndex
  · rw [basis_mul_of_complement b hkl sourceIndex targetIndex (hdisjoint_iff.mpr htarget)]
    simp [wedgePairingBasis, htarget, Module.Basis.isUnitSMul_apply, Basis.reindex_apply,
      Basis.groupSMul_apply]
  · rw [basis_mul_of_not_disjoint b sourceIndex targetIndex (hdisjoint_iff.not.mpr htarget)]
    simp [wedgePairingBasis, htarget, Module.Basis.isUnitSMul_apply, Basis.reindex_apply,
      Basis.groupSMul_apply]

lemma bijective_wedgePairing :
    Bijective (wedgePairing vol hvol hkl) := by
  let b := finBasis K V
  let basisEquiv := (b.exteriorPower l).equiv (wedgePairingBasis b vol hvol hkl) (Equiv.refl _)
  have basisEquiv_eq : basisEquiv.toLinearMap = wedgePairing vol hvol hkl := by
    refine LinearMap.ext_basis (b.exteriorPower l) (b.exteriorPower k)
      fun sourceIndex targetIndex ↦ ?_
    change basisEquiv (b.exteriorPower l sourceIndex) (b.exteriorPower k targetIndex) =
      wedgePairing vol hvol hkl (b.exteriorPower l sourceIndex)
        (b.exteriorPower k targetIndex)
    simpa only [basisEquiv, Basis.equiv_apply, Equiv.refl_apply] using
      wedgePairingBasis_apply b vol hvol hkl sourceIndex targetIndex
  rw [← basisEquiv_eq]
  exact basisEquiv.bijective

end FiniteDimensional
end Basis
end exteriorPower
end private_defs

namespace exteriorPower

variable [FiniteDimensional K V]
variable (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
variable (k l : ℕ) (hkl : k + l = finrank K V)

/-- The linear equivalence induced by wedging with `vol` in complementary degrees. -/
public noncomputable def wedgePairingEquiv :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  LinearEquiv.ofBijective (wedgePairing vol hvol hkl)
    (bijective_wedgePairing vol hvol hkl)

end exteriorPower
