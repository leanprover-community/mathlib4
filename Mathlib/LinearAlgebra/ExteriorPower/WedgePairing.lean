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

lemma complementEquiv_disjoint (k l : ℕ) (hkl : k + l = finrank K V)
    (sourceIndex : powersetCard (Fin (finrank K V)) l) :
    Disjoint (complementEquiv k l hkl sourceIndex).val sourceIndex.val := by
  simpa [complementEquiv] using
    (disjoint_compl_right : Disjoint sourceIndex.val sourceIndex.valᶜ).symm

def basisUniv (b : Basis (Fin (finrank K V)) K V) {k l : ℕ}
    (hkl : k + l = finrank K V) : ⋀[K]^(k + l) V :=
  ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
    rw [hkl, ExteriorAlgebra.basis_eq_coe_basis b
      (⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V))]
    exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩

lemma basis_mul_of_disjoint (b : Basis (Fin (finrank K V)) K V) {k l : ℕ}
    (hkl : k + l = finrank K V)
    (sourceIndex : powersetCard (Fin (finrank K V)) l)
    (targetIndex : powersetCard (Fin (finrank K V)) k)
    (hdisjoint : Disjoint targetIndex.val sourceIndex.val) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex) =
      (permOfDisjoint hdisjoint).sign • basisUniv b hkl := by
  apply Subtype.ext
  change (b.exteriorPower k targetIndex : ExteriorAlgebra K V) *
      (b.exteriorPower l sourceIndex : ExteriorAlgebra K V) = _
  rw [← ExteriorAlgebra.basis_eq_coe_basis b targetIndex,
    ← ExteriorAlgebra.basis_eq_coe_basis b sourceIndex]
  have source_eq_compl : sourceIndex.val = targetIndex.valᶜ :=
    (Finset.compl_eq_of_disjoint_of_card_add_eq hdisjoint (by
      simpa [targetIndex.prop, sourceIndex.prop] using hkl)).symm
  simpa [basisUniv, Finset.disjUnion_eq_union, source_eq_compl] using
    ExteriorAlgebra.basis_mul_of_disjoint b targetIndex sourceIndex hdisjoint

lemma basis_mul_of_not_disjoint (b : Basis (Fin (finrank K V)) K V) {k l : ℕ}
    (sourceIndex : powersetCard (Fin (finrank K V)) l)
    (targetIndex : powersetCard (Fin (finrank K V)) k)
    (hdisjoint : ¬Disjoint targetIndex.val sourceIndex.val) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex) = 0 := by
  apply Subtype.ext
  change (b.exteriorPower k targetIndex : ExteriorAlgebra K V) *
      (b.exteriorPower l sourceIndex : ExteriorAlgebra K V) = _
  simpa only [← ExteriorAlgebra.basis_eq_coe_basis, Submodule.coe_zero] using
    ExteriorAlgebra.basis_mul_of_not_disjoint b targetIndex sourceIndex hdisjoint

section FiniteDimensional

variable [FiniteDimensional K V]

def volumeBasis (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) :
    Basis Unit K (⋀[K]^(finrank K V) V) :=
  FiniteDimensional.basisSingleton Unit (by simp) vol hvol

def volumeCoordinate (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
    {k l : ℕ} (hkl : k + l = finrank K V) : ⋀[K]^(k + l) V →ₗ[K] K :=
  (hkl ▸ volumeBasis vol hvol).coord default

def wedgePairing (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
  {k l : ℕ} (hkl : k + l = finrank K V) :
    ⋀[K]^l V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  (LinearMap.flip (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V))).compr₂
    (volumeCoordinate vol hvol hkl)

lemma volumeCoordinate_basisUniv_ne_zero (b : Basis (Fin (finrank K V)) K V)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) {k l : ℕ}
    (hkl : k + l = finrank K V) :
    volumeCoordinate vol hvol hkl (basisUniv b hkl) ≠ 0 := by
  intro hzero
  apply (b.ExteriorAlgebra).ne_zero (Finset.univ : Finset (Fin (finrank K V)))
  exact congrArg Subtype.val
    (((hkl ▸ volumeBasis vol hvol).forall_coord_eq_zero_iff).mp fun coordinateIndex ↦ by
      simpa [volumeCoordinate] using hzero)

def wedgePairingBasis (b : Basis (Fin (finrank K V)) K V)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    Basis (powersetCard (Fin (finrank K V)) l) K (⋀[K]^k V →ₗ[K] K) :=
  (((b.exteriorPower k).dualBasis.reindex (complementEquiv k l hkl).symm).isUnitSMul
      (fun _ ↦ isUnit_iff_ne_zero.mpr
        (volumeCoordinate_basisUniv_ne_zero b vol hvol hkl))).groupSMul
    (fun sourceIndex ↦ (permOfDisjoint
      (complementEquiv_disjoint k l hkl sourceIndex)).sign)

def wedgePairingEquivOfBasis (b : Basis (Fin (finrank K V)) K V)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  (b.exteriorPower l).equiv (wedgePairingBasis b vol hvol k l hkl) (Equiv.refl _)

lemma wedgePairingEquivOfBasis_toLinearMap (b : Basis (Fin (finrank K V)) K V)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    (wedgePairingEquivOfBasis b vol hvol k l hkl).toLinearMap = wedgePairing vol hvol hkl := by
  refine LinearMap.ext_basis (b.exteriorPower l) (b.exteriorPower k)
    fun sourceIndex targetIndex ↦ ?_
  change wedgePairingEquivOfBasis b vol hvol k l hkl
      (b.exteriorPower l sourceIndex) (b.exteriorPower k targetIndex) =
    volumeCoordinate vol hvol hkl
      (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex))
  rw [wedgePairingEquivOfBasis, Basis.equiv_apply]
  by_cases target_eq_complement : targetIndex = complementEquiv k l hkl sourceIndex
  · have hdisjoint : Disjoint targetIndex.val sourceIndex.val := by
      simpa [target_eq_complement] using complementEquiv_disjoint k l hkl sourceIndex
    rw [basis_mul_of_disjoint b hkl sourceIndex targetIndex hdisjoint]
    simp [target_eq_complement, wedgePairingBasis, Module.Basis.isUnitSMul_apply,
      Basis.reindex_apply, Basis.groupSMul_apply]
  · have hdisjoint : ¬Disjoint targetIndex.val sourceIndex.val := by
      intro disjoint
      apply target_eq_complement
      simpa [powersetCard.eq_iff_subset, complementEquiv] using
        Finset.subset_compl_iff_disjoint_right.mpr disjoint
    rw [basis_mul_of_not_disjoint b sourceIndex targetIndex hdisjoint]
    simp [target_eq_complement, wedgePairingBasis, Module.Basis.isUnitSMul_apply,
      Basis.reindex_apply, Basis.groupSMul_apply]

lemma bijective_wedgePairing (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    Bijective (wedgePairing vol hvol hkl) := by
  rw [← wedgePairingEquivOfBasis_toLinearMap (finBasis K V) vol hvol k l hkl]
  exact (wedgePairingEquivOfBasis (finBasis K V) vol hvol k l hkl).bijective

end FiniteDimensional

end exteriorPower

end private_defs

namespace exteriorPower

variable [FiniteDimensional K V]

/-- The linear equivalence induced by wedging with `vol` in complementary degrees. -/
public noncomputable def wedgePairingEquiv
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  LinearEquiv.ofBijective (wedgePairing vol hvol hkl)
    (bijective_wedgePairing vol hvol k l hkl)

end exteriorPower
