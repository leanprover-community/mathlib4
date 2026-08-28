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

open Module Set Set.powersetCard

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable section private_defs

namespace exteriorPower

/-! ### Complementary basis indices -/

def complementEquiv (k l : ℕ) (hkl : k + l = finrank K V) :
    powersetCard (Fin (finrank K V)) l ≃ powersetCard (Fin (finrank K V)) k :=
  powersetCard.compl (by simpa using hkl)

lemma complementEquiv_disjoint (k l : ℕ) (hkl : k + l = finrank K V)
    (sourceIndex : powersetCard (Fin (finrank K V)) l) :
    Disjoint (complementEquiv k l hkl sourceIndex).val sourceIndex.val := by
  simpa [complementEquiv] using
    (disjoint_compl_right : Disjoint sourceIndex.val sourceIndex.valᶜ).symm

/-! ### The top-degree basis vector -/

def basisUniv (b : Basis (Fin (finrank K V)) K V) {k l : ℕ}
    (hkl : k + l = finrank K V) : ⋀[K]^(k + l) V :=
  ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
    rw [hkl, ExteriorAlgebra.basis_eq_coe_basis b
      (⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V))]
    exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩

/-! ### The wedge pairing -/

lemma basis_mul_of_complement (b : Basis (Fin (finrank K V)) K V) (k l : ℕ)
    (hkl : k + l = finrank K V)
    (sourceIndex : powersetCard (Fin (finrank K V)) l)
    (targetIndex : powersetCard (Fin (finrank K V)) k)
    (target_is_complement : targetIndex = complementEquiv k l hkl sourceIndex) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex) =
      (permOfDisjoint (complementEquiv_disjoint k l hkl sourceIndex)).sign • basisUniv b hkl := by
  subst targetIndex
  apply Subtype.ext
  change (b.exteriorPower k (complementEquiv k l hkl sourceIndex) : ExteriorAlgebra K V) *
      (b.exteriorPower l sourceIndex : ExteriorAlgebra K V) = _
  rw [← ExteriorAlgebra.basis_eq_coe_basis b (complementEquiv k l hkl sourceIndex),
    ← ExteriorAlgebra.basis_eq_coe_basis b sourceIndex]
  simpa [basisUniv, complementEquiv, Finset.union_comm] using
    ExteriorAlgebra.basis_mul_of_disjoint b (complementEquiv k l hkl sourceIndex) sourceIndex
      (by simpa [complementEquiv] using
        complementEquiv_disjoint k l hkl sourceIndex)

lemma basis_mul_of_not_complement (b : Basis (Fin (finrank K V)) K V) (k l : ℕ)
    (hkl : k + l = finrank K V)
    (sourceIndex : powersetCard (Fin (finrank K V)) l)
    (targetIndex : powersetCard (Fin (finrank K V)) k)
    (target_not_complement : targetIndex ≠ complementEquiv k l hkl sourceIndex) :
    DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex) = 0 := by
  have hdisjoint : ¬Disjoint targetIndex.val sourceIndex.val := by
    intro disjoint
    apply target_not_complement
    simpa [powersetCard.eq_iff_subset, complementEquiv] using
      Finset.subset_compl_iff_disjoint_right.mpr disjoint
  apply Subtype.ext
  change (b.exteriorPower k targetIndex : ExteriorAlgebra K V) *
      (b.exteriorPower l sourceIndex : ExteriorAlgebra K V) = _
  rw [← ExteriorAlgebra.basis_eq_coe_basis b targetIndex,
    ← ExteriorAlgebra.basis_eq_coe_basis b sourceIndex]
  simpa using ExteriorAlgebra.basis_mul_of_not_disjoint b targetIndex sourceIndex hdisjoint

section FiniteDimensional

variable [FiniteDimensional K V]

/-! ### The top-degree coordinate -/

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

end FiniteDimensional

end exteriorPower

end private_defs

namespace exteriorPower

variable [FiniteDimensional K V]

/-- The linear equivalence induced by wedging with `vol` in complementary degrees. -/
public noncomputable def wedgePairingEquiv
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) := by
  classical
  let b := finBasis K V
  let bk := b.exteriorPower k
  let bl := b.exteriorPower l
  have hcoord : volumeCoordinate vol hvol hkl (basisUniv b hkl) ≠ 0 := by
    intro hzero
    apply (b.ExteriorAlgebra).ne_zero (Finset.univ : Finset (Fin (finrank K V)))
    exact congrArg Subtype.val
      (((hkl ▸ volumeBasis vol hvol).forall_coord_eq_zero_iff).mp fun coordinateIndex ↦ by
        simpa [volumeCoordinate] using hzero)
  let pairingBasis := ((bk.dualBasis.reindex (complementEquiv k l hkl).symm).isUnitSMul
      (fun _ ↦ isUnit_iff_ne_zero.mpr hcoord)).groupSMul
    (fun sourceIndex ↦ (permOfDisjoint
      (complementEquiv_disjoint k l hkl sourceIndex)).sign)
  let basisEquiv := bl.equiv pairingBasis (Equiv.refl _)
  have basisEquiv_eq : basisEquiv.toLinearMap = wedgePairing vol hvol hkl := by
    refine LinearMap.ext_basis bl bk fun sourceIndex targetIndex ↦ ?_
    change basisEquiv (bl sourceIndex) (bk targetIndex) = volumeCoordinate vol hvol hkl
      (DirectSum.gMulLHom K (fun degree ↦ ⋀[K]^degree V) (b.exteriorPower k targetIndex)
        (b.exteriorPower l sourceIndex))
    rw [Basis.equiv_apply]
    by_cases target_eq_complement : targetIndex = complementEquiv k l hkl sourceIndex
    · rw [basis_mul_of_complement b k l hkl sourceIndex targetIndex target_eq_complement]
      simp [target_eq_complement, pairingBasis, Module.Basis.isUnitSMul_apply,
        Basis.reindex_apply, Basis.groupSMul_apply]
    · rw [basis_mul_of_not_complement b k l hkl sourceIndex targetIndex target_eq_complement]
      simp [target_eq_complement, pairingBasis, Module.Basis.isUnitSMul_apply,
        Basis.reindex_apply, Basis.groupSMul_apply]
  exact LinearEquiv.ofBijective (wedgePairing vol hvol hkl) (by
    rw [← basisEquiv_eq]
    exact basisEquiv.bijective)

end exteriorPower
