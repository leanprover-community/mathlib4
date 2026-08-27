/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

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
    (s : powersetCard (Fin (finrank K V)) l) :
    Disjoint (complementEquiv k l hkl s).val s.val := by
  simpa [complementEquiv] using (disjoint_compl_right : Disjoint s.val s.valᶜ).symm

/-! ### The top-degree basis vector -/

def basisUniv (b : Basis (Fin (finrank K V)) K V) {k l : ℕ}
    (hkl : k + l = finrank K V) : ⋀[K]^(k + l) V :=
  ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
    rw [hkl, ExteriorAlgebra.basis_eq_coe_basis b
      (⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V))]
    exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩

/-! ### The wedge pairing -/

lemma basis_mul_of_complement (b : Basis (Fin (finrank K V)) K V) (k l : ℕ)
    (hkl : k + l = finrank K V) (s : powersetCard (Fin (finrank K V)) l)
    (t : powersetCard (Fin (finrank K V)) k) :
    DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V) (b.exteriorPower k t)
        (b.exteriorPower l s) =
      if t = complementEquiv k l hkl s then
        (permOfDisjoint (complementEquiv_disjoint k l hkl s)).sign •
          basisUniv b hkl
      else 0 := by
  apply Subtype.ext
  change (b.exteriorPower k t : ExteriorAlgebra K V) *
      (b.exteriorPower l s : ExteriorAlgebra K V) = _
  rw [← ExteriorAlgebra.basis_eq_coe_basis b t, ← ExteriorAlgebra.basis_eq_coe_basis b s]
  split_ifs with ht
  · subst t
    rw [ExteriorAlgebra.basis_mul_of_disjoint b _ s
      (complementEquiv_disjoint k l hkl s)]
    simp [basisUniv, complementEquiv, Finset.union_comm]
  · have hdisj : ¬Disjoint t.val s.val := by
      intro h
      apply ht
      simpa [powersetCard.eq_iff_subset, complementEquiv] using
        Finset.subset_compl_iff_disjoint_right.mpr h
    rw [ExteriorAlgebra.basis_mul_of_not_disjoint b t s hdisj]
    simp

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
  (LinearMap.flip (DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V))).compr₂
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
      (((hkl ▸ volumeBasis vol hvol).forall_coord_eq_zero_iff).mp fun i ↦ by
        simpa [volumeCoordinate] using hzero)
  let pairingBasis := ((bk.dualBasis.reindex (complementEquiv k l hkl).symm).isUnitSMul
      (fun _ ↦ isUnit_iff_ne_zero.mpr hcoord)).groupSMul
    (fun s ↦ (permOfDisjoint
      (complementEquiv_disjoint k l hkl s)).sign)
  let basisEquiv := bl.equiv pairingBasis (Equiv.refl _)
  have basisEquiv_eq : basisEquiv.toLinearMap = wedgePairing vol hvol hkl := by
    apply bl.ext
    intro s
    change basisEquiv (bl s) = wedgePairing vol hvol hkl (bl s)
    rw [Basis.equiv_apply]
    apply bk.ext
    intro t
    change _ = volumeCoordinate vol hvol hkl
      (DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V) (b.exteriorPower k t)
        (b.exteriorPower l s))
    rw [basis_mul_of_complement b k l hkl s t]
    by_cases h : t = complementEquiv k l hkl s <;>
      simp [h, pairingBasis, Module.Basis.isUnitSMul_apply, Basis.reindex_apply,
        Basis.groupSMul_apply, Equiv.symm_symm, smul_eq_mul]
  exact LinearEquiv.ofBijective (wedgePairing vol hvol hkl) (by
    rw [← basisEquiv_eq]
    exact basisEquiv.bijective)

end exteriorPower
