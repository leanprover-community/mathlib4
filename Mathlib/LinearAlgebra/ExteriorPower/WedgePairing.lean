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

@[expose] public section

namespace exteriorPower

open Module Set Set.powersetCard

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The linear equivalence induced by wedging with `vol` in complementary degrees. -/
noncomputable def wedgePairingEquiv
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) := by
  classical
  let b := finBasis K V
  let bk := b.exteriorPower k
  let bl := b.exteriorPower l
  have hkl' : l + k = Fintype.card (Fin (finrank K V)) := by
    simpa [Nat.add_comm] using hkl
  let c : powersetCard (Fin (finrank K V)) k ≃
      powersetCard (Fin (finrank K V)) l := powersetCard.compl hkl'
  have c_val (s : powersetCard (Fin (finrank K V)) k) : (c s).val = s.valᶜ :=
    powersetCard.coe_compl
  have hdisj (s : powersetCard (Fin (finrank K V)) k) :
      Disjoint s.val (c s).val := by
    simpa only [c_val] using (disjoint_compl_right : Disjoint s.val s.valᶜ)
  let topVector : ⋀[K]^(k + l) V :=
    ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
      rw [hkl]
      change b.ExteriorAlgebra
        ((⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V)) :
          Finset (Fin (finrank K V))) ∈ ⋀[K]^(finrank K V) V
      rw [ExteriorAlgebra.basis_eq_coe_basis]
      exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩
  let topCoordinateBasis : Basis Unit K (⋀[K]^(k + l) V) :=
    hkl ▸ FiniteDimensional.basisSingleton Unit
      (by simp) vol hvol
  let topCoordinate := topCoordinateBasis.coord default
  let wedgeMul : ⋀[K]^k V →ₗ[K] ⋀[K]^l V →ₗ[K] ⋀[K]^(k + l) V :=
    DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V)
  let f : ⋀[K]^l V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
    (LinearMap.flip wedgeMul).compr₂ topCoordinate
  let d : K := topCoordinate topVector
  have hd : d ≠ 0 := by
    intro hd
    apply (b.ExteriorAlgebra).ne_zero _
    simpa [topVector] using congrArg Subtype.val
      ((topCoordinateBasis.forall_coord_eq_zero_iff (x := topVector)).mp (fun i ↦ by
        cases i
        exact hd))
  let complementBasis : Basis (powersetCard (Fin (finrank K V)) k) K (⋀[K]^l V) :=
    (bl.reindex c.symm).groupSMul (fun s ↦ (permOfDisjoint (hdisj s)).sign)
  have complementBasis_coe (s : powersetCard (Fin (finrank K V)) k) :
    (complementBasis s : ExteriorAlgebra K V) =
        (permOfDisjoint (hdisj s)).sign • b.ExteriorAlgebra (c s) := by
    simp [complementBasis, bl, exteriorPower.basis_apply,
      ExteriorAlgebra.basis_eq_coe_basis, Basis.groupSMul_apply]
  have hmul (s : powersetCard (Fin (finrank K V)) k) :
      wedgeMul (bk s) (complementBasis s) = topVector := by
    apply Subtype.ext
    change (bk s : ExteriorAlgebra K V) * (complementBasis s : ExteriorAlgebra K V) =
      b.ExteriorAlgebra Finset.univ
    rw [← ExteriorAlgebra.basis_eq_coe_basis b s, complementBasis_coe]
    rw [Units.smul_def, mul_smul_comm,
      ExteriorAlgebra.basis_mul_of_disjoint b s (c s) (hdisj s)]
    rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union]
    rw [c_val, Finset.union_compl]
    rcases Int.units_eq_one_or (permOfDisjoint (hdisj s)).sign with h | h
    · simp [h]
    · simp [h, Units.smul_def]
  have hcomp_eq {s t : powersetCard (Fin (finrank K V)) k}
      (h : Disjoint t.val (c s).val) : t = s := by
    apply Subtype.ext
    have ht : (c s).valᶜ = t.val :=
      Finset.compl_eq_of_disjoint_of_card_add_eq h.symm (by
        simpa [t.prop, (c s).prop, Fintype.card_fin] using hkl')
    simpa [c_val s] using ht.symm
  have hzero (s t : powersetCard (Fin (finrank K V)) k) (h : t ≠ s) :
      wedgeMul (bk t) (complementBasis s) = 0 := by
    have hnotdisj : ¬Disjoint t.val (c s).val := fun h' ↦ h (hcomp_eq h')
    apply Subtype.ext
    change (bk t : ExteriorAlgebra K V) * (complementBasis s : ExteriorAlgebra K V) = 0
    rw [← ExteriorAlgebra.basis_eq_coe_basis b t, complementBasis_coe]
    rw [Units.smul_def, mul_smul_comm,
      ExteriorAlgebra.basis_mul_of_not_disjoint b t (c s) hnotdisj]
    simp
  have fpair (s t : powersetCard (Fin (finrank K V)) k) :
      f (complementBasis s) (bk t) = if t = s then d else 0 := by
    change topCoordinate (wedgeMul (bk t) (complementBasis s)) = _
    by_cases h : t = s
    · subst t
      rw [hmul]
      simp [d]
    · rw [hzero s t h]
      simp [h]
  let targetBasis : Basis (powersetCard (Fin (finrank K V)) k) K (⋀[K]^k V →ₗ[K] K) :=
    bk.dualBasis.unitsSMul (fun _ ↦ Units.mk0 d hd)
  let e : (⋀[K]^l V) ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
    complementBasis.equiv targetBasis (Equiv.refl _)
  have he : e.toLinearMap = f := by
    apply complementBasis.ext
    intro s
    apply bk.ext
    intro t
    simp [e, fpair, targetBasis, Module.Basis.unitsSMul_apply,
      Units.smul_def, Finsupp.single_apply, eq_comm]
  exact LinearEquiv.ofBijective f (by
    rw [← he]
    exact e.bijective)

end exteriorPower
