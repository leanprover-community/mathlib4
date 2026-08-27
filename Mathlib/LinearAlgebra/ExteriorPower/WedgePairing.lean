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
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k : ℕ)
    (l : ℕ) (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) := by
  classical
  let b := finBasis K V
  let bk := b.exteriorPower k
  let bl := b.exteriorPower l
  let c : powersetCard (Fin (finrank K V)) k ≃
      powersetCard (Fin (finrank K V)) l :=
    powersetCard.compl (by simpa [Nat.add_comm] using hkl)
  have c_val (s : powersetCard (Fin (finrank K V)) k) : (c s).val = s.valᶜ :=
    powersetCard.coe_compl
  have hdisj (s : powersetCard (Fin (finrank K V)) k) :
      Disjoint s.val (c s).val := by
    simpa only [c_val] using (disjoint_compl_right : Disjoint s.val s.valᶜ)
  let topVector : ⋀[K]^(k + l) V :=
    ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
      rw [hkl, ExteriorAlgebra.basis_eq_coe_basis b
        (⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V))]
      exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩
  let topCoordinateBasis : Basis Unit K (⋀[K]^(k + l) V) :=
    hkl ▸ FiniteDimensional.basisSingleton Unit (by simp) vol hvol
  let topCoordinate := topCoordinateBasis.coord default
  let f := (LinearMap.flip (DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V))).compr₂ topCoordinate
  let d := topCoordinate topVector
  have hd : d ≠ 0 := fun hd ↦
    (b.ExteriorAlgebra).ne_zero (Finset.univ : Finset (Fin (finrank K V))) <| by
      simpa [topVector] using congrArg Subtype.val
        ((topCoordinateBasis.forall_coord_eq_zero_iff (x := topVector)).mp
          (fun i ↦ (show i = default from Subsingleton.elim _ _) ▸ hd))
  let complementBasis : Basis (powersetCard (Fin (finrank K V)) k) K
      (⋀[K]^l V) :=
    (bl.reindex c.symm).groupSMul (fun s ↦ (permOfDisjoint (hdisj s)).sign⁻¹)
  have complementBasis_coe (s : powersetCard (Fin (finrank K V)) k) :
    (complementBasis s : ExteriorAlgebra K V) =
        (permOfDisjoint (hdisj s)).sign⁻¹ • b.ExteriorAlgebra (c s) := by
    simp [complementBasis, bl,
      ExteriorAlgebra.basis_eq_coe_basis, Basis.groupSMul_apply]
  have hcomp_eq {s t : powersetCard (Fin (finrank K V)) k}
      (h : Disjoint t.val (c s).val) : t = s := by
    apply Subtype.ext
    apply compl_injective
    simpa [c_val s] using Finset.compl_eq_of_disjoint_of_card_add_eq h (by
      simpa [t.prop, (c s).prop, Fintype.card_fin] using hkl)
  have hpair (s t : powersetCard (Fin (finrank K V)) k) :
      DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V) (bk t) (complementBasis s) =
        if t = s then topVector else 0 := by
    split_ifs with h
    · subst t
      apply Subtype.ext
      change (bk s : ExteriorAlgebra K V) * (complementBasis s : ExteriorAlgebra K V) =
        b.ExteriorAlgebra Finset.univ
      rw [← ExteriorAlgebra.basis_eq_coe_basis b s, complementBasis_coe, mul_smul_comm,
        ExteriorAlgebra.basis_mul_of_disjoint b s (c s) (hdisj s)]
      simp [c_val, smul_smul]
    · have hnotdisj : ¬Disjoint t.val (c s).val := mt hcomp_eq h
      apply Subtype.ext
      change (bk t : ExteriorAlgebra K V) * (complementBasis s : ExteriorAlgebra K V) = 0
      rw [← ExteriorAlgebra.basis_eq_coe_basis b t, complementBasis_coe, mul_smul_comm,
        ExteriorAlgebra.basis_mul_of_not_disjoint b t (c s) hnotdisj]
      simp
  let targetBasis := bk.dualBasis.unitsSMul (fun _ ↦ Units.mk0 d hd)
  have hmap : f ∘ complementBasis = targetBasis := by
    funext s
    apply bk.ext
    intro t
    by_cases h : t = s <;>
      simp [f, hpair, h, d, targetBasis, Module.Basis.unitsSMul_apply, Units.smul_def]
  exact LinearEquiv.ofBijective f
    (LinearMap.bijective_of_linearIndependent_of_span_eq_top complementBasis.span_eq
      (hmap.symm ▸ targetBasis.linearIndependent)
      (hmap.symm ▸ targetBasis.span_eq))

end exteriorPower
