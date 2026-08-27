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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable section private_defs

namespace exteriorPower

/-! ### The top-degree coordinate -/

def volumeBasis (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) :
    Basis Unit K (⋀[K]^(finrank K V) V) :=
  FiniteDimensional.basisSingleton Unit (by simp) vol hvol

def volumeCoordinate (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
    (k l : ℕ) (hkl : k + l = finrank K V) : ⋀[K]^(k + l) V →ₗ[K] K :=
  (hkl ▸ volumeBasis vol hvol).coord default

/-! ### Complementary basis indices -/

def topVector (b : Basis (Fin (finrank K V)) K V) (k l : ℕ)
    (hkl : k + l = finrank K V) : ⋀[K]^(k + l) V :=
  ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
    rw [hkl, ExteriorAlgebra.basis_eq_coe_basis b
      (⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V))]
    exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩

def complementEquiv (k l : ℕ) (hkl : k + l = finrank K V) :
    powersetCard (Fin (finrank K V)) k ≃ powersetCard (Fin (finrank K V)) l :=
  powersetCard.compl (by simpa [Nat.add_comm] using hkl)

omit [FiniteDimensional K V] in
lemma complementEquiv_disjoint (k l : ℕ) (hkl : k + l = finrank K V)
    (s : powersetCard (Fin (finrank K V)) k) :
    Disjoint s.val (complementEquiv k l hkl s).val := by
  simpa [complementEquiv] using (disjoint_compl_right : Disjoint s.val s.valᶜ)

/-! ### The wedge pairing -/

omit [FiniteDimensional K V] in
lemma wedgeMul_basis_pair (b : Basis (Fin (finrank K V)) K V) (k l : ℕ)
    (hkl : l + k = finrank K V) (s : powersetCard (Fin (finrank K V)) l)
    (t : powersetCard (Fin (finrank K V)) k) :
    DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V) (b.exteriorPower k t)
        (b.exteriorPower l s) =
      if t = complementEquiv l k hkl s then
        (permOfDisjoint (complementEquiv_disjoint l k hkl s).symm).sign •
          topVector b k l (by simpa [Nat.add_comm] using hkl)
      else 0 := by
  apply Subtype.ext
  change (b.exteriorPower k t : ExteriorAlgebra K V) *
      (b.exteriorPower l s : ExteriorAlgebra K V) = _
  rw [← ExteriorAlgebra.basis_eq_coe_basis b t, ← ExteriorAlgebra.basis_eq_coe_basis b s]
  by_cases h : Disjoint t.val s.val
  · have ht : t = complementEquiv l k hkl s := by
      simpa [Set.powersetCard.eq_iff_subset, complementEquiv] using
        Finset.subset_compl_iff_disjoint_right.mpr h
    subst t
    rw [ExteriorAlgebra.basis_mul_of_disjoint b _ s h]
    simp [topVector, complementEquiv, Finset.union_comm]
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint b t s h]
    have ht : t ≠ complementEquiv l k hkl s := by
      intro ht
      subst t
      exact h (complementEquiv_disjoint l k hkl s).symm
    simp [ht]

lemma volumeCoordinate_topVector_ne_zero (b : Basis (Fin (finrank K V)) K V)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    volumeCoordinate vol hvol k l hkl (topVector b k l hkl) ≠ 0 := by
  intro hd
  apply (b.ExteriorAlgebra).ne_zero (Finset.univ : Finset (Fin (finrank K V)))
  change (topVector b k l hkl : ExteriorAlgebra K V) = 0
  have htop : topVector b k l hkl = 0 := (hkl ▸ volumeBasis vol hvol).ext_elem fun i ↦ by
    cases i
    simpa [volumeCoordinate] using hd
  exact congrArg Subtype.val htop

def wedgePairing (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
  (k l : ℕ) (hkl : k + l = finrank K V) :
    ⋀[K]^l V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  (LinearMap.flip (DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V))).compr₂
    (volumeCoordinate vol hvol k l hkl)

end exteriorPower

end private_defs

namespace exteriorPower

/-- The linear equivalence induced by wedging with `vol` in complementary degrees. -/
public noncomputable def wedgePairingEquiv
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) := by
  classical
  let b := finBasis K V
  let bk := b.exteriorPower k
  let bl := b.exteriorPower l
  let f := wedgePairing vol hvol k l hkl
  let d := volumeCoordinate vol hvol k l hkl (topVector b k l hkl)
  have hd : d ≠ 0 := volumeCoordinate_topVector_ne_zero b vol hvol k l hkl
  have hlk : l + k = finrank K V := by simpa [Nat.add_comm] using hkl
  let complement := complementEquiv l k hlk
  let target := ((bk.dualBasis.reindex complement.symm).isUnitSMul
      (fun _ ↦ isUnit_iff_ne_zero.mpr hd)).groupSMul
    (fun s ↦ (permOfDisjoint
      (complementEquiv_disjoint l k hlk s).symm).sign)
  have hpair (s : powersetCard (Fin (finrank K V)) l)
      (t : powersetCard (Fin (finrank K V)) k) :
      f (bl s) (bk t) =
        if t = complementEquiv l k hlk s then
          (permOfDisjoint (complementEquiv_disjoint l k hlk s).symm).sign • d
        else 0 := by
    change volumeCoordinate vol hvol k l hkl
      (DirectSum.gMulLHom K (fun i ↦ ⋀[K]^i V) (b.exteriorPower k t)
        (b.exteriorPower l s)) = _
    rw [wedgeMul_basis_pair b k l hlk s t]
    split <;> simp [d, Units.smul_def]
  let e := bl.equiv target (Equiv.refl _)
  have he : e.toLinearMap = f := by
    apply bl.ext
    intro s
    change e (bl s) = f (bl s)
    rw [Basis.equiv_apply]
    apply bk.ext
    intro t
    simp [hpair, target, Module.Basis.isUnitSMul_apply, Basis.reindex_apply,
      Basis.groupSMul_apply, Finsupp.single_apply, complement, Equiv.symm_symm,
      smul_eq_mul]
  exact LinearEquiv.ofBijective f (by
    rw [← he]
    exact e.bijective)

end exteriorPower
