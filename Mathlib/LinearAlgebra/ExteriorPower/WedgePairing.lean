/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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
    calc
      l + k = k + l := Nat.add_comm _ _
      _ = finrank K V := hkl
      _ = Fintype.card (Fin (finrank K V)) := (Fintype.card_fin _).symm
  let c : powersetCard (Fin (finrank K V)) k ≃
      powersetCard (Fin (finrank K V)) l := powersetCard.compl hkl'
  have hdisj (s : powersetCard (Fin (finrank K V)) k) :
      Disjoint s.val (c s).val := by
    rw [show (c s).val = s.valᶜ by exact powersetCard.coe_compl]
    exact disjoint_compl_right
  have hunion (s : powersetCard (Fin (finrank K V)) k) :
      s.val ∪ (c s).val = Finset.univ := by
    rw [show (c s).val = s.valᶜ by exact powersetCard.coe_compl]
    exact Finset.union_compl _
  let top : ExteriorAlgebra K V :=
    b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V)))
  have top_mem : top ∈ ⋀[K]^(finrank K V) V := by
    change b.ExteriorAlgebra
      ((⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V)) :
        Finset (Fin (finrank K V))) ∈ ⋀[K]^(finrank K V) V
    rw [ExteriorAlgebra.basis_eq_coe_basis]
    exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property
  let topProjection : ExteriorAlgebra K V →ₗ[K] ⋀[K]^(finrank K V) V :=
    (GradedAlgebra.proj (fun i : ℕ ↦ ⋀[K]^i V) (finrank K V)).codRestrict
      (⋀[K]^(finrank K V) V) (fun _ ↦ SetLike.coe_mem _)
  have topProjection_top : topProjection top = ⟨top, top_mem⟩ := by
    apply Subtype.ext
    change GradedAlgebra.proj (fun i : ℕ ↦ ⋀[K]^i V) (finrank K V) top = top
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same]
    exact top_mem
  have topProjection_top' :
      (topProjection (b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V)))) :
        ExteriorAlgebra K V) = b.ExteriorAlgebra Finset.univ := by
    simpa [top] using congrArg Subtype.val topProjection_top
  let topCoordinateBasis : Basis Unit K (⋀[K]^(finrank K V) V) :=
    FiniteDimensional.basisSingleton Unit (by simp [exteriorPower.finrank_eq]) vol hvol
  let topCoordinate := topCoordinateBasis.coord default
  let wedgeMul : ⋀[K]^k V →ₗ[K] ⋀[K]^l V →ₗ[K] ⋀[K]^(finrank K V) V :=
    ((LinearMap.mul K (ExteriorAlgebra K V)).compl₁₂
      (Submodule.subtype (⋀[K]^k V)) (Submodule.subtype (⋀[K]^l V))).compr₂
      topProjection
  let f : ⋀[K]^l V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
    (LinearMap.flip wedgeMul).compr₂ topCoordinate
  let d : K := topCoordinate (topProjection top)
  have hd : d ≠ 0 := by
    intro hd
    have hzero : topProjection top = 0 := by
      apply topCoordinateBasis.forall_coord_eq_zero_iff.mp
      intro i
      cases i
      exact hd
    have htop : (⟨top, top_mem⟩ : ⋀[K]^(finrank K V) V) = 0 :=
      topProjection_top.symm.trans hzero
    have htop' : top = 0 := by
      simpa using congrArg Subtype.val htop
    exact (b.ExteriorAlgebra).ne_zero _ htop'
  let complementVector : powersetCard (Fin (finrank K V)) k → ⋀[K]^l V :=
    fun s ↦ (permOfDisjoint (hdisj s)).sign • bl (c s)
  have complementVector_coe (s : powersetCard (Fin (finrank K V)) k) :
      (complementVector s : ExteriorAlgebra K V) =
        (permOfDisjoint (hdisj s)).sign • b.ExteriorAlgebra (c s) := by
    simp [complementVector, bl, exteriorPower.basis_apply,
      ExteriorAlgebra.basis_eq_coe_basis]
  have hmul (s : powersetCard (Fin (finrank K V)) k) :
      wedgeMul (bk s) (complementVector s) = topProjection top := by
    simp only [wedgeMul, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp only [LinearMap.mul_apply', Submodule.coe_subtype]
    rw [← ExteriorAlgebra.basis_eq_coe_basis b s]
    apply Subtype.ext
    rw [complementVector_coe]
    rw [Units.smul_def, mul_smul_comm,
      ExteriorAlgebra.basis_mul_of_disjoint b s (c s) (hdisj s)]
    rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union, hunion]
    rcases Int.units_eq_one_or (permOfDisjoint (hdisj s)).sign with h | h
    · simp [h, top, topProjection_top']
    · simp [h, Units.smul_def, top, topProjection_top']
  have hcomp_eq {s t : powersetCard (Fin (finrank K V)) k}
      (h : Disjoint t.val (c s).val) : t = s := by
    apply Subtype.ext
    have ht : (c s).valᶜ = t.val :=
      Finset.compl_eq_of_disjoint_of_card_add_eq h.symm (by
        simpa [t.prop, (c s).prop, Fintype.card_fin] using hkl')
    rw [show (c s).val = s.valᶜ by exact powersetCard.coe_compl] at ht
    simpa using ht.symm
  have hzero (s t : powersetCard (Fin (finrank K V)) k) (h : t ≠ s) :
      wedgeMul (bk t) (complementVector s) = 0 := by
    have hnotdisj : ¬Disjoint t.val (c s).val := fun h' ↦ h (hcomp_eq h')
    simp only [wedgeMul, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
    simp only [LinearMap.mul_apply', Submodule.coe_subtype]
    rw [← ExteriorAlgebra.basis_eq_coe_basis b t]
    apply Subtype.ext
    rw [complementVector_coe]
    rw [Units.smul_def, mul_smul_comm,
      ExteriorAlgebra.basis_mul_of_not_disjoint b t (c s) hnotdisj]
    simp
  have fpair (s t : powersetCard (Fin (finrank K V)) k) :
      f (complementVector s) (bk t) = if t = s then d else 0 := by
    change topCoordinate (wedgeMul (bk t) (complementVector s)) = _
    by_cases h : t = s
    · subst t
      rw [hmul]
      simp [d]
    · rw [hzero s t h]
      simp [h]
  let g : (⋀[K]^k V →ₗ[K] K) →ₗ[K] ⋀[K]^l V :=
    bk.dualBasis.constr K (fun s ↦ d⁻¹ • complementVector s)
  have hfg : f ∘ₗ g = LinearMap.id := by
    apply bk.dualBasis.ext
    intro s
    apply bk.ext
    intro t
    by_cases h : t = s
    · subst t
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Basis.dualBasis_apply_self]
      dsimp [g]
      rw [Basis.constr_basis, f.map_smul, LinearMap.smul_apply, fpair]
      simpa [d] using inv_mul_cancel₀ hd
    · simp only [LinearMap.comp_apply, LinearMap.id_apply, Basis.dualBasis_apply_self]
      dsimp [g]
      rw [Basis.constr_basis, f.map_smul, LinearMap.smul_apply, fpair]
      simp [h]
  have hk : k ≤ finrank K V := by
    rw [← hkl]
    exact Nat.le_add_right _ _
  have hdim : finrank K (⋀[K]^l V) =
      finrank K (⋀[K]^k V →ₗ[K] K) := by
    calc
      finrank K (⋀[K]^l V) = Nat.choose (finrank K V) l :=
        exteriorPower.finrank_eq K V l
      _ = Nat.choose (finrank K V) k := by
        rw [Nat.eq_sub_of_add_eq' hkl, Nat.choose_symm hk]
      _ = finrank K (⋀[K]^k V) := (exteriorPower.finrank_eq K V k).symm
      _ = finrank K (⋀[K]^k V →ₗ[K] K) :=
        (Module.finBasis K (⋀[K]^k V)).toDualEquiv.finrank_eq
  have hright : Function.RightInverse g f := by
    intro x
    have hx := congrArg (fun h ↦ h x) hfg
    simpa [LinearMap.comp_apply] using hx
  exact LinearMap.linearEquivOfInjective f
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hright.surjective) hdim

end exteriorPower
