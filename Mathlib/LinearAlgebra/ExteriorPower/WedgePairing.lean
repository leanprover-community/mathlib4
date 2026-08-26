/-
Copyright (c) 2026 Kirill Kondrashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kirill Kondrashov
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Wedge pairing on exterior powers

We construct the linear equivalence induced by wedging with a nonzero top-degree element.
-/

@[expose] public section

namespace exteriorPower

open Module Set Set.powersetCard

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.privateInPublic true in
private lemma finrank_top :
    finrank K (⋀[K]^(finrank K V) V) = 1 := by
  rw [exteriorPower.finrank_eq]
  simp

set_option backward.privateInPublic true in
private noncomputable def volumeBasis (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) :
    Basis Unit K (⋀[K]^(finrank K V) V) :=
  FiniteDimensional.basisSingleton Unit finrank_top vol hvol

set_option backward.privateInPublic true in
private noncomputable def volumeCoordinate (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) :
    ⋀[K]^(finrank K V) V →ₗ[K] K :=
  (volumeBasis vol hvol).coord default

set_option backward.privateInPublic true in
private noncomputable def topProjection :
    ExteriorAlgebra K V →ₗ[K] ⋀[K]^(finrank K V) V :=
  (GradedAlgebra.proj (fun i : ℕ ↦ ⋀[K]^i V) (finrank K V)).codRestrict
    (⋀[K]^(finrank K V) V) (fun _ ↦ SetLike.coe_mem _)

set_option backward.privateInPublic true in
private noncomputable def wedgeMul (k : ℕ) :
    ⋀[K]^k V →ₗ[K] ⋀[K]^(finrank K V - k) V →ₗ[K]
      ⋀[K]^(finrank K V) V :=
  ((LinearMap.mul K (ExteriorAlgebra K V)).compl₁₂
      (Submodule.subtype (⋀[K]^k V))
      (Submodule.subtype (⋀[K]^(finrank K V - k) V))).compr₂
    topProjection

set_option backward.privateInPublic true in
private noncomputable def wedgePairing (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k : ℕ) :
    ⋀[K]^(finrank K V - k) V →ₗ[K] (⋀[K]^k V →ₗ[K] K) :=
  (LinearMap.flip (wedgeMul k)).compr₂ (volumeCoordinate vol hvol)

set_option backward.privateInPublic true in
private def hodgeStarComplement (n k : ℕ) (s : powersetCard (Fin n) k) :
    powersetCard (Fin n) (n - k) := by
  let hcard : Fintype.card (Fin n) = n := Fintype.card_fin _
  let hm : (Fintype.card (Fin n) - k) + k = Fintype.card (Fin n) := by
    exact Nat.sub_add_cancel (by
      simpa [hcard] using Finset.card_le_card (Finset.subset_univ s.val))
  let c := compl hm s
  simpa only [hcard] using c

set_option backward.privateInPublic true in
private theorem hodgeStarComplement_coe (n k : ℕ) (s : powersetCard (Fin n) k) :
    (hodgeStarComplement n k s).val = s.valᶜ := by
  simp [hodgeStarComplement]

set_option backward.privateInPublic true in
private theorem hodgeStarComplement_disjoint (n k : ℕ) (s : powersetCard (Fin n) k) :
    Disjoint s.val (hodgeStarComplement n k s).val := by
  rw [hodgeStarComplement_coe, Finset.disjoint_left]
  intro i hi hci
  exact (Finset.mem_compl.mp hci) hi

set_option backward.privateInPublic true in
private theorem hodgeStarComplement_union (n k : ℕ) (s : powersetCard (Fin n) k) :
    s.val ∪ (hodgeStarComplement n k s).val = Finset.univ := by
  rw [hodgeStarComplement_coe]
  ext i
  simp

set_option backward.privateInPublic true in
private noncomputable def complementVector (b : Basis (Fin (finrank K V)) K V) (k : ℕ)
    (s : powersetCard (Fin (finrank K V)) k) : ⋀[K]^(finrank K V - k) V :=
  (permOfDisjoint (hodgeStarComplement_disjoint (finrank K V) k s)).sign •
    b.exteriorPower (finrank K V - k) (hodgeStarComplement (finrank K V) k s)

set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem complement_eq_of_disjoint (k : ℕ)
    (s : powersetCard (Fin (finrank K V)) k)
    (t : powersetCard (Fin (finrank K V)) (finrank K V - k))
    (h : Disjoint s.val t.val) :
    t = hodgeStarComplement (finrank K V) k s := by
  have hsk : k ≤ finrank K V := by
    simpa [s.prop] using Finset.card_le_card (Finset.subset_univ s.val)
  have hu : s.val ∪ t.val = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint h, s.prop, t.prop, Fintype.card_fin]
    exact Nat.add_sub_of_le hsk
  have ht : t.val = s.valᶜ := by
    apply Finset.ext
    intro i
    rw [Finset.mem_compl]
    constructor
    · intro hi hsi
      exact (Finset.disjoint_left.mp h) hsi hi
    · intro hi
      have hi' : i ∈ s.val ∪ t.val := by rw [hu]; simp
      rcases Finset.mem_union.mp hi' with hsi | hti
      · exact (hi hsi).elim
      · exact hti
  apply Subtype.ext
  exact ht.trans (hodgeStarComplement_coe (finrank K V) k s).symm

set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem complement_injective (k : ℕ)
    {s t : powersetCard (Fin (finrank K V)) k}
    (h : hodgeStarComplement (finrank K V) k s =
      hodgeStarComplement (finrank K V) k t) :
    s = t := by
  apply Subtype.ext
  apply compl_injective
  simp only [← hodgeStarComplement_coe (finrank K V) k s,
    ← hodgeStarComplement_coe (finrank K V) k t, congrArg Subtype.val h]

set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem topProjection_basis (b : Basis (Fin (finrank K V)) K V) :
    topProjection (b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V)))) =
      ⟨b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))), by
        change b.ExteriorAlgebra
          ((⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V)) :
            Finset (Fin (finrank K V))) ∈ ⋀[K]^(finrank K V) V
        rw [ExteriorAlgebra.basis_eq_coe_basis]
        exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property⟩ := by
  apply Subtype.ext
  change GradedAlgebra.proj (fun i : ℕ ↦ ⋀[K]^i V) (finrank K V)
      (b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V)))) = _
  rw [GradedAlgebra.proj_apply]
  apply DirectSum.decompose_of_mem_same
  change b.ExteriorAlgebra
    ((⟨Finset.univ, by simp⟩ : powersetCard (Fin (finrank K V)) (finrank K V)) :
      Finset (Fin (finrank K V))) ∈ ⋀[K]^(finrank K V) V
  rw [ExteriorAlgebra.basis_eq_coe_basis]
  exact (b.exteriorPower _ ⟨Finset.univ, by simp⟩).property

set_option backward.privateInPublic true in
private theorem volumeCoordinate_top_nonzero (b : Basis (Fin (finrank K V)) K V)
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) :
    volumeCoordinate vol hvol (topProjection (b.ExteriorAlgebra Finset.univ)) ≠ 0 := by
  intro hc
  have hz : topProjection (b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V)))) = 0 := by
    apply (volumeBasis vol hvol).forall_coord_eq_zero_iff.mp
    intro i
    cases i
    simpa [volumeCoordinate, topProjection_basis b] using hc
  have htop : b.ExteriorAlgebra (Finset.univ : Finset (Fin (finrank K V))) ≠ 0 := by
    exact (b.ExteriorAlgebra).ne_zero _
  exact htop (by simpa [topProjection_basis b] using congrArg Subtype.val hz)

set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem wedge_basis_complement (b : Basis (Fin (finrank K V)) K V) (k : ℕ)
    (s : powersetCard (Fin (finrank K V)) k) :
    wedgeMul k (b.exteriorPower k s) (complementVector b k s) =
      topProjection (b.ExteriorAlgebra Finset.univ) := by
  simp only [wedgeMul, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  simp only [LinearMap.mul_apply', Submodule.coe_subtype]
  rw [← ExteriorAlgebra.basis_eq_coe_basis b s]
  apply Subtype.ext
  rw [show (complementVector b k s : ExteriorAlgebra K V) =
      (permOfDisjoint (hodgeStarComplement_disjoint (finrank K V) k s)).sign •
        b.ExteriorAlgebra (hodgeStarComplement (finrank K V) k s) by
    simp [complementVector, ExteriorAlgebra.basis_eq_coe_basis]]
  rw [Units.smul_def, mul_smul_comm,
    ExteriorAlgebra.basis_mul_of_disjoint b s (hodgeStarComplement (finrank K V) k s)
      (hodgeStarComplement_disjoint (finrank K V) k s)]
  · rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union,
      hodgeStarComplement_union]
    rcases Int.units_eq_one_or
        (permOfDisjoint (hodgeStarComplement_disjoint (finrank K V) k s)).sign with h | h <;>
      simp [h, topProjection_basis b, Units.smul_def]

set_option backward.privateInPublic true in
omit [FiniteDimensional K V] in
private theorem wedge_basis_zero (b : Basis (Fin (finrank K V)) K V) (k : ℕ)
    (s : powersetCard (Fin (finrank K V)) k)
    (t : powersetCard (Fin (finrank K V)) (finrank K V - k))
    (ht : t ≠ hodgeStarComplement (finrank K V) k s) :
    wedgeMul k (b.exteriorPower k s) (b.exteriorPower (finrank K V - k) t) = 0 := by
  have hdisj : ¬Disjoint s.val t.val := by
    intro h
    exact ht (complement_eq_of_disjoint k s t h)
  simp only [wedgeMul, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply]
  simp only [LinearMap.mul_apply', Submodule.coe_subtype]
  rw [← ExteriorAlgebra.basis_eq_coe_basis b s,
    ← ExteriorAlgebra.basis_eq_coe_basis b t]
  apply Subtype.ext
  rw [ExteriorAlgebra.basis_mul_of_not_disjoint b s t hdisj]
  simp

set_option backward.privateInPublic true in
private noncomputable def wedgePairingInverse
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k : ℕ) :
    (⋀[K]^k V →ₗ[K] K) →ₗ[K] ⋀[K]^(finrank K V - k) V := by
  let b := finBasis K V
  let c := volumeCoordinate vol hvol (topProjection (b.ExteriorAlgebra Finset.univ))
  let q : powersetCard (Fin (finrank K V)) k → ⋀[K]^(finrank K V - k) V :=
    fun s ↦ c⁻¹ • complementVector b k s
  exact (b.exteriorPower k).dualBasis.constr K q

set_option backward.privateInPublic true in
private theorem wedgePairing_complement
    (b : Basis (Fin (finrank K V)) K V) (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0)
    (k : ℕ) (s : powersetCard (Fin (finrank K V)) k)
    (t : powersetCard (Fin (finrank K V)) k) :
    wedgePairing vol hvol k (complementVector b k s) (b.exteriorPower k t) =
      if t = s then volumeCoordinate vol hvol (topProjection (b.ExteriorAlgebra Finset.univ))
      else 0 := by
  change volumeCoordinate vol hvol
      (wedgeMul k (b.exteriorPower k t) (complementVector b k s)) = _
  by_cases hts : t = s
  · subst t
    rw [wedge_basis_complement]
    simp
  · have hcomp : hodgeStarComplement (finrank K V) k s ≠
        hodgeStarComplement (finrank K V) k t := by
      intro h
      exact hts (complement_injective k h.symm)
    rw [show complementVector b k s =
        (permOfDisjoint (hodgeStarComplement_disjoint (finrank K V) k s)).sign •
          b.exteriorPower (finrank K V - k) (hodgeStarComplement (finrank K V) k s) by rfl]
    simp only [Units.smul_def, map_zsmul]
    rw [wedge_basis_zero b k t (hodgeStarComplement (finrank K V) k s) hcomp]
    simp [hts]

set_option backward.privateInPublic true in
private theorem wedgePairing_comp_inverse
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k : ℕ) :
    wedgePairing vol hvol k ∘ₗ wedgePairingInverse vol hvol k =
      LinearMap.id := by
  let b := finBasis K V
  let c := volumeCoordinate vol hvol (topProjection (b.ExteriorAlgebra Finset.univ))
  have hc : c ≠ 0 := volumeCoordinate_top_nonzero b vol hvol
  apply (b.exteriorPower k).dualBasis.ext
  intro s
  apply (b.exteriorPower k).ext
  intro t
  by_cases hts : t = s
  · subst t
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Basis.dualBasis_apply_self]
    dsimp [wedgePairingInverse]
    rw [Basis.constr_basis]
    rw [(wedgePairing vol hvol k).map_smul, LinearMap.smul_apply, wedgePairing_complement]
    simpa [c] using inv_mul_cancel₀ hc
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, Basis.dualBasis_apply_self]
    dsimp [wedgePairingInverse]
    rw [Basis.constr_basis]
    rw [(wedgePairing vol hvol k).map_smul, LinearMap.smul_apply, wedgePairing_complement]
    simp [hts]

set_option backward.privateInPublic true in
private noncomputable def wedgePairingEquivAux
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k : ℕ)
    (hk : k ≤ finrank K V) :
    ⋀[K]^(finrank K V - k) V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) := by
  let f := wedgePairing vol hvol k
  have hdim : finrank K (⋀[K]^(finrank K V - k) V) =
      finrank K (⋀[K]^k V →ₗ[K] K) := by
    calc
      finrank K (⋀[K]^(finrank K V - k) V) =
          Nat.choose (finrank K V) (finrank K V - k) := exteriorPower.finrank_eq K V _
      _ = Nat.choose (finrank K V) k := Nat.choose_symm hk
      _ = finrank K (⋀[K]^k V) := (exteriorPower.finrank_eq K V _).symm
      _ = finrank K (⋀[K]^k V →ₗ[K] K) :=
        (Module.finBasis K (⋀[K]^k V)).toDualEquiv.finrank_eq
  have hright : Function.RightInverse (wedgePairingInverse vol hvol k) f := by
    intro x
    have hx := congrArg (fun g ↦ g x) (wedgePairing_comp_inverse vol hvol k)
    simpa [f, LinearMap.comp_apply] using hx
  exact LinearMap.linearEquivOfInjective f
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hright.surjective) hdim

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The linear equivalence induced by wedging with `vol` in complementary degrees. -/
noncomputable def wedgePairingEquiv
    (vol : ⋀[K]^(finrank K V) V) (hvol : vol ≠ 0) (k l : ℕ)
    (hkl : k + l = finrank K V) :
    ⋀[K]^l V ≃ₗ[K] (⋀[K]^k V →ₗ[K] K) := by
  have hk : k ≤ finrank K V := by
    rw [← hkl]
    exact Nat.le_add_right _ _
  have hl : finrank K V - k = l := (Nat.eq_sub_of_add_eq' hkl).symm
  rw [← hl]
  exact wedgePairingEquivAux vol hvol k hk

end exteriorPower
