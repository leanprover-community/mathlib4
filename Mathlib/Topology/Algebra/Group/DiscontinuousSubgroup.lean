/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.Complement
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Properly discontinuous actions of subgroups
-/

open Topology Pointwise Filter Set TopologicalSpace Subgroup

public section

variable {Γ α : Type*} [Group Γ] [TopologicalSpace α]

@[to_additive]
protected lemma Subgroup.properlyDiscontinuousSMul_iff
    [SMul Γ α] (S : Subgroup Γ) : ProperlyDiscontinuousSMul S α ↔ ∀ {K L : Set α},
      IsCompact K → IsCompact L →  {g : Γ | g ∈ S ∧ (g • K ∩ L).Nonempty}.Finite := by
  rw [properlyDiscontinuousSMul_iff]
  congr! with K L hK hL
  convert injOn_subtype_val (s := {m : S | (m • K ∩ L).Nonempty}) |>.bijOn_image.finite_iff_finite
  ext g
  simp [and_comm]

@[to_additive]
lemma Subgroup.properlyDiscontinuousSMul_of_le
    [SMul Γ α] {G H : Subgroup Γ} (hG : ProperlyDiscontinuousSMul G α) (hGH : H ≤ G) :
    ProperlyDiscontinuousSMul H α := by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hG ⊢
  intro K L hK hL
  exact (hG hK hL).subset fun _ ⟨hg, hg'⟩ ↦ ⟨hGH hg, hg'⟩

/-- If `Γ` acts properly discontinuously, so does every subgroup of `Γ`. -/
@[to_additive]
instance [SMul Γ α] [ProperlyDiscontinuousSMul Γ α] (G : Subgroup Γ) :
    ProperlyDiscontinuousSMul G α := by
  refine Subgroup.properlyDiscontinuousSMul_of_le ?_ le_top
  simp only [Subgroup.properlyDiscontinuousSMul_iff, Subgroup.mem_top, true_and]
  exact finite_disjoint_inter_image

open Pointwise in
/-- If `G, H` are subgroups of `Γ` which acts on `α`, and `G ∩ H` has finite index in `G`,
then `G` acts properly discontinuously if `H` does. -/
@[to_additive]
lemma ProperlyDiscontinuousSMul.ofFiniteRelIndex [MulAction Γ α] [ContinuousConstSMul Γ α]
    (G H : Subgroup Γ) [hH : ProperlyDiscontinuousSMul H α] [H.IsFiniteRelIndex G] :
    ProperlyDiscontinuousSMul G α := by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hH ⊢
  intro K L hK hL
  have (t : Γ) : {g | g ∈ H ∧ (g • t • K ∩ L).Nonempty}.Finite :=
    hH (hK.image <| continuous_const_smul t) hL
  obtain ⟨S, hS, -⟩ := (H.subgroupOf G).exists_isComplement_right 1
  have hT : (Subtype.val '' S).Finite := by
    have : Fintype (G ⧸ H.subgroupOf G) := Subgroup.fintypeQuotientOfFiniteIndex
    have : Fintype S := .ofEquiv _ hS.rightQuotientEquiv
    exact (toFinite S).image _
  have hS' {g : Γ} (hg : g ∈ G) : ∃ t ∈ Subtype.val '' S, g * t⁻¹ ∈ H := by
    obtain ⟨p, hp⟩ := (hS.existsUnique ⟨g, hg⟩).exists
    aesop
  refine (hT.biUnion <| fun t ht ↦ (this t).map fun g ↦ g * t).subset fun g ↦ ?_
  simp [mul_smul]
  grind

@[to_additive]
lemma Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex
    [MulAction Γ α] [ContinuousConstSMul Γ α]
    {G H : Subgroup Γ} (hGH : G ≤ H) [IsFiniteRelIndex G H] :
    ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α :=
  ⟨fun _ ↦ .ofFiniteRelIndex H G, (properlyDiscontinuousSMul_of_le · hGH)⟩

@[to_additive]
lemma Subgroup.Commensurable.properlyDiscontinuousSMul_iff
    [MulAction Γ α] [ContinuousConstSMul Γ α]
    {G H : Subgroup Γ} (h : G.Commensurable H) :
    ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α := by
  have : IsFiniteRelIndex (G ⊓ H) H := ⟨Subgroup.inf_relIndex_right G H ▸ h.1⟩
  have : IsFiniteRelIndex (G ⊓ H) G := ⟨Subgroup.inf_relIndex_left G H ▸ h.2⟩
  calc ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul ↑(G ⊓ H) α :=
    (properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ ProperlyDiscontinuousSMul H α :=
    properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le_right

end
