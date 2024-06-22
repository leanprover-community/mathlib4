/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Order.Irreducible
import Mathlib.Data.Set.Subset
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Sets.Closeds

/-!
# Hull-Kernel Topology

-/

variable {α}

open TopologicalSpace
open Topology
open Set
open Set.Notation

section SemilatticeInf

variable [SemilatticeInf α] [TopologicalSpace α] [IsLower α]

variable (T : Set α) (hT : ∀ p ∈ T, InfPrime p)

lemma basis1 (a b : α) : (T ↓∩ (Ici a)ᶜ) ∩ (T ↓∩ (Ici b)ᶜ) = (T ↓∩ (Ici (a ⊓ b))ᶜ) := by
  ext p
  simp only [preimage_compl, mem_inter_iff, mem_compl_iff, mem_preimage, mem_Ici]
  rw [← not_or]
  constructor
  · intro h
    by_contra h2
    have e1 : a ≤ ↑p ∨ b ≤ ↑p := by
      apply (hT p (Subtype.coe_prop p)).2  h2
    exact h e1
  · intros h
    by_contra h2
    cases' h2 with h1 h3
    have e1 : a ⊓ b ≤ p := inf_le_of_left_le h1
    exact h e1
    have e1 : a ⊓ b ≤ p := inf_le_of_right_le h3
    exact h e1

variable [DecidableEq α] [OrderTop α]

open Finset in
lemma basis2  (F : Finset α) : T ↓∩ (↑(upperClosure F.toSet))ᶜ = T ↓∩ (Ici (inf F id))ᶜ := by
  rw [coe_upperClosure]
  simp only [compl_iUnion]
  rw [preimage_iInter₂]
  induction' F using Finset.induction_on with a F' _ I4
  · simp only [Finset.coe_empty, mem_empty_iff_false, iInter_of_empty,
    iInter_univ, sInf_empty, Ici_top]
    simp only [inf_empty, Ici_top, Set.preimage_compl]
    rw [eq_compl_comm]
    simp only [Set.compl_univ]
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty] at hf
    simp at hf
    cases' hf with x hx
    simp at hx
    apply (hT x (Subtype.coe_prop x)).1
    exact isMax_iff_eq_top.mpr hx
  · simp only [coe_insert, mem_insert_iff, mem_coe,  iInter_iInter_eq_or_left,
      inf_insert, id_eq]
    rw [← basis1, ← I4]
    simp only [Set.preimage_compl, mem_coe]
    exact hT

lemma isBasis1 : IsTopologicalBasis { S : Set T | ∃ (a : α), T \ Ici a = S } := by
  convert isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis T
  rw [IsLower.lowerBasis]
  ext R
  simp only [mem_setOf_eq, mem_image, exists_exists_and_eq_and, preimage_compl]
  constructor
  · intro ha
    cases' ha with a ha'
    use {a}
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, true_and]
    rw [← (Function.Injective.preimage_image Subtype.val_injective R)]
    rw [← ha']
    rw [← preimage_compl]
    simp only [preimage_compl, preimage_diff, Subtype.coe_preimage_self]
    exact compl_eq_univ_diff (Subtype.val ⁻¹' Ici a)
  · intro ha
    cases' ha with F hF
    lift F to Finset α using hF.1
    use Finset.inf F id -- As F is finite, do we need complete?
    rw [← hF.2]
    rw [← preimage_compl]
    rw [basis2]
    simp only [preimage_compl, image_val_compl, Subtype.image_preimage_coe, diff_self_inter]
    exact fun p a ↦ hT p a

lemma isBasis1' : IsTopologicalBasis { S : Set T | ∃ (a : α), T ↓∩ (Ici a)ᶜ = S } := by
  convert isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis T
  rw [IsLower.lowerBasis]
  ext R
  --simp only [mem_setOf_eq, mem_image, exists_exists_and_eq_and, preimage_compl]
  simp only [preimage_compl, mem_setOf_eq, mem_image, exists_exists_and_eq_and]
  constructor
  · intro ha
    cases' ha with a ha'
    use {a}
    simp  [mem_setOf_eq]
    rw [← (Function.Injective.preimage_image Subtype.val_injective R)]
    rw [← ha']
    --rw [← preimage_compl]
    simp [preimage_compl, preimage_diff, Subtype.coe_preimage_self]
    exact compl_eq_univ_diff (Subtype.val ⁻¹' Ici a)
  · intro ha
    cases' ha with F hF
    lift F to Finset α using hF.1
    use Finset.inf F id -- As F is finite, do we need complete?
    rw [← hF.2]
    rw [← preimage_compl]
    rw [← basis2]
    simp [preimage_compl, image_val_compl, Subtype.image_preimage_coe, diff_self_inter]
    rfl
    exact fun p a ↦ hT p a


end SemilatticeInf

section PrimativeSpectrum

variable [CompleteLattice α] [TopologicalSpace α] [IsLower α] [DecidableEq α]

variable (T : Set α) (hT : ∀ p ∈ T, InfPrime p)




lemma basis3 (S : Set α) : ⋃₀ { T ↓∩ (Ici a)ᶜ | a ∈ S } = T ↓∩ (Ici (sSup S))ᶜ := by
  rw [le_antisymm_iff]
  constructor
  · simp only [preimage_compl, le_eq_subset, sUnion_subset_iff, mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, compl_subset_compl]
    intro a ha
    apply Set.preimage_val_subset_preimage_val
    apply antitone_Ici
    exact CompleteLattice.le_sSup S a ha
  · simp only [preimage_compl, le_eq_subset]
    intro a ha
    simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_compl_iff, mem_preimage,
      mem_Ici]
    simp at ha
    exact ha


lemma isOpen_iff (S : Set T) : IsOpen S ↔ ∃ (a : α), S = T ↓∩ (Ici a)ᶜ := by
  constructor
  · intro h
    let R := {a : α | T ↓∩ (Ici a)ᶜ ⊆ S}
    use sSup R
    rw [← basis3]
    rw [IsTopologicalBasis.open_eq_sUnion' (isBasis1' T hT) h]
    simp only [preimage_compl, mem_setOf_eq, R]
    aesop
  · intro h
    cases' h with a ha
    use (Ici a)ᶜ
    constructor
    · simp only [isOpen_compl_iff]
      exact isClosed_Ici
    · rw [ha]

theorem PrimativeSpectrum.gc : GaloisConnection (β := (Set T)ᵒᵈ) (fun a => T ↓∩ (Ici a))
    (fun S =>  sInf (↑(OrderDual.ofDual S) : (Set α))) := by
  rw [GaloisConnection]
  intros a S
  constructor
  · intro h
    simp only at h
    simp only [le_sInf_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intro b hbT hbS
    rw [← mem_Ici]
    apply h hbS
  · intro h
    simp only [le_sInf_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      forall_exists_index] at h
    intro b hbS
    rw [mem_preimage]
    rw [mem_Ici]
    apply h
    exact hbS
    exact Subtype.coe_prop b

theorem PrimativeSpectrum.gc' : GaloisConnection (α := Set T) (β := αᵒᵈ) (fun S => OrderDual.toDual (sInf (S : (Set α))))
    (fun a => T ↓∩ (Ici (OrderDual.ofDual a))) := by
  rw [GaloisConnection]
  intros S a
  constructor
  · intro h
    intro b hbS
    rw [mem_preimage, mem_Ici]
    rw [← OrderDual.ofDual_le_ofDual] at h
    simp at h
    apply h
    exact hbS
    exact Subtype.coe_prop b
  · intro h
    simp at h
    rw [← OrderDual.ofDual_le_ofDual]
    rw [OrderDual.ofDual_toDual]
    simp
    intros b hbT hbS
    rw [← mem_Ici]
    apply h hbS





#check TopologicalSpace.Closeds.gc.closureOperator
#check (TopologicalSpace.Closeds.gc (α := T)).closureOperator
#check (PrimativeSpectrum.gc' T).closureOperator
#check (PrimativeSpectrum.gc T).dual.closureOperator

#check (TopologicalSpace.Closeds.gc (α := T)).closureOperator = (PrimativeSpectrum.gc' T).closureOperator

#check (TopologicalSpace.Closeds.gc (α := T)).closureOperator = (PrimativeSpectrum.gc T).dual.closureOperator

end PrimativeSpectrum
