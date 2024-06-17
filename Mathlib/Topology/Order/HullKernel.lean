/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Order.Irreducible
import Mathlib.Data.Set.Subset

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

open Finset in
lemma basis2 [OrderTop α] (F : Finset α) : T ↓∩ (↑(upperClosure F.toSet))ᶜ = T ↓∩ (Ici (inf F id))ᶜ := by
  rw [coe_upperClosure]
  simp only [compl_iUnion]
  rw [preimage_iInter₂]
  induction' F using Finset.induction_on with a F' I3 I4
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
  · simp only [coe_insert, mem_insert_iff, mem_coe, Set.preimage_compl, iInter_iInter_eq_or_left,
    inf_insert, id_eq]


end SemilatticeInf

section PrimativeSpectrum

variable [SemilatticeInf α] [TopologicalSpace α] [IsLower α]

variable (T : Set α) (hT : ∀ p ∈ T, InfPrime p)





lemma test1 [DecidableEq α] : IsTopologicalBasis { S : Set T | ∃ (a : α), T \ Ici a = S } := by
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
    use sInf F -- As F is finite, do we need complete?
    rw [← hF.2]
    rw [← preimage_compl]
    have e1 : Subtype.val '' (Subtype.val (p := T) ⁻¹' (↑(upperClosure F))ᶜ) = T ∩ (upperClosure F)ᶜ := by
      rw [← (Subtype.image_preimage_coe T (↑(upperClosure F : Set α))ᶜ)]
      rfl
    have e3 : T ↓∩ ⋂ i ∈ F, (Ici i)ᶜ =  ⋂ i ∈ F, T ↓∩ (Ici i)ᶜ := by
      exact preimage_iInter₂
    have e2 : T ↓∩ (↑(upperClosure F))ᶜ = T ↓∩ (Ici (sInf F))ᶜ  := by
      rw [coe_upperClosure]
      simp only [compl_iUnion]
      rw [preimage_iInter₂]
      lift F to Finset α using hF.1
      induction F using Finset.induction_on
      · simp only [Finset.coe_empty, mem_empty_iff_false, preimage_compl, iInter_of_empty,
        iInter_univ, sInf_empty, Ici_top]
        rw [eq_compl_comm]
        simp only [compl_univ]
        by_contra hf
        rw [← Set.not_nonempty_iff_eq_empty] at hf
        simp at hf
        cases' hf with x hx
        simp at hx
        apply (hT x (Subtype.coe_prop x)).1
        exact isMax_iff_eq_top.mpr hx
      · simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, preimage_compl,
        iInter_iInter_eq_or_left, sInf_insert]
        sorry
    rw [← e2]
    exact id (Eq.symm e1)

/-
lemma test (S : Set T) : IsOpen S ↔ ∃ (a : α), S = T ∩ Ici a := by
  constructor
  · intro h
    sorry
  · --intro h
    --cases' h with a ha
    exact False.elim β
-/

end PrimativeSpectrum
