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

section PrimativeSpectrum

variable [CompleteLattice α] [TopologicalSpace α] [IsLower α]

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
