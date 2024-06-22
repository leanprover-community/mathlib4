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

lemma closed_basis3 (S : Set α) : ⋂₀ { T ↓∩ (Ici a) | a ∈ S } = T ↓∩ (Ici (sSup S)) := by
  rw [← compl_inj_iff]
  rw [← preimage_compl]
  rw [compl_sInter]
  rw [← basis3]
  apply congrArg sUnion
  --simp only [preimage_compl]
  aesop




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

lemma isClosed_iff (S : Set T) : IsClosed S ↔ ∃ (a : α), S = T ↓∩ (Ici a) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff]
  constructor
  · intros h
    cases' h with a ha
    use a
    rw [preimage_compl, compl_inj_iff] at ha
    exact ha
  · intros h
    cases' h with a ha
    use a
    rw [preimage_compl, compl_inj_iff]
    exact ha
  exact fun p a ↦ hT p a



/-
lemma isOpen_iff' (S : Set T) : IsOpen S ↔ S = T ↓∩ (Ici (sSup {a : α | T ↓∩ (Ici a)ᶜ ⊆ S}))ᶜ := by
  constructor
  · intro h
    let R := {a : α | T ↓∩ (Ici a)ᶜ ⊆ S}

    rw [← basis3]
    simp only [preimage_compl, mem_setOf_eq]
    rw [IsTopologicalBasis.open_eq_sUnion' (isBasis1' T hT) h]
    simp  [preimage_compl, mem_setOf_eq]
    aesop
  · intro h
    use (Ici (sSup {a | T ↓∩ (Ici a)ᶜ ⊆ S}))ᶜ
    constructor
    · simp only [isOpen_compl_iff]
      exact isClosed_Ici
    · exact id (Eq.symm h)
-/

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

theorem PrimativeSpectrum.gc' : GaloisConnection (α := Set T) (β := αᵒᵈ)
    (fun S => OrderDual.toDual (sInf (S : (Set α))))
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
    simp only [le_sInf_iff, mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      forall_exists_index]
    intros b hbT hbS
    rw [← mem_Ici]
    apply h hbS

/-- `T` is said to order generate `α` if, for every `a` in `α`, there exists a subset of `T` such
that `a` is the inf of `S`. -/
def OrderGenerate := ∀ (a : α), ∃ (S : Set T), a = sInf (S : Set α)

/--
When `T` is order generating, the kernel and the hull form a Galois insertion
-/
def PrimativeSpectrum.gi (hG : OrderGenerate T) : GaloisInsertion (α := Set T) (β := αᵒᵈ)
    (fun S => OrderDual.toDual (sInf (S : (Set α))))
    (fun a => T ↓∩ (Ici (OrderDual.ofDual a))) :=
  (PrimativeSpectrum.gc' T).toGaloisInsertion fun a ↦ (by
    rw [OrderDual.le_toDual]
    cases' hG a with S hS
    have e1 : S ⊆ T ↓∩ Ici (OrderDual.ofDual a) := by
      intros c hcS
      rw [mem_preimage, mem_Ici]
      rw [hS]
      apply CompleteSemilatticeInf.sInf_le
      exact mem_image_of_mem Subtype.val hcS
    have e2 : sInf (T ↓∩ Ici (OrderDual.ofDual a) : Set α) ≤ sInf (S : Set α) := by
      apply sInf_le_sInf
      exact image_val_mono e1
    exact le_of_le_of_eq e2 (id (Eq.symm hS)))

/-
lemma hk1 (hG : OrderGenerate T) (C : Set T) (h : IsClosed C) :
    (PrimativeSpectrum.gc' T).closureOperator C = C := by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]
  have e1 : ∃ (a : α), C = T ↓∩ (Ici a) := (isClosed_iff T hT C).mp h
  cases' e1 with c hc
  rw [hc]
-/

lemma test (S R : Set α) (h : ∀ (a : α), a ∈ S ↔ a ∈ R) : S = R := by
  exact ext h

lemma test' (S R : Set α) (h : S = R) : ∀ (a : α), a ∈ S ↔ a ∈ R := by
  exact fun a ↦ Eq.to_iff (congrArg (Membership.mem a) h)

lemma testhk (S : Set T) : (PrimativeSpectrum.gc' T).closureOperator S = T ↓∩ (Ici (sInf S)) := by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]

/-
theorem hull_kernel : (TopologicalSpace.Closeds.gc (α := T)).closureOperator =
    (PrimativeSpectrum.gc' T).closureOperator := by
  ext S a
  rw [testhk]
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, toDual_sInf, ofDual_sSup,
    mem_preimage]
  --rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]
  --rw [← mem_preimage]
  --rw [←  closed_basis3 ]
  --apply congrArg
  --apply fun a ↦ Eq.to_iff (congrArg (Membership.mem a) _ _)
  rw [closure]
  simp_rw [isClosed_iff]
  --rw [closed_basis3 ]
  simp?
  constructor
  · intro h
  · intro h a ha
  rw [← OrderDual.toDual_symm_eq ]
  simp only [OrderDual.toDual_symm_eq, mem_Ici]

  --simp_rw []
  rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]
  simp only [mem_sInter, mem_setOf_eq, and_imp, forall_exists_index, forall_eq_apply_imp_iff,
    mem_preimage, mem_Ici, preimage_id_eq, id_eq]
  simp_rw [OrderDual.ofDual_toDual]
-/

end PrimativeSpectrum
