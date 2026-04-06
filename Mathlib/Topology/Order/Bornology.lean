/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Bornology.Constructions

/-!
# Bornology of order-bounded sets

This file relates the notion of bornology-boundedness (sets that lie in a bornology) to the notion
of order-boundedness (sets that are bounded above and below).

## Main declarations

* `orderBornology`: The bornology of order-bounded sets of a nonempty lattice.
* `IsOrderBornology`: Typeclass predicate for a preorder to be equipped with its order-bornology.
-/

@[expose] public section

open Bornology Set

variable {α : Type*} {s t : Set α}

section Lattice
variable [Lattice α] [Nonempty α]

/-- Order-bornology on a nonempty lattice. The bounded sets are the sets that are bounded both above
and below. -/
@[implicit_reducible]
def orderBornology : Bornology α := .ofBounded
  {s | BddBelow s ∧ BddAbove s}
  (by simp)
  (fun _ hs _ hst ↦ ⟨hs.1.mono hst, hs.2.mono hst⟩)
  (fun _ hs _ ht ↦ ⟨hs.1.union ht.1, hs.2.union ht.2⟩)
  (by simp)

@[simp] lemma orderBornology_isBounded : orderBornology.IsBounded s ↔ BddBelow s ∧ BddAbove s := by
  simp [IsBounded, IsCobounded, -isCobounded_compl_iff]

end Lattice

variable [Bornology α]

variable (α) [Preorder α] in
/-- Predicate for a preorder to be equipped with its order-bornology, namely for its bounded sets
to be the ones that are bounded both above and below. -/
class IsOrderBornology : Prop where
  protected isBounded_iff_bddBelow_bddAbove (s : Set α) : IsBounded s ↔ BddBelow s ∧ BddAbove s

lemma isOrderBornology_iff_eq_orderBornology [Lattice α] [Nonempty α] :
    IsOrderBornology α ↔ ‹Bornology α› = orderBornology := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun s ↦ by rw [h, orderBornology_isBounded]⟩⟩
  ext s
  exact isBounded_compl_iff.symm.trans (h.1 _)

section Preorder
variable [Preorder α] [IsOrderBornology α]

lemma isBounded_iff_bddBelow_bddAbove : IsBounded s ↔ BddBelow s ∧ BddAbove s :=
  IsOrderBornology.isBounded_iff_bddBelow_bddAbove _

protected lemma Bornology.IsBounded.bddBelow (hs : IsBounded s) : BddBelow s :=
  (isBounded_iff_bddBelow_bddAbove.1 hs).1

protected lemma Bornology.IsBounded.bddAbove (hs : IsBounded s) : BddAbove s :=
  (isBounded_iff_bddBelow_bddAbove.1 hs).2

protected lemma BddBelow.isBounded (hs₀ : BddBelow s) (hs₁ : BddAbove s) : IsBounded s :=
  isBounded_iff_bddBelow_bddAbove.2 ⟨hs₀, hs₁⟩

protected lemma BddAbove.isBounded (hs₀ : BddAbove s) (hs₁ : BddBelow s) : IsBounded s :=
  isBounded_iff_bddBelow_bddAbove.2 ⟨hs₁, hs₀⟩

lemma BddBelow.isBounded_inter (hs : BddBelow s) (ht : BddAbove t) : IsBounded (s ∩ t) :=
  (hs.mono inter_subset_left).isBounded <| ht.mono inter_subset_right

lemma BddAbove.isBounded_inter (hs : BddAbove s) (ht : BddBelow t) : IsBounded (s ∩ t) :=
  (hs.mono inter_subset_left).isBounded <| ht.mono inter_subset_right

instance OrderDual.instIsOrderBornology : IsOrderBornology αᵒᵈ where
  isBounded_iff_bddBelow_bddAbove s := by
    rw [← isBounded_preimage_toDual, ← bddBelow_preimage_toDual, ← bddAbove_preimage_toDual,
      isBounded_iff_bddBelow_bddAbove, and_comm]

instance Prod.instIsOrderBornology {β : Type*} [Preorder β] [Bornology β] [IsOrderBornology β] :
    IsOrderBornology (α × β) where
  isBounded_iff_bddBelow_bddAbove s := by
    rw [← isBounded_image_fst_and_snd, bddBelow_prod, bddAbove_prod, and_and_and_comm,
      isBounded_iff_bddBelow_bddAbove, isBounded_iff_bddBelow_bddAbove]

instance Pi.instIsOrderBornology {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)]
    [∀ i, Bornology (α i)] [∀ i, IsOrderBornology (α i)] : IsOrderBornology (∀ i, α i) where
  isBounded_iff_bddBelow_bddAbove s := by
    simp_rw [← forall_isBounded_image_eval_iff, bddBelow_pi, bddAbove_pi, ← forall_and,
      isBounded_iff_bddBelow_bddAbove]

end Preorder

section LinearOrder

variable [Nonempty α] [LinearOrder α] [NoMaxOrder α] [NoMinOrder α] [IsOrderBornology α]

lemma IsOrderBornology.cobounded_eq : Bornology.cobounded α = Filter.atTop ⊔ Filter.atBot := by
  refine Filter.ext ?_
  intro s
  rw [Filter.mem_sup, Filter.atTop_basis_Ioi.mem_iff, Filter.atBot_basis_Iio.mem_iff,
    ← compl_compl s, ← isBounded_def, isBounded_iff_bddBelow_bddAbove, compl_compl s]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [mem_lowerBounds_iff_subset_Ici, ← compl_compl (Ici a), compl_subset_compl, compl_Ici] at ha
    rw [mem_upperBounds_iff_subset_Iic, ← compl_compl (Iic b), compl_subset_compl, compl_Iic] at hb
    constructor
    · use b
    · use a
  · rintro ⟨⟨b, _, hb⟩, ⟨a, _, ha⟩⟩
    obtain ⟨b', hb'⟩ := exists_gt b
    obtain ⟨a', ha'⟩ := exists_lt a
    constructor
    · use a'
      intro x hx
      by_contra! hx'
      have : x ∈ Iio a := hx'.trans ha'
      exact hx (mem_of_mem_of_subset this ha)
    · use b'
      intro x hx
      by_contra! hx'
      have : x ∈ Ioi b := hb'.trans hx'
      exact hx (mem_of_mem_of_subset this hb)

lemma IsOrderBornology.atTop_le_cobounded : .atTop ≤ Bornology.cobounded α := by
  simp [IsOrderBornology.cobounded_eq]

lemma IsOrderBornology.atBot_le_cobounded : .atTop ≤ Bornology.cobounded α := by
  simp [IsOrderBornology.cobounded_eq]

end LinearOrder

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [IsOrderBornology α] {s : Set α}

protected lemma Bornology.IsBounded.subset_Icc_sInf_sSup (hs : IsBounded s) :
    s ⊆ Icc (sInf s) (sSup s) := subset_Icc_csInf_csSup hs.bddBelow hs.bddAbove

end ConditionallyCompleteLattice
