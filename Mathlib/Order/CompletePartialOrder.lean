/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Directed
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic

/-!
# Complete Partial Order

This file begins by showing that each set `s` in a join-semilattice generates a set
`directedClosure s` such that:

- `directedClosure_directedOn`: `directedClosure s` is directed
- `subset_toDirectedSet`: `s` is a subset of `directedClosure s`
- `Set_DirectedSet_LUB`: `u` is the least upper bound of `s` if and only if it is the least upper
  bound of `directedClosure s`

It follows that if every directed set in a join-semilattice has a least upper bound then the join is
complete.

The second part of this file considers complete partial orders (sometimes called directedly complete
partial orders). These are partial orders for which every directed set has a least upper bound.

## References

- [B. A. Davey and H. A. Priestley, Introduction to lattices and order][davey_priestley]

## Tags

complete partial order, directedly complete partial order

-/

section SemilatticeSup

variable {α : Type*} [SemilatticeSup α]

/--
Every subset of a join-semilattice generates a directed set
-/
def directedClosure (s : Set α) :=
  { a | ∃ F : Finset α, ∃ H : F.Nonempty, ↑F ⊆ s ∧  a = F.sup' H id }

lemma directedClosure_directedOn (s : Set α) :
    DirectedOn (. ≤ .) (directedClosure s) := by classical
  rintro a ⟨Fa,hFa⟩ b ⟨Fb,hFb⟩
  use a⊔b
  constructor
  · use (Fa ⊔ Fb)
    simp
    rw [exists_and_left] at hFa
    rw [exists_and_left] at hFb
    constructor
    · exact ⟨hFa.1, hFb.1⟩
    · obtain ⟨hnFa,ha⟩ := hFa.2
      obtain ⟨hnFb,hb⟩ := hFb.2
      use (Finset.Nonempty.inl hnFa)
      rw [le_antisymm_iff]
      constructor
      · rw [sup_le_iff]
        constructor
        · rw [ha]
          exact Finset.sup'_mono _ (Finset.subset_union_left Fa Fb) _
        · rw [hb]
          exact Finset.sup'_mono _ (Finset.subset_union_right Fa Fb) _
      · simp
        intros c hc
        cases' hc with h₁ h₂
        · apply le_sup_of_le_left
          rw [ha]
          exact Finset.le_sup'_of_le _ h₁ (Eq.le rfl)
        · apply le_sup_of_le_right
          rw [hb]
          exact Finset.le_sup'_of_le _ h₂ (Eq.le rfl)
  · exact ⟨le_sup_left,le_sup_right⟩

lemma subset_toDirectedSet {s : Set α} :
    s ⊆ directedClosure s := by
  intro a ha
  rw [directedClosure]
  simp only [id_eq, exists_and_left, Set.mem_setOf_eq]
  use ({a} : Finset α)
  constructor
  · exact Iff.mpr Finset.singleton_subset_set_iff ha
  · use (Finset.singleton_nonempty a)
    rfl

@[simp] lemma Set_DirectedSet_upperBounds (s : Set α) :
    upperBounds (directedClosure s) = upperBounds s := by
  rw [subset_antisymm_iff]
  constructor
  · exact upperBounds_mono_set subset_toDirectedSet
  · intro u hu
    rw [mem_upperBounds]
    intro b hb
    obtain ⟨Fb,⟨H,hFb⟩⟩ := hb
    rw [hFb.2, Finset.sup'_le_iff]
    intro c hc
    exact hu (hFb.1 hc)

@[simp] lemma Set_DirectedSet_LUB [SemilatticeSup α] {s : Set α} {u : α} :
    IsLUB (directedClosure s) u ↔ IsLUB s u := by
  constructor
  · intro h
    constructor
    · rw [← Set_DirectedSet_upperBounds]
      exact Set.mem_of_mem_inter_left h
    · intro v hv
      rw [← Set_DirectedSet_upperBounds] at hv
      exact Iff.mpr (isLUB_le_iff h) hv
  · intro hsu
    constructor
    · rw [Set_DirectedSet_upperBounds, mem_upperBounds]
      exact hsu.1
    · rw [mem_lowerBounds]
      intro b hb
      rw [isLUB_le_iff hsu]
      exact upperBounds_mono_set subset_toDirectedSet hb

/--
A join semi-lattice where every directed subset has a least upper bound is automatically complete
-/
def SemilatticeSup.toCompleteSemilatticeSup (dSup : Set α → α)
    (h : ∀ d, DirectedOn (. ≤ .) d → IsLUB d (dSup d)) : CompleteSemilatticeSup α where
  sSup := fun s => dSup (directedClosure s)
  le_sSup := by
    intros s a ha
    have e1: IsLUB (directedClosure s) (dSup (directedClosure s)) := by
      rw [← Set_DirectedSet_LUB]
      exact Iff.mpr Set_DirectedSet_LUB (h (directedClosure s) (directedClosure_directedOn s))
    simp only [ge_iff_le]
    rw [IsLUB, IsLeast] at e1
    exact e1.1 (subset_toDirectedSet ha)
  sSup_le := by
    intros s a ha
    have e1: IsLUB (directedClosure s) (dSup (directedClosure s)) := by
      rw [← Set_DirectedSet_LUB]
      exact Iff.mpr Set_DirectedSet_LUB (h (directedClosure s) (directedClosure_directedOn s))
    simp only [ge_iff_le]
    rw [isLUB_le_iff e1, Set_DirectedSet_upperBounds]
    exact ha

end SemilatticeSup

section CompletePartialOrder

/--
Complete partial orders are partial orders where every directed set has a least upper bound.
-/
class CompletePartialOrder (α : Type*) extends PartialOrder α where
  /-- The supremum of an increasing sequence -/
  dSup : Set α → α
  /-- For each directed set `d`, `dSup d` is the least upper bound of `d` -/
  is_LUB: ∀ d, DirectedOn (. ≤ .) d → IsLUB d (dSup d)

variable {α : Type*}

/-
A complete lattice is a complete partial order
-/
instance [CompleteLattice α] : CompletePartialOrder α := {
  dSup := fun d => sSup d,
  is_LUB := fun d => by
    intro _
    exact ⟨fun _ ↦ le_sSup, fun x a ↦ sSup_le a⟩
}

variable [CompletePartialOrder α]

lemma CompletePartialOrder.le_dSup  (d : Set α) (hd: DirectedOn (. ≤ .) d) :
  ∀ a ∈ d, a ≤ dSup d := fun _ ha => (is_LUB d hd).1 ha

lemma CompletePartialOrder.dSup_le  (d : Set α) (hd: DirectedOn (. ≤ .) d)
  (x : α) : (∀ a ∈ d, a  ≤ x) → dSup d ≤ x := fun h => (is_LUB d hd).2 h

/-
Scott continuity takes on a simpler form in complete partial orders
-/
lemma CompletePartialOrder.ScottContinuous {β : Type*} [Preorder β] {f : α → β} :
    ScottContinuous f ↔
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (. ≤ .) d → IsLUB (f '' d) (f (dSup d)) := by
  constructor
  · intros h d hd₁ hd₂
    apply h hd₁ hd₂ (is_LUB d hd₂)
  · intro h
    rw [_root_.ScottContinuous]
    intros d hne hd a hda
    have e1: a = (dSup d) := by apply IsLUB.unique hda (is_LUB d hd)
    rw [e1]
    exact h hne hd

open OmegaCompletePartialOrder

/-
A complete partial order is a ω-complete partial order
-/
instance : OmegaCompletePartialOrder α where
  ωSup := fun c => CompletePartialOrder.dSup (Set.range c)
  le_ωSup := fun c => fun i =>
      CompletePartialOrder.le_dSup (Set.range c) (IsChain.directedOn (Chain.isChain_range c)) (c i)
    (by rw [Set.mem_range]; use i)
  ωSup_le := fun c => fun x => by
    intros h
    apply CompletePartialOrder.dSup_le (Set.range c) (IsChain.directedOn (Chain.isChain_range c)) x
    intros a ha
    rw [Set.mem_range] at ha
    obtain ⟨i,hi⟩:= ha
    rw [← hi]
    exact h i

end CompletePartialOrder
