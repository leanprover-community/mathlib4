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
-/

structure DirectedSet (α : Type _) [PartialOrder α] where
  set : Set α
  directed : DirectedOn (. ≤ .) set



class CompletePartialOrder (α : Type _) extends PartialOrder α where
  /-- The supremum of an increasing sequence -/
  dSup : DirectedSet α → α
  /-- `dSup` is an upper bound of the increasing sequence -/
  le_dSup : ∀ d : DirectedSet α, ∀ a ∈ d.set, a ≤ dSup d
  /-- `dSup` is a lower bound of the set of upper bounds of the increasing sequence -/
  dSup_le : ∀ (d : DirectedSet α) (x), (∀ a ∈ d.set, a  ≤ x) → dSup d ≤ x

/-
A complete lattice is a complete partial order
-/
instance [CompleteLattice α] : CompletePartialOrder α := {
  dSup := fun d => sSup d.set,
  le_dSup := fun _ _ ha => le_sSup ha
  dSup_le := fun _ _ h => sSup_le_iff.mpr h
}

open OmegaCompletePartialOrder

def Chain.to_DirectedSet [PartialOrder α] (c : Chain α) : DirectedSet α := {
  set := Set.range c,
  directed := by
    intros x hx y hy
    obtain ⟨n,cn⟩ := Set.mem_range.mp hx
    obtain ⟨m,cm⟩ := Set.mem_range.mp hy
    cases' le_or_gt n m with hnm hmn
    · use y
      constructor
      · exact hy
      · simp only [le_refl, and_true]
        rw [← cn, ← cm]
        apply (c.monotone' hnm)
    · use x
      constructor
      · exact hx
      · simp
        rw [← cn, ← cm]
        apply (c.monotone' (Nat.le_of_lt hmn)) }

def Set.ToDirectedSet [Lattice α] [DecidableEq α] (s : Set α) : DirectedSet α := {
  set := { a | ∃ F : Finset α, ∃ H : F.Nonempty, ↑F ⊆ s ∧  a = F.sup' H id   },
  directed := by
    intros a ha b hb
    simp at ha hb
    obtain ⟨Fa,hFa⟩ := ha
    obtain ⟨Fb,hFb⟩ := hb
    use a⊔b
    constructor
    · simp
      use (Fa ∪ Fb)
      simp
      simp at hFa
      constructor
      · constructor
        · exact hFa.1
        · exact hFb.1
      · obtain ⟨hnFa,ha⟩ := hFa.2
        obtain ⟨hnFb,hb⟩ := hFb.2
        use (Finset.Nonempty.inl hnFa)
        rw [le_antisymm_iff]
        constructor
        · simp
          constructor
          · rw [hFa.2.2]
            apply Finset.sup'_mono
            exact Finset.subset_union_left Fa Fb
          · rw [hFb.2.2]
            apply Finset.sup'_mono
            exact Finset.subset_union_right Fa Fb
        · simp
          intros c hc
          cases' hc with h₁ h₂
          · apply le_sup_of_le_left
            rw [ha]
            apply Finset.le_sup'_of_le
            exact h₁
            exact Eq.le rfl
          · apply le_sup_of_le_right
            rw [hb]
            apply Finset.le_sup'_of_le
            exact h₂
            exact Eq.le rfl
    · constructor
      · exact le_sup_left
      · exact le_sup_right
}

lemma Chain_Set [PartialOrder α] (c : Chain α) : (Chain.to_DirectedSet c).set = Set.range c := rfl

/-
A complete partial order is a ω-complete partial order
-/
instance [CompletePartialOrder α] : OmegaCompletePartialOrder α where
  ωSup := fun c => CompletePartialOrder.dSup (Chain.to_DirectedSet c)
  le_ωSup := fun c => fun i => CompletePartialOrder.le_dSup (Chain.to_DirectedSet c) (c i)
    (by rw [Chain_Set, Set.mem_range]; use i)
  ωSup_le := fun c => fun x => by
    intros h
    apply CompletePartialOrder.dSup_le (Chain.to_DirectedSet c) x
    intros a ha
    rw [Chain_Set, Set.mem_range] at ha
    obtain ⟨i,hi⟩:= ha
    rw [← hi]
    exact h i


instance [Lattice α] (dSup : DirectedSet α → α) (h : ∀ (d : DirectedSet α), IsLUB d.set (dSup d)) :
    CompleteLattice α where
  sSup := fun s
