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

section SemilatticeSup

structure DirectedSet (α : Type _) [PartialOrder α] where
  set : Set α
  directed : DirectedOn (. ≤ .) set

variable [SemilatticeSup α]

/--
Every subset of a join-semilattice generates a directed set
-/
def Set.ToDirectedSet (s : Set α) : DirectedSet α := {
  set := { a | ∃ F : Finset α, ∃ H : F.Nonempty, ↑F ⊆ s ∧  a = F.sup' H id   },
  directed := by classical
    intros a ha b hb
    simp at ha hb
    obtain ⟨Fa,hFa⟩ := ha
    obtain ⟨Fb,hFb⟩ := hb
    use a⊔b
    constructor
    · simp
      use (Fa ⊔ Fb)
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
            exact Finset.le_sup'_of_le _ h₁ (Eq.le rfl)
          · apply le_sup_of_le_right
            rw [hb]
            exact Finset.le_sup'_of_le _ h₂ (Eq.le rfl)
    · constructor
      · exact le_sup_left
      · exact le_sup_right
}

lemma Set_subseteq_DirectedSet {s : Set α} :
    s ⊆ ↑(Set.ToDirectedSet s).set := by
  intro a ha
  rw [Set.ToDirectedSet]
  simp only [id_eq, exists_and_left, Set.mem_setOf_eq]
  use ({a} : Finset α)
  constructor
  · exact Iff.mpr Finset.singleton_subset_set_iff ha
  · use (Finset.singleton_nonempty a)
    rfl

lemma Set_DirectedSet_upperBounds {s : Set α} :
    upperBounds (Set.ToDirectedSet s).set = upperBounds s := by
  rw [subset_antisymm_iff]
  constructor
  · exact upperBounds_mono_set Set_subseteq_DirectedSet
  · intro u hu
    rw [mem_upperBounds]
    intro b hb
    obtain ⟨Fb,⟨H,hFb⟩⟩ := hb
    rw [hFb.2, Finset.sup'_le_iff]
    intro c hc
    exact hu (hFb.1 hc)

lemma Set_DirectedSet_LUB [SemilatticeSup α] {s : Set α} {u : α} : IsLUB s u ↔
    IsLUB (Set.ToDirectedSet s).set u := by
  constructor
  · intro hsu
    constructor
    · rw [Set_DirectedSet_upperBounds, mem_upperBounds]
      exact hsu.1
    · rw [mem_lowerBounds]
      intro b hb
      rw [isLUB_le_iff hsu]
      exact upperBounds_mono_set Set_subseteq_DirectedSet hb
  · intro h
    constructor
    · rw [← Set_DirectedSet_upperBounds]
      exact Set.mem_of_mem_inter_left h
    · intro v hv
      rw [← Set_DirectedSet_upperBounds] at hv
      exact Iff.mpr (isLUB_le_iff h) hv

instance (dSup : DirectedSet α → α)
    (h : ∀ (d : DirectedSet α), IsLUB d.set (dSup d)) : CompleteSemilatticeSup α where
  sSup := fun s => dSup (Set.ToDirectedSet s)
  le_sSup := by
    intros s a ha
    have e1: IsLUB (Set.ToDirectedSet s).set (dSup (Set.ToDirectedSet s)) := by
      rw [← Set_DirectedSet_LUB]
      exact Iff.mpr Set_DirectedSet_LUB (h (Set.ToDirectedSet s))
    simp only [ge_iff_le]
    rw [IsLUB, IsLeast] at e1
    exact e1.1 (Set_subseteq_DirectedSet ha)
  sSup_le := by
    intros s a ha
    have e1: IsLUB (Set.ToDirectedSet s).set (dSup (Set.ToDirectedSet s)) := by
      rw [← Set_DirectedSet_LUB]
      exact Iff.mpr Set_DirectedSet_LUB (h (Set.ToDirectedSet s))
    simp only [ge_iff_le]
    rw [isLUB_le_iff e1, Set_DirectedSet_upperBounds]
    exact ha

end SemilatticeSup

class CompletePartialOrder (α : Type _) extends PartialOrder α where
  /-- The supremum of an increasing sequence -/
  dSup : DirectedSet α → α
  /-- For each directed set `d`, `dSup d` is the least upper bound of `d` -/
  is_LUB: ∀ d : DirectedSet α, IsLUB d.set (dSup d)

lemma CompletePartialOrder.le_dSup [CompletePartialOrder α] (d : DirectedSet α) :
    ∀ a ∈ d.set, a ≤ dSup d := fun _ ha => (is_LUB d).1 ha

lemma CompletePartialOrder.dSup_le [CompletePartialOrder α] (d : DirectedSet α) (x : α) :
    (∀ a ∈ d.set, a  ≤ x) → dSup d ≤ x := fun h => (is_LUB d).2 h

/-
A complete lattice is a complete partial order
-/
instance [CompleteLattice α] : CompletePartialOrder α := {
  dSup := fun d => sSup d.set,
  is_LUB := fun d => by
    simp
    constructor
    · exact fun _ ↦ le_sSup
    · exact fun x a ↦ sSup_le a
}

/-
Scott continuity takes on a simpler form in complete partial orders
-/
lemma CompletePartialOrder.ScottContinuous [CompletePartialOrder α] [Preorder β] {f : α → β} :
    ScottContinuous f ↔
    ∀ ⦃d : DirectedSet α⦄, d.set.Nonempty → IsLUB (f '' d.set) (f (dSup d)) := by
  constructor
  · intros h d hd
    apply h hd d.directed (is_LUB d)
  · intro h
    rw [_root_.ScottContinuous]
    intros d hne hd a hda
    let D := DirectedSet.mk d hd
    have e1: a = (dSup D) := by apply IsLUB.unique hda (is_LUB D)
    rw [e1]
    apply h
    apply hne

open OmegaCompletePartialOrder

/--
Every chain in a partial order gives rise to a directed set
-/
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
