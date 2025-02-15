/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Lattice

/-!
# Accumulate

The function `Dissipate` takes a set `s` and returns `⋂ y ≤ x, s y`.
-/


variable {α β : Type*} {s : α → Set β}

namespace Set

/-- `Dissipate s` is the intersection of `s y` for `y ≤ x`. -/
def Dissipate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋂ y ≤ x, s y

theorem dissipate_def [LE α] {x : α} : Dissipate s x = ⋂ y ≤ x, s y :=
  rfl

@[simp]
theorem mem_dissipate [LE α] {x : α} {z : β} : z ∈ Dissipate s x ↔ ∀ y ≤ x, z ∈ s y := by
  simp_rw [dissipate_def, mem_iInter₂]

theorem dissipate_subset [Preorder α] {x y : α} (hy : y ≤ x): Dissipate s x ⊆ s y :=
  biInter_subset_of_mem hy

theorem dissipate_subset_iInter [Preorder α] (x : α) : ⋂ i, s i ⊆ Dissipate s x := by
  simp [Dissipate]
  exact fun x h ↦ iInter_subset_of_subset x fun ⦃a⦄ a ↦ a

theorem antitone_dissipate [Preorder α] : Antitone (Dissipate s) :=
  fun _ _ hab ↦ biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]
theorem dissipate_subset_dissipate [Preorder α] {x y} (h : y ≤ x) :
    Dissipate s x ⊆ Dissipate s y :=
  antitone_dissipate h

#check antitone_dissipate

example [Preorder α] (x : α) : x ≤ x := by exact Preorder.le_refl x

@[simp]
theorem biInter_dissipate [Preorder α] {s : α → Set β} {x : α} :
    ⋂ y ≤ x, s y = ⋂ y ≤ x, ⋂ z ≤ y, s z := by
  apply Set.Subset.antisymm
  · sorry
  · exact iInter₂_mono fun y _ => dissipate_subset (le_refl y)

    have h := fun y hy ↦ antitone_dissipate hy
    refine iInter₂_subset

--    antitone_dissipate hy

    sorry
    simp only [subset_iInter_iff, Dissipate]
    exact fun i hi z hz ↦ biInter_subset_of_mem <| le_trans hz hi
  · apply iInter_mono
    intro z y hy
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h ↦ hy h z <| le_refl z

@[simp]
theorem biInter_dissipate [Preorder α] {s : α → Set β} {x : α} :
    ⋂ y ≤ x, s y = ⋂ y ≤ x, ⋂ z ≤ y, s z := by
  apply Set.Subset.antisymm
  · simp only [subset_iInter_iff, Dissipate]
    exact fun i hi z hz ↦ biInter_subset_of_mem <| le_trans hz hi
  · apply iInter_mono
    intro z y hy
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h ↦ hy h z <| le_refl z


theorem biInter_dissipate' [Preorder α] (x : α) : ⋃ y ≤ x, Accumulate s y = ⋃ y ≤ x, s y := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

theorem iUnion_accumulate [Preorder α] : ⋃ x, Accumulate s x = ⋃ x, s x := by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate

@[simp]
lemma accumulate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : Accumulate s ⊥ = s ⊥ := by
  simp [Set.accumulate_def]

@[simp]
lemma accumulate_zero_nat (s : ℕ → Set β) : Accumulate s 0 = s 0 := by
  simp [accumulate_def]

open Function in
theorem disjoint_accumulate [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α} (hij : i < j) :
    Disjoint (Accumulate s i) (s j) := by
  apply disjoint_left.2 (fun x hx ↦ ?_)
  simp only [Accumulate, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hx⟩
  exact disjoint_left.1 (hs (hk.trans_lt hij).ne) hx

end Set
