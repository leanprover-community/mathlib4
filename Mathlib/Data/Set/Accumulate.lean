/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.PartialSups

/-!
# Accumulate

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.

This is closely related to the function `partialSups`, although these two functions have
slightly different typeclass assumptions and API. `partialSups_eq_accumulate` shows
that they coincide on `ℕ`.
-/

@[expose] public section


variable {α β : Type*} {s : α → Set β}

namespace Set

/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y

@[deprecated (since := "2025-12-14")] alias Accumulate := accumulate

theorem accumulate_def [LE α] {x : α} : accumulate s x = ⋃ y ≤ x, s y :=
  rfl

@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ y ≤ x, z ∈ s y := by
  simp_rw [accumulate_def, mem_iUnion₂, exists_prop]

theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ accumulate s x := fun _ => mem_biUnion le_rfl

theorem accumulate_subset_iUnion [LE α] (x : α) : accumulate s x ⊆ ⋃ i, s i :=
  (biUnion_subset_biUnion_left (subset_univ _)).trans_eq (biUnion_univ _)

theorem monotone_accumulate [Preorder α] : Monotone (accumulate s) := fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy

@[gcongr]
theorem accumulate_subset_accumulate [Preorder α] {x y} (h : x ≤ y) :
    accumulate s x ⊆ accumulate s y :=
  monotone_accumulate h

theorem biUnion_accumulate [Preorder α] (x : α) : ⋃ y ≤ x, accumulate s y = ⋃ y ≤ x, s y := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

theorem iUnion_accumulate [Preorder α] : ⋃ x, accumulate s x = ⋃ x, s x := by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate

@[simp]
lemma accumulate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : accumulate s ⊥ = s ⊥ := by
  simp [Set.accumulate_def]

@[simp]
lemma accumulate_zero_nat (s : ℕ → Set β) : accumulate s 0 = s 0 := by
  simp [accumulate_def]

open Function in
theorem disjoint_accumulate [Preorder α] (hs : Pairwise (Disjoint on s)) {i j : α} (hij : i < j) :
    Disjoint (accumulate s i) (s j) := by
  apply disjoint_left.2 (fun x hx ↦ ?_)
  simp only [accumulate, mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hx⟩
  exact disjoint_left.1 (hs (hk.trans_lt hij).ne) hx

theorem accumulate_succ (u : ℕ → Set α) (n : ℕ) :
    accumulate u (n + 1) = accumulate u n ∪ u (n + 1) := biUnion_le_succ u n

lemma partialSups_eq_accumulate (f : ℕ → Set α) :
    partialSups f = accumulate f := by
  ext n
  simp [partialSups_eq_sup_range, accumulate, Nat.lt_succ_iff]

end Set
