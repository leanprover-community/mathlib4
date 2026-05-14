/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module

public import Mathlib.Order.PartialSups
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Accumulate

The function `accumulate` takes `s : α → Set β` with `LE α` and returns `⋃ y ≤ x, s y`.
It is related to `dissipate s := ⋂ y ≤ x, s y`.

`accumulate` is closely related to the function `partialSups`, although these two functions have
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

theorem accumulate_eq_biInter_lt {s : ℕ → Set β} {n : ℕ} : accumulate s n = ⋃ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, accumulate]

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

@[simp]
theorem biUnion_accumulate [Preorder α] (x : α) : ⋃ y ≤ x, accumulate s y = ⋃ y ≤ x, s y := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate

@[simp]
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

@[simp]
theorem accumulate_succ (u : ℕ → Set α) (n : ℕ) :
    accumulate u (n + 1) = accumulate u n ∪ u (n + 1) := biUnion_le_succ u n

lemma partialSups_eq_accumulate (f : ℕ → Set α) :
    partialSups f = accumulate f := by
  ext n
  simp [partialSups_eq_sup_range, accumulate, Nat.lt_succ_iff]

/-- For a directed set of sets `s : ℕ → Set α` and `n : ℕ`, there exists `m : ℕ` (maybe
larger than `n`) such that `accumulate s n ⊆ s m`. -/
lemma exists_subset_accumulate_of_directed {s : ℕ → Set α}
  (hd : Directed (· ⊆ ·) s) (n : ℕ) : ∃ m, accumulate s n ⊆ s m := by
  induction n with
  | zero => use 0; simp [accumulate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    obtain ⟨k, hk⟩ := hd m (n + 1)
    simp at hk
    exact ⟨k, by simp; grind⟩

lemma directed_accumulate {s : ℕ → Set α} : Directed (· ⊆ ·) (accumulate s) :=
  monotone_accumulate.directed_le

lemma exists_accumulate_eq_univ_iff_of_directed {s : ℕ → Set α} (hd : Directed (· ⊆ ·) s) :
    (∃ n, accumulate s n = univ) ↔ ∃ n, s n = univ := by
  refine ⟨?_, fun ⟨n, hn⟩ ↦ ⟨n,
    subset_antisymm (subset_univ _) (hn.symm.le.trans subset_accumulate)⟩⟩
  contrapose!
  intro h n
  obtain ⟨m, hm⟩ := exists_subset_accumulate_of_directed hd n
  grind

end Set
