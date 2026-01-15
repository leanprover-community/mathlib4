/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Peter Pfaffelhuber
-/
module

public import Mathlib.Data.Nat.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.PartialSups
public import Mathlib.MeasureTheory.PiSystem

/-!
# Accumulate and Dissiate

The function `accumulate` takes `s : α → Set β` with `LE α` and returns `⋃ y ≤ x, s y`.
The function `dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.

`accumulate` is closely related to the function `partialSups`, although these two functions have
slightly different typeclass assumptions and API. `partialSups_eq_accumulate` shows
that they coincide on `ℕ`.
-/

@[expose] public section

variable {α β : Type*} {s : α → Set β}

namespace Set

section accumulate

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

end accumulate


section dissipate

/-- `dissipate s` is the intersection of `s y` for `y ≤ x`. -/
def dissipate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋂ y ≤ x, s y

theorem dissipate_def [LE α] {x : α} : dissipate s x = ⋂ y ≤ x, s y := rfl

theorem dissipate_eq {s : ℕ → Set β} {n : ℕ} : dissipate s n = ⋂ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff, dissipate]

@[simp]
theorem dissipate_eq_accumulate_compl [LE α] {s : α → Set β} {x : α} :
     (Set.accumulate (fun y ↦ (s y)ᶜ) x)ᶜ = dissipate s x := by
  simp [accumulate_def, dissipate_def]

@[simp]
theorem accumulate_eq_dissipate_compl [LE α] {s : α → Set β} {x : α} :
     (Set.dissipate (fun y ↦ (s y)ᶜ) x)ᶜ = accumulate s x := by
  simp [accumulate_def, dissipate_def]

@[simp]
theorem mem_dissipate [LE α] {x : α} {z : β} : z ∈ dissipate s x ↔ ∀ y ≤ x, z ∈ s y := by
  simp [dissipate_def]

theorem dissipate_subset [LE α] {x y : α} (hy : y ≤ x) : dissipate s x ⊆ s y :=
  biInter_subset_of_mem hy

theorem iInter_subset_dissipate [LE α] (x : α) : ⋂ i, s i ⊆ dissipate s x := by
  simp only [dissipate, subset_iInter_iff]
  exact fun x h ↦ iInter_subset_of_subset x fun ⦃a⦄ a ↦ a

theorem antitone_dissipate [Preorder α] : Antitone (dissipate s) :=
  fun _ _ hab ↦ biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]
theorem dissipate_subset_dissipate [Preorder α] {x y} (h : y ≤ x) :
    dissipate s x ⊆ dissipate s y :=
  antitone_dissipate h

@[simp]
theorem dissipate_dissipate [Preorder α] {s : α → Set β} {x : α} :
    ⋂ y, ⋂ (_ : y ≤ x), dissipate s y = dissipate s x := by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy ↦ ?_
    simp only [mem_iInter, mem_dissipate] at *
    exact fun h ↦ hy h z (le_refl z)
  · simp only [subset_iInter_iff]
    exact fun i j ↦ dissipate_subset_dissipate j

@[simp]
theorem iInter_dissipate [Preorder α] : ⋂ x, dissipate s x = ⋂ x, s x := by
  apply Subset.antisymm <;> simp_rw [subset_def, dissipate_def, mem_iInter]
  · exact fun z h x' ↦ h x' x' (le_refl x')
  · exact fun z h x' y hy ↦ h y

@[simp]
lemma dissipate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : dissipate s ⊥ = s ⊥ := by
  simp [dissipate_def]

open Nat

@[simp]
theorem dissipate_succ (s : ℕ → Set α) (n : ℕ) :
  dissipate s (n + 1) = (dissipate s n) ∩ s (n + 1)
    := by
  ext x
  simp_all only [dissipate_def, mem_iInter, mem_inter_iff]
  grind

@[simp]
lemma dissipate_zero (s : ℕ → Set β) : dissipate s 0 = s 0 := by
  simp [dissipate_def]

/-- For a directed set of sets `s : ℕ → Set α` (i.e. `∀ i j, ∃ k, s k ⊆ s i ∩ s j`) and `n : ℕ`,
there exists `m : ℕ` (maybe larger than `n`) such that `s m ⊆ dissipate s n`. -/
lemma exists_subset_dissipate_of_directed {s : ℕ → Set α}
  (hd : Directed (fun (x y : Set α) => y ⊆ x) s) (n : ℕ) : ∃ m, s m ⊆ dissipate s n := by
  induction n with
  | zero => use 0; simp [dissipate_def]
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    simp_rw [dissipate_succ]
    obtain ⟨k, hk⟩ := hd m (n+1)
    simp only at hk
    use k
    simp only [subset_inter_iff]
    exact ⟨le_trans hk.1 hm, hk.2⟩

lemma directed_dissipate {s : ℕ → Set α} :
    Directed (fun (x y : Set α) => y ⊆ x) (dissipate s) :=
  antitone_dissipate.directed_ge

lemma exists_dissipate_eq_empty_iff_of_directed (C : ℕ → Set α)
    (hd : Directed (fun (x y : Set α) => y ⊆ x) C) :
    (∃ n, dissipate C n = ∅) ↔ (∃ n, C n = ∅) := by
  refine ⟨?_, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩
  · rw [← not_imp_not]
    push_neg
    intro h n
    obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
    exact Set.Nonempty.mono hm (h m)
  · exact subset_eq_empty (dissipate_subset (Nat.le_refl n)) hn

/-- For a ∩-stable set of sets `p` on `α` and a sequence of sets `s` with this attribute,
`dissipate s n` belongs to `p`. -/
lemma IsPiSystem.dissipate_mem {s : ℕ → Set α} {p : Set (Set α)}
    (hp : IsPiSystem p) (h : ∀ n, s n ∈ p) (n : ℕ) (h' : (dissipate s n).Nonempty) :
      (dissipate s n) ∈ p := by
  induction n with
  | zero =>
    simp only [dissipate_def, Nat.le_zero_eq, iInter_iInter_eq_left]
    exact h 0
  | succ n hn =>
    rw [dissipate_succ] at *
    apply hp (dissipate s n) (hn (Nonempty.left h')) (s (n+1)) (h (n+1)) h'

end dissipate

end Set
