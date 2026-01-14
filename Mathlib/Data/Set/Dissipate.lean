/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
module

public import Mathlib.Data.Set.Accumulate
public import Mathlib.MeasureTheory.PiSystem

/-!
# Dissipate

The function `dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.

In large parts, this file is parallel to `Mathlib.Data.Set.Accumulate`, where
`Accumulate s := ⋃ y ≤ x, s y` is defined.

-/

@[expose] public section

open Nat

variable {α β : Type*} {s : α → Set β}

namespace Set

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
    simp only [dissipate_def, le_zero_eq, iInter_iInter_eq_left]
    exact h 0
  | succ n hn =>
    rw [dissipate_succ] at *
    apply hp (dissipate s n) (hn (Nonempty.left h')) (s (n+1)) (h (n+1)) h'


end Set
