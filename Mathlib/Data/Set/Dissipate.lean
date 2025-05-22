/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Directed
import Mathlib.MeasureTheory.PiSystem

/-!
# Dissipate

The function `dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.

In large parts, this file is parallel to `Mathlib.Data.Set.Accumulate`, where
`Accumulate s := ⋃ y ≤ x, s y` is defined.

-/

open Nat

variable {α β : Type*} {s : α → Set β}

namespace Set

/-- `dissipate s` is the intersection of `s y` for `y ≤ x`. -/
def dissipate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋂ y ≤ x, s y

@[simp]
theorem dissipate_def [LE α] {x : α} : dissipate s x = ⋂ y ≤ x, s y := rfl

theorem dissipate_eq {s : ℕ → Set β} {n : ℕ} : dissipate s n = ⋂ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff]
  rfl

theorem mem_dissipate [LE α] {x : α} {z : β} : z ∈ dissipate s x ↔ ∀ y ≤ x, z ∈ s y := by
  simp only [dissipate_def, mem_iInter]

theorem dissipate_subset [Preorder α] {x y : α} (hy : y ≤ x) : dissipate s x ⊆ s y :=
  biInter_subset_of_mem hy

theorem iInter_subset_dissipate [Preorder α] (x : α) : ⋂ i, s i ⊆ dissipate s x := by
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
    ⋂ y, ⋂ (_ : y ≤ x), ⋂ y_1, ⋂ (_ : y_1 ≤ y), s y_1 = ⋂ y, ⋂ (_ : y ≤ x), s y := by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy ↦ ?_
    simp only [mem_iInter] at *
    exact fun h ↦ hy h z <| le_refl z
  · simp only [subset_iInter_iff]
    exact fun i hi z hz ↦ biInter_subset_of_mem <| le_trans hz hi

@[simp]
theorem iInter_dissipate [Preorder α] : ⋂ x, ⋂ y, ⋂ (_ : y ≤ x), s y = ⋂ x, s x := by
  apply Subset.antisymm <;> simp_rw [subset_def, mem_iInter]
  · exact fun z h x' ↦ h x' x' (le_refl x')
  · exact fun z h x' y hy ↦ h y

lemma dissipate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : dissipate s ⊥ = s ⊥ := by
  simp only [dissipate_def, le_bot_iff, iInter_iInter_eq_left]

open Nat

@[simp]
theorem dissipate_succ (s : ℕ → Set α) (n : ℕ) :
    ⋂ i, ⋂ (_ : i ≤ n + 1), s i = (dissipate s n) ∩ s (n + 1)
    := by
  ext x
  simp_all only [dissipate_def, mem_iInter, mem_inter_iff]
  refine ⟨fun a ↦ ?_, fun a i c ↦ ?_⟩
  · simp_all only [le_refl, and_true]
    intro i i_1
    apply a i <| le_trans i_1 (le_succ n)
  · obtain ⟨left, right⟩ := a
    · by_cases h : i ≤ n
      · exact left i h
      · have h : i = n + 1 := by
          simp only [not_le] at h
          exact le_antisymm c h
        exact h.symm ▸ right

lemma dissipate_zero (s : ℕ → Set β) : dissipate s 0 = s 0 := by
  simp [dissipate_def]

lemma exists_subset_dissipate_of_directed {s : ℕ → Set α}
  (hd : Directed (fun (x y : Set α) => y ⊆ x) s) (n : ℕ) : ∃ m, s m ⊆ dissipate s n := by
  induction n with
  | zero => use 0; simp
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    simp_rw [dissipate_def, dissipate_succ]
    obtain ⟨k, hk⟩ := hd m (n+1)
    simp at hk
    use k
    simp only [subset_inter_iff]
    exact ⟨le_trans hk.1 hm, hk.2⟩

lemma exists_dissipate_eq_empty_iff {s : ℕ → Set α}
    (hd : Directed (fun (x y : Set α) => y ⊆ x) s) :
      (∃ n, dissipate s n = ∅) ↔ (∃ n, s n = ∅) := by
  refine ⟨?_, fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩⟩
  · rw [← not_imp_not]
    push_neg
    intro h n
    obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
    exact Set.Nonempty.mono hm (h m)
  · by_cases hn' : n = 0
    · rw [hn']
      exact Eq.trans (dissipate_zero s) (hn' ▸ hn)
    · obtain ⟨k, hk⟩ := exists_eq_add_one_of_ne_zero hn'
      rw [hk, dissipate_def, dissipate_succ, ← hk, hn, Set.inter_empty]

lemma directed_dissipate {s : ℕ → Set α} :
    Directed (fun (x y : Set α) => y ⊆ x) (dissipate s) :=
     antitone_dissipate.directed_ge

lemma exists_dissipate_eq_empty_iff_of_directed (C : ℕ → Set α)
    (hd : Directed (fun (x y : Set α) => y ⊆ x) C) :
    (∃ n, C n = ∅) ↔ (∃ n, dissipate C n = ∅) := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩ , ?_⟩
  · by_cases hn' : n = 0
    · rw [hn', dissipate_zero]
      exact hn' ▸ hn
    · obtain ⟨k, hk⟩ := exists_eq_succ_of_ne_zero hn'
      simp_rw [hk, succ_eq_add_one, dissipate_succ,
        ← succ_eq_add_one, ← hk, hn, Set.inter_empty]
  · rw [← not_imp_not]
    push_neg
    intro h n
    obtain ⟨m, hm⟩ := exists_subset_dissipate_of_directed hd n
    exact Set.Nonempty.mono hm (h m)


/-- For a ∩-stable set of sets `p` on `α` and a sequence of sets `s` with this attribute,
`p (dissipate s n)` holds. -/
lemma IsPiSystem.dissipate_mem {s : ℕ → Set α} {p : Set (Set α)}
    (hp : IsPiSystem p) (h : ∀ n, s n ∈ p) (n : ℕ) (h' : (dissipate s n).Nonempty) :
      (dissipate s n) ∈ p := by
  induction n with
  | zero =>
    simp only [dissipate_def, le_zero_eq, iInter_iInter_eq_left]
    exact h 0
  | succ n hn =>
    rw [dissipate_def, dissipate_succ] at *
    apply hp (dissipate s n) (hn (Nonempty.left h')) (s (n+1)) (h (n+1)) h'

end Set
