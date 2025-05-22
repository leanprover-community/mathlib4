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

The function `Dissipate` takes `s : α → Set β` with `LE α` and returns `⋂ y ≤ x, s y`.

In large parts, this file is parallel to `Mathlib.Data.Set.Accumulate`, where
`Accumulate s := ⋃ y ≤ x, s y` is defined.

-/

open Nat

variable {α β : Type*} {s : α → Set β}

namespace Set

/-- `Dissipate s` is the intersection of `s y` for `y ≤ x`. -/
def Dissipate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋂ y ≤ x, s y

@[simp]
theorem dissipate_def [LE α] {x : α} : Dissipate s x = ⋂ y ≤ x, s y := rfl

theorem dissipate_eq {s : ℕ → Set β} {n : ℕ} : Dissipate s n = ⋂ k < n + 1, s k := by
  simp_rw [Nat.lt_add_one_iff]
  rfl

theorem mem_dissipate [LE α] {x : α} {z : β} : z ∈ Dissipate s x ↔ ∀ y ≤ x, z ∈ s y := by
  simp only [dissipate_def, mem_iInter]

theorem dissipate_subset [Preorder α] {x y : α} (hy : y ≤ x) : Dissipate s x ⊆ s y :=
  biInter_subset_of_mem hy

theorem dissipate_subset_iInter [Preorder α] (x : α) : ⋂ i, s i ⊆ Dissipate s x := by
  simp only [Dissipate, subset_iInter_iff]
  exact fun x h ↦ iInter_subset_of_subset x fun ⦃a⦄ a ↦ a

theorem antitone_dissipate [Preorder α] : Antitone (Dissipate s) :=
  fun _ _ hab ↦ biInter_subset_biInter_left fun _ hz => le_trans hz hab

@[gcongr]
theorem dissipate_subset_dissipate [Preorder α] {x y} (h : y ≤ x) :
    Dissipate s x ⊆ Dissipate s y :=
  antitone_dissipate h

@[simp]
theorem biInter_dissipate [Preorder α] {s : α → Set β} {x : α} :
    ⋂ y ≤ x, Dissipate s y = Dissipate s x := by
  apply Subset.antisymm
  · apply iInter_mono fun z y hy ↦ ?_
    simp only [dissipate_def, mem_iInter] at *
    exact fun h ↦ hy h z <| le_refl z
  · simp only [subset_iInter_iff, Dissipate]
    exact fun i hi z hz ↦ biInter_subset_of_mem <| le_trans hz hi

@[simp]
theorem iInter_dissipate [Preorder α] : ⋂ x, Dissipate s x = ⋂ x, s x := by
  apply Subset.antisymm <;> simp_rw [subset_def, mem_iInter, mem_dissipate]
  · exact fun z h x' ↦ h x' x' (le_refl x')
  · exact fun z h x' y hy ↦ h y

@[simp]
lemma dissipate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : Dissipate s ⊥ = s ⊥ := by
  simp only [dissipate_def, le_bot_iff, iInter_iInter_eq_left]

open Nat

@[simp]
theorem dissipate_succ (s : ℕ → Set α) (n : ℕ) :
    Dissipate s (n + 1) = Dissipate s n ∩ s (n + 1) := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp only [mem_inter_iff, mem_iInter, Dissipate] at *
    exact ⟨fun i hi ↦ hx i <| le_trans hi <|
      le_add_right n 1, hx (n + 1) <| le_refl (n + 1)⟩
  · simp only [Dissipate, mem_inter_iff, mem_iInter] at *
    intro i hi
    by_cases h : i ≤ n
    · exact hx.1 i h
    · simp only [not_le] at h
      exact le_antisymm hi h ▸ hx.2

@[simp]
lemma dissipate_zero (s : ℕ → Set β) : Dissipate s 0 = s 0 := by
  simp [dissipate_def]

lemma exists_subset_dissipate_of_directed {s : ℕ → Set α}
  (hd : Directed (fun (x1 x2 : Set α) => x2 ⊆ x1) s) (n : ℕ) : ∃ m, s m ⊆ Dissipate s n := by
  induction n with
  | zero => use 0; simp
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    simp_rw [dissipate_succ]
    obtain ⟨k, hk⟩ := hd m (n+1)
    simp at hk
    use k
    simp only [subset_inter_iff]
    exact ⟨le_trans hk.1 hm, hk.2⟩

lemma exists_dissipate_eq_empty_iff {s : ℕ → Set α}
    (hd : Directed (fun (x1 x2 : Set α) => x2 ⊆ x1) s) :
      (∃ n, Dissipate s n = ∅) ↔ (∃ n, s n = ∅) := by
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
      rw [hk, dissipate_succ, ← hk, hn, Set.inter_empty]

lemma directed_dissipate {s : ℕ → Set α} :
    Directed (fun (x1 x2 : Set α) => x2 ⊆ x1) (Dissipate s) :=
     antitone_dissipate.directed_ge

lemma exists_dissipate_eq_empty_iff_of_directed (C : ℕ → Set α)
    (hd : Directed (fun (x1 x2 : Set α) => x2 ⊆ x1) C) :
    (∃ n, C n = ∅) ↔ (∃ n, Dissipate C n = ∅) := by
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

/-- For a ∩-stable attribute `p` on `Set α` and a sequence of sets `s` with this attribute,
`p (Dissipate s n)` holds. -/
lemma dissipate_of_piSystem {s : ℕ → Set α} {p : Set α → Prop}
    (hp : IsPiSystem p) (h : ∀ n, p (s n)) (n : ℕ) (h' : (Dissipate s n).Nonempty) :
      p (Dissipate s n) := by
  induction n with
  | zero =>
    simp only [dissipate_def, le_zero_eq, iInter_iInter_eq_left]
    exact h 0
  | succ n hn =>
    rw [dissipate_succ] at *
    apply hp (Dissipate s n) (hn (Nonempty.left h')) (s (n+1)) (h (n+1)) h'

end Set
