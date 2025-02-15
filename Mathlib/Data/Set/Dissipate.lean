/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Lattice

/-!
# Dissipate

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

@[simp]
theorem biInter_dissipate [Preorder α] {s : α → Set β} {x : α} :
    ⋂ y ≤ x, s y = ⋂ y ≤ x, ⋂ z ≤ y, s z := by
  apply Subset.antisymm
  · simp only [subset_iInter_iff, Dissipate]
    exact fun i hi z hz ↦ biInter_subset_of_mem <| le_trans hz hi
  · apply iInter_mono fun z y hy ↦ ?_
    simp only [mem_iInter] at *
    exact fun h ↦ hy h z <| le_refl z

theorem iInter_dissipate [Preorder α] : ⋂ x, s x = ⋂ x, Dissipate s x := by
  apply Subset.antisymm <;> simp [subset_def, mem_iInter, exists_imp, mem_dissipate]
  · exact fun z h x' y hy ↦ h y
  · exact fun z h x' ↦ h x' x' (le_refl x')

@[simp]
lemma dissipate_bot [PartialOrder α] [OrderBot α] (s : α → Set β) : Dissipate s ⊥ = s ⊥ := by
  simp [Set.dissipate_def]

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

lemma subset_of_directed {C : ℕ → Set α} (hd : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C)
    (n : ℕ) : ∃ m, ⋂ i ≤ n, C i ⊇ C m := by
  induction n with
  | zero => use 0; simp
  | succ n hn =>
    obtain ⟨m, hm⟩ := hn
    simp_rw [← dissipate_def, dissipate_succ]
    obtain ⟨k, hk⟩ := hd m (n+1)
    simp at hk
    use k
    simp only [subset_inter_iff]
    exact ⟨le_trans hk.1 hm, hk.2⟩

lemma empty_of_directed {C : ℕ → Set α} (hd : Directed (fun (x1 x2 : Set α) => x1 ⊇ x2) C) :
      (∃ n, C n = ∅) ↔ (∃ n, Dissipate C n = ∅) := by
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, ?_⟩, ?_⟩
  · by_cases hn' : n = 0
    · rw [hn']
      exact Eq.trans (dissipate_zero C) (hn' ▸ hn)
    · obtain ⟨k, hk⟩ := exists_eq_succ_of_ne_zero hn'
      rw [hk, dissipate_succ, ← succ_eq_add_one, ← hk, hn, Set.inter_empty]
  · rw [← not_imp_not]
    push_neg
    intro h n
    obtain ⟨m, hm⟩ := subset_of_directed hd n
    exact Set.Nonempty.mono hm (h m)

end Set
