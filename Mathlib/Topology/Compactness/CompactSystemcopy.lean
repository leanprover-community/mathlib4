/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.Set.Dissipate

variable {α : Type*} (p : ℕ → (ℕ → α) → Prop)

variable (h0 : ∃ x : (ℕ → α), p 0 x)
  (h : ∀ (n : ℕ) (x : (ℕ → α)) (hx : p n x),
    ∃ y, p (n + 1) (Function.update x n y))

-- p n x ↔ (∀ k < n, K k ∈ β k) ∧ (r n K)

noncomputable def m' : (n : ℕ) → ((x : ℕ → α) ×' (p n x))
  | 0 => ⟨h0.choose, h0.choose_spec⟩
  | n + 1 => by
    have g := h n (m' n).1 (m' n).2
    refine ⟨Function.update (m' n).1 n g.choose, g.choose_spec⟩






def join {n : ℕ} (K' : (k : ℕ) → Set α) (hK' : ∀ k, K' k ∈ L k) (K : Set α) (hK : K ∈ L (n + 1))
    (k : ℕ) : Set α := dite (k < n + 1) (fun c ↦ K' k) (fun c ↦ K)

lemma join_of_lt_succ {n : ℕ} (K' : (k : ℕ)  → (L k)) (K : L (n + 1)) {j : ℕ} (hj : j < n + 1) :
    join K' K j (lt_trans hj (lt_add_one (n + 1))) = K' j := by
  simp only [join, dite_eq_left_iff, not_lt]
  intro h
  linarith

lemma join_of_eq_succ {n : ℕ} (K' : (k : ℕ)  → (L k)) (K : L (n + 1)) :
    join K' K (n + 1) (lt_add_one (n + 1)) = K := by
  simp [join]

lemma l {n : ℕ} (K' : (k : ℕ) → (L k)) (s : Set α) :
  ⋂ (k : ℕ) (hk : k < n + 1), (K' k) ∩ ⋃₀ (L (n + 1)) ∩ s ⊆
    ⋃ (a : L (n + 1)), ⋂ (k : ℕ) (hk : k < n + 2), (join K' a k hk) ∩ s
     := by
  intro x
  simp only [mem_iInter, mem_inter_iff, mem_sUnion, Finset.mem_coe, mem_iUnion, Subtype.exists]
  intro h
  obtain h₁ : ∀ i < n + 1, (x ∈ ((K' i) : Set α)) := by exact fun i hi ↦ (h i hi).1.1
  obtain h₂ : ∃ t ∈ (L (n + 1) : Set (Set α)), x ∈ t:= (h 0 (zero_lt_succ n)).1.2
  rcases h₂ with ⟨t, ht, j⟩

  sorry

example (s t : Set α) : s = t ↔ s ⊆ t ∧ t ⊆ s := by exact Subset.antisymm_iff

lemma iUnion_join {n : ℕ} (K' : (k : ℕ) → (L k)) (s : Set α) :
  ⋃ (a : L (n + 1)), ⋂ (k : ℕ) (hk : k < n + 2), (join K' a k hk) ∩ s =
    ⋂ (k : ℕ) (hk : k < n + 1), (K' k) ∩ ⋃₀ (L (n + 1)) ∩ s := by
  apply Subset.antisymm_iff.mpr
  simp only [subset_iInter_iff, subset_inter_iff, iUnion_subset_iff, Subtype.forall]
  refine ⟨fun i hi ↦ ⟨⟨?_, ?_⟩, ?_⟩, fun x hx ↦ ?_⟩
  · intro K hK
    intro x hx
    simp only [mem_iInter, mem_inter_iff] at *
    specialize hx i (lt_trans hi <| lt_add_one (n + 1))
    rw [join_of_lt_succ K' ⟨K, hK⟩ hi] at hx
    exact hx.1
  · intro K hK
    intro x hx
    simp only [mem_iInter, mem_inter_iff, mem_sUnion, Finset.mem_coe] at *
    specialize hx (n + 1) (lt_add_one (n + 1))
    rw [join_of_eq_succ] at hx
    use K
    exact ⟨hK, hx.1⟩
  · intro K hK x h
    simp? at h
    refine (h 0 (zero_lt_succ (n + 1))).2
  · simp only [mem_iInter, mem_inter_iff, mem_sUnion, Finset.mem_coe, mem_iUnion,
    Subtype.exists] at *
    obtain h₁ : ∀ i < n + 1, (x ∈ ((K' i) : Set α)) := by exact fun i hi ↦ (hx i hi).1.1
    obtain h₂ := (hx 0 (zero_lt_succ n)).1.2
    obtain h₃ := (hx 0 (zero_lt_succ n)).2
    rcases h₂ with ⟨t, ht, j⟩
    use t, ht
    intro i hi
    by_cases g : i < n + 1
    · rw [join_of_lt_succ K' ⟨t, ht⟩ g]
      exact ⟨(hx i g).1.1, (hx i g).2⟩
    · have g' : i = n + 1 := by linarith
      obtain h₄ := join_of_eq_succ K' ⟨t, ht⟩
      have h₅ : (join K' ⟨t, ht⟩ i hi) = g'.symm ▸ join K' ⟨t, ht⟩ (n + 1) (lt_add_one (n + 1))  :=  by sorry
      rw [h₅]

      rw [join_of_eq_succ K' ⟨t, ht⟩]
      refine ⟨?_, h₃⟩


      sorry




    simp only [mem_iInter, mem_inter_iff] at *

    sorry

  simp only [mem_iUnion, mem_iInter, mem_inter_iff, Subtype.exists, mem_sUnion, Finset.mem_coe]
  refine ⟨fun h i hi ↦ ⟨⟨?_, ?_⟩, ?_⟩ , fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨K, ⟨hK, h'⟩⟩ := h
    specialize h' i (lt_trans hi <| lt_add_one (n + 1))
    rw [join_of_lt_succ K' ⟨K, hK⟩ hi] at h'
    exact h'.1
  · obtain ⟨K, ⟨hK, h'⟩⟩ := h
    specialize h' (n + 1) (lt_add_one (n + 1))
    rw [join_of_eq_succ] at h'
    use K
    exact ⟨hK, h'.1⟩
  · obtain ⟨K, ⟨hK, h'⟩⟩ := h
    refine (h' 0 (zero_lt_succ (n + 1))).2
  · obtain h₁ : ∀ i < n + 1, (x ∈ ((K' i) : Set α)) := by exact fun i hi ↦ (h i hi).1.1
    obtain h₂ : ∃ t ∈ (L (n + 1) : Set (Set α)), x ∈ t:= (h 0 (zero_lt_succ n)).1.2
    change ∃ t, t ∈ (L (n + 1) : Set (Set α)) ∧ x ∈ t at h₂
    rcases h₂ with ⟨t, ht, j⟩
    sorry
  · sorry
  · sorry
