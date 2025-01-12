import Mathlib

variable {α : Type*} (F : α → ℕ)

example (h : ∀ n m, {a | F a ∈ Finset.Icc m n}.Finite) {m n : ℕ} :
    ∑ k ∈ Finset.Icc m n, Nat.card {a // F a = k} = Nat.card {a // F a ∈ Finset.Icc m n} := by
  classical
  have : Fintype {a | F a ∈ Finset.Icc m n} := (h n m).fintype
  have : ∀ k, Fintype {a | F a = k} := by
    intro k
    have := h k k
    rw [Finset.Icc_eq_singleton_iff.mpr ⟨rfl, rfl⟩] at this
    simp_rw [Finset.mem_singleton] at this
    exact this.fintype
  have : ∀ a ∈ {a | F a ∈ Finset.Icc m n}.toFinset, F a ∈ Finset.Icc m n := by
    intro a ha
    rwa [Set.mem_toFinset] at ha
  rw [← Set.coe_setOf, Nat.card_eq_card_toFinset, Finset.card_eq_sum_card_fiberwise this]
  refine Finset.sum_congr rfl ?_
  · intro k hk
    rw [← Set.coe_setOf, Nat.card_eq_card_toFinset]
    refine Finset.card_equiv (Equiv.refl _) ?_
    intro a
    simp at hk
    simp
    intro h
    rwa [← h] at hk

#exit

  have : ∀ a ∈ {a | F a ∈ Finset.Icc m n}.toFinset, F a ∈ Finset.Icc m n := sorry
  rw [Nat.card_eq_card_toFinset, Finset.card_eq_sum_card_fiberwise this]
  refine Finset.sum_congr rfl fun k hk ↦ ?_

  have : ∀ n m, Fintype {a | F a ∈ Finset.Icc m n} := by
    exact fun n m ↦ (h n m).fintype
  have : ∀ k ∈ Finset.Icc m n,
    {a // F a = k} ≃ Finset.filter (fun a ↦ F a = k) {a | F a ∈ Finset.Icc m n}.toFinset := sorry
  rw [Finset.sum_congr rfl]
  rotate_left
  intro k hk
  exact Nat.card_congr (this k hk)
  rw [← Finset.card_eq_sum_card_fiberwise]
