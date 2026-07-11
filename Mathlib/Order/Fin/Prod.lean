
/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Order.Fin.Basic

/-!
# Property of the order on a binary product of `Fin` types

If elements `(x₀, y₀)` and `(x₂, y₂)` in `Fin p × Fin q` satisfy
`(x₀, y₀) ≤ (x₂, y₂)` and `x₀ + y₀ + 2 ≤ x₂ + y₂`, then
there exists `(x₁, y₁)` such that `(x₀, y₀) < (x₁, y₁) < (x₂, y₂)`.

(This is used in `Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean`.)

-/

public lemma Fin.prod_exists_lt_lt_of_le_of_le
    {p q : ℕ} (k₀ k₂ : Fin p × Fin q) (h₀₂ : k₀ ≤ k₂)
    (h : k₀.1.val + k₀.2.val + 2 ≤ k₂.1.val + k₂.2.val) :
    ∃ k₁, k₀ < k₁ ∧ k₁ < k₂ := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := p) (by grind)
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := q) (by grind)
  obtain ⟨x₀, y₀⟩ := k₀
  obtain ⟨x₂, y₂⟩ := k₂
  simp only [Prod.le_def] at h₀₂ h
  obtain ⟨hx, hy⟩ := h₀₂
  obtain hx' | rfl := hx.lt_or_eq
  · obtain hy' | rfl := hy.lt_or_eq
    · exact ⟨⟨x₀, y₂⟩, by aesop⟩
    · obtain ⟨x₂', rfl⟩ := x₂.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hx')
      refine ⟨⟨x₂'.castSucc, y₀⟩, ?_⟩
      rw [Fin.val_succ] at h
      simp [Fin.lt_def]
      grind
  · obtain ⟨y₂', rfl⟩ := y₂.eq_succ_of_ne_zero (by grind)
    refine ⟨⟨x₀, y₂'.castSucc⟩, ?_⟩
    rw [Fin.val_succ] at h
    simp [Fin.lt_def]
    lia
