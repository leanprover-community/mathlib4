/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.GRW
import Mathlib.Tactic.GRW.Core
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential

private axiom test_sorry : ∀ {α}, α

private axiom α : Type
@[instance] private axiom inst : LinearOrderedCommRing α

variable (a b c d e : α)

section inequalities

example (h₁ : a ≤ b) (h₂ : b ≤ c) : a + 5 ≤ c + 6 := by
  grw [h₁, h₂]
  guard_target =ₛ c + 5 ≤ c + 6
  exact test_sorry

example (h₁ : a ≤ b) (h₂ : b ≤ c) : c + 6 > a + 5 := by
  grw [h₁, h₂]
  guard_target =ₛ c + 6 > c + 5
  exact test_sorry

example (h₁ : c ≤ b) : a + 5 ≤ b + 6 := by
  grw [← h₁]
  guard_target =ₛ a + 5 ≤ c + 6
  exact test_sorry

example (h₁ : c ≤ b) (h₂ : a + 5 < c + 6) : a + 5 < b + 6 := by
  grw [← h₁]
  guard_target =ₛ a + 5 < c + 6
  exact h₂

example (h₁ : a + e ≤ b + e) (h₂ : b < c) (h₃ : c ≤ d) : a + e ≤ d + e := by
  grw [h₂, h₃] at h₁
  guard_hyp h₁ :ₛ a + e ≤ d + e
  exact h₁

example (f g : α → α) (h : ∀ x : α, f x ≤ g x) (h₂ : g a + g b ≤ 5): f a + f b ≤ 5 := by
  grw [h]
  guard_target =ₛ g a + f b ≤ 5
  grw [h]
  guard_target =ₛ g a + g b ≤ 5
  grw [h₂]

example (f g : α → α) (h : ∀ x : α, f x < g x) : f a ≤ g b := by
  grw [h, ← h b]
  guard_target =ₛ g a ≤ f b
  exact test_sorry

example (h₁ : a ≥ b) (h₂ : 0 ≤ c) : a * c ≥ 100 - a := by
  grw [h₁]
  guard_target =ₛ b * c ≥ 100 - b
  exact test_sorry

example {n : ℕ} (bound : n ≤ 5) : n ≤ 10 := by
  have h' := (show 5 ≤ 10 by norm_num)
  grw [h'] at bound
  assumption

example (h₁ : a ≤ b) : a + 5 ≤ b + 6 := by grw [h₁, show (5 : α) ≤ 6 by norm_num]

example (h₁ : a ≤ b) : a * 5 ≤ b * 5 := by grw [h₁]

example (h₁ : a ≤ b) (h₂ : c ≥ 0) : a * c ≤ b * c := by grw [h₁]

example (h₁ : a ≤ b) : a * c ≤ b * c := by
  grw [h₁]
  guard_target =ₛ 0 ≤ c
  exact test_sorry


end inequalities

section subsets

variable (X Y Z W: Set α)

example (h₁ : X ⊆ Y) (h₂ : Y ⊆ Z) (h₃ : a ∈ X) : true := by
  grw [h₁] at h₃
  guard_hyp h₃ :ₛ a ∈ Y
  grw [h₂] at h₃
  guard_hyp h₃ :ₛ a ∈ Z
  exact test_sorry

example (h₁ : Y ⊇ W) : X ⊂ (Y ∪ Z) := by
  grw [h₁]
  guard_target =ₛ X ⊂ (W ∪ Z)
  exact test_sorry

example (h₁ : W ⊂ Y) (h₂ : X ⊂ (W ∪ Z)): X ⊂ (Y ∪ Z) := by
  grw [← h₁]
  guard_target =ₛ X ⊂ (W ∪ Z)
  exact h₂

end subsets

section reals

example (x y z w : ℝ) (h₁ : x < z) (h₂ : w ≤ y + 4) (h₃ : Real.exp z < 5 * w)
  : Real.exp x < 5 * (y + 4) := by
  grw [h₁, ← h₂]
  exact h₃

end reals
