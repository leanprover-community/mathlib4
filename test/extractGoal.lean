import Mathlib.Tactic.extractGoal
import Mathlib.Data.Nat.Basic

-- the example in the documentation for the tactic.
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k := by
  extractGoal
  exact h₀.trans h₁

-- an example with all binder types
example {α : Type u} {β : Type v} [Add α] [_h : Sub β] (f : α → β) ⦃_g : ℤ⦄ (a : α) {b : β} :
    (f a = b) ∨ True := by
  extractGoal
  exact Or.inr trivial

-- an example with a hygienic variable
example (n : ℕ) : n = n := by
  cases n
  rfl
  extractGoal
  rfl
