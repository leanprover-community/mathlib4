import Mathlib.Tactic.CancelDenoms
import Mathlib.Tactic.Ring

variable {α : Type u} [LinearOrderedField α] (a b c d : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h

example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b := by
  cancel_denoms
  rw [← h]
  ring
