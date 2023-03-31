import Mathlib.Tactic.GPT.Sagredo.Dialog
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factors

example : ∀ N : Nat, ∃ n, N < n ∧ Prime n := by
  sagredo
