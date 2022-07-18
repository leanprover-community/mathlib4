import Mathlib.Tactic.Rename

example (a : Nat) (b : Int) : Int × Nat := by
  rename' a => b, b => a
  exact (a, b)
