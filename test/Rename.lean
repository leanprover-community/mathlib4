import Mathlib.Tactic.Rename

example (a : Nat) (b : Int) : Int × Nat := by
  rename' a => c, b => d
  exact (d, c)
