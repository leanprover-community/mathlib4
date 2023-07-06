import Mathlib.Tactic.Consume

structure a where
  l : Nat := by fail
  k : Nat := by exact 2

example : a := by
  constructor
  guard_target = Nat
  sorry
  done
