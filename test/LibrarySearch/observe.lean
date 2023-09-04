import Mathlib.Tactic.Observe

example (x y : Nat) : True := by
  observe h : x + y = y + x
  guard_hyp h : x + y = y + x
  trivial
