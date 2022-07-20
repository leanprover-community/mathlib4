import Mathlib.Tactic.Trace

example : True := by
  trace 2 + 2 + 3
  trivial

example : True := by
  trace "hello" ++ " world"
  trivial
