module

public import Mathlib.Tactic.Linter.HaveLetI

/--
info: Try this:
  [apply] have : True := trivial
-/
#guard_msgs in
example : True := by
  haveI : True := trivial
  trivial
