module

public import Mathlib.Tactic.Linter.HaveLetI

/--
info: Try this:
  [apply] have
---
info: Try this:
  [apply] let
-/
#guard_msgs in
example : True := by
  haveI : True := trivial
  letI : True := trivial
  trivial
