import Mathlib.Tactic.Trace

set_option linter.unusedTactic false

/--
info: 7
-/
#guard_msgs in
example : True := by
  trace 2 + 2 + 3
  trivial

/--
info: hello world
-/
#guard_msgs in
example : True := by
  trace "hello" ++ " world"
  trivial
