import Mathlib.Tactic.Linter.UnusedSetOptionIn

/--
warning: unused 'set_option maxHeartbeats' in 'example'
note: this linter can be disabled with `set_option linter.unusedSetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 2 in
example : True := .intro

set_option maxHeartbeats 1

set_option maxHeartbeats 2 in
example : True := .intro
