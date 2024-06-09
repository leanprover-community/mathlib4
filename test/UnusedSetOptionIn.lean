import Mathlib.Tactic.Linter.UnusedSetOptionIn

/-- info: unused 'set_option' in 'example' -/
#guard_msgs in
set_option maxHeartbeats 2 in
example : True := .intro

set_option maxHeartbeats 1

set_option maxHeartbeats 2 in
example : True := .intro
