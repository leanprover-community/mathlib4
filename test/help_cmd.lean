import Mathlib.Tactic.HelpCmd
import Std.Tactic.GuardMsgs

#guard_msgs(error, drop info) in
#help tactic
def foo := 1
