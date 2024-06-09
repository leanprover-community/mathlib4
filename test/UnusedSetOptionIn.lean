import Mathlib.Tactic.Linter.UnusedSetOptionIn

/--
warning: unused 'set_option maxHeartbeats' in 'example'
note: this linter can be disabled with `set_option linter.unusedSetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 2 in
example : True := .intro

-- Test disabling the linter.
set_option linter.unusedSetOptionIn false in
set_option maxHeartbeats 2 in
example : True := .intro

set_option maxHeartbeats 1

-- The linter doesn't act because of the low heartbeats count.
set_option maxHeartbeats 2 in
example : True := .intro

set_option maxHeartbeats 20000

def foo : True := by trivial

-- XXX: why is this line not flagged as "unnecessary"?
set_option genSizeOfSpec false in
def foo' : True := by trivial

-- This linter would generate a warning: suppressing it should not be considered unnecessary".
#guard_msgs in
set_option linter.unusedVariables false in
lemma bar (h : Nat) : True := by trivial
