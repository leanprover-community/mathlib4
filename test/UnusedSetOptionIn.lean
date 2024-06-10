import Mathlib.Tactic.Linter.UnusedSetOptionIn

/--
warning: unnecessary `set_option maxHeartbeats 2`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 2 in
example : True := .intro

-- Test disabling the linter.
set_option linter.unnecessarySetOptionIn false in
set_option maxHeartbeats 0 in
example : True := .intro

set_option maxHeartbeats 1

-- The linter doesn't act because of the low heartbeats count.
set_option maxHeartbeats 2 in
example : True := .intro

set_option maxHeartbeats 20000

def foo : True := by trivial

/--
warning: unnecessary `set_option genSizeOfSpec false`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
-- flag `def`s
set_option genSizeOfSpec false in
def foo' : True := by trivial

/--
warning: unnecessary `set_option genSizeOfSpec false`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
-- flag `def`s
set_option genSizeOfSpec false in
def foo'' := 0

-- The 'unnecessarySetOptionIn' linter ignores `option`s whose name contains `linter`
-- as one of their parts.  This is mostly due to difficulty in silencing linter warnings.
#guard_msgs in
set_option linter.unusedVariables false in
lemma bar (h : Nat) : True := by trivial

/--
warning: unnecessary `set_option maxHeartbeats 0`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 0 in
--set_option linter.unnecessarySetOptionIn true in
instance (priority := high) d : Inhabited Nat := ⟨0⟩

/--
warning: unnecessary `set_option maxHeartbeats 0`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 0 in
instance (priority := high) : Inhabited Nat := ⟨0⟩

/--
warning: unnecessary `set_option maxHeartbeats 0`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 0 in
instance d1 : Inhabited Nat := ⟨0⟩

/--
warning: unnecessary `set_option maxHeartbeats 0`
note: this linter can be disabled with `set_option linter.unnecessarySetOptionIn false`
-/
#guard_msgs in
set_option maxHeartbeats 0 in
instance : Inhabited Nat := ⟨0⟩
