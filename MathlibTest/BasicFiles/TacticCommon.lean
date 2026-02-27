module

import Mathlib.Tactic.Common

/-! Checks that some utilities are available already when importing `Mathlib.Tactic.Common`. -/

/-- info: Loogle Usage -/
#guard_msgs (substring := true) in
#loogle

/-- Nat.add: ℕ → ℕ → ℕ -/
#guard_msgs (substring := true) in
#find Nat → Nat → Nat

/-- info: trivial : True -/
#guard_msgs (substring := true) in
theorem test_check_tactic : True := by
  -- `#check` is defined in Core, but `#check` as a tactic is defined in Mathlib
  #check trivial
  trivial

/-- info: 0 -/
#guard_msgs in
#simp only [] => 0

/-- theorem test_whatsnew : True -/
#guard_msgs (substring := true) in
whatsnew in
theorem test_whatsnew : True := trivial

/-- info: Used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats approximately in
theorem test_count_heartbeats : True := trivial

/--
info: Declarations are sorry-free!
---
warning: declaration uses `sorry`
-/
#guard_msgs in
#print sorries in
theorem test_print_sorries : True := by
  sorry

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Tactic.Common] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
