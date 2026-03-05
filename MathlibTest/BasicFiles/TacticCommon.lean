module

import Mathlib.Tactic.Common

/-! Checks that some utilities are available already when importing `Mathlib.Tactic.Common`. -/

#guard_msgs (substring := true) in
#loogle

#guard_msgs (substring := true) in
#find Nat → Nat → Nat

#guard_msgs (substring := true) in
theorem test_check_tactic : True := by
  -- `#check` is defined in Core, but `#check` as a tactic is defined in Mathlib
  #check trivial
  trivial

#guard_msgs (substring := true) in
#simp only [] => 0

#guard_msgs (substring := true) in
whatsnew in
theorem test_whatsnew : True := trivial

#guard_msgs (substring := true) in
#count_heartbeats in
theorem test_count_heartbeats : True := trivial

#guard_msgs (substring := true) in
#print sorries in
theorem test_print_sorries : True := sorry

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Tactic.Common] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
