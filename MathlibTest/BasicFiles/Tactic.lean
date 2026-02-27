module

import Mathlib.Tactic

/-! Checks that some utilities are available already when importing `Mathlib.Tactic`. -/

@[inherit_doc] notation "test_find_syntax" => id
/-- info: Found -/
#guard_msgs (substring := true) in
#find_syntax "test_find_syntax" approx

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Tactic] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
