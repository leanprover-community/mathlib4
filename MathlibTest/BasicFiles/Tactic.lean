module

import Mathlib.Tactic

/-! Checks that some utilities are available already when importing `Mathlib.Tactic`. -/

/-- info: Found 0 uses among over 0 syntax declarations -/
#guard_msgs in
#find_syntax "↦" approx

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Tactic] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
