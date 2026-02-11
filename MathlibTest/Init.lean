module

import Mathlib.Init

/-! Checks that some utilities are available when importing `Mathlib.Init` alone -/

/-- error: no tactic declarations start with exact -/
#guard_msgs in
#help tactic exact

/-- info: [grind]: The `[grind]` attribute -/
#guard_msgs (substring := true) in
#help attr grind

/-- info: -- Found 0 errors -/
#guard_msgs (substring := true) in
#lint

-- `#min_imports` and `#min_imports in` are defined in different places, we check them both
/-- info: import ImportGraph.Tools.MinImports -/
#guard_msgs (substring := true) in
#min_imports in
#min_imports

/-- info: [Init.Prelude] -/
#guard_msgs in
#find_home Nat

/-- info: Loogle Usage -/
#guard_msgs (substring := true) in
#loogle

proof_wanted please_prove_this : True

-- Guard against the shake tool modifying our imports
/--
info: [public import Init, import Mathlib.Init]
-/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
