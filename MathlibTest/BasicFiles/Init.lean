module

import Mathlib.Init

/-! Checks that some utilities are available already when importing `Mathlib.Init`. -/

/-- error: no tactic declarations start with exact -/
#guard_msgs in
#help tactic exact

/-- error: no command declarations start with #help -/
#guard_msgs in
#help command "#help"

/-- info: [grind]: The `[grind]` attribute -/
#guard_msgs (substring := true) in
#help attr grind

/--
info: -- Found 0 errors in 0 declarations (plus 0 automatically generated ones) in the current file with 16 linters


-- All linting checks passed!
-/
#guard_msgs in
#lint

/--
info: Found the following transitively redundant imports:
Init
-/
#guard_msgs in
#redundant_imports

-- `#min_imports` and `#min_imports in` are defined in different places, we check them both
/-- info: import ImportGraph.Tools.MinImports -/
#guard_msgs (substring := true) in
#min_imports in
#min_imports

/-- Init.Prelude -/
#guard_msgs (substring := true) in
#find_home Nat

/-- info: Found 0 additional imports: -/
#guard_msgs in
#import_diff

proof_wanted please_prove_this : True

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Init] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
