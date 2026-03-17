module

import Mathlib.Init

/-! Checks that some utilities are available already when importing `Mathlib.Init`. -/

#guard_msgs (substring := true) in
#help tactic test_help_tactic

#guard_msgs (substring := true) in
#help command test_help_command

#guard_msgs (substring := true) in
#help attr test_help_attr

#guard_msgs (substring := true) in
#lint

#guard_msgs (substring := true) in
#redundant_imports

-- `#min_imports` and `#min_imports in` are defined in different places, we check them both
#guard_msgs (substring := true) in
#min_imports in
#min_imports

#guard_msgs (substring := true) in
#find_home Nat

#guard_msgs (substring := true) in
#import_diff

proof_wanted please_prove_this : True

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Init] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
