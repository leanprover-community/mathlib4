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

-- The bare `#min_imports` above only records a request. A module linter reports the request at
-- the end of the file, where `#guard_msgs` cannot capture the warning: report it here and clear it.
/-- warning: Imports can be reduced -/
#guard_msgs (substring := true) in
run_cmd ImportGraph.Shake.logAllMinImports #[]; ImportGraph.Shake.resetMinImports

#guard_msgs (substring := true) in
#find_home Nat

#guard_msgs (substring := true) in
#import_diff

proof_wanted please_prove_this : True

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, public meta import Init, import Mathlib.Init] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"

theorem test_type_star (α : Type*) : α = α := rfl

lemma test_lemma : True := trivial

alias test2 := test_lemma

#adaptation_note /-- This ensures that adaptation_note is available. -/
