import MathlibTest.Tactic.DuplicateDeclsAux

open Lean Mathlib.Tactic.DuplicateDecls

/--
-- MathlibTest.Tactic.DuplicateDeclsAux

one_add_one : 1 + 1 = 2
one_add_one' : 1 + 1 = 2
-/
#guard_msgs (substring := true) in
run_meta do logInfo m!"{← lintDuplicateDeclarations .theorems}"
