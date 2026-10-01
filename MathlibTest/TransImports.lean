import Mathlib.Util.TransImports

/--
info: 'MathlibTest.TransImports' has at most 2000 transitive imports

3 starting with "MathlibInit.Tactic.Linter.H":
[MathlibInit.Tactic.Linter.HashCommandLinter, MathlibInit.Tactic.Linter.HaveILetI, MathlibInit.Tactic.Linter.Header]
-/
#guard_msgs in
#trans_imports "MathlibInit.Tactic.Linter.H" at_most 2000
