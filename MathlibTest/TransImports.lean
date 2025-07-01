import Mathlib.Util.TransImports

/--
info: 'MathlibTest.TransImports' has at most 1000 transitive imports

2 starting with "Mathlib.Tactic.Linter.H":
[Mathlib.Tactic.Linter.HashCommandLinter, Mathlib.Tactic.Linter.Header]
-/
#guard_msgs in
#trans_imports "Mathlib.Tactic.Linter.H" at_most 1000
