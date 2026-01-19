import Mathlib.Util.TransImports

/--
info: 'MathlibTest.TransImports' has at most 2000 transitive imports

2 starting with "Mathlib.Tactic.Linter.H":
[Mathlib.Tactic.Linter.HashCommandLinter, Mathlib.Tactic.Linter.Header]
-/
#guard_msgs in
#trans_imports "Mathlib.Tactic.Linter.H" at_most 2000
