import Mathlib.Util.TransImports

/--
info: 'MathlibTest.TransImports' has at most 500 transitive imports

3 starting with "Lean.Elab.I":
[Lean.Elab.InfoTree, Lean.Elab.InfoTree.Main, Lean.Elab.InfoTree.Types]
-/
#guard_msgs in
#trans_imports "Lean.Elab.I" at_most 500
