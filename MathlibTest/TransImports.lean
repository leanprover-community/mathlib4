import Mathlib.Util.TransImports

/--
info: 'MathlibTest.TransImports' has at most 1000 transitive imports

4 starting with "Lean.Elab.I":
[Lean.Elab.InfoTree, Lean.Elab.InfoTree.InlayHints, Lean.Elab.InfoTree.Main, Lean.Elab.InfoTree.Types]
-/
#guard_msgs in
#trans_imports "Lean.Elab.I" at_most 1000
