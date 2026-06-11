module
public import Mathlib.Tactic.Recall

@[expose] public section

/-- Test that `recall` works inside a `module` file. -/
def recallModuleTest := 42

recall recallModuleTest := 42

recall recallModuleTest : Nat
