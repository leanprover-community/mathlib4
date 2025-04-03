import Mathlib.Tactic.AutoInduction.Attr

/-!

## TODOS

- check if variable name exists in `autoinduction` attribute

-/

set_option autoImplicit false
set_option linter.unusedTactic false

open Lean Elab Tactic Meta

def foobar' (n : Nat := by simp) : Nat := n

@[autoinduction (foo := by omega) (bla := by simp)]
theorem foobar (foo bla : Nat) : foo = bla :=
  sorry

#autoindprinciples
