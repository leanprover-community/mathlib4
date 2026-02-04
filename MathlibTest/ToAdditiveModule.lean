module

public import Mathlib.Algebra.Notation.Defs

-- check that Lean doesn't panic
-- check that Lean doesn't turn a theorem into an axiom and errors instead
/--
error: theorem Nat.add_comm is declared in an imported module
-/
#guard_msgs (substring := true) in
attribute [to_additive foo] Nat.add_comm

class MyRing (R : Type*) extends Add R, Mul R


-- test name printing
/--
Failed to add declaration
bar:
Application type mismatch: The argument
  inst✝.toMul
has type
  Mul F
but is expected to have type
  Add F
in the application
  @instHAdd F inst✝.toMul
---
trace: [translate] Added translation foo ↦ bar
-/
#guard_msgs (substring := true) in
@[to_additive? bar]
def foo {F : Type*} [MyRing F] (x : F) : F := x * x
