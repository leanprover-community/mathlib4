module

public import Mathlib.Algebra.Notation.Defs
import all Mathlib.Algebra.Notation.Defs


/-! Check that `to_additive` works well with the module system. -/

-- check that `to_additive` doesn't panic
-- check that `to_additive` doesn't turn a theorem into an axiom and errors instead
/--
error: theorem `Nat.add_comm` is declared in an imported module, and its value/proof is not available, so it cannot be translated.
Possible solutions: put this attribute in the module where the declaration was declared,avoid the module system, or run
import all Init.Data.Nat.Basic.
-/
#guard_msgs (substring := true) in
attribute [to_additive foo] Nat.add_comm

-- with import all, no error is raised
set_option linter.translateRedundant false in
attribute [to_additive bar] add_ite

#print bar
open Lean
run_meta do
  logInfo m!"{(← getEnv).contains (← resolveGlobalName `bar)[0]!.1}"


class MyRing (R : Type*) extends Add R, Mul R
#check Lean.Environment.addConstAsync
-- test name printing
/--
Failed to add declaration
dummyBar:
Application type mismatch: The argument
  inst✝.toMul
has type
  Mul F
but is expected to have type
  Add F
in the application
  @instHAdd F inst✝.toMul
---
trace: [translate] Added translation dummyFoo ↦ dummyBar
-/
#guard_msgs (substring := true) in
@[to_additive? dummyBar]
def dummyFoo {F : Type*} [MyRing F] (x : F) : F := x * x
#check Lean.Declaration

@[to_additive bar]
def duplicateName {F : Type*} [Mul F] (x : F) : F := x * x

@[to_additive bar1] private theorem foo1 {α : Type*} [Mul α] (x : α) : x * x = x * x := rfl
@[to_additive bar3] theorem foo3 {α : Type*} [Mul α] (x : α) : x * x = x * x := rfl

public section

-- to delete
open Lean
run_meta do
  logInfo m!"{(← getEnv).contains `bar}"
  logInfo m!"{(← getEnv).contains `bar1}"
  logInfo m!"{(← getEnv).contains `bar3}"
  logInfo m!"{(← getEnv).contains (← resolveGlobalName `bar)[0]!.1}"
  logInfo m!"{(← resolveGlobalName `bar1) != []}"
  logInfo m!"{(← getEnv).contains (← resolveGlobalName `bar1)[0]!.1}"
  logInfo m!"{(← getEnv).contains (← resolveGlobalName `bar3)[0]!.1}"


@[to_additive bar1] theorem foo2 {α : Type*} [Mul α] (x : α) : x * x * x = x * x * x := rfl
@[to_additive bar3] private theorem foo4 {α : Type*} [Mul α] (x : α) : x * x * x = x * x * x := rfl

end
