module

public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Lean.Meta

import all Mathlib.Algebra.Notation.Defs


/-! Check that `to_additive` works well with the module system. -/

-- check that `to_additive` doesn't panic
-- check that `to_additive` doesn't turn a theorem into an axiom and errors instead
/--
error: theorem `Nat.add_comm` is declared in an imported module, and its value/proof is not available, so it cannot be translated.
Possible solutions: put this attribute in the module where the declaration was declared, avoid the module system, or run
  import all Init.Data.Nat.Basic
-/
#guard_msgs (substring := true) in
attribute [to_additive foo] Nat.add_comm

-- no error is raised, because we `import all` the file where this is declared
set_option linter.translateRedundant false in
attribute [to_additive bar] add_ite


class MyRing (R : Type*) extends Add R, Mul R

-- test name printing
/--
Failed to add declaration `dummyBar`:
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


-- no panics when the declaration exists privately

/--
warning: The translated declaration `bar` already exists. Please specify this explicitly using `@[to_additive existing]`.

Note: This linter can be disabled with `set_option linter.translateExisting false`
---
error: `to_additive` validation failed: expected
  {F : Type u_2} → [Add F] → F → F
but 'bar' has type
  ∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : Add α] (a b c : α),
    (a + if P then b else c) = if P then a + b else a + c
-/
#guard_msgs in
@[to_additive bar]
def duplicateName {F : Type*} [Mul F] (x : F) : F := x * x

@[to_additive bar1] private theorem foo1 {α : Type*} [Mul α] (x : α) : x * x = x * x := rfl
@[to_additive bar3] theorem foo3 {α : Type*} [Mul α] (x : α) : x * x = x * x := rfl

public section

open Lean

/--
warning: The translated declaration `bar1` already exists. Please specify this explicitly using `@[to_additive existing]`.

Note: This linter can be disabled with `set_option linter.translateExisting false`
---
error: `to_additive` validation failed: expected
  ∀ {α : Type u_1} [inst : Add α] (x : α), x + x + x = x + x + x
but 'bar1' has type
  ∀ {α : Type u_1} [inst : Add α] (x : α), x + x = x + x
-/
#guard_msgs in
@[to_additive bar1] theorem foo2 {α : Type*} [Mul α] (x : α) : x * x * x = x * x * x := rfl

/--
warning: The translated declaration `bar3` already exists. Please specify this explicitly using `@[to_additive existing]`.

Note: This linter can be disabled with `set_option linter.translateExisting false`
---
error: `to_additive` validation failed: expected
  ∀ {α : Type u_1} [inst : Add α] (x : α), x + x + x = x + x + x
but 'bar3' has type
  ∀ {α : Type u_1} [inst : Add α] (x : α), x + x = x + x
-/
#guard_msgs in
@[to_additive bar3] private theorem foo4 {α : Type*} [Mul α] (x : α) : x * x * x = x * x * x := rfl

end
