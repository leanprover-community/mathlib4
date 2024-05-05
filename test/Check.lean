import Mathlib.Tactic.Check
/- Override metavariable delaborator for natural metavariables to print `?m` instead
of including a unique number, for `#guard_msgs`. -/
open Lean PrettyPrinter Delaborator in @[delab mvar] def delabMVar : Delab := do
  let kind ← (← SubExpr.getExpr).mvarId!.getKind
  unless kind.isNatural do failure
  `(?m)

/-!
Basic check of `#check`
-/

/-- info: x + y : Nat -/
#guard_msgs in
example (x y : Nat) : True := by
  #check x + y
  trivial


/-!
`#check` is ok with metavariables
and `have := e` is not a substitute for `#check`
-/

/-- info: x + ?m✝ : Nat -/
#guard_msgs in
example (x : Nat) : True := by
  #check x + _
  trivial

/--
error: don't know how to synthesize placeholder
context:
x : Nat
⊢ Nat
---
error: unsolved goals
x : Nat
⊢ True
-/
#guard_msgs in
example (x : Nat) : True := by
  have := x + _


/-!
`#check` cannot be used to accidentally assign metavariables, since it saves the state.
This is in contrasted against `have`.
-/

/--
info: rfl : x = x
---
error: unsolved goals
x : Nat
y : Nat := ?a
⊢ True

case a
x : Nat
⊢ Nat
---
info: x : Nat
y : Nat := ?a
⊢ True

case a
x : Nat
⊢ Nat
-/
#guard_msgs in
example (x : Nat) : True := by
  let y : Nat := ?a
  #check (by refine rfl : ?a = x)
  trace_state

/--
error: unsolved goals
x : Nat
y : Nat := x
this : x = x
⊢ True
---
info: x : Nat
y : Nat := x
this : x = x
⊢ True
-/
#guard_msgs in
example (x : Nat) : True := by
  let y : Nat := ?a
  have := (by refine rfl : ?a = x)
  trace_state
