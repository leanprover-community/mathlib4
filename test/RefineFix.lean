/-
Copyright (c) 2023 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Tactic.RefineFix
import Std.Tactic.GuardMsgs
import Mathlib.Util.Delaborators

set_option pp.anonymousMVarSuffixes false


/--
info: Try this: refine id ?_
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  refine? id _

def f {_α _β : Type} : True := trivial

/- Delayed mvars should not be a problem. -/
/--
info: Try this: refine fun (_ : _) => ?_
---
error: unsolved goals
x✝ : Nat
⊢ Nat
-/
#guard_msgs in
example : Nat → Nat := by
  refine? fun (_ : _) => _

/--
info: Try this: refine fun (_ : Nat) => id ?_
---
error: unsolved goals
x✝ : Nat
⊢ Nat
-/
#guard_msgs in
example : Nat → Nat := by
  refine? fun (_ : Nat) => id _

/-
The following test relies on not matching the `MVarErrorInfo.kind` to `.hole`.

The resulting goal states also reflect the fact that we've re-elaborated `refine e` instead of just
changing the `MetavarKind`s of the mvars we got from `refine? e`, as `?_`'s are elaborated
differently in this case.
-/
/--
info: Try this: refine
  let e : ?_ := ?_;
  (fun (_ : ?_) => ?_) ?_
---
error: unsolved goals
case refine_1
⊢ Sort ?u✝

case refine_2
⊢ ?refine_1

case refine_3
e : ?refine_1 := ?refine_2
⊢ Sort ?u✝

case refine_4
e : ?refine_1 := ?refine_2
x✝ : ?refine_3
⊢ True

case refine_5
e : ?refine_1 := ?refine_2
⊢ ?refine_3
-/
#guard_msgs in
example : True := by
  refine? let e : _ := _; (fun (_ : _) => _) _

/- This invocation should error: the unassigned natural mvars are implicit arguments, not `_`'s.
Further, it should not produce a suggestion, while still producing an "unsolved goals" message just
like `refine` does. This means that `refine` did not abort the tactic, but still logged new errors,
which we wanted to detect and use to stop `refine?` from adding a suggestion.
-/
/--
error: don't know how to synthesize implicit argument
  @f ?m✝ ?m✝
context:
⊢ Type
---
error: don't know how to synthesize implicit argument
  @f ?m✝ ?m✝
context:
⊢ Type
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  refine? f

/-- info: Try this: refine @f ?_ ?_ -/
#guard_msgs in
example : True := by
  refine? @f _ _
  <;> exact Nat

/-- info: Try this: refine @f ?_ ?_ -/
#guard_msgs in
example : True := by
  refine? @f ?_ _
  <;> exact Nat

/- This test ensures that the syntax manipulation still works inside a macro.

It also can be used by a human to show something else: that no 'unknown mvar' rpc error appears in
the infoview when the cursor is placed at the specified spot. This was occurring because the
infotrees were not reset after the initial elaboration, and required
`Term.withoutModifyingState (restoreInfo := true)`. Note that we wanted to reset the infotrees, not
wrap them in a context, lest we wind up with duplicate info.
-/
/--
info: Try this: refine @f ?_ ?_
---
info: Try this: refine @f ?_ ?_
---
error: unsolved goals
case left.refine_1
⊢ Type

case left.refine_2
⊢ Type

case right.refine_1
⊢ Type

case right.refine_2
⊢ Type
-/
#guard_msgs in
example : True ∧ True := by
  constructor <;> refine? @f _ _
                              --^ unknown mvar if infotree is not reset

section macroErrors

/- These tests should error: the syntax `_` is not present in the original syntax, and so cannot be
replaced. -/

macro m:"macroYieldingHole" : term => `(_%$m)

/--
error: don't know how to synthesize placeholder for argument '_α'
context:
⊢ Type
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  refine? @f macroYieldingHole _

def g : Nat → Nat → True
| _,_ => trivial

/--
error: don't know how to synthesize implicit argument
  g ?m✝ ?m✝
context:
⊢ Nat
---
error: don't know how to synthesize implicit argument
  g ?m✝ ?m✝
context:
⊢ Nat
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  refine? g ..

structure Foo where
  x : Nat

/--
error: don't know how to synthesize placeholder
context:
⊢ Nat
---
error: unsolved goals
⊢ Foo
-/
#guard_msgs in
example : Foo := by
  refine? { .. : Foo }

end macroErrors

/--
info: Try this: refine { x := ?_ }
---
error: unsolved goals
⊢ Nat
-/
#guard_msgs in
example : Foo := by
  refine? { x := _ }

def h {_α : Type} : True := trivial

/- The following suggestion should not include the comment which follows the tactic. -/
/-- info: Try this: refine h (_α := Nat) -/
#guard_msgs in
example : True := by
  refine? h (_α := Nat)

-- a comment
