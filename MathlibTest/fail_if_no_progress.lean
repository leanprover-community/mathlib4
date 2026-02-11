import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Basic

set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option pp.unicode.fun true

section success

example : 1 = 1 := by fail_if_no_progress rfl
example (h : 1 = 1) : True := by
  fail_if_no_progress simp at h
  trivial

example : let x := 1; x = x := by
  intro x
  fail_if_no_progress clear_value x
  rfl

-- New fvarids. This is not easily avoided without remapping fvarids manually.
example : let x := 1; x = x := by
  intro x
  fail_if_no_progress
    revert x
    intro x
  rfl

open Lean Elab Tactic in
example : let x := id 0; x = x := by
  intro x
  fail_if_no_progress
    -- Reduce the value of `x` to `Nat.zero`
    run_tac do
      let g ← getMainGoal
      let decl ← g.getDecl
      let some d := decl.lctx.findFromUserName? `x | throwError "no x"
      let lctx := decl.lctx.modifyLocalDecl d.fvarId fun d =>
        d.setValue (.const ``Nat.zero [])
      let g' ← Meta.mkFreshExprMVarAt lctx decl.localInstances decl.type
      g.assign g'
      replaceMainGoal [g'.mvarId!]
    guard_hyp x : Nat :=ₛ Nat.zero
  rfl

end success

section failure

/--
error: no progress made on
x : Bool
h : x = true
⊢ x = true
-/
#guard_msgs in
example (x : Bool) (h : x = true) : x = true := by
  fail_if_no_progress skip

/--
error: no progress made on
x : Bool
h : x = true
⊢ x = true
-/
#guard_msgs in
example (x : Bool) (h : x = true) : x = true := by
  fail_if_no_progress simp -failIfUnchanged

/--
error: no progress made on
x : Bool
h : x = true
⊢ True
-/
#guard_msgs in
example (x : Bool) (h : x = true) : True := by
  fail_if_no_progress simp -failIfUnchanged at h

/--
error: no progress made on
x : Nat := (fun x ↦ x) Nat.zero
⊢ x = x
-/
#guard_msgs in
open Lean Elab Tactic in
example : let x := (fun x => x) Nat.zero; x = x := by
  intro x
  fail_if_no_progress
    -- Reduce the value of `x` to `Nat.zero`
    run_tac do
      let g ← getMainGoal
      let decl ← g.getDecl
      let some d := decl.lctx.findFromUserName? `x | throwError "no x"
      let lctx := decl.lctx.modifyLocalDecl d.fvarId fun d =>
        d.setValue (.const ``Nat.zero [])
      let g' ← Meta.mkFreshExprMVarAt lctx decl.localInstances decl.type
      g.assign g'
      replaceMainGoal [g'.mvarId!]
    guard_hyp x : Nat :=ₛ Nat.zero

end failure
