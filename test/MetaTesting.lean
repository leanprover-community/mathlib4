import Mathlib.Algebra.Group.Nat
import Mathlib.Tactic.MoveAdd
import Mathlib.Tactic.MetaTesting

section exclude

/--
info: Skipped since it contains 'guard_target'

Use '#meta_test cmd' if you really want to run the test on 'cmd'
-/
#guard_msgs in
set_option linter.metaTest true in
/--
info: Skipped since it contains 'guard_target'

Use '#meta_test cmd' if you really want to run the test on 'cmd'
-/
#guard_msgs in
example : Nat := by
  guard_target = _
  exact 0

/--
info: Skipped since it contains 'guard_target'

Use '#meta_test cmd' if you really want to run the test on 'cmd'
-/
#guard_msgs in
set_option linter.metaTest true in
/--
warning: missing withContext?

  let _h : ?a✝ := _h
  let _d : ?a✝¹ := _d
  guard_target = _
  exact 0
  done
---
warning: missing withContext?

  let _h : ?a✝ := _h
  let _d : ?a✝¹ := _d
  unfold_let  at *
  guard_target = _
  exact 0
  done
-/
#guard_msgs in
#meta_test
example (_h : {_a : Int} → Nat → Nat) (_d : Nat) : Nat := by
  guard_target = _
  exact 0

end exclude

section buggy_tactic

open Lean Elab Command Tactic

/--  a sample tactic that behaves like `exact` but has bugs. -/
elab (name := buggyExactTac) "buggy_exact " md:"clearMD"? imv:"instMV"? h:ident : tactic => do
  let ctx ← getLCtx
  let hh := ctx.findFromUserName? h.getId
  match hh with
    | none => logWarningAt h m!"hypothesis '{h}' not found"
    | some h1 =>
      let r ← elabTermEnsuringType h h1.type
      let tgt := ← if md.isNone then getMainTarget else return (← getMainTarget).consumeMData
      -- warning: syntactic matching of the target
      if tgt == (← if imv.isSome then instantiateMVars h1.type else return h1.type) then
        replaceMainGoal (← (← getMainGoal).apply r)
      else logWarning "goal does not match"

@[inherit_doc buggyExactTac]
elab "buggy_exact " md:"clearMD"? "withMC" h:ident : tactic => withMainContext do
  if md.isSome then evalTactic (← `(tactic| buggy_exact clearMD $h))
  else              evalTactic (← `(tactic| buggy_exact $h))

@[inherit_doc buggyExactTac]
elab "buggy_exact " "withMC" "clearMD" h:ident : tactic => do
  evalTactic (← `(tactic| buggy_exact clearMD $h))

end buggy_tactic
/--
warning: goal does not match
---
warning: hypothesis 'h'' not found
---
warning: goal does not match
---
warning: goal does not match
-/
#guard_msgs in
example {a : Nat} (h : a + 0 = a) : a + 0 = a := by
  have := 0
  have h' := h
  buggy_exact h                  -- mdata  `goal does not match`
  buggy_exact h'                 -- missing context  `hypothesis 'h'' not found`
  buggy_exact withMC h'          -- mvars not instantiated  `goal does not match`
  buggy_exact clearMD withMC h'  -- further evidence of mvars  `goal does not match`
  buggy_exact clearMD withMC h   -- dealing with mdata

section trace_is_true

set_option trace.Tactic.tests true
/--
warning: is mdata correctly handled?

  have := 0
  buggy_exact h
  done
---
warning: missing withContext?

  let j : ?a✝ := j
  buggy_exact h
  done
---
warning: missing instantiateMVars?

  have h__h__0 := h
  buggy_exact h__h__0
  done
---
warning: missing withContext?

  let j : ?a✝ := j
  unfold_let  at *
  buggy_exact h
  done
---
info:
[Tactic.tests] ❌ 'have := 0'
[Tactic.tests] ✅ 'set's [set j : ?a✝ := j]
[Tactic.tests] ❌ 'let's [let j : ?a✝ := j]
[Tactic.tests] ❌ 'have's
        have h__h__0 := h
        buggy_exact h__h__0
        done
[Tactic.tests] ✅ 'set's [set j : ?a✝ := j, unfold_let  at *]
[Tactic.tests] ❌ 'let's [let j : ?a✝ := j, unfold_let  at *]
-/
#guard_msgs in
example {j : Bool} {h : True} : True := by
  test buggy_exact h

/--
warning: missing instantiateMVars?

  have h__h__0 := h
  buggy_exact clearMD h__h__0
  done
---
info:
[Tactic.tests] ✅ 'have := 0'
[Tactic.tests] ✅ 'set's []
[Tactic.tests] ✅ 'let's []
[Tactic.tests] ❌ 'have's
        have h__h__0 := h
        buggy_exact clearMD h__h__0
        done
[Tactic.tests] ✅ 'set's [unfold_let  at *]
[Tactic.tests] ✅ 'let's [unfold_let  at *]
-/
#guard_msgs in
example {h : True} : True := by
  test buggy_exact clearMD h

/--
warning: is mdata correctly handled?

  have := 0
  buggy_exact withMC h
  done
---
warning: missing instantiateMVars?

  have h__h__0 := h
  buggy_exact withMC h__h__0
  done
---
info:
[Tactic.tests] ❌ 'have := 0'
[Tactic.tests] ✅ 'set's []
[Tactic.tests] ✅ 'let's []
[Tactic.tests] ❌ 'have's
        have h__h__0 := h
        buggy_exact withMC h__h__0
        done
[Tactic.tests] ✅ 'set's [unfold_let  at *]
[Tactic.tests] ✅ 'let's [unfold_let  at *]
-/
#guard_msgs in
example {h : True} : True := by
  test buggy_exact withMC h

/--
warning: missing instantiateMVars?

  have h__h__0 := h
  buggy_exact clearMD withMC h__h__0
  done
---
info:
[Tactic.tests] ✅ 'have := 0'
[Tactic.tests] ✅ 'set's []
[Tactic.tests] ✅ 'let's []
[Tactic.tests] ❌ 'have's
        have h__h__0 := h
        buggy_exact clearMD withMC h__h__0
        done
[Tactic.tests] ✅ 'set's [unfold_let  at *]
[Tactic.tests] ✅ 'let's [unfold_let  at *]
-/
#guard_msgs in
example {h : True} : True := by
  test buggy_exact clearMD withMC h

/--
info:
[Tactic.tests] ✅ 'have := 0'
[Tactic.tests] ✅ 'set's [set a : ?a✝ := a, set b : ?a✝ := b]
[Tactic.tests] ✅ 'let's [let a : ?a✝ := a, let b : ?a✝ := b]
[Tactic.tests] ✅ 'have's
        move_add [← 9]
        move_add [← a]
        rfl
        done
[Tactic.tests] ✅
'set's [set a : ?a✝ := a, set b : ?a✝ := b, unfold_let  at *]
[Tactic.tests] ✅
'let's [let a : ?a✝ := a, let b : ?a✝ := b, unfold_let  at *]
-/
#guard_msgs in
example {a b : Nat} : 9 + a + b = b + a + 9 := by
test
  move_add [← 9]
  move_add [← a]
  rfl

/--
info: [Tactic.tests] testing 'hif'
[Tactic.tests] ✅ 'have := 0'
[Tactic.tests] ✅ 'set's
[set _n1 : ?a✝ := _n1, set _m1 : ?a✝ := _m1, set _n : ?a✝ := _n, set _m : ?a✝ := _m]
[Tactic.tests] ✅ 'let's
[let _n1 : ?a✝ := _n1, let _m1 : ?a✝ := _m1, let _n : ?a✝ := _n, let _m : ?a✝ := _m]
[Tactic.tests] ✅ 'have's
        have _hn___hn__0 := _hn
        exact .intro
        done
[Tactic.tests] ✅ 'set's [set _n1 : ?a✝ := _n1,
     set _m1 : ?a✝ := _m1,
     set _n : ?a✝ := _n,
     set _m : ?a✝ := _m,
     unfold_let  at *]
[Tactic.tests] ✅ 'let's [let _n1 : ?a✝ := _n1,
     let _m1 : ?a✝ := _m1,
     let _n : ?a✝ := _n,
     let _m : ?a✝ := _m,
     unfold_let  at *]
-/
#guard_msgs in
#meta_test
theorem hif {_n1 _m1 : Nat} {_n _m : Int} (_hn : _n + _m = 0) : True := by
  exact .intro

/--
info:
[Tactic.tests] testing 'example'
[Tactic.tests] ✅ 'have := 0'
[Tactic.tests] ✅ 'set's []
[Tactic.tests] ✅ 'let's []
[Tactic.tests] ✅ 'have's
        exact .intro
        skip
        done
[Tactic.tests] ✅ 'set's [unfold_let  at *]
[Tactic.tests] ✅ 'let's [unfold_let  at *]
-/
#guard_msgs in
#meta_test
example : True := by
  exact .intro
  skip

/--
warning: goal does not match
-/
-- `goal does not match` --> not dealing with `mdata`?
#guard_msgs in
example {a : Nat} (h : a = 0) : a = 0 := by
  have := 0
  buggy_exact h
  assumption

/--
warning: goal does not match
-/
#guard_msgs in
-- `goal does not match` --> missing `instantiateMVars`?
example {a : Nat} (ha : a = 0) : a = 0 := by
  have h := ha  -- `h` is a metavariable
  clear ha
  buggy_exact clearMD withMC h
  assumption

/--
warning: hypothesis 'h' not found
-/
#guard_msgs in
-- `hypothesis 'h' not found` --> missing `withMainContext`?
example {a : Nat} (ha : a = 0) : a = 0 := by
  have h := ha
  clear ha
  buggy_exact h
  assumption

set_option linter.metaTest true
/--
warning: is mdata correctly handled?

  have := 0
  buggy_exact h
  done
---
warning: missing withContext?

  let _j : ?a✝ := _j
  buggy_exact h
  done
---
warning: missing instantiateMVars?

  have _h2___h2__0 := _h2
  have h__h__1 := h
  buggy_exact h__h__1
  done
---
warning: missing withContext?

  let _j : ?a✝ := _j
  unfold_let  at *
  buggy_exact h
  done-/
#guard_msgs in
example {_j : Bool} {_h2 : True} {h : True} : True := by
  buggy_exact h


/--
warning: missing instantiateMVars?

  have _h2___h2__0 := _h2
  have h__h__1 := h
  buggy_exact clearMD withMC h__h__1
  done
-/
#guard_msgs in
example {_j : Bool} {_h2 : True} {h : True} : True := by
  buggy_exact clearMD withMC h

end trace_is_true

section testing_internals
open Lean Elab Parser Command Mathlib Tactic MetaTesting

run_cmd liftTermElabM do
  let stx ← `(tacticSeq| exact .intro)
  let gh := stx.insertMany #[(← `(tactic| guard_hyp h))]
  let gt := stx.insertMany #[(← `(tactic| guard_target = h))]
  guard <| (test? stx).isNone && (test? gh).isSome && (test? gt).isSome

run_cmd liftTermElabM do
  let stx ← `(command| /-- -/ #guard_msgs in import)
  guard <| (test? stx).isNone
  let stx ← `(command| #guard_msgs in import)
  guard <| (test? stx).isNone

end testing_internals
