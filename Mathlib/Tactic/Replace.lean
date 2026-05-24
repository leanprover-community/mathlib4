/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Mario Carneiro
-/
module

public import Mathlib.Tactic.Have

/-!
# Extending `replace`

This file extends the `replace` tactic from the standard library to allow the addition of hypotheses
to the context without requiring their proofs to be provided immediately.

As a style choice, this should not be used in mathlib; but is provided for downstream users who
preferred the old style.
-/

public meta section

namespace Mathlib.Tactic

open Lean Elab.Tactic

/--
`replace h : t`, without a subsequent proof, creates a new main goal `case h : ... ⊢ t`.
This form is considered deprecated in Mathlib: use `replace h : t := _` instead.
-/
tactic_extension Lean.Parser.Tactic.replace

@[tactic_alt Lean.Parser.Tactic.replace]
syntax (name := replace') "replace" haveIdLhs' : tactic

elab_rules : tactic
| `(tactic| replace $n:optBinderIdent $bs* $[: $t:term]?) => withMainContext do
    let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
    let name := optBinderIdent.name n
    let hId? := (← getLCtx).findFromUserName? name |>.map fun d ↦ d.fvarId
    match hId? with
    | some hId => replaceMainGoal [goal1, (← observing? <| goal2.clear hId).getD goal2]
    | none     => replaceMainGoal [goal1, goal2]

end Mathlib.Tactic
