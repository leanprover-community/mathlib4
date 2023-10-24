/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
import Mathlib.Tactic.Set
import Mathlib.Tactic.Change

/-!
# The `setm` tactic

The `setm` tactic ("`set` with matching") is TODO WRITE THIS
-/

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `Tactic.setm

/--
TODO: Write docs
-/

syntax (name := setM) "setm " term : tactic
elab_rules : tactic
| `(tactic| setm $expr:term) => do
  withMainContext do
    /- Elaborate `expr` from a Syntax into meaningful Terms -/
    let (origPattern, mvarIds) ← elabTermWithHoles expr none (←getMainTag) (allowNaturalHoles := true)

    /- Named holes are by default syntheticOpaque and not assignable, so we change that -/
    mvarIds.forM fun mvarId => mvarId.setKind .natural
    trace[Tactic.setm] "origPattern : {origPattern}"

    /- Create new placeholder mvars -/
    let name (x : MVarId) := do return (←x.getDecl).userName
    let mvarIdsPairs ← mvarIds.mapM
      (fun x => return (x, ←mkFreshExprMVar none (userName := ←name x)))
    let mvarIdsMap := @HashMap.ofList _ _ instBEqMVarId instHashableMVarId mvarIdsPairs

    /- newPattern is the placeholder pattern with a bunch of placeholder mvars -/
    let newPattern := origPattern.replace (fun x =>
      match x with
      | .mvar x => mvarIdsMap.find? x
      | _ => none
    )

    /- Let isDefEq match the given pattern -/
    if ←isDefEq (←getMainTarget) newPattern then
      /- Iterate over the (old, new) vars -/
      mvarIdsPairs.forM fun (mvarIdOld, mvarExprNew) => do
        let mvarIdNew := mvarExprNew.mvarId!
        match ←name mvarIdNew with
        | Name.anonymous => return ()
        | name =>
          let a := mkIdent name
          let ha := mkIdent $ name.appendBefore "h"
          let goal ← getMainGoal
          match (←getExprMVarAssignment? mvarIdNew) with
          | some mvAss =>
            /-
            Here mvarIdNew is assigned to mvAss, and mvarIdOld <-> mvarIdNew, so we
              (1) let $a := mvAss -- Here fvarId stores $a (?)
              (2) have $ha : $a = mvAss := rfl
              (3) assign $a to mvarIdOld
            -/
            let mvarType ← inferType mvAss
            let (fvarId, goal) ← (←goal.define a.getId mvarType mvAss).intro1P
            replaceMainGoal [goal]
            evalTactic (←`(tactic| have $ha : $a = $(←Term.exprToSyntax mvAss) := rfl))
            mvarIdOld.assign (.fvar fvarId)
          | none => throwError "setm: Ass not defined. File a bug report!"
    else
      throwError "setm: pattern is not definitionally equal to the goal."

    /- At the end, all the original mvars are replaced with the new fvars -/
    evalTactic (←`(tactic| change $(←Term.exprToSyntax origPattern)))
