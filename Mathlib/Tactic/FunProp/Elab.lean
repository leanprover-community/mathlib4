/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Tactic.FunProp.Core

/-!
## `funProp` tactic syntax
-/

namespace Mathlib
open Lean Meta Elab Tactic

namespace Meta.FunProp

open Lean.Parser.Tactic

/-- Tactic to prove function properties -/
syntax (name := funPropTacStx)
  "fun_prop" (discharger)? (" [" withoutPosition(ident,*,?) "]")? : tactic

private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
      pure none

/-- Tactic to prove function properties -/
@[tactic funPropTacStx]
def funPropTac : Tactic
  | `(tactic| fun_prop $[$d]? $[[$names,*]]?) => do

    let disch ← show MetaM (Expr → MetaM (Option Expr)) from do
      match d with
      | none => pure emptyDischarge
      | some d =>
        match d with
        | `(discharger| (discharger:=$tac)) => pure <| tacticToDischarge (← `(tactic| ($tac)))
        | _ => pure emptyDischarge

    let namesToUnfold : Array Name :=
      match names with
      | none => #[]
      | .some ns => ns.getElems.map (fun n => n.getId)

    let namesToUnfold := namesToUnfold.append defaultNamesToUnfold

    let goal ← getMainGoal
    goal.withContext do
      let goalType ← goal.getType

      -- the whnf and telscope is here because the goal can be
      -- `∀ y, let f := fun x => x + y; Continuous fun x => x + f x`
      -- However it is still not complete solution. How should we deal with mix of let and forall?
      withReducible <| forallTelescopeReducing (← whnfR goalType) fun _ type => do
        unless (← getFunProp? type).isSome do
          let hint :=
            if let .some n := type.getAppFn.constName?
            then s!" Maybe you forgot marking `{n}` with `@[fun_prop]`."
            else ""
          throwError "`{← ppExpr type}` is not a `fun_prop` goal!{hint}"

      let ctx : Context := {disch := disch, constToUnfold := .ofArray namesToUnfold _}
      let (r?, s) ← funProp goalType ctx |>.run {}
      if let .some r := r? then
        goal.assign r.proof
      else
        let mut msg := s!"`fun_prop` was unable to prove `{← Meta.ppExpr goalType}`\n\n"

        msg := msg ++ "Issues:"
        msg := s.mainMsgLog.foldl (init := msg) (fun msg m => msg ++ "\n  " ++ m)

        -- todo enable only when an option is set
        msg := msg ++ "\n\nSecondary issues:"
        msg := s.secondaryMsgLog.foldl (init := msg) (fun msg m => msg ++ "\n  " ++ m)

        throwError msg


  | _ => throwUnsupportedSyntax
