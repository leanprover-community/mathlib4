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

      let cfg : Config := {disch := disch, constToUnfold := .ofArray namesToUnfold _}
      let (r?, s) ← funProp goalType cfg |>.run {}
      if let .some r := r? then
        goal.assign r.proof
      else
        let mut msg := s!"`fun_prop` was unable to prove `{← Meta.ppExpr goalType}`\n\n"
        if d.isSome then
          msg := msg ++ "Try running with a different discharger tactic like \
          `aesop`, `assumption`, `linarith`, `omega` etc.\n"
        else
          msg := msg ++ "Try running with discharger `fun_prop (disch:=aesop)` or with a different \
          discharger tactic like `assumption`, `linarith`, `omega`.\n"

        msg := msg ++ "Sometimes it is useful to run `fun_prop (disch:=trace_state; sorry)` \
          which will print all the necessary subgoals for `fun_prop` to succeed.\n"
        msg := msg ++ "\nPotential issues to fix:"
        msg := s.msgLog.foldl (init := msg) (fun msg m => msg ++ "\n  " ++ m)
        msg := msg ++ "\n\nFor more detailed information use \
          `set_option trace.Meta.Tactic.fun_prop true`"
        throwError msg


  | _ => throwUnsupportedSyntax
