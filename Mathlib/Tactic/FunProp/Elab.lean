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
syntax (name := funPropTacStx) "fun_prop" (discharger)? : tactic

private def emptyDischarge : Expr → MetaM (Option Expr) :=
  fun e =>
    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] discharging: {← ppExpr e}") do
      pure none

/-- Tactic to prove function properties -/
@[tactic funPropTacStx]
def funPropTac : Tactic
  | `(tactic| fun_prop $[$d]?) => do

    let disch ← show MetaM (Expr → MetaM (Option Expr)) from do
      match d with
      | none => pure emptyDischarge
      | some d =>
        match d with
        | `(discharger| (discharger:=$tac)) => pure <| tacticToDischarge (← `(tactic| ($tac)))
        | _ => pure emptyDischarge

    let goal ← getMainGoal
    goal.withContext do
      let goalType ← goal.getType

      let (.some r, _) ← funProp goalType {disch := disch} |>.run {}
        | throwError "funProp was unable to prove `{← Meta.ppExpr goalType}`"

      goal.assign r.proof
  | _ => throwUnsupportedSyntax
