/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Tactic.FProp.Core

namespace Mathlib
open Lean Meta Elab Tactic

namespace Meta.FProp

open Lean.Parser.Tactic

syntax (name := fpropTacStx) "fprop" (discharger)? : tactic

@[tactic fpropTacStx]
def fpropTac : Tactic 
| `(tactic| fprop $[$d]?) => do

  let disch : Expr → MetaM (Option Expr) := 
    match d with
    | none => fun _ => pure none
    | some d => 
      match d with
      | `(discharger| (discharger:=$tac)) => tacticToDischarge tac
      | _ => fun _ => pure none

  let goal ← getMainGoal
  goal.withContext do
    let goalType ← goal.getType
  
    let (.some r, _) ← fprop goalType {disch := disch} |>.run {}
      | throwError "fprop was unable to prove `{← Meta.ppExpr goalType}`"

    goal.assign r.proof
| _ => throwUnsupportedSyntax
