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

/-- -/
elab (name := fpropTac) "fprop" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let goalType ← goal.getType
  
    let (.some r, _) ← fprop goalType {} |>.run {}
      | throwError "fprop was unable to prove `{← Meta.ppExpr goalType}`"

    goal.assign r.proof


