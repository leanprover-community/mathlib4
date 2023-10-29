/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.GCongr

/-! # Fake module docstring -/

namespace Mathlib.Tactic.GCongr
open Lean Meta Elab Tactic


elab "gcongr_var" template:(colGt term)?
    withArg:((" with " (colGt binderIdent)+)?) : tactic => do
  let g ← getMainGoal
  g.withContext do
  let .app (.app _rel lhs) _rhs ← withReducible g.getType'
    | throwError "gcongr failed, not a relation"
  -- Elaborate the template (e.g. `x * ?_ + _`), if the user gave one
  let template ← template.mapM fun e => do
    Term.elabTerm e (← inferType lhs)
  -- Get the names from the `with x y z` list
  let names := (withArg.raw[1].getArgs.map TSyntax.mk).toList
  -- The core tactic `Lean.MVarId.gcongr` will be run with side-goal discharger being
  -- `gcongr_discharger`
  let disch g := Term.TermElabM.run' do
    let [] ← Tactic.run g <| evalTactic (Unhygienic.run `(tactic| gcongr_discharger))
      | failure
  -- Time to actually run the core tactic `Lean.MVarId.gcongr`!
  let (progress, _, unsolvedGoalStates) ← g.gcongr template names disch
    (fun _ ↦ throwError "let's not bother trying to resolve the main goals using assumptions")
  if progress then
    replaceMainGoal unsolvedGoalStates.toList
  else
    throwError "gcongr did not make progress"
