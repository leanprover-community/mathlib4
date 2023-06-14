/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Std.Data.List.Basic

/-!

# `prune` tactic

The `prune` tactic `clear`s hypotheses from the main goal.  The default behaviour is
to remove the hypotheses very conservatively.  See the tactic doc-string for more details.

This tactic is intended as a way to clean up the local context at the beginning of a proof,
pruning away all variables that are in scope, but do not appear in the goal.

## Implementation notes

The tactic has two stages:
1. an iterative stage, where variables are successively `revert`ed in "layers of dependent batches";
2. a final step, in which all left-over variables are `clear`ed and all previously`revert`ed
   variables are `intro`duced.

The tactic `prune n` stops the iterative stage at the `n`-th step.
The tactic `prune` performs the whole iterative stage.

Both tactics then `clear` the remaining variables and re-`intro`duce the `revert`ed variables.
-/

namespace Mathlib.Tactic.Prune

open Lean Elab Meta Tactic

/-- `revertVarsOnce` `revert`s all hypotheses that appear in the main goal.
It returns the array of `FVarIds` of the reverted hypotheses. -/
def revertVarsOnce : TacticM (Array FVarId) := focus do
  let ctx := (← getLCtx).decls.toList.reduceOption
  let gMVar := ← getMainGoal
  let goal := ← getMainTarget
  let foundDecls := (ctx.map fun x =>
    if x.toExpr.occurs goal then some x else none).reduceOption
  let fvarIdFound := (foundDecls.map Lean.LocalDecl.fvarId).toArray
  let (fvs, newGoal) := ← gMVar.revert fvarIdFound
  setGoals [newGoal]
  pure fvs

/-- `revertLoop` iterates `revertVarsOnce`, reverting all variables that
recursively appear in the main goal. -/
partial
def revertLoop : TacticM Unit := focus do
  let fvars := ← revertVarsOnce
  if fvars.size == 0 then pure () else revertLoop

/-- `revertNLoop n` iterates `revertVarsOnce` up to `n` times.
If at some point, no new variables get reverted, then `revertNLoop`
shows a message, suggesting to use `prune`, instead of `prune n`. -/
def revertNLoop (n : Nat) : TacticM Unit := focus do
  match n with
  | 0     => do let _goal := ← getMainGoal; pure ()
  | n + 1 => focus do
    let fvars := ← revertVarsOnce
    if fvars.size == 0 then
      logInfo m!"Excessive number of iterations.\nTry this: prune"
      pure () else revertNLoop n

/-- `pruneTac offset` clears all hypotheses and then re`intro`duces all hypotheses contained in
the goal, except for the last `offset`.  The `offset` is intended to leave the final goal
as it was before all the previous `revert`s and introduce only the variables that have been
explicitly reverted by one of the `revertX` tactics above. -/
def pruneTac (offset : Nat := 0) : TacticM Unit := focus do
  let dcls := (← getLCtx).decls.toList.reduceOption
  let goal := ← getMainGoal
  let newGoal ← goal.tryClearMany (dcls.map LocalDecl.fvarId).toArray
  setGoals [newGoal]
  let nms := (← getMainTarget).getForallBinderNames
  let (_newfvs, rGoal) := ← introNCore newGoal (nms.length - offset) [] True True
  setGoals [rGoal]

/-- The `prune` tactic `clear`s hypotheses from the main goal.  The default behaviour is
to remove the hypotheses very conservatively.  `prune` also takes an optional natural
number input:
* `prune 0` removes all hypotheses that do not appear in the main goal;
* `prune 1` removes all hypotheses that do not appear in the main goal nor contain hypotheses
  that `prune 0` had kept;
* ...
* `prune n+1` removes all hypotheses that do not appear in the main goal nor contain hypotheses
  that `prune n` had kept.

For sufficiently large `n`, `prune n` is a synonym for `prune`.  The tactic reports when
this happens, suggesting to use `prune`, if `n` is too large. -/
syntax "prune" (num)? : tactic

elab_rules : tactic
  | `(tactic| prune)        => do
    let offset := (← getMainTarget).getForallBinderNames.length
    revertLoop
    pruneTac offset
  | `(tactic| prune $[$n]?) => do
    let offset := (← getMainTarget).getForallBinderNames.length
    revertNLoop (n.getD default).getNat
    pruneTac offset

end Mathlib.Tactic.Prune
