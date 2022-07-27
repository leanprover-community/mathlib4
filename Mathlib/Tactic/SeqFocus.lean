/-
Copyright (c) 2022 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Lean

open Lean Elab Meta Tactic

namespace Tactic

/-- Assuming there are `n` goals, `map_tacs [t1, t2, ..., tn]` applies each `ti` to the respective
goal and leaves the resulting subgoals. -/
elab "map_tacs " "[" ts:tactic,* "]" : tactic => do
  let mvarIds ← getGoals
  let tacs := ts.getElems
  let length := tacs.size
  if length < mvarIds.length then
    throwError "not enough tactics"
  else if length > mvarIds.length then
    throwError "too many tactics"
  let mut mvarIdsNew := #[]
  for tac in tacs, mvarId in mvarIds do
    unless ← mvarId.isAssigned do
      setGoals [mvarId]
      try
        evalTactic tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

/-- `t <;> [t1, t2, ..., tn]` focuses on the first goal and applies `t`, which should result in `n`
subgoals. It then applies each `ti` to the corresponding goal and collects the resulting
subgoals. -/
macro (name := seq_focus) t:tactic " <;> " "[" ts:tactic,* "]" : tactic =>
  `(tactic| focus ( $t:tactic; map_tacs [$ts,*]) )

end Tactic
