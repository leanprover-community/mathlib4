/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arthur Paulino, Mario Carneiro
-/

import Lean
import Mathlib.Data.List.Defs

namespace Mathlib.Tactic

open Lean Elab.Tactic

/--
`work_on_goal n { tac }` creates a block scope for the `n`-th goal (indexed from zero),
but does not require that the goal be solved at the end of the block
(any resulting subgoals are inserted back into the list of goals, replacing the `n`-th goal).
-/
elab (name := workOnGoal) "work_on_goal " n:num ppSpace seq:tacticSeq : tactic => do
  match (← getGoals).splitAt n.toNat with
    | (_, []) => throwError "not enough goals"
    | (gls, g :: grs) =>
      setGoals [g]
      evalTactic seq
      setGoals $ gls ++ (← getUnsolvedGoals) ++ grs
