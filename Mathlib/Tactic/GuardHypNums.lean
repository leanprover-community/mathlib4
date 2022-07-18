/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import Lean

/-!
A tactic stub file for the `guard_hyp_nums` tactic.
-/

open Lean Meta Elab Tactic

/-- `localContextLength` returns the number of hypotheses in the local context,
including hidden and auxiliary hypotheses. -/
def localContextLength : TacticM Nat := do
  let mut numHyps := 0
  for _ in (← getLCtx) do
    numHyps := numHyps + 1
  return numHyps

/--
`guard_hyp_nums n` succeeds if there are exactly `n` hypotheses and fails otherwise.

Note that, depending on what options are set, some hypotheses in the local context might
not be printed in the goal view. This tactic computes the total number of hypotheses,
not the number of visible hypotheses.
-/
elab (name := guardHypNums) "guard_hyp_nums " n:num : tactic => do
  let numHyps ← localContextLength
  guard (numHyps = n.getNat) <|>
    throwError "expected {n.getNat} goals but found {numHyps}"
