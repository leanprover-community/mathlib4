/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic

/-!
A tactic stub file for the `guard_hyp_nums` tactic.
-/

public meta section

open Lean Meta Elab Tactic

/--
`guard_hyp_nums n` succeeds if there are exactly `n` hypotheses and fails otherwise.

Note that, depending on what options are set, some hypotheses in the local context might
not be printed in the goal view. This tactic computes the total number of hypotheses,
not the number of visible hypotheses.
-/
elab (name := guardHypNums) "guard_hyp_nums " n:num : tactic => do
  let numHyps := (← getLCtx).size
  guard (numHyps = n.getNat) <|>
    throwError "expected {n.getNat} hypotheses but found {numHyps}"
