/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Init
import Lean.Elab.Tactic.Basic

/-!

A tactic stub file for the `guard_goal_nums` tactic.

-/

open Lean Meta Elab Tactic

/-- `guard_goal_nums n` succeeds if there are exactly `n` goals and fails otherwise. -/
elab (name := guardGoalNums) "guard_goal_nums " n:num : tactic => do
  let numGoals := (← getGoals).length
  guard (numGoals = n.getNat) <|>
    throwError "expected {n.getNat} goals but found {numGoals}"
