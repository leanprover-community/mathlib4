/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Mathlib.Tactic.Core

/-!
# Repeating tactics

We provide variations on `repeat`:
* `repeat1 tac` behaves like `repeat`, but fails if `tac` fails on the main goal.
* `repeat! tac` behaves like `repeat`, but when `tac` fails on a subgoal, it will continue
  applying `tac` to later subgoals.
* `repeat1! tac` behaves like `repeat!`, but fails if `tac` fails on the main goal.

(Here the `!` indicates that the tactic should work as hard as possible.)

We also provide a `TacticM` level analogue of `repeat!`, called `repeatAllSubgoals`.
-/


/--
`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
macro "repeat1 " seq:tacticSeq : tactic => `(tactic| ($seq); repeat $seq)

/--
`repeat! tac` applies `tac` to the main goal. If the application succeeds,
the tactic is applied recursively to the generated subgoals
until it has failed on all remaining subgoals.

`repeat! tac` always succeeds. See `repeat1!` for the analogue which succeeds if and only if
`tac` succeeds on the main goal.

(Compare this to `repeat tac`, which will terminate after the first failure on a subgoal.)
-/
syntax "repeat! " tacticSeq : tactic
macro_rules
  | `(tactic| repeat! $seq) => `(tactic| first | ($seq); all_goals repeat! $seq | skip)

/--
`repeat1! tac` applies `tac` to the main goal. If the application succeeds,
the tactic is applied recursively to the generated subgoals
until it has failed on all remaining subgoals.

`repeat1! tac` succeeds if and only if `tac` succeeds on the main goal.

(Compare this to `repeat1 tac`, which will terminate after the first failure on a subgoal.)
-/
macro "repeat1! " seq:tacticSeq : tactic => `(tactic| ($seq); all_goals repeat! $seq)

namespace Mathlib.Tactic
open Lean Elab Tactic

/-- `repeatAllGoals n t`: repeat the tactic `t` on all goals,
and then on any subgoals thus produced, until it has failed on each remaining goal,
or a total of `n` invocations of `t` have been made. Always succeeds. -/
def repeatAllGoals : Nat → TacticM Unit → TacticM Unit
| 0,   _   => throwError "maximal iterations reached"
| n+1, tac => allGoals $ (do tac; repeatAllGoals n tac) <|> pure ()

/--
`repeatAllSubgoals n t`: repeat the tactic `t` on the main goal,
and then on any subgoals thus produced, until it has failed on each remaining goal,
or a total of `n` invocations of `t` have been made.
Fails iff `t` fails on the main goal.

This is a `TacticM` analogue of `repeat!`, with additional control of the maximum number of repeats.
-/
def repeatAllSubgoals : Nat → TacticM Unit → TacticM Unit
| 0,   _   => pure ()
| n+1, tac => focus (do tac; repeatAllGoals n tac)
