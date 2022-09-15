/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Mathlib.Tactic.Core

/-!
# Repeating tactics

We provide a variation on `repeat`:
* `repeat1 tac` behaves like `repeat`, but fails unless `tac` succeeds at least once.

Note also the macro
* `repeat' tac` defined in `Std`, which runs `tac` on each subgoal, continuing after failures.

We provide an analogue of `repeat'` as a combinator in `MetaM`.
-/

/--
`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.
-/
macro "repeat1 " seq:tacticSeq : tactic => `(tactic| ($seq); repeat $seq)

namespace Mathlib.Tactic
open Lean Elab Tactic

/--
A repeat-until-exhausted combinator.
Given a tactic `tac`, `repeat' tac` is a tactic which runs `tac`, then recursively runs `tac` again
on all subgoals, returning the list of all subgoals on which `tac` failed.
-/
partial def repeat' (tac : MVarId → MetaM (List MVarId)) : MVarId → MetaM (List MVarId) := fun g =>
  try
    pure (←(← tac g).mapM (fun g' => repeat' tac g')).join
  catch _ =>
    pure [g]
