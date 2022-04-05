/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ian Benway.
-/
import Lean
namespace Mathlib.Tactic
open Lean Elab.Tactic Meta
/--
`propagate_tags tac` carries the tag of the main goal to the main goal of the result of doing `tac`.
-/
elab "propagate_tags " tac:tacticSeq : tactic => do
  withMainContext do
  let g ← getMainGoal
  let tag ← getMainTag
  match tag with
  | Name.anonymous => evalTactic tac
  | _ => withMainContext do
    evalTactic tac
    let gs ← getGoals
    unless gs.isEmpty do
      let newTag ← getMainTag
      match newTag with
      | Name.anonymous => setMVarTag (← getMainGoal) tag
      | _ => pure ()
