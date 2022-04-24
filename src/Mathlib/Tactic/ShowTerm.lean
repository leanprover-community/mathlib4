/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.TryThis

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Tactic.TryThis

namespace Lean.Elab.Tactic

/--
`show_term tac` runs `tac`, then prints the generated term in the form
"Try this: exact X Y Z" or "Try this: refine X ?_ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)
-/
elab (name := showTerm) tk:"show_term " t:tacticSeq : tactic => withMainContext do
  let g ← getMainGoal
  evalTactic t
  addExactSuggestion tk /- FIXME: we'd like the range for the whole tactic -/
    (← instantiateMVars (mkMVar g)).headBeta

end Lean.Elab.Tactic
