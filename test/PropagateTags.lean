/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Ian Benway.
-/

import Mathlib.Tactic.PropagateTags
import Mathlib.Tactic.Basic
open Lean Elab.Tactic Meta

/-Rids the first goal of any tags, for testing.-/
elab "retag" x:(ident <|> "_") : tactic => liftMetaTactic1 fun g => do
  let g2 ← mkFreshExprMVar (← getMVarType g) (userName := x.getId)
  assignExprMVar g g2
  pure g2.mvarId!

example (h : Nat → Nat → Nat) : Nat := by
  cases true
  propagate_tags retag _ -- does nothing
  propagate_tags
    apply h; retag _; rotate_left; retag _; rotate_right
  propagate_tags
    rotate_left;
  all_goals {apply h 4 4}

example (h g : Prop) (a : h) (b : g) : h ∧ g := by
  apply And.intro
  cases true
  propagate_tags
    retag _; rotate_right; rotate_left
  case left.false => apply a
  case left.true => apply a
  case right => apply b
