/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Ian Benway.
-/

import Mathlib.Tactic.PropagateTags
import Mathlib.Tactic.Basic
open Lean Elab.Tactic Meta

/-tests for guard_tags-/
example : True := by
  cases true
  guard_tags false; trivial
  guard_tags true; trivial

example : True ∧ True := by
  apply And.intro
  guard_tags left; trivial
  guard_tags right; trivial

example : True ∧ True := by
  cases true
  all_goals apply And.intro
  guard_tags false.left; trivial
  guard_tags false.right; trivial
  guard_tags true.left; trivial
  guard_tags true.right; trivial

/-tests for propagate_tags-/
/-Rids the first goal of any tags, for testing.-/
elab "retag" x:(ident <|> "_") : tactic => liftMetaTactic1 fun g => do
  let g2 ← mkFreshExprMVar (← getMVarType g) (userName := x.getId)
  assignExprMVar g g2
  pure g2.mvarId!

example (h : Nat → Nat → Nat) : Nat := by
  cases true
  propagate_tags retag _ -- does nothing
  guard_tags false
  propagate_tags
    apply h; retag _; rotate_left; retag _; rotate_right
  guard_tags false
  propagate_tags
    rotate_left;
  all_goals {apply h 4 4}

example (h g : Prop) (a : h) (b : g) : h ∧ g := by
  apply And.intro
  cases true
  propagate_tags
    retag _; rotate_right; rotate_left
  guard_tags left.false
  case left.false => apply a
  guard_tags left.true
  case left.true => apply a
  guard_tags right
  case right => apply b
