/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/
import Mathlib.Tactic.Replace

set_option linter.unusedVariables false

private axiom test_sorry : ∀ {α}, α

/-- Test the `:=` syntax works -/
example {A B : Type} (h : A) (f : A → B) : B := by
  replace h := f h
  exact h

-- tests without `:=`, creating a new subgoal

example (z : Int) : Nat := by
  replace z : Nat
  exact 0
  assumption

example : True := by
  have : 1 + 1 = 2 := by simp_arith
  replace : 2 + 2 = 4
  simp_arith
  trivial

-- Regression test. `replace h` used to close goal and leave metavariables.
-- Note that `replace h` does *not* delete `h` in this case because the type of the new `h`
-- is a metavariable whose context includes the old `h`.
example (h : True) : False := by
  guard_hyp h : True
  replace h
  · exact true
  guard_hyp h : Bool
  rename_i h'
  guard_hyp h' : True
  exact test_sorry
