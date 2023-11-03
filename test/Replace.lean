/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/
import Mathlib.Tactic.Replace

set_option linter.unusedVariables false

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
