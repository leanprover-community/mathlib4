/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Benway.
-/

import Mathlib.Tactic.Set
import Mathlib.Tactic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
--import Mathlib.Analysis.Complex.AbsMax
--import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

example (x : Nat) (h : x = x) : x = x := by
  set! p := h
  set q : x = x := p
  apply q

example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by
  set! y := x with ← h2
  set w := x
  guard_hyp y := x
  guard_hyp w := x
  guard_hyp h : w + w - w = 3
  guard_hyp h2 : w = y
  set z := w with _h3
  set a := 3
  guard_target = z + z - z = a
  set i'm_the_goal : Prop := z + z - z = a
  guard_target = i'm_the_goal
  apply h

example (x : Nat) (h : x - x = 0) : x = x := by
  set y : Nat := x
  set! z := y + 1 with ← _eq1
  set! p : x - x = 0 := h with _eq2
  rfl

example : True := by
  set g : Nat → Int := (fun ε => ε) with h
  trivial

open Complex
open scoped Real
/-
example : True := by
  let a : ℝ := sorry
  let d : ℝ  := sorry
  set aff : ℂ → ℂ := (fun w => d * (w - a * I) )
  set g : ℝ → ℂ → ℂ  := fun ε w => exp (ε * (exp (aff w) + exp (-aff w)))
  -/
--en Set Function Filter Asymptotics Metric Complex
--en scoped Topology Filter Real


variable {a b C l o p m n b v c j l k u y : ℝ}
set_option trace.Meta.synthInstance true
set_option trace.profiler true
theorem horizontal_strip
   : True := by
  set aff : ℂ → ℂ := sorry
  set g : ℝ → ℂ → ℂ  := fun ε w => (ε * ( (aff w) ))
  sorry
