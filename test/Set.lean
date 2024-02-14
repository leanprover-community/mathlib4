/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Benway.
-/

import Mathlib.Tactic.Set
import Mathlib.Tactic.Basic
import Mathlib.Util.SleepHeartbeats
import Qq

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
  set g : Nat → Int := (fun ε => ε) with _h
  trivial

-- simulate a slow to elaborate term
open Qq in
elab "test" : term => do
  sleepAtLeastHeartbeats (1000 * 1000)
  return q((1 : Nat))

-- this will timeout if test is elaborated multiple times
set_option maxHeartbeats 3000 in
example {_a _b _c _d _e _f _g _h : Nat} : 1 = 1 := by
  set a : Nat := test with _h
  trivial
