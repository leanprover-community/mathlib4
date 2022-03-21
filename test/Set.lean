/-
Copyright (c) 2022 Ian Benway. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ian Benway.
-/

import Mathlib.Tactic.Set

example (x : Nat) (h : x = x): x = x := by
  set! p := h
  set q : x = x := p
  apply q

example (x : Nat) (h : x + x - x = 3) : x + x - x = 3 := by
  set! y := x with ←h2
  set w := x
  set z := w with h3
  set a := 3
  set i'm_the_goal : Prop := z + z - z = a
  apply h

example (x : Nat) (h : x - x = 0) : x = x := by
  set! y : Nat := x
  set! z := y + 1 with ←eq1
  set! p : x - x = 0 := h with eq2
  rfl
