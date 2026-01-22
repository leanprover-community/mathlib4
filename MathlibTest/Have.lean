/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/
import Mathlib.Tactic.Have

example : Nat := by
  have h : Nat
  exact 5
  exact h

example : Nat := by
  have : Nat
  · exact 5
  exact this

example {a : Nat} : a = a := by
  have h : a = a
  · rfl
  exact h

example {a : Nat} : a = a := by
  have : a = a
  · rfl
  exact this

example : True := by
  let _N; -- FIXME: https://github.com/leanprover/lean4/issues/1670
  exact Nat
  have
  · exact 0
  have _h : Nat
  · exact this
  have _h' x : x < x + 1
  · exact Nat.lt_add_one x
  have _h'' (x : Nat) : x < x + 1
  · exact Nat.lt_add_one x
  let _m
  · exact 6
  let _m' x (y : Nat) : x + y = y + x
  rw [Nat.add_comm]
  have _q
  · exact 6
  simp

/--
error: type expected, got
  (Nat.zero : Nat)
-/
#guard_msgs in
example : True := by have h : Nat.zero
