/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Gabriel Ebner
-/
import Std.Tactic.Simpa

example {P : Prop} (p : P) : P := by simpa

example {P : Prop} (p : P) : P := by simpa using p

def foo (n : α) := [n]

example : foo n = [n] := by
  fail_if_success simpa only [foo]
  simp only [foo]

example (p : Nat → Prop) (h : p (a + b)) : p (b + a) := by
  have : a + b = b + a := Nat.add_comm _ _
  simpa [this] using h
