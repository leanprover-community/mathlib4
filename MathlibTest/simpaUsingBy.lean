/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import Mathlib.Tactic.Linter.SimpaUsingBy

/-! Tests for the `simpaUsingBy` linter. -/

/--
warning: `simpa ... using by tactic` is a convoluted way to write `simp; tactic`
that potentially by-passes the flexible linter. Please change this to `simp; assumption`,
and adjust accordingly if this is flagged by the flexible linter.

Note: This linter can be disabled with `set_option linter.style.simpaUsingBy false`
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : a = b := by simpa using by assumption

-- tests on nested multiline proofs
/-- simpaUsingBy -/
#guard_msgs (substring := true) in
example (a b : Nat) (h : a = b) : a = b := by
  rw [eq_comm] at h
  have : b = a := by simpa using by grind
  simpa using by grind

-- tests on various syntaxes of `simpa`.
/-- simpaUsingBy -/
#guard_msgs (substring := true) in
example (a b : Nat) (h : a = b) : a = b := by
  simpa ?! +zetaDelta (disch := assumption) only [Nat.add_assoc] using by exact h

-- tests on the `simpa!` variant.
/-- simpaUsingBy -/
#guard_msgs (substring := true) in
example (a b : Nat) (h : a = b) : a = b := by
  simpa! +zetaDelta (disch := assumption) only [Nat.add_assoc] using by exact h

section

-- Test disabling the linter.
set_option linter.style.simpaUsingBy false

example (a b : Nat) (h : a = b) : a = b := by simpa using by assumption

end

-- Test disabling the linter.
set_option linter.style.simpaUsingBy false in
example (a b : Nat) (h : a = b) : a = b := by simpa using by assumption
