/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Contrapose

example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  contrapose
  guard_target = ¬q → ¬p
  exact h

example (p q : Prop) (h : p) (hpq : ¬q → ¬p) : q := by
  contrapose h
  guard_target = ¬p
  exact hpq h

example (p q : Prop) (h : p) (hpq : ¬q → ¬p) : q := by
  contrapose h with h'
  guard_target = ¬p
  exact hpq h'

example (p q : Prop) (h : q → p) : ¬p → ¬q := by
  contrapose
  guard_target = q → p
  exact h

example (p q : Prop) (h : q → ¬p) : p → ¬q := by
  contrapose
  guard_target = q → ¬p
  exact h

example (p q : Prop) (h : ¬q → p) : ¬p → q := by
  contrapose
  guard_target = ¬q → p
  exact h

example (p q : Prop) (h : q → p) : ¬p → ¬q := by
  contrapose!
  guard_target = q → p
  exact h

example (p q : Prop) (h : ¬p) (hpq : q → p) : ¬q := by
  contrapose! h
  guard_target = p
  exact hpq h

example (p q : Prop) (h : ¬p) (hpq : q → p) : ¬q := by
  contrapose! h with h'
  guard_target = p
  exact hpq h'

example (p q r : Prop) (h : ¬ q ∧ ¬ r → ¬ p) : p → q ∨ r := by
  fail_if_success (contrapose; exact h)
  contrapose!; exact h

example (p : Prop) (h : p) : p := by
  fail_if_success contrapose
  exact h

example (p q : Type) (h : p → q) : p → q := by
  fail_if_success { contrapose }
  exact h

/-! test contraposing `↔` -/

example (p q : Prop) (h : p ↔ q) : ¬p ↔ ¬q := by
  contrapose
  guard_target = p ↔ q
  exact h

example (p q : Prop) (h : ¬p ↔ q) : p ↔ ¬q := by
  contrapose
  guard_target = ¬p ↔ q
  exact h

example (p q : Prop) (h : p ↔ ¬q) : ¬p ↔ q := by
  contrapose
  guard_target = p ↔ ¬q
  exact h

example (p q : Prop) (h : p ↔ q) : ¬p ↔ ¬q := by
  contrapose
  guard_target = p ↔ q
  exact h

example (p q r : Prop) (h : ¬p ↔ ¬q ∧ ¬r) : p ↔ q ∨ r := by
  contrapose!
  guard_target = ¬p ↔ ¬q ∧ ¬r
  exact h

set_option contrapose.iff false in
/--
error: Tactic `contrapose` failed: contraposing `↔` relations has been disabled.
To enable it, use `set_option contrapose.iff true`.

p q : Prop
h : p ↔ q
⊢ ¬p ↔ ¬q
-/
#guard_msgs in
example (p q : Prop) (h : p ↔ q) : ¬p ↔ ¬q := by
  contrapose
