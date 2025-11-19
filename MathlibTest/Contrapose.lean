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

/--
error: Tactic `contrapose` failed: the goal `p` is not of the form `_ → _` or `_ ↔ _`

p : Prop
h : p
⊢ p
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  contrapose
  exact h

/--
error: Tactic `contrapose` failed: hypothesis `p` is not a proposition

p q : Type
h : p → q
⊢ p → q
-/
#guard_msgs in
example (p q : Type) (h : p → q) : p → q := by
  contrapose
  exact h

/--
error: Tactic `contrapose` failed: the goal `∀ (h : p), q h` is a dependent arrow

p : Prop
q : p → Prop
⊢ ∀ (h : p), q h
-/
#guard_msgs in
example (p : Prop) (q : p → Prop) : (h : p) → q h := by
  contrapose

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

set_option contrapose.negate_iff false in
/--
error: Tactic `contrapose` failed: contraposing `↔` relations has been disabled.
To enable it, use `set_option contrapose.negate_iff true`.

p q : Prop
h : p ↔ q
⊢ ¬p ↔ ¬q
-/
#guard_msgs in
example (p q : Prop) (h : p ↔ q) : ¬p ↔ ¬q := by
  contrapose

/-! Test that we unfold reducible, but not semireducible definitions -/

example {α : Type} (a b : α) (p : Prop) (h : a = b → p) : ¬p → a ≠ b := by
  contrapose
  guard_target = a = b → p
  exact h

abbrev MyImp' (p q : Prop) := p → q
def MyImp := MyImp'
abbrev MyNot' (p : Prop) := ¬p
def MyNot := MyNot'

example (p q : Prop) (h : ¬q → ¬p) : MyImp p q := by
  fail_if_success contrapose
  unfold MyImp
  contrapose
  exact h

example (p q : Prop) (h : q → ¬p) : p → MyNot q := by
  fail_if_success (contrapose; exact h)
  unfold MyNot
  contrapose; exact h
