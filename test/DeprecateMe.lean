import Mathlib.Tactic.DeprecateMe
import Mathlib.Tactic.ToAdditive

namespace Nat

#guard_msgs in
deprecate_to depr_mul depr_add 2024-02-23
/-- I also have a doc-string -/
@[to_additive "As do I"]
theorem new_mul : True := .intro

/-- info:
Generated deprecations:
-------

@[deprecated]
alias old_mul := Nat.easy.mul

@[deprecated]
alias old_add := Nat.easy.add

-------
Pairings used (new, deprecated):
  (Nat.easy.mul, old_mul)
  (Nat.easy.add, old_add)
-------
* Ignoring: #[test.DeprecateMe._auxLemma.1]
-/
#guard_msgs in
deprecate_to! old_mul old_add 2024-01-01
/-- This is a doc-string -/
@[to_additive (attr := simp) "And this one is also a doc-string"]
nonrec def easy.mul : True := .intro

/-- warning:
Warnings:

Un-deprecated declarations: [Nat.foo.add]
-/
-- we provide one fewer name than we should and `deprecate_to` raises a warning.
#guard_msgs in
deprecate_to depr_foo_mul 2024-01-01
@[to_additive]
def foo.mul : Nat → Nat
  | 0 => 1
  | n => n

-- we provide too many names and `deprecate_to` throws an error and raises a warning.
/-- error: unused
---
warning: Warnings:

Unused names: [`three]
-/
#guard_msgs in
deprecate_to one two three 2024-01-01
@[to_additive]
def bar.mul : Nat → Nat
  | 0 => 1
  | n => n

/-- warning: `Nat.depr_mul` has been deprecated, use `Nat.new_mul` instead -/
--  we check that `depr_mul` is auto-deprecated.
#guard_msgs in
example : True := depr_mul

/-- warning: `Nat.depr_add` has been deprecated, use `Nat.new_add` instead -/
--  we check that `depr_add` is auto-deprecated.
#guard_msgs in
example : True := depr_add
