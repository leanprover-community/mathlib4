/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Commutator  -- shake: keep (tactic dependency)
public import Mathlib.Algebra.Order.Sub.Basic  -- shake: keep (tactic dependency)
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Ring

/-!
# `group` tactic

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using the `ring_nf` tactic. The process needs to be repeated
since `ring_nf` can normalize an exponent to zero, leading to a factor that can be removed
before collecting exponents again. The simplifier step also uses some extra lemmas to avoid
some `ring_nf` invocations.

## Tags

group theory
-/

public meta section

namespace Mathlib.Tactic.Group

open Lean Meta Parser Tactic

-- The next three lemmas are not general purpose lemmas, they are intended for use only by
-- the `group` tactic.
@[to_additive]
theorem _zpow_trick {G : Type*} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ m = a * b ^ (n + m) := by rw [mul_assoc, ← zpow_add]

@[to_additive _zsmul_trick_one]
theorem _zpow_trick_one {G : Type*} [Group G] (a b : G) (m : ℤ) :
    a * b * b ^ m = a * b ^ (m + 1) := by rw [mul_assoc, mul_self_zpow]

@[to_additive _zsmul_trick_one']
theorem _zpow_trick_one' {G : Type*} [Group G] (a b : G) (n : ℤ) :
    a * b ^ n * b = a * b ^ (n + 1) := by rw [mul_assoc, mul_zpow_self]

/-- `group` normalizes expressions in multiplicative groups that occur in the goal. `group` does not
assume commutativity, instead using only the group axioms without any information about which group
is manipulated. If the goal is an equality, and after normalization the two sides are equal, `group`
closes the goal.

For additive commutative groups, use the `abel` tactic instead.

* `group at l1 l2 ...` normalizes at the given locations.

Example:
```lean
example {G : Type} [Group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a := by
  group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]     -- the goal is now `a*d*d⁻¹ = a`
  group      -- which then normalized and closed
```
-/
syntax (name := group) "group" (location)? : tactic

macro_rules
| `(tactic| group $[$loc]?) => do
  let simpTacStx ← `(tactic| simp -decide -failIfUnchanged only
    [commutatorElement_def, mul_one, one_mul,
      ← zpow_neg_one, ← zpow_natCast, ← zpow_mul,
      Int.natCast_add, Int.natCast_mul,
      Int.mul_neg, Int.neg_mul, neg_neg,
      one_zpow, zpow_zero, zpow_one, mul_zpow_neg_one,
      ← mul_assoc,
      ← zpow_add, ← zpow_add_one, ← zpow_one_add,
      _zpow_trick, _zpow_trick_one, _zpow_trick_one',
      tsub_self, sub_self, add_neg_cancel, neg_add_cancel]
    $[$loc]?)
  `(tactic| first
    | repeat1 fail_if_no_progress ($simpTacStx <;> ring_nf (ifUnchanged := .silent) $[$loc]?)
    | fail "`group` made no progress")

end Mathlib.Tactic.Group

/-!
We register `group` with the `hint` tactic.
-/

register_hint 900 group
