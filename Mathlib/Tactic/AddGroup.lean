/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Massot
-/
module

public import Mathlib.Algebra.Order.Sub.Basic  -- shake: keep (tactic dependency)
public meta import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring

/-!
# `add_group` tactic

Normalizes expressions in the language of additive groups. The basic idea is to use the simplifier
to put everything into a sum of integer scalar multiples (`zsmul` which takes an integer and an
additive group element), then simplify the scalars using the `ring` tactic. The process needs to be
repeated since `ring` can normalize a scalar to zero, leading to a summand that can be removed
before collecting scalars again. The simplifier step also uses some extra lemmas to avoid
some `ring` invocations.

Note: Unlike the multiplicative `group` tactic which uses `← zpow_neg_one` to convert `a⁻¹` to
`a ^ (-1 : ℤ)`, the additive version cannot use `← neg_one_zsmul` to convert `-a` to
`(-1 : ℤ) • a` because `(-1 : ℤ)` is itself `-(1 : ℤ)`, causing simp to loop (since `ℤ` is also
an `AddGroup`). Instead, we handle negation via `neg_add_rev` to distribute negation over sums,
`zsmul_neg`/`neg_zsmul` for `n • (-a)`, and custom trick lemmas for combining `-b` with adjacent
`zsmul` terms.

Other than this issue, this is a direct port from Thomas Browning and Patrick Massot's `group`
tactic.

## Tags

group theory, additive group
-/

public meta section

namespace Mathlib.Tactic.AddGroup

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic

-- The next three lemmas are not general purpose lemmas, they are intended for use only by
-- the `add_group` tactic.
-- They handle the case where a negated element `-b` appears adjacent to a `zsmul` of the same
-- element, or adjacent to another negated copy.
theorem zsmul_neg_trick {G : Type*} [AddGroup G] (a b : G) (n : ℤ) :
    a + n • b + (-b) = a + (n + (-1)) • b := by
  rw [add_assoc, ← neg_one_zsmul b, ← add_zsmul]

theorem zsmul_neg_trick' {G : Type*} [AddGroup G] (a b : G) (n : ℤ) :
    a + (-b) + n • b = a + ((-1) + n) • b := by
  rw [add_assoc, ← neg_one_zsmul b, ← add_zsmul]

theorem neg_neg_trick {G : Type*} [AddGroup G] (a b : G) :
    a + (-b) + (-b) = a + (-2 : ℤ) • b := by
  have h : -b = (-1 : ℤ) • b := (neg_one_zsmul b).symm
  rw [h, add_assoc, ← add_zsmul]; norm_num

/-- Auxiliary tactic for the `add_group` tactic. Calls the simplifier only. -/
syntax (name := aux_add_group₁) "aux_add_group₁" (location)? : tactic

macro_rules
| `(tactic| aux_add_group₁ $[at $location]?) =>
  `(tactic| simp -decide -failIfUnchanged only
    [neg_add_rev, neg_zero, zsmul_neg, ← neg_zsmul,
      add_zero, zero_add,
      ← natCast_zsmul, ← mul_zsmul',
      Int.natCast_add, Int.natCast_mul, neg_neg,
      zsmul_zero, zero_zsmul, one_zsmul,
      ← add_assoc,
      ← add_zsmul, ← add_one_zsmul, ← one_add_zsmul,
      Mathlib.Tactic.Group.zsmul_trick,
      Mathlib.Tactic.Group.zsmul_trick_zero,
      Mathlib.Tactic.Group.zsmul_trick_zero',
      zsmul_neg_trick, zsmul_neg_trick',
      add_neg_cancel_right, neg_add_cancel_right,
      neg_neg_trick,
      tsub_self, sub_self, add_neg_cancel, neg_add_cancel]
  $[at $location]?)

/-- Auxiliary tactic for the `add_group` tactic. Calls `ring_nf` to normalize scalars. -/
syntax (name := aux_add_group₂) "aux_add_group₂" (location)? : tactic

macro_rules
| `(tactic| aux_add_group₂ $[at $location]?) =>
  `(tactic| ring_nf -failIfUnchanged $[at $location]?)

/-- `add_group` normalizes expressions in additive groups that occur in the goal. `add_group` does
not assume commutativity, instead using only the additive group axioms without any information about
which group is manipulated. If the goal is an equality, and after normalization the two sides are
equal, `add_group` closes the goal.

For multiplicative groups, use the `group` tactic instead.
For additive commutative groups, use the `abel` tactic instead.

* `add_group at l1 l2 ...` normalizes at the given locations.

Example:
```lean
example {G : Type} [AddGroup G] (a b c d : G) (h : c = (a + 2 • b) + (-(b + b) + (-a)) + d) :
    a + c + (-d) = a := by
  add_group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]         -- the goal is now `a + d + (-d) = a`
  add_group      -- which is then normalized and closed
```
-/
syntax (name := add_group) "add_group" (location)? : tactic

macro_rules
| `(tactic| add_group $[$loc]?) =>
  `(tactic| repeat (fail_if_no_progress (aux_add_group₁ $[$loc]? <;> aux_add_group₂ $[$loc]?)))

end Mathlib.Tactic.AddGroup

/-!
We register `add_group` with the `hint` tactic.
-/

register_hint 900 add_group
