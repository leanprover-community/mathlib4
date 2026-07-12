/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Tactic.Group

/-!
# `add_group` tactic

Normalizes expressions in the language of additive groups. The basic idea is to use the simplifier
to put everything into a sum of integer scalar multiples (`zsmul` which takes an integer and an
additive group element), then simplify the scalars using the `ring_nf` tactic. The process needs
to be repeated since `ring_nf` can normalize a scalar to zero, leading to a summand that can be
removed before collecting scalars again. The simplifier step also uses some extra lemmas to avoid
some `ring_nf` invocations.

Note: Unlike the multiplicative `group` tactic which uses `← zpow_neg_one` to convert `a⁻¹` to
`a ^ (-1 : ℤ)`, the additive version cannot use `← neg_one_zsmul` to convert `-a` to
`(-1 : ℤ) • a` because `(-1 : ℤ)` is itself `-(1 : ℤ)`, causing simp to loop (since `ℤ` is also
an `AddGroup`). Instead, we handle negation via `neg_add_rev` to distribute negation over sums,
`zsmul_neg`/`neg_zsmul` for `n • (-a)`, and custom trick lemmas for combining `-b` with adjacent
`zsmul` terms. We also use `neg_one_zsmul` in the forward direction to normalize `(-1) • b`
to `-b`.

Other than this issue, the strategy parallels Thomas Browning and Patrick Massot's `group`
tactic.

## TODO

- Surface non-progress-related errors from `repeat`.
- Allow `add_group`s `ifUnchanged` behavior to be configurable.

## Tags

group theory, additive group
-/

public meta section

namespace Mathlib.Tactic.AddGroup

open Lean Meta Parser Tactic

-- The next six lemmas are not general purpose lemmas; they are intended for use only by
-- the `add_group` tactic, and so are prefixed with `_` to keep them out of autocomplete.
-- They handle the case where a negated element `-b` appears adjacent to a `zsmul` of the same
-- element, or adjacent to another negated copy.
-- This means we also want to convert `(-1) • b` to `-b` in order to apply these lemmas.
theorem _zsmul_neg_trick {G : Type*} [AddGroup G] (b : G) (n : ℤ) :
    n • b + (-b) = (n + (-1)) • b := by
  rw [← neg_one_zsmul b, ← add_zsmul]

theorem _neg_zsmul_trick {G : Type*} [AddGroup G] (b : G) (n : ℤ) :
    (-b) + n • b = ((-1) + n) • b := by
  rw [← neg_one_zsmul b, ← add_zsmul]

theorem _neg_neg_trick {G : Type*} [AddGroup G] (b : G) :
    (-b) + (-b) = (-2 : ℤ) • b := by
  have h : -b = (-1 : ℤ) • b := (neg_one_zsmul b).symm
  rw [h, ← add_zsmul]; norm_num

theorem _add_zsmul_neg_trick {G : Type*} [AddGroup G] (a b : G) (n : ℤ) :
    a + n • b + (-b) = a + (n + (-1)) • b := by
  rw [add_assoc, _zsmul_neg_trick]

theorem _add_neg_zsmul_trick {G : Type*} [AddGroup G] (a b : G) (n : ℤ) :
    a + (-b) + n • b = a + ((-1) + n) • b := by
  rw [add_assoc, _neg_zsmul_trick]

theorem _add_neg_neg_trick {G : Type*} [AddGroup G] (a b : G) :
    a + (-b) + (-b) = a + (-2 : ℤ) • b := by
  rw [add_assoc, _neg_neg_trick]

/--
`add_group` normalizes expressions in additive groups without assuming commutativity. Unlike
`abel`, which does take advantage of commutativity, `add_group` instead only uses the additive
group axioms without any information about which group is manipulated. If the goal is an equality,
and after normalization the two sides are equal, `add_group` closes the goal.

`add_group at l1 l2 ...` normalizes at the given locations.

For additive commutative groups, use the `abel` tactic instead.
For multiplicative groups, use the `group` tactic instead.

Example:
```lean
example {G : Type} [AddGroup G] (a b c d : G) (h : c = (a + 2 • b) + (-(b + b) + (-a)) + d) :
    a + c + (-d) = a := by
  add_group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]         -- the goal is now `a + d + (-d) = a`
  add_group      -- which is then normalized and closed
```
-/
syntax (name := addGroup) "add_group" (location)? : tactic

macro_rules
| `(tactic| add_group $[$loc]?) =>
  `(tactic| first
    | repeat1 fail_if_no_progress
        (simp -decide -failIfUnchanged only
          [addCommutatorElement_def, add_zero, zero_add,
            neg_add_rev, neg_zero, zsmul_neg, ← neg_zsmul,
            ← natCast_zsmul, ← mul_zsmul',
            Int.natCast_add, Int.natCast_mul, neg_neg,
            zsmul_zero, zero_zsmul, one_zsmul, neg_one_zsmul,
            ← add_assoc,
            ← add_zsmul, ← add_one_zsmul, ← one_add_zsmul,
            Mathlib.Tactic.Group._zsmul_trick,
            Mathlib.Tactic.Group._zsmul_trick_one,
            Mathlib.Tactic.Group._zsmul_trick_one',
            _zsmul_neg_trick, _neg_zsmul_trick, _neg_neg_trick,
            _add_zsmul_neg_trick, _add_neg_zsmul_trick, _add_neg_neg_trick,
            add_neg_cancel_right, neg_add_cancel_right,
            sub_eq_add_neg,
            tsub_self, sub_self, add_neg_cancel, neg_add_cancel]
          $[$loc]?
        <;> ring_nf (ifUnchanged := .silent) $[$loc]?)
    | fail "`add_group` made no progress")

end Mathlib.Tactic.AddGroup

/-!
We register `add_group` with the `hint` tactic.
-/

register_hint 900 add_group
