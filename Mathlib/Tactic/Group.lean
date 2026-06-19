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

## TODO

- Surface non-progress-related errors from `repeat`.
- Allow `group`s `ifUnchanged` behavior to be configurable.
- Use cycling to normalise expressions further. For instance:
  `b ^ 17 * c⁻¹ * d * b ^ 3 = 1` to `b^20 * c⁻¹ * d = 1` and
  `(a * b *c)^m * a * b * (c * a * b)^n * c = (a * b * c)^(n + m +1)`

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

-- The next lemmas are not general purpose lemmas, they are intended for use only by
-- the `group` tactic. In particular, they deal with *left* and *right* cancellation.
@[to_additive]
theorem _mul_right_cancel_aux₁ {G : Type*} [Group G] (a b c : G) :
   a * b = c * b ↔ a = c := mul_right_cancel_iff

@[to_additive]
theorem _mul_right_cancel_aux₂ {G : Type*} [Group G] (a b c : G) (n : ℤ) :
    a * b = c * b ^ n ↔ a = c * b ^ (n - 1) := by
  rw [zpow_sub_one, ← mul_assoc, ← eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem _mul_right_cancel_aux₃ {G : Type*} [Group G] (a b c : G) (n : ℤ) :
    a * b ^ n = c * b ↔ a = c * b ^ (-n + 1) := by
  rw [← mul_self_zpow, zpow_neg, ← mul_assoc, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem _mul_right_cancel_aux₄ {G : Type*} [Group G] (a b c : G) (n m : ℤ) :
    a * b ^ n = c * b ^ m ↔ a = c * b ^ (m - n) := by
  rw [zpow_sub, ← mul_assoc, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem _mul_right_cancel_aux₅ {G : Type*} [Group G] (a b : G) :
    a * b = b ↔ a = 1 := mul_eq_right

@[to_additive]
theorem _mul_right_cancel_aux₆ {G : Type*} [Group G] (a b : G) (n : ℤ) :
    a * b = b ^ n ↔ a = b ^ (n - 1) := by rw [zpow_sub_one, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem _mul_right_cancel_aux₇ {G : Type*} [Group G] (a b : G) (n : ℤ) :
    a * b ^ n = b ↔ a = b ^ (1 - n) := by rw [zpow_sub, eq_mul_inv_iff_mul_eq, zpow_one]

@[to_additive]
theorem _mul_right_cancel_aux₈ {G : Type*} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n = b ^ m ↔ a = b ^ (m - n) := by rw [zpow_sub, eq_mul_inv_iff_mul_eq]

@[to_additive]
theorem _mul_left_cancel_aux₁ {G : Type*} [Group G] (a b c : G) :
    b * a = b * c ↔ a = c := by rw [mul_left_cancel_iff]

@[to_additive]
theorem _mul_left_cancel_aux₂ {G : Type*} [Group G] (a b c : G) (n : ℤ) :
    b * a = b ^ n * c  ↔ a = b ^ (n - 1) * c := by
  rw [← eq_inv_mul_iff_mul_eq, ← mul_assoc, ← zpow_neg_one, zpow_mul_comm, zpow_sub_one,
    zpow_neg_one]

@[to_additive]
theorem _mul_left_cancel_aux₃ {G : Type*} [Group G] (a b c : G) (n : ℤ) :
    b ^ n * a = b * c ↔ a = b ^ (-n + 1) * c:= by
  rw [← eq_inv_mul_iff_mul_eq, ← mul_assoc, ← zpow_neg, zpow_add, zpow_one]

@[to_additive]
theorem _mul_left_cancel_aux₄ {G : Type*} [Group G] (a b c : G) (n m : ℤ) :
    b ^ n * a = b ^ m * c ↔ a = b ^ (m - n) * c := by
  rw [zpow_sub, ← zpow_neg, zpow_mul_comm, mul_assoc, zpow_neg, eq_inv_mul_iff_mul_eq]

@[to_additive]
theorem _mul_left_cancel_aux₅ {G : Type*} [Group G] (a b : G) :
    b * a = b ↔ a = 1 := mul_eq_left

@[to_additive]
theorem _mul_left_cancel_aux₆ {G : Type*} [Group G] (a b : G) (n : ℤ) :
    b * a = b ^ n ↔ a = b ^ (n - 1) := by
  rw [zpow_sub_one, ← zpow_neg_one, zpow_mul_comm, zpow_neg_one, eq_inv_mul_iff_mul_eq]

@[to_additive]
theorem _mul_left_cancel_aux₇ {G : Type*} [Group G] (a b : G) (n : ℤ) :
    b ^ n * a = b ↔ a = b ^ (1 - n) := by
  rw [zpow_sub, ← zpow_neg,zpow_mul_comm, zpow_neg, zpow_one, eq_inv_mul_iff_mul_eq]

@[to_additive]
theorem _mul_left_cancel_aux₈ {G : Type*} [Group G] (a b : G) (n m : ℤ) :
    b ^ n * a = b ^ m ↔ a = b ^ (m - n) := by
  rw [zpow_sub, ← zpow_neg, zpow_mul_comm, zpow_neg, eq_inv_mul_iff_mul_eq]

@[to_additive]
theorem _move_mul_left_neg {G : Type*} [Group G] (a b c : G) (n : ℤ) :
  a = b ^ (- n) * c ↔ b ^ n * a = c := by rw [zpow_neg, eq_inv_mul_iff_mul_eq]

@[to_additive]
theorem _move_mul_right_neg {G : Type*} [Group G] (a b c : G) (n : ℤ) :
  a = c * b ^ (- n) ↔ a * b ^ n = c := by rw [zpow_neg, eq_mul_inv_iff_mul_eq]

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
  let baseSimpTac ← `(tactic |
    simp -decide -failIfUnchanged only
          [commutatorElement_def, mul_one, one_mul,
            ← zpow_neg_one, ← zpow_natCast, ← zpow_mul,
            Int.natCast_add, Int.natCast_mul,
            Int.mul_neg, Int.neg_mul, neg_neg,
            one_zpow, zpow_zero, zpow_one, mul_zpow_neg_one,
            ← mul_assoc, ← sq,
            ← zpow_add, ← zpow_add_one, ← zpow_one_add,
            _zpow_trick, _zpow_trick_one, _zpow_trick_one',
            tsub_self, sub_self, add_neg_cancel, neg_add_cancel]
          $[$loc]?)
  -- a tactic block calling the `ring_nf` tactic to simplify exponents
  let simpExpTac ← `(tactic |
    ring_nf (ifUnchanged := .silent) $[$loc]?)
  -- tactic block for applying cancellation on the *right*
  let rightCancelAux₁ ← `(tactic |
    simp -decide -failIfUnchanged only [_mul_right_cancel_aux₁, _mul_right_cancel_aux₂,
      _mul_right_cancel_aux₃, _mul_right_cancel_aux₄, _mul_right_cancel_aux₅,
      _mul_right_cancel_aux₆, _mul_right_cancel_aux₇, _mul_right_cancel_aux₈] $[$loc]?)
  let rightCancelAux₂ ← `(tactic |
      simp -decide -failIfUnchanged only [_move_mul_right_neg] $[$loc]?)
  -- tactic block for applying cancellation on the *left*
  let leftCancelAux₁ ← `(tactic |
    simp -decide -failIfUnchanged only [↓mul_assoc, _mul_left_cancel_aux₁, _mul_left_cancel_aux₂,
    _mul_left_cancel_aux₃, _mul_left_cancel_aux₄, _mul_left_cancel_aux₅,
    _mul_left_cancel_aux₆, _mul_left_cancel_aux₇, _mul_left_cancel_aux₈] $[$loc]?)
  let leftCancelAux₂ ← `(tactic | simp -decide -failIfUnchanged only [_move_mul_left_neg] $[$loc]?)
  -- post-processing tactic for cleaning up expressions of the form ( · )^(-1) to ( · )⁻¹
  let cleanUpTac ← `(tactic |
    simp -decide -failIfUnchanged only [zpow_neg _ 1, zpow_one, ↓← mul_assoc] $[$loc]?)
  -- normalise the expression, apply left and right cancellation and then clean up the expression
  -- after the simplifying the expression
  `(tactic| first
    | fail_if_no_progress (
      repeat (fail_if_no_progress ($baseSimpTac <;> $simpExpTac));
      <;> repeat (fail_if_no_progress ($rightCancelAux₁ <;> $simpExpTac <;> $rightCancelAux₂ <;>
        $leftCancelAux₁ <;> $simpExpTac <;> $leftCancelAux₂));
      -- <;> repeat ((fail_if_no_progress ($leftCancelAux₁ <;> $simpExpTac <;> $leftCancelAux₂)));
      <;> $cleanUpTac
    )
    | fail "`group` made no progress")

end Mathlib.Tactic.Group

/-!
We register `group` with the `hint` tactic.
-/

register_hint 900 group
