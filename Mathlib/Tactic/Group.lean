/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Massot
-/
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commutator

/-!
# `group` tactic

Normalizes expressions in the language of groups. The basic idea is to use the simplifier
to put everything into a product of group powers (`zpow` which takes a group element and an
integer), then simplify the exponents using a few carefully chosen `simp` lemmas.

This is a cheaper version of the `group_exp` tactic that doesn't use `ring_nf` to normalize
exponents.

## Tags

group_theory
-/

namespace Mathlib.Tactic.Group

open Lean
open Lean.Meta
open Lean.Parser.Tactic
open Lean.Elab.Tactic

-- The next three lemmas are not general purpose lemmas, they are intended for use only by
-- the `group` tactic.
@[to_additive]
theorem zpow_trick {G : Type*} [Group G] (a b : G) (n m : ℤ) :
    a * b ^ n * b ^ m = a * b ^ (n + m) := by rw [mul_assoc, ← zpow_add]

@[to_additive]
theorem zpow_trick_one {G : Type*} [Group G] (a b : G) (m : ℤ) :
    a * b * b ^ m = a * b ^ (m + 1) := by rw [mul_assoc, mul_self_zpow]

@[to_additive]
theorem zpow_trick_one' {G : Type*} [Group G] (a b : G) (n : ℤ) :
    a * b ^ n * b = a * b ^ (n + 1) := by rw [mul_assoc, mul_zpow_self]

/-- Auxiliary tactic for the `group` tactic. Calls the simplifier only. -/
syntax (name := group) "group" (location)? : tactic

macro_rules
| `(tactic| group $[at $location]?) =>
  `(tactic| simp -decide -failIfUnchanged only
    [commutatorElement_def,
      ← zpow_neg_one, ← zpow_natCast, ← zpow_mul,
      Int.ofNat_zero, Int.ofNat_add, Int.ofNat_mul,
      Int.mul_neg, Int.neg_mul, neg_neg,
      one_zpow, zpow_zero, zpow_one, mul_zpow_neg_one,
      ← mul_assoc,
      ← zpow_add, ← zpow_add_one, ← zpow_one_add, zpow_trick, zpow_trick_one, zpow_trick_one',
      Nat.sub_self, Int.sub_self,
      one_mul, Int.one_mul,
      mul_one, Int.mul_one,
      Int.add_neg_cancel,
      Int.neg_add_cancel]
  $[at $location]?)

end Mathlib.Tactic.Group
