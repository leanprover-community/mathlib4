/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.WithZero
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Nat.Basic

#align_import data.nat.order.basic from "leanprover-community/mathlib"@"3ed3f98a1e836241990d3d308f1577e434977130"

/-!
# Algebraic order instances for the natural numbers

This file contains algebraic order instances on the natural numbers and a few lemmas about them.

## Implementation note

Std has a home-baked development of the algebraic and order theoretic theory of `ℕ` which, in
particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness libraries
in mathlib (naturals show up as indices in lists, cardinality in finsets, powers in groups, ...).
This home-baked development is pursued in `Data.Nat.Defs`.

Less basic uses of `ℕ` should however use the typeclass-mediated development. `Data.Nat.Basic` gives
access to the algebraic instances. The current file is the one giving access to the algebraic
order instances.

## TODO

The names of this file, `Data.Nat.Defs` and `Data.Nat.Basic` are archaic and don't match up with
reality anymore. Rename them.
-/

universe u v

namespace Nat

/-! ### instances -/

instance orderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
#align nat.order_bot Nat.orderBot

instance linearOrderedCommSemiring : LinearOrderedCommSemiring ℕ :=
  { Nat.commSemiring, Nat.linearOrder with
    lt := Nat.lt, add_le_add_left := @Nat.add_le_add_left,
    le_of_add_le_add_left := @Nat.le_of_add_le_add_left,
    zero_le_one := Nat.le_of_lt (Nat.zero_lt_succ 0),
    mul_lt_mul_of_pos_left := @Nat.mul_lt_mul_of_pos_left,
    mul_lt_mul_of_pos_right := @Nat.mul_lt_mul_of_pos_right,
    exists_pair_ne := ⟨0, 1, ne_of_lt Nat.zero_lt_one⟩ }

instance linearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ :=
  { Nat.linearOrderedCommSemiring, (inferInstance : CommMonoidWithZero ℕ) with
    mul_le_mul_left := fun _ _ h c => Nat.mul_le_mul_left c h }

/-! Extra instances to short-circuit type class resolution and ensure computability -/


-- Not using `inferInstance` avoids `Classical.choice` in the following two
instance linearOrderedSemiring : LinearOrderedSemiring ℕ :=
  inferInstance

instance strictOrderedSemiring : StrictOrderedSemiring ℕ :=
  inferInstance

instance strictOrderedCommSemiring : StrictOrderedCommSemiring ℕ :=
  inferInstance

instance orderedSemiring : OrderedSemiring ℕ :=
  StrictOrderedSemiring.toOrderedSemiring'

instance orderedCommSemiring : OrderedCommSemiring ℕ :=
  StrictOrderedCommSemiring.toOrderedCommSemiring'

instance linearOrderedCancelAddCommMonoid : LinearOrderedCancelAddCommMonoid ℕ :=
  inferInstance

instance canonicallyOrderedCommSemiring : CanonicallyOrderedCommSemiring ℕ :=
  { Nat.nontrivial, Nat.orderBot, (inferInstance : OrderedAddCommMonoid ℕ),
    (inferInstance : LinearOrderedSemiring ℕ), (inferInstance : CommSemiring ℕ) with
    exists_add_of_le := fun {_ _} h => (Nat.le.dest h).imp fun _ => Eq.symm,
    le_self_add := Nat.le_add_right,
    eq_zero_or_eq_zero_of_mul_eq_zero := Nat.eq_zero_of_mul_eq_zero }

instance canonicallyLinearOrderedAddCommMonoid : CanonicallyLinearOrderedAddCommMonoid ℕ :=
  { (inferInstance : CanonicallyOrderedAddCommMonoid ℕ), Nat.linearOrder with }

instance : OrderedSub ℕ := by
  constructor
  intro m n k
  induction' n with n ih generalizing k
  · simp
  · simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

theorem _root_.NeZero.one_le {n : ℕ} [NeZero n] : 1 ≤ n := one_le_iff_ne_zero.mpr (NeZero.ne n)

end Nat
