/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Ring.Defs

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"

/-!
# Algebraic instances for the natural numbers

This file contains the commutative semiring instance on the natural numbers.

## Implementation note

Std has a home-baked development of the algebraic and order theoretic theory of `ℕ` which, in
particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness libraries
in mathlib (naturals show up as indices in lists, cardinality in finsets, powers in groups, ...).
This home-baked development is pursued in `Data.Nat.Defs`.

Less basic uses of `ℕ` should however use the typeclass-mediated development. This file is the one
giving access to the algebraic instances. `Data.Nat.Order.Basic` is the one giving access to the
algebraic order instances.

## TODO

The names of this file, `Data.Nat.Defs` and `Data.Nat.Order.Basic` are archaic and don't match up
with reality anymore. Rename them.
-/

open Multiplicative

namespace Nat

/-! ### Instances -/

instance commSemiring : CommSemiring ℕ where
  __ := addCommMonoidWithOne
  __ := commMonoid
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

/-! Extra instances to short-circuit type class resolution and ensure computability -/


instance distrib : Distrib ℕ :=
  inferInstance

instance semiring : Semiring ℕ :=
  inferInstance

instance cancelCommMonoidWithZero : CancelCommMonoidWithZero ℕ :=
  { (inferInstance : CommMonoidWithZero ℕ) with
    mul_left_cancel_of_ne_zero :=
      fun h1 h2 => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) h2 }
#align nat.cancel_comm_monoid_with_zero Nat.cancelCommMonoidWithZero

end Nat
