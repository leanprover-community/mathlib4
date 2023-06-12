
/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module algebra.order.nonneg.ring
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Subring.Basic

/-!
# The nonnegative elements as subobjects

This file realizes the set `{x : α | 0 ≤ x}` as a subobject of the approriate category (note:
this is not actually connected to the category theory library at this time) under appropriate
hypotheses on the type `α`.

We separate this from the file `Algebra.Order.Nonneg.Ring` in order to avoid import creep.
-/

variable (α : Type _)

@[to_additive AddSubmonoid.nonneg]
def Submonoid.oneLE [OrderedCommMonoid α] : Submonoid α where
  carrier := Set.Ici 1
  mul_mem' := one_le_mul
  one_mem' := le_rfl

def Subsemiring.nonneg [OrderedSemiring α] : Subsemiring α where
  carrier := Set.Ici 0
  mul_mem' := mul_nonneg
  one_mem' := zero_le_one
  add_mem' := add_nonneg
  zero_mem' := le_rfl
