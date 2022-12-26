/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.type_tags
! leanprover-community/mathlib commit 4dc134b97a3de65ef2ed881f3513d56260971562
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.Monoid.TypeTags

/-! # Ordered group structures on `Multiplicative α` and `Additive α`. -/


variable {α : Type _}

instance Multiplicative.orderedCommGroup [OrderedAddCommGroup α] :
    OrderedCommGroup (Multiplicative α) :=
  { Multiplicative.commGroup, Multiplicative.orderedCommMonoid with }

instance Additive.orderedAddCommGroup [OrderedCommGroup α] :
    OrderedAddCommGroup (Additive α) :=
  { Additive.addCommGroup, Additive.orderedAddCommMonoid with }

instance Multiplicative.linearOrderedCommGroup [LinearOrderedAddCommGroup α] :
    LinearOrderedCommGroup (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommGroup with }

instance Additive.linearOrderedAddCommGroup [LinearOrderedCommGroup α] :
    LinearOrderedAddCommGroup (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommGroup with }
