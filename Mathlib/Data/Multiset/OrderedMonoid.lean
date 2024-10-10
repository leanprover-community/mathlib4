/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Multisets as ordered monoids

The `OrderedCancelAddCommMonoid` and `CanonicallyOrderedAddCommMonoid` instances on `Multiset α`

-/

variable {α : Type*}

namespace Multiset

open List

instance : OrderedCancelAddCommMonoid (Multiset α) where
  add_le_add_left := fun _ _ => add_le_add_left
  le_of_add_le_add_left := fun _ _ _ => le_of_add_le_add_left

instance : CanonicallyOrderedAddCommMonoid (Multiset α) where
  __ := inferInstanceAs (OrderBot (Multiset α))
  le_self_add := le_add_right
  exists_add_of_le h := exists_add_of_le h

end Multiset
