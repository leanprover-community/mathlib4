/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.AddGroupWithTop

@[expose] public section
/-!
# Instances on PUnit

This file collects facts about ordered algebraic structures on the one-element type.
-/

namespace PUnit

instance canonicallyOrderedAdd : CanonicallyOrderedAdd PUnit where
  exists_add_of_le {_ _} _ := ⟨unit, by subsingleton⟩
  le_add_self _ _ := trivial
  le_self_add _ _ := trivial

instance isOrderedCancelAddMonoid : IsOrderedCancelAddMonoid PUnit where
  le_of_add_le_add_left _ _ _ _ := trivial
  add_le_add_left := by intros; rfl

instance : LinearOrderedAddCommMonoidWithTop PUnit where
  top := ()
  le_top _ := le_rfl
  top_add' _ := rfl

end PUnit
