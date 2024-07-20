/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.PUnitInstances.Algebra
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Order.Heyting.Basic

/-!
# Instances on PUnit

This file collects facts about ordered algebraic structures on the one-element type.
-/

namespace PUnit

instance canonicallyOrderedAddCommMonoid : CanonicallyOrderedAddCommMonoid PUnit where
  exists_add_of_le {_ _} _ := ⟨unit, by subsingleton⟩
  add_le_add_left _ _ _ _ := trivial
  le_self_add _ _ := trivial

instance linearOrderedCancelAddCommMonoid : LinearOrderedCancelAddCommMonoid PUnit where
  __ := PUnit.instLinearOrder
  le_of_add_le_add_left _ _ _ _ := trivial
  add_le_add_left := by intros; rfl

instance : LinearOrderedAddCommMonoidWithTop PUnit where
  top_add' _ := rfl

end PUnit
