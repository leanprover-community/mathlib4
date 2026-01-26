import Mathlib.Algebra.Order.Monoid.Canonical.Defs
/-!
# Instances on PUnit

This file collects facts about ordered algebraic structures on the one-element type.
-/

@[expose] public section

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
  isAddLeftRegular_of_ne_top := by simp

end PUnit
