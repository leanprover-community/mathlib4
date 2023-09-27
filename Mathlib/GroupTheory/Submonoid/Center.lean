/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.GroupTheory.Subsemigroup.Center

#align_import group_theory.submonoid.center from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

/-!
# Centers of monoids

## Main definitions

* `Submonoid.center`: the center of a monoid
* `AddSubmonoid.center`: the center of an additive monoid

We provide `Subgroup.center`, `AddSubgroup.center`, `Subsemiring.center`, and `Subring.center` in
other files.
-/


namespace Submonoid

section

variable (M : Type*) [Monoid M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a monoid `M` is the set of elements that commute with everything in `M`"]
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center M
  mul_mem' := Set.mul_mem_center
#align submonoid.center Submonoid.center
#align add_submonoid.center AddSubmonoid.center

@[to_additive]
theorem coe_center : ↑(center M) = Set.center M :=
  rfl
#align submonoid.coe_center Submonoid.coe_center
#align add_submonoid.coe_center AddSubmonoid.coe_center

@[to_additive (attr := simp) AddSubmonoid.center_toAddSubsemigroup]
theorem center_toSubsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl
#align submonoid.center_to_subsemigroup Submonoid.center_toSubsemigroup

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align submonoid.mem_center_iff Submonoid.mem_center_iff
#align add_submonoid.mem_center_iff AddSubmonoid.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff
#align submonoid.decidable_mem_center Submonoid.decidableMemCenter
#align add_submonoid.decidable_mem_center AddSubmonoid.decidableMemCenter

/-- The center of a monoid is commutative. -/
instance center.commMonoid : CommMonoid (center M) :=
  { (center M).toMonoid with
    mul_comm := fun _ b => Subtype.ext <| b.prop _ }

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_left : SMulCommClass (center M) M M
    where smul_comm m x y := (Commute.left_comm (m.prop x) y).symm
#align submonoid.center.smul_comm_class_left Submonoid.center.smulCommClass_left

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _
#align submonoid.center.smul_comm_class_right Submonoid.center.smulCommClass_right

/-! Note that `smulCommClass (center M) (center M) M` is already implied by
`Submonoid.smulCommClass_right` -/

example : SMulCommClass (center M) (center M) M := by infer_instance

end

section

variable (M : Type*) [CommMonoid M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align submonoid.center_eq_top Submonoid.center_eq_top

end

end Submonoid

-- Guard against import creep
assert_not_exists Finset
