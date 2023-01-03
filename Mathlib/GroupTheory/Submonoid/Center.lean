/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.submonoid.center
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.GroupTheory.Subsemigroup.Center

/-!
# Centers of monoids

## Main definitions

* `submonoid.center`: the center of a monoid
* `add_submonoid.center`: the center of an additive monoid

We provide `subgroup.center`, `add_subgroup.center`, `subsemiring.center`, and `subring.center` in
other files.
-/


namespace Submonoid

section

variable (M : Type _) [Monoid M]

/-- The center of a monoid `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a monoid `M` is the set of elements that commute with everything in\n`M`"]
def center : Submonoid M where
  carrier := Set.center M
  one_mem' := Set.one_mem_center M
  mul_mem' a b := Set.mul_mem_center
#align submonoid.center Submonoid.center

@[to_additive]
theorem coe_center : ↑(center M) = Set.center M :=
  rfl
#align submonoid.coe_center Submonoid.coe_center

@[simp]
theorem center_to_subsemigroup : (center M).toSubsemigroup = Subsemigroup.center M :=
  rfl
#align submonoid.center_to_subsemigroup Submonoid.center_to_subsemigroup

theorem AddSubmonoid.center_to_add_subsemigroup (M) [AddMonoid M] :
    (AddSubmonoid.center M).toAddSubsemigroup = AddSubsemigroup.center M :=
  rfl
#align add_submonoid.center_to_add_subsemigroup AddSubmonoid.center_to_add_subsemigroup

attribute [to_additive AddSubmonoid.center_to_add_subsemigroup] Submonoid.center_to_subsemigroup

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align submonoid.mem_center_iff Submonoid.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff
#align submonoid.decidable_mem_center Submonoid.decidableMemCenter

/-- The center of a monoid is commutative. -/
instance : CommMonoid (center M) :=
  { (center M).toMonoid with mul_comm := fun a b => Subtype.ext <| b.Prop _ }

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smul_comm_class_left : SMulCommClass (center M) M M
    where smul_comm m x y := (Commute.left_comm (m.Prop x) y).symm
#align submonoid.center.smul_comm_class_left Submonoid.center.smul_comm_class_left

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smul_comm_class_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _
#align submonoid.center.smul_comm_class_right Submonoid.center.smul_comm_class_right

/-! Note that `smul_comm_class (center M) (center M) M` is already implied by
`submonoid.smul_comm_class_right` -/


example : SMulCommClass (center M) (center M) M := by infer_instance

end

section

variable (M : Type _) [CommMonoid M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align submonoid.center_eq_top Submonoid.center_eq_top

end

end Submonoid

-- Guard against import creep
assert_not_exists finset

