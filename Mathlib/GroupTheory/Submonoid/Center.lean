/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Submonoid.Operations
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

section MulOneClass

variable (M : Type*) [MulOneClass M]

/-- The center of a multiplication with unit `M` is the set of elements that commute with everything
in `M` -/
@[to_additive
      "The center of an addition with zero `M` is the set of elements that commute with everything
      in `M`"]
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

/-- The center of a multiplication with unit is commutative and associative.

This is not an instance as it forms an non-defeq diamond with `Submonoid.toMonoid` in the `npow`
field. -/
@[to_additive "The center of an addition with zero is commutative and associative."]
abbrev center.commMonoid' : CommMonoid (center M) :=
  { (center M).toMulOneClass, Subsemigroup.center.commSemigroup with }

end MulOneClass

section Monoid

variable {M} [Monoid M]

/-- The center of a monoid is commutative. -/
@[to_additive]
instance center.commMonoid : CommMonoid (center M) :=
  { (center M).toMonoid, Subsemigroup.center.commSemigroup with }

-- no instance diamond, unlike the primed version
example : center.commMonoid.toMonoid = Submonoid.toMonoid (center M) := by
  with_reducible_and_instances rfl

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
#align submonoid.mem_center_iff Submonoid.mem_center_iff
#align add_submonoid.mem_center_iff AddSubmonoid.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff
#align submonoid.decidable_mem_center Submonoid.decidableMemCenter
#align add_submonoid.decidable_mem_center AddSubmonoid.decidableMemCenter



/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_left : SMulCommClass (center M) M M where
  smul_comm m x y := Commute.left_comm (m.prop.comm x) y
#align submonoid.center.smul_comm_class_left Submonoid.center.smulCommClass_left

/-- The center of a monoid acts commutatively on that monoid. -/
instance center.smulCommClass_right : SMulCommClass M (center M) M :=
  SMulCommClass.symm _ _ _
#align submonoid.center.smul_comm_class_right Submonoid.center.smulCommClass_right

/-! Note that `smulCommClass (center M) (center M) M` is already implied by
`Submonoid.smulCommClass_right` -/

example : SMulCommClass (center M) (center M) M := by infer_instance

end Monoid

section

variable (M : Type*) [CommMonoid M]

@[simp]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align submonoid.center_eq_top Submonoid.center_eq_top

end

end Submonoid

variable (M)

/-- For a monoid, the units of the center inject into the center of the units. This is not an
equivalence in general; one case when it is is for groups with zero, which is covered in
`centerUnitsEquivUnitsCenter`. -/
@[to_additive (attr := simps! apply_coe_val)
  "For an additive monoid, the units of the center inject into the center of the units."]
def unitsCenterToCenterUnits [Monoid M] : (Submonoid.center M)ˣ →* Submonoid.center (Mˣ) :=
  (Units.map (Submonoid.center M).subtype).codRestrict _ <|
      fun u ↦ Submonoid.mem_center_iff.mpr <|
        fun r ↦ Units.ext <| by
        rw [Units.val_mul, Units.coe_map, Submonoid.coe_subtype, Units.val_mul, Units.coe_map,
          Submonoid.coe_subtype, u.1.prop.comm r]

@[to_additive]
theorem unitsCenterToCenterUnits_injective [Monoid M] :
    Function.Injective (unitsCenterToCenterUnits M) :=
  fun _a _b h => Units.ext <| Subtype.ext <| congr_arg (Units.val ∘ Subtype.val) h

-- Guard against import creep
assert_not_exists Finset
