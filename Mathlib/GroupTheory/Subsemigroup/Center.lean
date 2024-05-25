/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Subsemigroup.Operations

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of semigroups, as subsemigroups.

## Main definitions

* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
-/


/-! ### `Set.center` as a `Subsemigroup`. -/

variable (M)
namespace Subsemigroup

section Mul
variable [Mul M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a semigroup `M` is the set of elements that commute with everything in `M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center
#align subsemigroup.center Subsemigroup.center
#align add_subsemigroup.center AddSubsemigroup.center

-- Porting note: `coe_center` is now redundant
#noalign subsemigroup.coe_center
#noalign add_subsemigroup.coe_center

variable {M}

/-- The center of a magma is commutative and associative. -/
@[to_additive "The center of an additive magma is commutative and associative."]
instance center.commSemigroup : CommSemigroup (center M) where
  mul_assoc _ b _ := Subtype.ext <| b.2.mid_assoc _ _
  mul_comm a _ := Subtype.ext <| a.2.comm _
#align subsemigroup.center.comm_semigroup Subsemigroup.center.commSemigroup
#align add_subsemigroup.center.add_comm_semigroup AddSubsemigroup.center.addCommSemigroup

end Mul

section Semigroup
variable {M} [Semigroup M]

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
#align subsemigroup.mem_center_iff Subsemigroup.mem_center_iff
#align add_subsemigroup.mem_center_iff AddSubsemigroup.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] :
    Decidable (a ∈ center M) :=
  decidable_of_iff' _ Semigroup.mem_center_iff
#align subsemigroup.decidable_mem_center Subsemigroup.decidableMemCenter
#align add_subsemigroup.decidable_mem_center AddSubsemigroup.decidableMemCenter

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

@[to_additive (attr := simp)]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align subsemigroup.center_eq_top Subsemigroup.center_eq_top
#align add_subsemigroup.center_eq_top AddSubsemigroup.center_eq_top

end CommSemigroup

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
