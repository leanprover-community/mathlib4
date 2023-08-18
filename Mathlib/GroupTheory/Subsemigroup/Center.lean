/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.Subsemigroup.Operations

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Subsemigroup.center`: the center of a semigroup
* `Set.addCenter`: the center of an additive magma
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.
-/


variable {M : Type*}

namespace Set

variable (M)

/-- The center of a magma. -/
@[to_additive addCenter " The center of an additive magma. "]
def center [Mul M] : Set M :=
  { z | ∀ m, m * z = z * m }
#align set.center Set.center
#align set.add_center Set.addCenter

-- porting note: The `to_additive` version used to be `mem_addCenter` without the iff
@[to_additive mem_addCenter_iff]
theorem mem_center_iff [Mul M] {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align set.mem_center_iff Set.mem_center_iff
#align set.mem_add_center Set.mem_addCenter_iff

instance decidableMemCenter [Mul M] [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (mem_center_iff M)
#align set.decidable_mem_center Set.decidableMemCenter

@[to_additive (attr := simp) zero_mem_addCenter]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.center M := by simp [mem_center_iff]
#align set.one_mem_center Set.one_mem_center
#align set.zero_mem_add_center Set.zero_mem_addCenter

@[simp]
theorem zero_mem_center [MulZeroClass M] : (0 : M) ∈ Set.center M := by simp [mem_center_iff]
#align set.zero_mem_center Set.zero_mem_center

variable {M}

@[to_additive (attr := simp) add_mem_addCenter]
theorem mul_mem_center [Semigroup M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a * b ∈ Set.center M := fun g => by rw [mul_assoc, ← hb g, ← mul_assoc, ha g, mul_assoc]
#align set.mul_mem_center Set.mul_mem_center
#align set.add_mem_add_center Set.add_mem_addCenter

@[to_additive (attr := simp) neg_mem_addCenter]
theorem inv_mem_center [Group M] {a : M} (ha : a ∈ Set.center M) :
    a⁻¹ ∈ Set.center M := fun g => by
  rw [← inv_inj, mul_inv_rev, inv_inv, ← ha, mul_inv_rev, inv_inv]
#align set.inv_mem_center Set.inv_mem_center
#align set.neg_mem_add_center Set.neg_mem_addCenter

@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M := fun c => by rw [add_mul, mul_add, ha c, hb c]
#align set.add_mem_center Set.add_mem_center

@[simp]
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a ∈ Set.center M) :
    -a ∈ Set.center M := fun c => by
  rw [← neg_mul_comm, ha (-c), neg_mul_comm]
#align set.neg_mem_center Set.neg_mem_centerₓ

@[to_additive subset_addCenter_add_units]
theorem subset_center_units [Monoid M] : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun _ ha _ => Units.ext <| ha _
#align set.subset_center_units Set.subset_center_units
#align set.subset_add_center_add_units Set.subset_addCenter_add_units

theorem center_units_subset [GroupWithZero M] : Set.center Mˣ ⊆ ((↑) : Mˣ → M) ⁻¹' center M :=
  fun a ha b => by
  obtain rfl | hb := eq_or_ne b 0
  · rw [zero_mul, mul_zero]
  · exact Units.ext_iff.mp (ha (Units.mk0 _ hb))
#align set.center_units_subset Set.center_units_subset

/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZero M] : Set.center Mˣ = ((↑) : Mˣ → M) ⁻¹' center M :=
  Subset.antisymm center_units_subset subset_center_units
#align set.center_units_eq Set.center_units_eq

@[simp]
theorem inv_mem_center₀ [GroupWithZero M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  obtain rfl | ha0 := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_center M
  rcases IsUnit.mk0 _ ha0 with ⟨a, rfl⟩
  rw [← Units.val_inv_eq_inv_val]
  exact center_units_subset (inv_mem_center (subset_center_units ha))
#align set.inv_mem_center₀ Set.inv_mem_center₀

@[to_additive (attr := simp) sub_mem_addCenter]
theorem div_mem_center [Group M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)
#align set.div_mem_center Set.div_mem_center
#align set.sub_mem_add_center Set.sub_mem_addCenter

@[simp]
theorem div_mem_center₀ [GroupWithZero M] {a b : M} (ha : a ∈ Set.center M)
    (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center₀ hb)
#align set.div_mem_center₀ Set.div_mem_center₀

variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
theorem center_eq_univ [CommSemigroup M] : center M = Set.univ :=
  (Subset.antisymm (subset_univ _)) fun x _ y => mul_comm y x
#align set.center_eq_univ Set.center_eq_univ
#align set.add_center_eq_univ Set.addCenter_eq_univ

end Set

namespace Subsemigroup

section

variable (M) [Semigroup M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a semigroup `M` is the set of elements that commute with everything in `M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center
#align subsemigroup.center Subsemigroup.center
#align add_subsemigroup.center AddSubsemigroup.center

-- porting note: `coe_center` is now redundant
#noalign subsemigroup.coe_center
#noalign add_subsemigroup.coe_center

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g :=
  Iff.rfl
#align subsemigroup.mem_center_iff Subsemigroup.mem_center_iff
#align add_subsemigroup.mem_center_iff AddSubsemigroup.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ mem_center_iff
#align subsemigroup.decidable_mem_center Subsemigroup.decidableMemCenter
#align add_subsemigroup.decidable_mem_center AddSubsemigroup.decidableMemCenter

/-- The center of a semigroup is commutative. -/
@[to_additive "The center of an additive semigroup is commutative."]
instance center.commSemigroup : CommSemigroup (center M) :=
  { MulMemClass.toSemigroup (center M) with mul_comm := fun _ b => Subtype.ext <| b.2 _ }
#align subsemigroup.center.comm_semigroup Subsemigroup.center.commSemigroup
#align add_subsemigroup.center.add_comm_semigroup AddSubsemigroup.center.addCommSemigroup

end

section

variable (M) [CommSemigroup M]

@[to_additive (attr := simp)]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align subsemigroup.center_eq_top Subsemigroup.center_eq_top
#align add_subsemigroup.center_eq_top AddSubsemigroup.center_eq_top

end

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
