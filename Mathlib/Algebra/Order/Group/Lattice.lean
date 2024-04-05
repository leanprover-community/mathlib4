/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.OrderIso

#align_import algebra.order.lattice_group from "leanprover-community/mathlib"@"5dc275ec639221ca4d5f56938eb966f6ad9bc89f"

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942]. They form the algebraic
underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

A lattice ordered group is a type `α` satisfying:
* `Lattice α`
* `CommGroup α`
* `CovariantClass α α (· * ·) (· ≤ ·)`
* `CovariantClass α α (swap (· * ·)) (· ≤ ·)`

This file establishes basic properties of lattice ordered groups. It is shown that when the group is
commutative, the lattice is distributive. This also holds in the non-commutative case
([Birkhoff][birkhoff1942],[Fuchs][fuchs1963]) but we do not yet have the machinery to establish this
in mathlib.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, order, group
-/

open Function

variable {α β : Type*}

section Group
variable [Lattice α] [Group α] [CovariantClass α α (· * ·) (· ≤ ·)]
  [CovariantClass α α (swap (· * ·)) (· ≤ ·)]

-- Special case of Bourbaki A.VI.9 (1)
@[to_additive]
lemma mul_sup (a b c : α) : c * (a ⊔ b) = c * a ⊔ c * b := (OrderIso.mulLeft _).map_sup _ _
#align mul_sup mul_sup
#align add_sup add_sup

@[to_additive]
lemma sup_mul (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c := (OrderIso.mulRight _).map_sup _ _
#align sup_mul sup_mul
#align sup_add sup_add

@[to_additive]
lemma mul_inf (a b c : α) : c * (a ⊓ b) = c * a ⊓ c * b := (OrderIso.mulLeft _).map_inf _ _
#align mul_inf mul_inf
#align add_inf add_inf
#align lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul mul_inf
#align lattice_ordered_comm_group.add_inf_eq_add_inf_add add_inf

@[to_additive]
lemma inf_mul (a b c : α) : (a ⊓ b) * c = a * c ⊓ b * c := (OrderIso.mulRight _).map_inf _ _
#align inf_mul inf_mul
#align inf_add inf_add

-- Special case of Bourbaki A.VI.9 (2)
@[to_additive] lemma inv_sup (a b : α) : (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ := (OrderIso.inv α).map_sup _ _
#align inv_sup_eq_inv_inf_inv inv_sup
#align neg_sup_eq_neg_inf_neg neg_sup

@[to_additive] lemma inv_inf (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ := (OrderIso.inv α).map_inf _ _
#align inv_inf_eq_sup_inv inv_inf
#align neg_inf_eq_sup_neg neg_inf

@[to_additive]
lemma div_sup (a b c : α) : c / (a ⊔ b) = c / a ⊓ c / b := (OrderIso.divLeft c).map_sup _ _

@[to_additive]
lemma sup_div (a b c : α) : (a ⊔ b) / c = a / c ⊔ b / c := (OrderIso.divRight _).map_sup _ _

@[to_additive]
lemma div_inf (a b c : α) : c / (a ⊓ b) = c / a ⊔ c / b := (OrderIso.divLeft c).map_inf _ _

@[to_additive]
lemma inf_div (a b c : α) : (a ⊓ b) / c = a / c ⊓ b / c := (OrderIso.divRight _).map_inf _ _

-- In fact 0 ≤ n•a implies 0 ≤ a, see L. Fuchs, "Partially ordered algebraic systems"
-- Chapter V, 1.E
-- See also `one_le_pow_iff` for the existing version in linear orders
@[to_additive]
lemma pow_two_semiclosed
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a : α} (ha : 1 ≤ a ^ 2) : 1 ≤ a := by
  suffices this : (a ⊓ 1) * (a ⊓ 1) = a ⊓ 1 by
    rwa [← inf_eq_right, ← mul_right_eq_self]
  rw [mul_inf, inf_mul, ← pow_two, mul_one, one_mul, inf_assoc, inf_left_idem, inf_comm,
    inf_assoc, inf_of_le_left ha]

end Group

variable [Lattice α] [CommGroup α]

-- Fuchs p67
-- Bourbaki A.VI.10 Prop 7
@[to_additive]
lemma inf_mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b), mul_inv_cancel_right, mul_inv_cancel_comm]
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]
#align inf_mul_sup inf_mul_sup
#align inf_add_sup inf_add_sup

/-- Every lattice ordered commutative group is a distributive lattice. -/
-- Non-comm case needs cancellation law https://ncatlab.org/nlab/show/distributive+lattice
@[to_additive "Every lattice ordered commutative additive group is a distributive lattice"]
def CommGroup.toDistribLattice (α : Type*) [Lattice α] [CommGroup α]
    [CovariantClass α α (· * ·) (· ≤ ·)] : DistribLattice α where
  le_sup_inf x y z := by
    rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z), ← inv_mul_le_iff_le_mul,
      le_inf_iff]
    constructor
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_left) inf_le_left
    · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
      exact mul_le_mul' (inf_le_inf_left _ inf_le_right) inf_le_right
#align lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice CommGroup.toDistribLattice
#align lattice_ordered_comm_group.lattice_ordered_add_comm_group_to_distrib_lattice AddCommGroup.toDistribLattice
