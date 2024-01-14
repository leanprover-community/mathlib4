/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Lattice
import Mathlib.Tactic.LibrarySearch

#align_import algebra.order.lattice_group from "leanprover-community/mathlib"@"5dc275ec639221ca4d5f56938eb966f6ad9bc89f"

/-!
# Positive & negative parts

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure).

This file defines `posPart` and `negPart`, the positive and negative parts of an element in a
lattice ordered group.

## Main statements

* `posPart_sub_negPart`: Every element `a` can be decomposed into `a⁺ - a⁻`, the difference of its
  positive and negative parts.
* `posPart_inf_negPart_eq_zero`: The positive and negative parts are coprime.

## Notations

* `a⁺ᵐ = a ⊔ 1`: The *positive component* of an element `a` of a lattice ordered group
* `a⁻ᵐ = (-a) ⊔ 1`: The *negative component* of an element `a` of a lattice ordered group
* `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered group
* `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered group

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

positive part, negative part
-/

/-- The positive part of an element admitting a decomposition into positive and negative parts.
-/
class PosPart (α : Type*) where
  /-- The positive part function. -/
  pos : α → α

#align has_pos_part PosPart

/-- The negative part of an element admitting a decomposition into positive and negative parts.
-/
class NegPart (α : Type*) where
  /-- The negative part function. -/
  neg : α → α

#align has_neg_part NegPart

@[inherit_doc]
postfix:max "⁺" => PosPart.pos

@[inherit_doc]
postfix:max "⁻" => NegPart.neg

open Function

universe u v

variable {α : Type u} {β : Type v}

section Lattice
variable [Lattice α]

section Group
variable [Group α] [CovariantClass α α (· * ·) (· ≤ ·)]
  [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a : α}

#noalign lattice_ordered_comm_group.has_one_lattice_has_pos_part
#noalign lattice_ordered_comm_group.has_zero_lattice_has_pos_part
#noalign lattice_ordered_comm_group.has_one_lattice_has_neg_part
#noalign lattice_ordered_comm_group.has_zero_lattice_has_neg_part

/-- The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 1`, denoted `a⁺ᵐ`. -/
@[to_additive
"The *positive part* of an element `a` in a lattice ordered group is `a ⊔ 0`, denoted `a⁺`."]
def oneLePart (a : α) : α := a ⊔ 1
#align lattice_ordered_comm_group.m_pos_part_def oneLePart
#align lattice_ordered_comm_group.pos_part_def posPart
#align has_pos_part.pos posPart

/-- The *negative part* of an element `a` in a lattice ordered group is `a⁻¹ ⊔ 1`, denoted `a⁻ᵐ `.
-/
@[to_additive
"The *negative part* of an element `a` in a lattice ordered group is `(-a) ⊔ 0`, denoted `a⁻`."]
def leOnePart (a : α) : α := a⁻¹ ⊔ 1
#align lattice_ordered_comm_group.m_neg_part_def leOnePart
#align lattice_ordered_comm_group.neg_part_def negPart
#align has_neg_part.neg negPart

@[inherit_doc] postfix:max "⁺ᵐ " => oneLePart
@[inherit_doc] postfix:max "⁻ᵐ" => leOnePart
@[inherit_doc] postfix:max "⁺" => posPart
@[inherit_doc] postfix:max "⁻" => negPart

@[to_additive] lemma oneLePart_mono : Monotone (oneLePart : α → α) :=
  fun _a _b hab ↦ sup_le_sup_right hab _

@[to_additive] lemma leOnePart_anti : Antitone (leOnePart : α → α) :=
  fun _a _b hab ↦ sup_le_sup_right (inv_le_inv_iff.2 hab) _

@[to_additive (attr := simp)] lemma oneLePart_one : (1 : α)⁺ᵐ = 1 := sup_idem
#align lattice_ordered_comm_group.pos_one oneLePart_one
#align lattice_ordered_comm_group.pos_zero posPart_zero

@[to_additive (attr := simp)] lemma leOnePart_one : (1 : α)⁻ᵐ = 1 := by simp [leOnePart]
#align lattice_ordered_comm_group.neg_one leOnePart_one
#align lattice_ordered_comm_group.neg_zero negPart_zero

@[to_additive posPart_nonneg] lemma one_le_oneLePart (a : α) : 1 ≤ a⁺ᵐ := le_sup_right
#align lattice_ordered_comm_group.one_le_pos one_le_oneLePart
#align lattice_ordered_comm_group.pos_nonneg posPart_nonneg

@[to_additive negPart_nonneg] lemma one_le_leOnePart (a : α) : 1 ≤ a⁻ᵐ := le_sup_right
#align lattice_ordered_comm_group.one_le_neg one_le_leOnePart
#align lattice_ordered_comm_group.neg_nonneg neg_nonneg

-- TODO: `to_additive` guesses `nonposPart`
@[to_additive le_posPart] lemma le_oneLePart (a : α) : a ≤ a⁺ᵐ := le_sup_left
#align lattice_ordered_comm_group.m_le_pos le_oneLePart
#align lattice_ordered_comm_group.le_pos le_posPart

@[to_additive] lemma inv_le_leOnePart (a : α) : a⁻¹ ≤ a⁻ᵐ := le_sup_left
#align lattice_ordered_comm_group.inv_le_neg inv_le_leOnePart
#align lattice_ordered_comm_group.neg_le_neg neg_le_negPart

@[to_additive] lemma oneLePart_eq_self : a⁺ᵐ = a ↔ 1 ≤ a := sup_eq_left
#align lattice_ordered_comm_group.pos_of_one_le oneLePart_eq_self
#align lattice_ordered_comm_group.pos_of_nonneg posPart_eq_self

@[to_additive] lemma oneLePart_eq_one : a⁺ᵐ = 1 ↔ a ≤ 1 := sup_eq_right
#align lattice_ordered_comm_group.pos_eq_one_iff oneLePart_eq_one
#align lattice_ordered_comm_group.pos_eq_zero_iff posPart_eq_zero
#align lattice_ordered_comm_group.pos_of_le_one oneLePart_eq_one
#align lattice_ordered_comm_group.pos_of_nonpos posPart_eq_zero

@[to_additive] lemma leOnePart_eq_inv' : a⁻ᵐ = a⁻¹ ↔ 1 ≤ a⁻¹ := sup_eq_left
@[to_additive] lemma leOnePart_eq_inv : a⁻ᵐ = a⁻¹ ↔ a ≤ 1 := by simp [leOnePart]
#align lattice_ordered_comm_group.neg_of_le_one leOnePart_eq_inv
#align lattice_ordered_comm_group.neg_of_nonpos negPart_eq_neg
#align lattice_ordered_comm_group.neg_of_one_le_inv leOnePart_eq_inv
#align lattice_ordered_comm_group.neg_of_inv_nonneg negPart_eq_neg

@[to_additive] lemma leOnePart_eq_one' : a⁻ᵐ = 1 ↔ a⁻¹ ≤ 1 := sup_eq_right
#align lattice_ordered_comm_group.neg_eq_one_iff' leOnePart_eq_one'
#align lattice_ordered_comm_group.neg_eq_zero_iff' negPart_eq_zero'
#align lattice_ordered_comm_group.neg_of_inv_le_one leOnePart_eq_one'
#align lattice_ordered_comm_group.neg_of_neg_nonpos negPart_eq_zero'

@[to_additive] lemma leOnePart_eq_one : a⁻ᵐ = 1 ↔ 1 ≤ a := by
  simp [leOnePart_eq_one']
#align lattice_ordered_comm_group.neg_eq_one_iff leOnePart_eq_one
#align lattice_ordered_comm_group.neg_eq_zero_iff negPart_eq_zero
#align lattice_ordered_comm_group.neg_of_one_le leOnePart_eq_one
#align lattice_ordered_comm_group.neg_of_nonneg negPart_eq_zero

@[to_additive] lemma oneLePart_le_one : a⁺ᵐ ≤ 1 ↔ a ≤ 1 := by simp [oneLePart]
#align lattice_ordered_comm_group.pos_le_one_iff oneLePart_le_one
#align lattice_ordered_comm_group.pos_nonpos_iff posPart_nonpos

@[to_additive] lemma leOnePart_le_one' : a⁻ᵐ ≤ 1 ↔ a⁻¹ ≤ 1 := by simp [leOnePart]
#align lattice_ordered_comm_group.neg_le_one_iff leOnePart_le_one'
#align lattice_ordered_comm_group.neg_nonpos_iff negPart_nonpos'

@[to_additive (attr := simp)] lemma oneLePart_inv (a : α) : a⁻¹⁺ᵐ = a⁻ᵐ := rfl
#align lattice_ordered_comm_group.neg_eq_pos_inv oneLePart_inv
#align lattice_ordered_comm_group.neg_eq_pos_neg posPart_neg

@[to_additive (attr := simp)] lemma leOnePart_inv (a : α) : a⁻¹⁻ᵐ = a⁺ᵐ := by
  simp [oneLePart, leOnePart]
#align lattice_ordered_comm_group.pos_eq_neg_inv leOnePart_inv
#align lattice_ordered_comm_group.pos_eq_neg_neg negPart_neg

@[to_additive] lemma leOnePart_le_one : a⁻ᵐ ≤ 1 ↔ a⁻¹ ≤ 1 := by simp [leOnePart]

@[to_additive]
lemma leOnePart_eq_inv_inf_one (a : α) : a⁻ᵐ = (a ⊓ 1)⁻¹ := by
  rw [leOnePart, ← inv_inj, inv_sup, inv_inv, inv_inv, inv_one]
#align lattice_ordered_comm_group.neg_eq_inv_inf_one leOnePart_eq_inv_inf_one
#align lattice_ordered_comm_group.neg_eq_neg_inf_zero negPart_eq_neg_inf_zero

-- Bourbaki A.VI.12 Prop 9 a)
@[to_additive (attr := simp)]
lemma oneLePart_div_leOnePart (a : α) : a⁺ᵐ / a⁻ᵐ = a := by
  rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul, leOnePart, mul_sup, mul_one, mul_right_inv, sup_comm,
    oneLePart]
#align lattice_ordered_comm_group.pos_div_neg oneLePart_div_leOnePart
#align lattice_ordered_comm_group.pos_sub_neg posPart_sub_negPart

-- The proof from Bourbaki A.VI.12 Prop 9 d)
@[to_additive]
lemma oneLePart_mul_leOnePart
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) :
    a⁺ᵐ * a⁻ᵐ = |a|ₘ := by
  rw [oneLePart, sup_mul, one_mul, leOnePart, mul_sup, mul_one, mul_inv_self, sup_assoc,
    ← @sup_assoc _ _ a, sup_eq_right.2 le_sup_right]
  exact sup_eq_left.2 <| one_le_mabs a
#align lattice_ordered_comm_group.pos_mul_neg oneLePart_mul_leOnePart
#align lattice_ordered_comm_group.pos_add_neg posPart_add_negPart

#noalign lattice_ordered_comm_group.m_pos_abs
#noalign lattice_ordered_comm_group.pos_abs
#noalign lattice_ordered_comm_group.m_neg_abs
#noalign lattice_ordered_comm_group.neg_abs

-- Bourbaki A.VI.12 Prop 9 a)
-- a⁺ᵐ ⊓ a⁻ᵐ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive] lemma oneLePart_inf_leOnePart_eq_one (a : α) : a⁺ᵐ ⊓ a⁻ᵐ = 1 := by
  rw [← mul_left_inj a⁻ᵐ⁻¹, inf_mul, one_mul, mul_right_inv, ← div_eq_mul_inv,
    oneLePart_div_leOnePart, leOnePart_eq_inv_inf_one, inv_inv]
#align lattice_ordered_comm_group.pos_inf_neg_eq_one oneLePart_inf_leOnePart_eq_one
#align lattice_ordered_comm_group.pos_inf_neg_eq_zero posPart_inf_negPart_eq_zero

end Group

section CommGroup
variable [Lattice α] [CommGroup α] [CovariantClass α α (· * ·) (· ≤ ·)]

-- Bourbaki A.VI.12 (with a and b swapped)
@[to_additive] lemma sup_eq_mul_oneLePart_div (a b : α) : a ⊔ b = b * (a / b)⁺ᵐ := by
  simp [oneLePart, mul_sup]
#align lattice_ordered_comm_group.sup_eq_mul_pos_div sup_eq_mul_oneLePart_div
#align lattice_ordered_comm_group.sup_eq_add_pos_sub sup_eq_add_posPart_sub

-- Bourbaki A.VI.12 (with a and b swapped)
@[to_additive] lemma inf_eq_div_oneLePart_div (a b : α) : a ⊓ b = a / (a / b)⁺ᵐ := by
  simp [oneLePart, div_sup, inf_comm]
#align lattice_ordered_comm_group.inf_eq_div_pos_div inf_eq_div_oneLePart_div
#align lattice_ordered_comm_group.inf_eq_sub_pos_sub inf_eq_sub_posPart_sub

-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive] lemma le_iff_oneLePart_leOnePart (a b : α) : a ≤ b ↔ a⁺ᵐ ≤ b⁺ᵐ ∧ b⁻ᵐ ≤ a⁻ᵐ := by
  refine ⟨fun h ↦ ⟨oneLePart_mono h, leOnePart_anti h⟩, fun h ↦ ?_⟩
  rw [← oneLePart_div_leOnePart a, ← oneLePart_div_leOnePart b]
  exact div_le_div'' h.1 h.2
#align lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge le_iff_oneLePart_leOnePart
#align lattice_ordered_comm_group.le_iff_pos_le_neg_ge le_iff_posPart_negPart

end CommGroup
end Lattice

section LinearOrder
variable [LinearOrder α] [CommGroup α] {a : α}

@[to_additive posPart_eq_of_posPart_pos]
lemma oneLePart_of_one_lt_oneLePart (ha : 1 < a⁺ᵐ) : a⁺ᵐ = a := by
  rw [oneLePart, right_lt_sup, not_le] at ha; exact oneLePart_eq_self.2 ha.le
#align lattice_ordered_comm_group.pos_eq_self_of_one_lt_pos oneLePart_of_one_lt_oneLePart
#align lattice_ordered_comm_group.pos_eq_self_of_pos_pos posPart_eq_of_posPart_pos

end LinearOrder
