/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Lattice
import Mathlib.Algebra.Module.Basic
import Mathlib.Order.Closure

#align_import algebra.order.lattice_group from "leanprover-community/mathlib"@"5dc275ec639221ca4d5f56938eb966f6ad9bc89f"

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered group has a decomposition `a⁺-a⁻` into the
  difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality (stated for a
  commutative group).

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered group
- `|a|ₘ = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered group

## Implementation notes

A lattice ordered group is a type `α` satisfying:

* `[Lattice α]`
* `[CommGroup α]`
* `[CovariantClass α α (*) (≤)]`
* `[CovariantClass α α (swap (· * ·)) (· ≤ ·)]`

The remainder of the file establishes basic properties of lattice ordered groups. It is shown that
when the group is commutative, the lattice is distributive. This also holds in the non-commutative
case ([Birkhoff][birkhoff1942],[Fuchs][fuchs1963]) but we do not yet have the machinery to establish
this in Mathlib.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
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

section Group

variable [Lattice α] [Group α]

namespace LatticeOrderedGroup

-- see Note [lower instance priority]
/--
Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `a ⊔ 1` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
@[to_additive
      "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type
      `α`,the element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`."]
instance (priority := 100) hasOneLatticeHasPosPart : PosPart α :=
  ⟨fun a => a ⊔ 1⟩
#align lattice_ordered_comm_group.has_one_lattice_has_pos_part LatticeOrderedGroup.hasOneLatticeHasPosPart
#align lattice_ordered_comm_group.has_zero_lattice_has_pos_part LatticeOrderedGroup.hasZeroLatticeHasPosPart

@[to_additive pos_part_def]
theorem m_pos_part_def (a : α) : a⁺ = a ⊔ 1 :=
  rfl
#align lattice_ordered_comm_group.m_pos_part_def LatticeOrderedGroup.m_pos_part_def
#align lattice_ordered_comm_group.pos_part_def LatticeOrderedGroup.pos_part_def

-- see Note [lower instance priority]
/--
Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `(-a) ⊔ 1` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
@[to_additive
      "Let `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type
      `α`, the element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`."]
instance (priority := 100) hasOneLatticeHasNegPart : NegPart α :=
  ⟨fun a => a⁻¹ ⊔ 1⟩
#align lattice_ordered_comm_group.has_one_lattice_has_neg_part LatticeOrderedGroup.hasOneLatticeHasNegPart
#align lattice_ordered_comm_group.has_zero_lattice_has_neg_part LatticeOrderedGroup.hasZeroLatticeHasNegPart

@[to_additive neg_part_def]
theorem m_neg_part_def (a : α) : a⁻ = a⁻¹ ⊔ 1 :=
  rfl
#align lattice_ordered_comm_group.m_neg_part_def LatticeOrderedGroup.m_neg_part_def
#align lattice_ordered_comm_group.neg_part_def LatticeOrderedGroup.neg_part_def

@[to_additive (attr := simp)]
theorem pos_one : (1 : α)⁺ = 1 :=
  sup_idem
#align lattice_ordered_comm_group.pos_one LatticeOrderedGroup.pos_one
#align lattice_ordered_comm_group.pos_zero LatticeOrderedGroup.pos_zero

@[to_additive (attr := simp)]
theorem neg_one : (1 : α)⁻ = 1 := by rw [m_neg_part_def, inv_one, sup_idem]
#align lattice_ordered_comm_group.neg_one LatticeOrderedGroup.neg_one
#align lattice_ordered_comm_group.neg_zero LatticeOrderedGroup.neg_zero

-- a⁻ = -(a ⊓ 0)
@[to_additive]
theorem neg_eq_inv_inf_one
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) :
    a⁻ = (a ⊓ 1)⁻¹ := by
  rw [m_neg_part_def, ← inv_inj, inv_sup, inv_inv, inv_inv, inv_one]
#align lattice_ordered_comm_group.neg_eq_inv_inf_one LatticeOrderedGroup.neg_eq_inv_inf_one
#align lattice_ordered_comm_group.neg_eq_neg_inf_zero LatticeOrderedGroup.neg_eq_neg_inf_zero

-- 0 ≤ a⁺
@[to_additive pos_nonneg]
theorem one_le_pos (a : α) : 1 ≤ a⁺ :=
  le_sup_right
#align lattice_ordered_comm_group.one_le_pos LatticeOrderedGroup.one_le_pos
#align lattice_ordered_comm_group.pos_nonneg LatticeOrderedGroup.pos_nonneg

-- 0 ≤ a⁻
@[to_additive neg_nonneg]
theorem one_le_neg (a : α) : 1 ≤ a⁻ :=
  le_sup_right
#align lattice_ordered_comm_group.one_le_neg LatticeOrderedGroup.one_le_neg
#align lattice_ordered_comm_group.neg_nonneg LatticeOrderedGroup.neg_nonneg

-- pos_nonpos_iff
@[to_additive]
theorem pos_le_one_iff {a : α} : a⁺ ≤ 1 ↔ a ≤ 1 := by
  rw [m_pos_part_def, sup_le_iff, and_iff_left le_rfl]
#align lattice_ordered_comm_group.pos_le_one_iff LatticeOrderedGroup.pos_le_one_iff
#align lattice_ordered_comm_group.pos_nonpos_iff LatticeOrderedGroup.pos_nonpos_iff

-- neg_nonpos_iff
@[to_additive]
theorem neg_le_one_iff {a : α} : a⁻ ≤ 1 ↔ a⁻¹ ≤ 1 := by
  rw [m_neg_part_def, sup_le_iff, and_iff_left le_rfl]
#align lattice_ordered_comm_group.neg_le_one_iff LatticeOrderedGroup.neg_le_one_iff
#align lattice_ordered_comm_group.neg_nonpos_iff LatticeOrderedGroup.neg_nonpos_iff

@[to_additive]
theorem pos_eq_one_iff {a : α} : a⁺ = 1 ↔ a ≤ 1 :=
  sup_eq_right
#align lattice_ordered_comm_group.pos_eq_one_iff LatticeOrderedGroup.pos_eq_one_iff
#align lattice_ordered_comm_group.pos_eq_zero_iff LatticeOrderedGroup.pos_eq_zero_iff

@[to_additive]
theorem neg_eq_one_iff' {a : α} : a⁻ = 1 ↔ a⁻¹ ≤ 1 :=
  sup_eq_right
#align lattice_ordered_comm_group.neg_eq_one_iff' LatticeOrderedGroup.neg_eq_one_iff'
#align lattice_ordered_comm_group.neg_eq_zero_iff' LatticeOrderedGroup.neg_eq_zero_iff'

@[to_additive]
theorem neg_eq_one_iff [CovariantClass α α HMul.hMul LE.le] {a : α} : a⁻ = 1 ↔ 1 ≤ a := by
  rw [le_antisymm_iff, neg_le_one_iff, inv_le_one', and_iff_left (one_le_neg _)]
#align lattice_ordered_comm_group.neg_eq_one_iff LatticeOrderedGroup.neg_eq_one_iff
#align lattice_ordered_comm_group.neg_eq_zero_iff LatticeOrderedGroup.neg_eq_zero_iff

@[to_additive le_pos]
theorem m_le_pos (a : α) : a ≤ a⁺ :=
  le_sup_left
#align lattice_ordered_comm_group.m_le_pos LatticeOrderedGroup.m_le_pos
#align lattice_ordered_comm_group.le_pos LatticeOrderedGroup.le_pos

-- -a ≤ a⁻
@[to_additive]
theorem inv_le_neg (a : α) : a⁻¹ ≤ a⁻ :=
  le_sup_left
#align lattice_ordered_comm_group.inv_le_neg LatticeOrderedGroup.inv_le_neg
#align lattice_ordered_comm_group.neg_le_neg LatticeOrderedGroup.neg_le_neg

-- Bourbaki A.VI.12
--  a⁻ = (-a)⁺
@[to_additive]
theorem neg_eq_pos_inv (a : α) : a⁻ = a⁻¹⁺ :=
  rfl
#align lattice_ordered_comm_group.neg_eq_pos_inv LatticeOrderedGroup.neg_eq_pos_inv
#align lattice_ordered_comm_group.neg_eq_pos_neg LatticeOrderedGroup.neg_eq_pos_neg

-- a⁺ = (-a)⁻
@[to_additive]
theorem pos_eq_neg_inv (a : α) : a⁺ = a⁻¹⁻ := by rw [neg_eq_pos_inv, inv_inv]
#align lattice_ordered_comm_group.pos_eq_neg_inv LatticeOrderedGroup.pos_eq_neg_inv
#align lattice_ordered_comm_group.pos_eq_neg_neg LatticeOrderedGroup.pos_eq_neg_neg

-- Bourbaki A.VI.12 Prop 9 a)
-- a = a⁺ - a⁻
@[to_additive (attr := simp)]
theorem pos_div_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ / a⁻ = a := by
  symm
  rw [div_eq_mul_inv]
  apply eq_mul_inv_of_mul_eq
  rw [m_neg_part_def, mul_sup, mul_one, mul_right_inv, sup_comm, m_pos_part_def]
#align lattice_ordered_comm_group.pos_div_neg LatticeOrderedGroup.pos_div_neg
#align lattice_ordered_comm_group.pos_sub_neg LatticeOrderedGroup.pos_sub_neg

-- pos_of_nonneg
/-- If `a` is positive, then it is equal to its positive component `a⁺`. -/
@[to_additive "If `a` is positive, then it is equal to its positive component `a⁺`."]
theorem pos_of_one_le (a : α) (h : 1 ≤ a) : a⁺ = a := by
  rw [m_pos_part_def]
  exact sup_of_le_left h
#align lattice_ordered_comm_group.pos_of_one_le LatticeOrderedGroup.pos_of_one_le
#align lattice_ordered_comm_group.pos_of_nonneg LatticeOrderedGroup.pos_of_nonneg

-- 0 ≤ a implies a⁺ = a
-- pos_of_nonpos
@[to_additive]
theorem pos_of_le_one (a : α) (h : a ≤ 1) : a⁺ = 1 :=
  pos_eq_one_iff.mpr h
#align lattice_ordered_comm_group.pos_of_le_one LatticeOrderedGroup.pos_of_le_one
#align lattice_ordered_comm_group.pos_of_nonpos LatticeOrderedGroup.pos_of_nonpos

@[to_additive neg_of_inv_nonneg]
theorem neg_of_one_le_inv (a : α) (h : 1 ≤ a⁻¹) : a⁻ = a⁻¹ := by
  rw [neg_eq_pos_inv]
  exact pos_of_one_le _ h
#align lattice_ordered_comm_group.neg_of_one_le_inv LatticeOrderedGroup.neg_of_one_le_inv
#align lattice_ordered_comm_group.neg_of_inv_nonneg LatticeOrderedGroup.neg_of_inv_nonneg

-- neg_of_neg_nonpos
@[to_additive]
theorem neg_of_inv_le_one (a : α) (h : a⁻¹ ≤ 1) : a⁻ = 1 :=
  neg_eq_one_iff'.mpr h
#align lattice_ordered_comm_group.neg_of_inv_le_one LatticeOrderedGroup.neg_of_inv_le_one
#align lattice_ordered_comm_group.neg_of_neg_nonpos LatticeOrderedGroup.neg_of_neg_nonpos

-- neg_of_nonpos
@[to_additive]
theorem neg_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : a ≤ 1) : a⁻ = a⁻¹ :=
  sup_eq_left.2 <| one_le_inv'.2 h
#align lattice_ordered_comm_group.neg_of_le_one LatticeOrderedGroup.neg_of_le_one
#align lattice_ordered_comm_group.neg_of_nonpos LatticeOrderedGroup.neg_of_nonpos

-- pos_eq_self_of_pos_pos
@[to_additive]
theorem pos_eq_self_of_one_lt_pos {α} [LinearOrder α] [CommGroup α] {x : α} (hx : 1 < x⁺) :
    x⁺ = x := by
  rw [m_pos_part_def, right_lt_sup, not_le] at hx
  rw [m_pos_part_def, sup_eq_left]
  exact hx.le
#align lattice_ordered_comm_group.pos_eq_self_of_one_lt_pos LatticeOrderedGroup.pos_eq_self_of_one_lt_pos
#align lattice_ordered_comm_group.pos_eq_self_of_pos_pos LatticeOrderedGroup.pos_eq_self_of_pos_pos

-- neg_of_nonneg'
@[to_additive]
theorem neg_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : a⁻ = 1 :=
  neg_eq_one_iff.mpr h
#align lattice_ordered_comm_group.neg_of_one_le LatticeOrderedGroup.neg_of_one_le
#align lattice_ordered_comm_group.neg_of_nonneg LatticeOrderedGroup.neg_of_nonneg

-- The proof from Bourbaki A.VI.12 Prop 9 d)
-- |a|ₘ = a⁺ - a⁻
@[to_additive]
theorem pos_mul_neg
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) :
    |a|ₘ = a⁺ * a⁻ := by
  rw [m_pos_part_def, sup_mul, one_mul, m_neg_part_def, mul_sup, mul_one, mul_inv_self, sup_assoc,
    ← @sup_assoc _ _ a, sup_eq_right.2 le_sup_right]
  exact (sup_eq_left.2 <| one_le_mabs a).symm
#align lattice_ordered_comm_group.pos_mul_neg LatticeOrderedGroup.pos_mul_neg
#align lattice_ordered_comm_group.pos_add_neg LatticeOrderedGroup.pos_add_neg

@[to_additive pos_abs]
theorem m_pos_abs [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    (a : α) : |a|ₘ⁺ = |a|ₘ := by
  rw [m_pos_part_def]
  apply sup_of_le_left
  apply one_le_mabs
#align lattice_ordered_comm_group.m_pos_abs LatticeOrderedGroup.m_pos_abs
#align lattice_ordered_comm_group.pos_abs LatticeOrderedGroup.pos_abs

@[to_additive neg_abs]
theorem m_neg_abs [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    (a : α) : |a|ₘ⁻ = 1 := by
  rw [m_neg_part_def]
  apply sup_of_le_right
  rw [Left.inv_le_one_iff]
  apply one_le_mabs
#align lattice_ordered_comm_group.m_neg_abs LatticeOrderedGroup.m_neg_abs
#align lattice_ordered_comm_group.neg_abs LatticeOrderedGroup.neg_abs

-- Bourbaki A.VI.12 Prop 9 a)
-- a⁺ ⊓ a⁻ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive]
theorem pos_inf_neg_eq_one
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) :
    a⁺ ⊓ a⁻ = 1 := by
  rw [← mul_left_inj (a⁻)⁻¹, inf_mul, one_mul, mul_right_inv, ← div_eq_mul_inv,
    pos_div_neg, neg_eq_inv_inf_one, inv_inv]
#align lattice_ordered_comm_group.pos_inf_neg_eq_one LatticeOrderedGroup.pos_inf_neg_eq_one
#align lattice_ordered_comm_group.pos_inf_neg_eq_zero LatticeOrderedGroup.pos_inf_neg_eq_zero

end LatticeOrderedGroup

end Group

namespace LatticeOrderedCommGroup
variable [Lattice α] [CommGroup α]

open LatticeOrderedGroup

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊔b = b + (a - b)⁺
@[to_additive]
theorem sup_eq_mul_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊔ b = b * (a / b)⁺ :=
  calc
    a ⊔ b = b * (a / b) ⊔ b * 1 :=
      by rw [mul_one b, div_eq_mul_inv, mul_comm a, mul_inv_cancel_left]
    _ = b * (a / b ⊔ 1) := by rw [← mul_sup (a / b) 1 b]
#align lattice_ordered_comm_group.sup_eq_mul_pos_div LatticeOrderedCommGroup.sup_eq_mul_pos_div
#align lattice_ordered_comm_group.sup_eq_add_pos_sub LatticeOrderedCommGroup.sup_eq_add_pos_sub

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊓b = a - (a - b)⁺
@[to_additive]
theorem inf_eq_div_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊓ b = a / (a / b)⁺ :=
  calc
    a ⊓ b = a * 1 ⊓ a * (b / a) :=
      by rw [mul_one a, div_eq_mul_inv, mul_comm b, mul_inv_cancel_left]
    _ = a * (1 ⊓ b / a) := by rw [← mul_inf 1 (b / a) a]
    _ = a * (b / a ⊓ 1) := by rw [inf_comm]
    _ = a * ((a / b)⁻¹ ⊓ 1) := by
      rw [div_eq_mul_inv]
      nth_rw 1 [← inv_inv b]
      rw [← mul_inv, mul_comm b⁻¹, ← div_eq_mul_inv]
    _ = a * ((a / b)⁻¹ ⊓ 1⁻¹) := by rw [inv_one]
    _ = a / (a / b ⊔ 1) := by rw [← inv_sup, ← div_eq_mul_inv]
#align lattice_ordered_comm_group.inf_eq_div_pos_div LatticeOrderedCommGroup.inf_eq_div_pos_div
#align lattice_ordered_comm_group.inf_eq_sub_pos_sub LatticeOrderedCommGroup.inf_eq_sub_pos_sub

-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive le_iff_pos_le_neg_ge]
theorem m_le_iff_pos_le_neg_ge [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ := by
  constructor <;> intro h
  · constructor
    · exact sup_le (h.trans (m_le_pos b)) (one_le_pos b)
    · rw [← inv_le_inv_iff] at h
      exact sup_le (h.trans (inv_le_neg a)) (one_le_neg a)
  · rw [← pos_div_neg a, ← pos_div_neg b]
    exact div_le_div'' h.1 h.2
#align lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge LatticeOrderedCommGroup.m_le_iff_pos_le_neg_ge
#align lattice_ordered_comm_group.le_iff_pos_le_neg_ge LatticeOrderedCommGroup.le_iff_pos_le_neg_ge

end LatticeOrderedCommGroup

namespace LatticeOrderedAddCommGroup

variable [Lattice β] [AddCommGroup β]

section solid

/-- A subset `s ⊆ β`, with `β` an `AddCommGroup` with a `Lattice` structure, is solid if for
all `x ∈ s` and all `y ∈ β` such that `|y| ≤ |x|`, then `y ∈ s`. -/
def IsSolid (s : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s
#align lattice_ordered_add_comm_group.is_solid LatticeOrderedAddCommGroup.IsSolid

/-- The solid closure of a subset `s` is the smallest superset of `s` that is solid. -/
def solidClosure (s : Set β) : Set β := { y | ∃ x ∈ s, |y| ≤ |x| }
#align lattice_ordered_add_comm_group.solid_closure LatticeOrderedAddCommGroup.solidClosure

theorem isSolid_solidClosure (s : Set β) : IsSolid (solidClosure s) :=
  fun _ ⟨y, hy, hxy⟩ _ hzx => ⟨y, hy, hzx.trans hxy⟩
#align lattice_ordered_add_comm_group.is_solid_solid_closure LatticeOrderedAddCommGroup.isSolid_solidClosure

theorem solidClosure_min (s t : Set β) (h1 : s ⊆ t) (h2 : IsSolid t) : solidClosure s ⊆ t :=
  fun _ ⟨_, hy, hxy⟩ => h2 (h1 hy) hxy
#align lattice_ordered_add_comm_group.solid_closure_min LatticeOrderedAddCommGroup.solidClosure_min

end solid

end LatticeOrderedAddCommGroup
