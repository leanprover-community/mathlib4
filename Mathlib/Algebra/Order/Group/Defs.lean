/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Util.AssertExists

#align_import algebra.order.group.defs from "leanprover-community/mathlib"@"b599f4e4e5cf1fbcb4194503671d3d9e569c1fce"

/-!
# Ordered groups

This file defines bundled ordered groups and develops a few basic results.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/


open Function

universe u

variable {α : Type u}

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  /-- Addition is monotone in an ordered additive commutative group. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
#align ordered_add_comm_group OrderedAddCommGroup

/-- An ordered commutative group is a commutative group
with a partial order in which multiplication is strictly monotone. -/
class OrderedCommGroup (α : Type u) extends CommGroup α, PartialOrder α where
  /-- Multiplication is monotone in an ordered commutative group. -/
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
#align ordered_comm_group OrderedCommGroup

attribute [to_additive] OrderedCommGroup

@[to_additive]
instance OrderedCommGroup.to_covariantClass_left_le (α : Type u) [OrderedCommGroup α] :
    CovariantClass α α (· * ·) (· ≤ ·) where
      elim a b c bc := OrderedCommGroup.mul_le_mul_left b c bc a
#align ordered_comm_group.to_covariant_class_left_le OrderedCommGroup.to_covariantClass_left_le
#align ordered_add_comm_group.to_covariant_class_left_le OrderedAddCommGroup.to_covariantClass_left_le

-- See note [lower instance priority]
@[to_additive OrderedAddCommGroup.toOrderedCancelAddCommMonoid]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid [OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
{ ‹OrderedCommGroup α› with le_of_mul_le_mul_left := fun a b c ↦ le_of_mul_le_mul_left' }
#align ordered_comm_group.to_ordered_cancel_comm_monoid OrderedCommGroup.toOrderedCancelCommMonoid
#align ordered_add_comm_group.to_ordered_cancel_add_comm_monoid OrderedAddCommGroup.toOrderedCancelAddCommMonoid

example (α : Type u) [OrderedAddCommGroup α] : CovariantClass α α (swap (· + ·)) (· < ·) :=
  IsRightCancelAdd.covariant_swap_add_lt_of_covariant_swap_add_le α

-- Porting note: this instance is not used,
-- and causes timeouts after lean4#2210.
-- It was introduced in https://github.com/leanprover-community/mathlib/pull/17564
-- but without the motivation clearly explained.
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
theorem OrderedCommGroup.to_contravariantClass_left_le (α : Type u) [OrderedCommGroup α] :
    ContravariantClass α α (· * ·) (· ≤ ·) where
      elim a b c bc := by simpa using mul_le_mul_left' bc a⁻¹
#align ordered_comm_group.to_contravariant_class_left_le OrderedCommGroup.to_contravariantClass_left_le
#align ordered_add_comm_group.to_contravariant_class_left_le OrderedAddCommGroup.to_contravariantClass_left_le

-- Porting note: this instance is not used,
-- and causes timeouts after lean4#2210.
-- See further explanation on `OrderedCommGroup.to_contravariantClass_left_le`.
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
theorem OrderedCommGroup.to_contravariantClass_right_le (α : Type u) [OrderedCommGroup α] :
    ContravariantClass α α (swap (· * ·)) (· ≤ ·) where
      elim a b c bc := by simpa using mul_le_mul_right' bc a⁻¹
#align ordered_comm_group.to_contravariant_class_right_le OrderedCommGroup.to_contravariantClass_right_le
#align ordered_add_comm_group.to_contravariant_class_right_le OrderedAddCommGroup.to_contravariantClass_right_le

alias OrderedCommGroup.mul_lt_mul_left' := mul_lt_mul_left'
#align ordered_comm_group.mul_lt_mul_left' OrderedCommGroup.mul_lt_mul_left'

attribute [to_additive OrderedAddCommGroup.add_lt_add_left] OrderedCommGroup.mul_lt_mul_left'
#align ordered_add_comm_group.add_lt_add_left OrderedAddCommGroup.add_lt_add_left

alias OrderedCommGroup.le_of_mul_le_mul_left := le_of_mul_le_mul_left'
#align ordered_comm_group.le_of_mul_le_mul_left OrderedCommGroup.le_of_mul_le_mul_left

attribute [to_additive] OrderedCommGroup.le_of_mul_le_mul_left
#align ordered_add_comm_group.le_of_add_le_add_left OrderedAddCommGroup.le_of_add_le_add_left

alias OrderedCommGroup.lt_of_mul_lt_mul_left := lt_of_mul_lt_mul_left'
#align ordered_comm_group.lt_of_mul_lt_mul_left OrderedCommGroup.lt_of_mul_lt_mul_left

attribute [to_additive] OrderedCommGroup.lt_of_mul_lt_mul_left
#align ordered_add_comm_group.lt_of_add_lt_add_left OrderedAddCommGroup.lt_of_add_lt_add_left


/-!
### Linearly ordered commutative groups
-/


/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrder α
#align linear_ordered_add_comm_group LinearOrderedAddCommGroup

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[to_additive]
class LinearOrderedCommGroup (α : Type u) extends OrderedCommGroup α, LinearOrder α
#align linear_ordered_comm_group LinearOrderedCommGroup

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {a b c : α}

@[to_additive LinearOrderedAddCommGroup.add_lt_add_left]
theorem LinearOrderedCommGroup.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
  _root_.mul_lt_mul_left' h c
#align linear_ordered_comm_group.mul_lt_mul_left' LinearOrderedCommGroup.mul_lt_mul_left'
#align linear_ordered_add_comm_group.add_lt_add_left LinearOrderedAddCommGroup.add_lt_add_left

@[to_additive eq_zero_of_neg_eq]
theorem eq_one_of_inv_eq' (h : a⁻¹ = a) : a = 1 :=
  match lt_trichotomy a 1 with
  | Or.inl h₁ =>
    have : 1 < a := h ▸ one_lt_inv_of_inv h₁
    absurd h₁ this.asymm
  | Or.inr (Or.inl h₁) => h₁
  | Or.inr (Or.inr h₁) =>
    have : a < 1 := h ▸ inv_lt_one'.mpr h₁
    absurd h₁ this.asymm
#align eq_one_of_inv_eq' eq_one_of_inv_eq'
#align eq_zero_of_neg_eq eq_zero_of_neg_eq

@[to_additive exists_zero_lt]
theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a := by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  obtain h|h := hy.lt_or_lt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
  · exact ⟨y, h⟩
#align exists_one_lt' exists_one_lt'
#align exists_zero_lt exists_zero_lt

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMaxOrder [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩
#align linear_ordered_comm_group.to_no_max_order LinearOrderedCommGroup.to_noMaxOrder
#align linear_ordered_add_comm_group.to_no_max_order LinearOrderedAddCommGroup.to_noMaxOrder

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMinOrder [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩
#align linear_ordered_comm_group.to_no_min_order LinearOrderedCommGroup.to_noMinOrder
#align linear_ordered_add_comm_group.to_no_min_order LinearOrderedAddCommGroup.to_noMinOrder

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
    [LinearOrderedCommGroup α] : LinearOrderedCancelCommMonoid α :=
{ ‹LinearOrderedCommGroup α›, OrderedCommGroup.toOrderedCancelCommMonoid with }
#align linear_ordered_comm_group.to_linear_ordered_cancel_comm_monoid LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
#align linear_ordered_add_comm_group.to_linear_ordered_cancel_add_comm_monoid LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid

@[to_additive (attr := simp)]
theorem inv_le_self_iff : a⁻¹ ≤ a ↔ 1 ≤ a := by simp [inv_le_iff_one_le_mul']
#align neg_le_self_iff neg_le_self_iff

@[to_additive (attr := simp)]
theorem inv_lt_self_iff : a⁻¹ < a ↔ 1 < a := by simp [inv_lt_iff_one_lt_mul]
#align neg_lt_self_iff neg_lt_self_iff

@[to_additive (attr := simp)]
theorem le_inv_self_iff : a ≤ a⁻¹ ↔ a ≤ 1 := by simp [← not_iff_not]
#align le_neg_self_iff le_neg_self_iff

@[to_additive (attr := simp)]
theorem lt_inv_self_iff : a < a⁻¹ ↔ a < 1 := by simp [← not_iff_not]
#align lt_neg_self_iff lt_neg_self_iff

end LinearOrderedCommGroup

section NormNumLemmas

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures.  -/
variable [OrderedCommGroup α] {a b : α}

@[to_additive (attr := gcongr) neg_le_neg]
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
  -- Porting note: explicit type annotation was not needed before.
  (@inv_le_inv_iff α ..).mpr
#align inv_le_inv' inv_le_inv'
#align neg_le_neg neg_le_neg

@[to_additive (attr := gcongr) neg_lt_neg]
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
  -- Porting note: explicit type annotation was not needed before.
  (@inv_lt_inv_iff α ..).mpr
#align inv_lt_inv' inv_lt_inv'
#align neg_lt_neg neg_lt_neg

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
  inv_lt_one_iff_one_lt.mpr
#align inv_lt_one_of_one_lt inv_lt_one_of_one_lt
#align neg_neg_of_pos neg_neg_of_pos

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
  inv_le_one'.mpr
#align inv_le_one_of_one_le inv_le_one_of_one_le
#align neg_nonpos_of_nonneg neg_nonpos_of_nonneg

@[to_additive neg_nonneg_of_nonpos]
theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ :=
  one_le_inv'.mpr
#align one_le_inv_of_le_one one_le_inv_of_le_one
#align neg_nonneg_of_nonpos neg_nonneg_of_nonpos

end NormNumLemmas

/-
`NeZero` should not be needed at this point in the ordered algebraic hierarchy.
-/
assert_not_exists NeZero
