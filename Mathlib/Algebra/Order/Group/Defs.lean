/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Util.AssertExists

/-!
# Ordered groups

This file defines bundled ordered groups and develops a few basic results.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

/-
`NeZero` theory should not be needed at this point in the ordered algebraic hierarchy.
-/
assert_not_imported Mathlib.Algebra.NeZero

open Function

universe u

variable {α : Type u}

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  /-- Addition is monotone in an ordered additive commutative group. -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

/-- An ordered commutative group is a commutative group
with a partial order in which multiplication is strictly monotone. -/
class OrderedCommGroup (α : Type u) extends CommGroup α, PartialOrder α where
  /-- Multiplication is monotone in an ordered commutative group. -/
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

attribute [to_additive] OrderedCommGroup

@[to_additive]
instance OrderedCommGroup.toMulLeftMono (α : Type u) [OrderedCommGroup α] :
    MulLeftMono α where
      elim a b c bc := OrderedCommGroup.mul_le_mul_left b c bc a

-- See note [lower instance priority]
@[to_additive OrderedAddCommGroup.toOrderedCancelAddCommMonoid]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid [OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
{ ‹OrderedCommGroup α› with le_of_mul_le_mul_left := fun _ _ _ ↦ le_of_mul_le_mul_left' }

example (α : Type u) [OrderedAddCommGroup α] : AddRightStrictMono α :=
  inferInstance

-- Porting note: this instance is not used,
-- and causes timeouts after lean4#2210.
-- It was introduced in https://github.com/leanprover-community/mathlib/pull/17564
-- but without the motivation clearly explained.
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
theorem OrderedCommGroup.toMulLeftReflectLE (α : Type u) [OrderedCommGroup α] :
    MulLeftReflectLE α where
      elim a b c bc := by simpa using mul_le_mul_left' bc a⁻¹

-- Porting note: this instance is not used,
-- and causes timeouts after lean4#2210.
-- See further explanation on `OrderedCommGroup.toMulLeftReflectLE`.
/-- A choice-free shortcut instance. -/
@[to_additive "A choice-free shortcut instance."]
theorem OrderedCommGroup.toMulRightReflectLE (α : Type u) [OrderedCommGroup α] :
    MulRightReflectLE α where
      elim a b c bc := by simpa using mul_le_mul_right' bc a⁻¹

alias OrderedCommGroup.mul_lt_mul_left' := mul_lt_mul_left'

attribute [to_additive OrderedAddCommGroup.add_lt_add_left] OrderedCommGroup.mul_lt_mul_left'

alias OrderedCommGroup.le_of_mul_le_mul_left := le_of_mul_le_mul_left'

attribute [to_additive] OrderedCommGroup.le_of_mul_le_mul_left

alias OrderedCommGroup.lt_of_mul_lt_mul_left := lt_of_mul_lt_mul_left'

attribute [to_additive] OrderedCommGroup.lt_of_mul_lt_mul_left


/-!
### Linearly ordered commutative groups
-/


/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrder α

/-- A linearly ordered commutative group is a
commutative group with a linear order in which
multiplication is monotone. -/
@[to_additive]
class LinearOrderedCommGroup (α : Type u) extends OrderedCommGroup α, LinearOrder α

section LinearOrderedCommGroup

variable [LinearOrderedCommGroup α] {a : α}

@[to_additive LinearOrderedAddCommGroup.add_lt_add_left]
theorem LinearOrderedCommGroup.mul_lt_mul_left' (a b : α) (h : a < b) (c : α) : c * a < c * b :=
  _root_.mul_lt_mul_left' h c

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

@[to_additive exists_zero_lt]
theorem exists_one_lt' [Nontrivial α] : ∃ a : α, 1 < a := by
  obtain ⟨y, hy⟩ := Decidable.exists_ne (1 : α)
  obtain h|h := hy.lt_or_lt
  · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
  · exact ⟨y, h⟩

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMaxOrder [Nontrivial α] : NoMaxOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a * y, lt_mul_of_one_lt_right' a hy⟩⟩

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_noMinOrder [Nontrivial α] : NoMinOrder α :=
  ⟨by
    obtain ⟨y, hy⟩ : ∃ a : α, 1 < a := exists_one_lt'
    exact fun a => ⟨a / y, (div_lt_self_iff a).mpr hy⟩⟩

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.toLinearOrderedCancelCommMonoid
    [LinearOrderedCommGroup α] : LinearOrderedCancelCommMonoid α :=
{ ‹LinearOrderedCommGroup α›, OrderedCommGroup.toOrderedCancelCommMonoid with }

@[to_additive (attr := simp)]
theorem inv_le_self_iff : a⁻¹ ≤ a ↔ 1 ≤ a := by simp [inv_le_iff_one_le_mul']

@[to_additive (attr := simp)]
theorem inv_lt_self_iff : a⁻¹ < a ↔ 1 < a := by simp [inv_lt_iff_one_lt_mul]

@[to_additive (attr := simp)]
theorem le_inv_self_iff : a ≤ a⁻¹ ↔ a ≤ 1 := by simp [← not_iff_not]

@[to_additive (attr := simp)]
theorem lt_inv_self_iff : a < a⁻¹ ↔ a < 1 := by simp [← not_iff_not]

end LinearOrderedCommGroup

section NormNumLemmas

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures. -/
variable [OrderedCommGroup α] {a b : α}

@[to_additive (attr := gcongr) neg_le_neg]
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ :=
  inv_le_inv_iff.mpr

@[to_additive (attr := gcongr) neg_lt_neg]
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ :=
  inv_lt_inv_iff.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 :=
  inv_lt_one_iff_one_lt.mpr

--  The additive version is also a `linarith` lemma.
@[to_additive]
theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 :=
  inv_le_one'.mpr

@[to_additive neg_nonneg_of_nonpos]
theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ :=
  one_le_inv'.mpr

end NormNumLemmas
