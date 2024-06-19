/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.MinMax

/-!
# Unbundled and weaker forms of canonically ordered monoids
-/

universe u


variable {α : Type u}
/-- An `OrderedAddCommMonoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedAddCommMonoid`. -/
class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  /-- For `a ≤ b`, there is a `c` so `b = a + c`. -/
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c

/-- An `OrderedCommMonoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedCommMonoid`. -/
@[to_additive]
class ExistsMulOfLE (α : Type u) [Mul α] [LE α] : Prop where
  /-- For `a ≤ b`, `a` left divides `b` -/
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c

/-- Prop-valued mixin for the condition that either `α` or `αᵒᵈ` respects `ExistsAddOfLE`.

This is useful to dualise results. -/
class ExistsAddOfLEOrGE (α : Type u) [Add α] [LE α] : Prop where
  exists_add_of_le_or_ge :
    (∀ {a b : α}, a ≤ b → ∃ c, b = a + c) ∨ ∀ {a b : α}, b ≤ a → ∃ c, b = a + c

/-- Prop-valued mixin for the condition that either `α` or `αᵒᵈ` respects `ExistsMulOfLE`.

This is useful to dualise results. -/
@[to_additive]
class ExistsMulOfLEOrGE (α : Type u) [Mul α] [LE α] : Prop where
  exists_mul_of_le_or_ge :
    (∀ {a b : α}, a ≤ b → ∃ c, b = a * c) ∨ ∀ {a b : α}, b ≤ a → ∃ c, b = a * c

export ExistsMulOfLE (exists_mul_of_le)
export ExistsAddOfLE (exists_add_of_le)
export ExistsMulOfLEOrGE (exists_mul_of_le_or_ge)
export ExistsAddOfLEOrGE (exists_add_of_le_or_ge)

section Mul
variable [Mul α] [LE α]

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) ExistsMulOfLE.toExistsMulOfLEOrGE [ExistsMulOfLE α] :
    ExistsMulOfLEOrGE α where
  exists_mul_of_le_or_ge := .inl exists_mul_of_le

@[to_additive] instance OrderDual.instExistsMulOfLEOrGE [ExistsMulOfLEOrGE α] :
    ExistsMulOfLEOrGE αᵒᵈ where
  exists_mul_of_le_or_ge := (exists_mul_of_le_or_ge (α := α)).symm

variable (α) in
@[to_additive] lemma existsMulOfLE_or_existsMulOfLE_orderDual [ExistsMulOfLEOrGE α] :
    ExistsMulOfLE α ∨ ExistsMulOfLE αᵒᵈ := exists_mul_of_le_or_ge.imp (⟨·⟩) (⟨·⟩)

end Mul

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.existsMulOfLE (α : Type u) [Group α] [LE α] : ExistsMulOfLE α :=
  ⟨fun {a b} _ => ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩

section MulOneClass
variable [MulOneClass α] [Preorder α] [ExistsMulOfLE α] {a b : α}

@[to_additive] lemma exists_one_le_mul_of_le [ContravariantClass α α (· * ·) (· ≤ ·)] (h : a ≤ b) :
    ∃ c, 1 ≤ c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h; exact ⟨c, one_le_of_le_mul_right h, rfl⟩

@[to_additive] lemma exists_one_lt_mul_of_lt' [ContravariantClass α α (· * ·) (· < ·)] (h : a < b) :
    ∃ c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le; exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩

@[to_additive] lemma le_iff_exists_one_le_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] : a ≤ b ↔ ∃ c, 1 ≤ c ∧ a * c = b :=
  ⟨exists_one_le_mul_of_le, by rintro ⟨c, hc, rfl⟩; exact le_mul_of_one_le_right' hc⟩

@[to_additive] lemma lt_iff_exists_one_lt_mul [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] : a < b ↔ ∃ c, 1 < c ∧ a * c = b :=
  ⟨exists_one_lt_mul_of_lt', by rintro ⟨c, hc, rfl⟩; exact lt_mul_of_one_lt_right' _ hc⟩

end MulOneClass

section ExistsMulOfLE

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)] {a b : α}

@[to_additive]
theorem le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
  le_of_forall_le_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ ((lt_mul_iff_one_lt_right' b).1 hxb)

@[to_additive]
theorem le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_forall_one_lt_le_mul fun ε hε => (h ε hε).le

@[to_additive]
theorem le_iff_forall_one_lt_lt_mul' : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩

end ExistsMulOfLE
