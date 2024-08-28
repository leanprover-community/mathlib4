/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Order.MinMax

/-!
# Unbundled and weaker forms of canonically ordered monoids
-/

universe u


variable {α : Type u}

/-- An `OrderedCommMonoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedCommMonoid`. -/
class ExistsMulOfLE (α : Type u) [Mul α] [LE α] : Prop where
  /-- For `a ≤ b`, `a` left divides `b` -/
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c

/-- An `OrderedAddCommMonoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `CanonicallyOrderedAddCommMonoid`. -/
class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  /-- For `a ≤ b`, there is a `c` so `b = a + c`. -/
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c

attribute [to_additive] ExistsMulOfLE

export ExistsMulOfLE (exists_mul_of_le)

export ExistsAddOfLE (exists_add_of_le)

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.existsMulOfLE (α : Type u) [Group α] [LE α] : ExistsMulOfLE α :=
  ⟨fun {a b} _ => ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩

section MulOneClass

variable [MulOneClass α] [Preorder α] [ContravariantClass α α (· * ·) (· < ·)] [ExistsMulOfLE α]
  {a b : α}

@[to_additive]
theorem exists_one_lt_mul_of_lt' (h : a < b) : ∃ c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le
  exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩

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


