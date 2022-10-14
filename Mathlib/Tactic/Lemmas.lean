/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring

/-!
# Temporary sorried lemmas, potentially used by `norm_num` and/or `ring`.

These should be removed as their original versions are ported into their proper homes.
-/

-- Lemmas that will be ported to `Algebra.Ring.Basic` (somewhat generalized)
section
variable [Ring α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  sorry

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  sorry

theorem mul_sub (a b c : α) : a * (b - c) = a * b - a * c :=
  sorry
end

-- Lemmas that will be ported to `Algebra.GroupPower.Basic`
@[simp]
theorem pow_one [Monoid M] (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, mul_one]

@[simp]
theorem one_pow [Monoid M] (n : ℕ) : (1 : M) ^ n = 1 := by
  induction' n with n ih
  · exact pow_zero _
  · rw [pow_succ, ih, one_mul]

-- Lemmas that will be ported to `Algebra.Order.Group.Basic`

/- The following lemmas are stated so that the `norm_num` tactic can use them with the
expected signatures.  -/
section NormNumLemmas

section
variable [OrderedCommGroup α] {a b : α}

@[to_additive neg_le_neg]
theorem inv_le_inv' : a ≤ b → b⁻¹ ≤ a⁻¹ := sorry

@[to_additive neg_lt_neg]
theorem inv_lt_inv' : a < b → b⁻¹ < a⁻¹ := sorry

theorem inv_lt_one_of_one_lt : 1 < a → a⁻¹ < 1 := sorry

theorem inv_le_one_of_one_le : 1 ≤ a → a⁻¹ ≤ 1 := sorry

theorem one_le_inv_of_le_one : a ≤ 1 → 1 ≤ a⁻¹ := sorry

end

section
variable [OrderedAddCommGroup α] {a b : α}

theorem neg_neg_of_pos : 0 < a → -a < 0 := sorry

theorem neg_nonpos_of_nonneg : 0 ≤ a → -a ≤ 0 := sorry

theorem neg_nonneg_of_nonpos : a ≤ 0 → 0 ≤ -a := sorry

end

end NormNumLemmas


-- This will be ported to `Logic.Nontrivial`.
/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class Nontrivial (α : Type _) : Prop where
  exists_pair_ne : ∃ x y : α, x ≠ y

-- This will be ported to `Algebra.Order.Ring`.

variable [OrderedSemiring α] [Nontrivial α]

@[simp]
theorem zero_lt_one : 0 < (1 : α) := sorry

-- TODO We will also want ports of
-- * `inv_neg` from `Algebra.Field.Basic`
-- * `div_pos` from `Algebra.Order.Field`
-- but we can't do these yet as we don't even have a `Field` typeclass in mathlib4.
