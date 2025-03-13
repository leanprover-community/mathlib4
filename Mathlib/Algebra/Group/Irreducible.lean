/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Yaël Dillies
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Units.Basic

/-!
# Irreducible elements in a monoid

This file defines irreducible elements of a monoid, as non-units that can't be written as the sum of
two non-units. This generalises irreducible elements of a ring.

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Prime`
(see `irreducible_iff_prime`), however this is not true in general.
-/

assert_not_exists MonoidWithZero OrderedCommMonoid Multiset

variable {M : Type*}

/-- `Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements. -/
structure AddIrreducible [AddMonoid M] (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isAddUnit : ¬IsAddUnit p
  /-- If an irreducible elements factors, then one factor is a unit. -/
  isAddUnit_or_isAddUnit ⦃a b⦄ : p = a + b → IsAddUnit a ∨ IsAddUnit b

section Monoid
variable [Monoid M] {p q x y : M}

/-- `Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements. -/
@[to_additive AddIrreducible]
structure Irreducible (p : M) : Prop where
  /-- An irreducible element is not a unit. -/
  not_isUnit : ¬IsUnit p
  /-- If an irreducible elements factors, then one factor is a unit. -/
  isUnit_or_isUnit ⦃a b⦄ : p = a * b → IsUnit a ∨ IsUnit b

@[deprecated (since := "2025-03-13")] alias Irreducible.not_unit := Irreducible.not_isUnit

@[deprecated (since := "2025-03-13")]
alias Irreducible.isUnit_or_isUnit' := Irreducible.isUnit_or_isUnit

@[to_additive]
lemma irreducible_iff : Irreducible p ↔ ¬IsUnit p ∧ ∀ a b, p = a * b → IsUnit a ∨ IsUnit b :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

@[to_additive (attr := simp)]
lemma not_irreducible_one : ¬Irreducible (1 : M) := by simp [irreducible_iff]

@[to_additive]
lemma Irreducible.ne_one (hp : Irreducible p) : p ≠ 1 := by rintro rfl; exact not_irreducible_one hp

@[to_additive]
lemma of_irreducible_mul : Irreducible (x * y) → IsUnit x ∨ IsUnit y | ⟨_, h⟩ => h rfl

@[to_additive]
lemma irreducible_or_factor (hp : ¬IsUnit p) :
    Irreducible p ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ a * b = p := by
  refine or_iff_not_imp_right.2 fun H ↦ ?_
  simp? [h, irreducible_iff] at H ⊢ says
    simp only [exists_and_left, not_exists, not_and, irreducible_iff, hp, not_false_eq_true,
      true_and] at H ⊢
  refine fun a b h ↦ by_contradiction fun o ↦ ?_
  simp? [not_or] at o says simp only [not_or] at o
  exact H _ o.1 _ o.2 h.symm

end Monoid
