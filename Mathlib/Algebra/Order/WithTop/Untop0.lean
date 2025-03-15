/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Conversion from WithTop to Base Type

For types α that are instances of `Zero`, we provide a convenient conversion,
`WithTop.untop₀`, that maps elements `a : WithTop α` to `α`, by mapping `⊤` to
zero.

For settings where `α` has additional structure, we provide a large number of
simplifier lemmas, akin to those that already exists for `ENat.toNat`.
-/

namespace WithTop
variable {α : Type*}

/-- Conversion from `WithTop α` to `α`, mapping `⊤` to zero. -/
def untop₀ [Zero α] (a : WithTop α) : α := a.untopD 0

/-!
## Simplifying Lemmas in cases where α is an Instance of Zero
-/

@[simp]
lemma untop₀_eq_zero [Zero α] (a : WithTop α) :
    a.untop₀ = 0 ↔ a = 0 ∨ a = ⊤ := by simp [WithTop.untop₀]

@[simp]
lemma untop₀_top [Zero α] :
    (⊤ : WithTop α).untop₀ = (0 : α) := by simp [WithTop.untop₀]

@[simp]
lemma untop₀_zero [Zero α] :
    (0 : WithTop α).untop₀ = (0 : α) := by simp [WithTop.untop₀]

@[simp]
lemma untop₀_coe [Zero α] (a : α) : (a : WithTop α).untop₀ = a := rfl

/-!
## Simplifying Lemmas in cases where α is an AddMonoid
-/
@[simp]
lemma untop₀_add [AddMonoid α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untop₀ = a.untop₀ + b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp [← WithTop.coe_add]

/-!
## Simplifying Lemmas in cases where α is a MulZeroClass
-/

@[simp]
lemma untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : WithTop α) :
    (a * b).untop₀ = a.untop₀ * b.untop₀ := by
  by_cases h₁a : a = 0
  · simp [h₁a]
  by_cases h₁b : b = 0
  · simp [h₁b]
  by_cases h₂a : a = ⊤
  · simp [h₂a, WithTop.top_mul h₁b]
  by_cases h₂b : b = ⊤
  · simp [h₂b, WithTop.mul_top h₁a]
  lift a to α using h₂a
  lift b to α using h₂b
  simp [← WithTop.coe_mul]

/-!
## Simplifying Lemmas in cases where α is a LinearOrderedAddCommGroup
-/
@[simp]
lemma untop₀_neg [LinearOrderedAddCommGroup α] (a : WithTop α) :
    (-a).untop₀ = -a.untop₀ := by
  by_cases ha : a = ⊤
  · simp [ha]
  · lift a to α using ha
    rw [(by rfl : -a = (↑(-a) : WithTop α)), WithTop.untop₀_coe]
    simp

end WithTop
