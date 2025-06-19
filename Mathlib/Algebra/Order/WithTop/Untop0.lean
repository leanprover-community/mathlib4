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

section Zero
variable [Zero α]

/-- Conversion from `WithTop α` to `α`, mapping `⊤` to zero. -/
def untop₀ [Zero α] (a : WithTop α) : α := a.untopD 0

/-!
## Simplifying Lemmas in cases where α is an Instance of Zero
-/

@[simp]
lemma untop₀_eq_zero {a : WithTop α} :
    a.untop₀ = 0 ↔ a = 0 ∨ a = ⊤ := by simp [untop₀]

@[simp]
lemma untop₀_top : untop₀ ⊤ = (0 : α) := by simp [untop₀]

@[simp]
lemma untop₀_zero : untop₀ 0 = (0 : α) := by simp [untop₀]

@[simp]
lemma untop₀_coe (a : α) : (a : WithTop α).untop₀ = a := rfl

lemma coe_untop₀_of_ne_top {a : WithTop α} (ha : a ≠ ⊤) :
    a.untop₀ = a := by
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 ha
  simp [← hb]

end Zero

/-!
## Simplifying Lemmas in cases where α is an AddMonoid
-/
@[simp]
lemma untopD_add [Add α] {a b : WithTop α} {c : α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untopD c = a.untopD c + b.untopD c := by
  lift a to α using ha
  lift b to α using hb
  simp [← coe_add]

@[simp]
lemma untop₀_add [AddZeroClass α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).untop₀ = a.untop₀ + b.untop₀ := untopD_add ha hb

/-!
## Simplifying Lemmas in cases where α is a MulZeroClass
-/

@[simp]
lemma untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : WithTop α) :
    (a * b).untop₀ = a.untop₀ * b.untop₀ := untopD_zero_mul a b

/-!
## Simplifying Lemmas in cases where α is a OrderedAddCommGroup
-/

/--
Elements of ordered additive commutative groups are nonnegative iff their untop₀ is nonnegative.
-/
@[simp]
lemma untop₀_nonneg [AddCommGroup α] [PartialOrder α] {a : WithTop α} :
    0 ≤ a.untop₀ ↔ 0 ≤ a := by
  cases a with
  | top => tauto
  | coe a => simp

/-!
## Simplifying Lemmas in cases where α is a LinearOrderedAddCommGroup
-/

@[simp]
lemma untop₀_neg [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a : WithTop α) :
    (-a).untop₀ = -a.untop₀ := by
  cases a with
  | top => simp
  | coe a =>
    rw [← LinearOrderedAddCommGroup.coe_neg, untop₀_coe]
    simp

end WithTop
