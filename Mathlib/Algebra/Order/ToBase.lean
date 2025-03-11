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
`WithTop.toBase`, that maps elements `a : WithTop α` to `α`, by mapping `⊤` to
zero.

For settings where `α` has additional structure, we provide a large number of
simplifier lemmas, akin to those that already exists for `ENat.toNat`.
-/

variable {α : Type*}

noncomputable def WithTop.toBase [Zero α] (a : WithTop α) : α := a.untopD 0

/-!
## Simplifying Lemmas in cases where α is an Instance of Zero
-/
lemma WithTop.toBase_def [Zero α] (a : WithTop α) :
    a.toBase = a.untopD 0 := rfl

@[simp]
lemma WithTop.toBase_eq_zero_iff [Zero α] (a : WithTop α) :
    a.toBase = 0 ↔ a = 0 ∨ a = ⊤ := by simp_all [WithTop.toBase_def]

@[simp]
lemma WithTop.toBase_of_top [Zero α] :
    (⊤ : WithTop α).toBase = (0 : α) := by simp_all [WithTop.toBase_def]

@[simp]
lemma WithTop.toBase_of_zero [Zero α] :
    (0 : WithTop α).toBase = (0 : α) := by simp_all [WithTop.toBase_def]

@[simp]
lemma WithTop.toBase_coe [Zero α] (a : α) : (a : WithTop α).toBase = a := rfl

/-!
## Simplifying Lemmas in cases where α is an AddMonoid
-/
@[simp]
lemma toBase_add [AddMonoid α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a + b).toBase = a.toBase + b.toBase := by
  lift a to α using ha
  lift b to α using hb
  simp [← WithTop.coe_add]

/-!
## Simplifying Lemmas in cases where α is a LinearOrderedAddCommGroup
-/
@[simp]
lemma toBase_neg [LinearOrderedAddCommGroup α] (a : WithTop α) :
    (-a).toBase = -a.toBase  := by
  by_cases ha : a = ⊤
  · simp [ha]
  · lift a to α using ha
    rw [(by rfl : -a = (↑(-a) : WithTop α)), WithTop.toBase_coe]
    simp

/-!
## Simplifying Lemmas in cases where α is a LinearOrderedCommRing
-/
@[simp]
lemma toBase_mul [LinearOrderedCommRing α] (a b : WithTop α) :
    (a * b).toBase = a.toBase * b.toBase := by
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
