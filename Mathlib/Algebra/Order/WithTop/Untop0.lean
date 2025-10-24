/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Conversion from WithTop to Base Type

For types α that are instances of `Zero`, we provide a convenient conversion, `WithTop.untop₀`, that
maps elements `a : WithTop α` to `α`, by mapping `⊤` to zero.

For settings where `α` has additional structure, we provide a large number of simplifier lemmas,
akin to those that already exists for `ENat.toNat`.
-/

namespace WithTop
variable {α : Type*}

section Zero
variable [Zero α]

/-- Conversion from `WithTop α` to `α`, mapping `⊤` to zero. -/
def untop₀ (a : WithTop α) : α := a.untopD 0

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
## Simplifying Lemmas involving addition and negation
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

@[simp]
lemma untop₀_natCast [AddMonoidWithOne α] (n : ℕ) : untop₀ (n : WithTop α) = n := rfl

@[simp]
lemma untop₀_ofNat [AddMonoidWithOne α] (n : ℕ) [n.AtLeastTwo] :
    untop₀ (ofNat(n) : WithTop α) = n := rfl

@[simp]
lemma untop₀_neg [AddCommGroup α] : ∀ a : WithTop α, (-a).untop₀ = -a.untop₀
  | ⊤ => by simp
  | (a : α) => rfl

/-!
## Simplifying Lemmas in cases where α is a MulZeroClass
-/

@[simp]
lemma untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : WithTop α) :
    (a * b).untop₀ = a.untop₀ * b.untop₀ := untopD_zero_mul a b

/-!
## Simplifying Lemmas in cases where α is a OrderedAddCommGroup
-/

section OrderedAddCommGroup

variable [AddCommGroup α] [PartialOrder α] {a b : WithTop α}

/--
Elements of ordered additive commutative groups are nonnegative iff their untop₀ is nonnegative.
-/
@[simp] lemma untop₀_nonneg : 0 ≤ a.untop₀ ↔ 0 ≤ a := by
  cases a with
  | top => tauto
  | coe a => simp

theorem le_of_untop₀_le_untop₀ (ha : a ≠ ⊤) (h : a.untop₀ ≤ b.untop₀) : a ≤ b := by
  lift a to α using ha
  by_cases hb : b = ⊤
  · simp_all
  lift b to α using hb
  simp_all

@[simp, gcongr] theorem untop₀_le_untop₀ (hb : b ≠ ⊤) (h : a ≤ b) : a.untop₀ ≤ b.untop₀ := by
  lift b to α using hb
  by_cases ha : a = ⊤
  · simp_all
  lift a to α using ha
  simp_all

theorem untop₀_le_untop₀_iff (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a.untop₀ ≤ b.untop₀ ↔ a ≤ b := by
  lift a to α using ha
  lift b to α using hb
  simp

end OrderedAddCommGroup

/-!
## Simplifying Lemmas in cases where α is a LinearOrderedAddCommGroup
-/

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] {a b : WithTop α}

@[simp] theorem untop₀_max (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (max a b).untop₀ = max a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  simp only [untop₀_coe]
  by_cases h : a ≤ b
  · simp [max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  rw [not_le] at h
  simp [max_eq_left h.le, max_eq_left (coe_lt_coe.mpr h).le]

@[simp] theorem untop₀_min (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (min a b).untop₀ = min a.untop₀ b.untop₀ := by
  lift a to α using ha
  lift b to α using hb
  norm_cast

end LinearOrderedAddCommGroup

end WithTop
