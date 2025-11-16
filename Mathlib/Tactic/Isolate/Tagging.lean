/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Isolate.Core
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

/-! # @[isolate] lemmas for elementary functions -/

variable {X : Type*}

namespace Mathlib.Tactic.Isolate

/- ### Addition -/

@[isolate]
theorem add_right_eq_iff [AddGroup X] (a b c : X) : a + b = c ↔ a = c - b := eq_sub_iff_add_eq.symm

@[isolate]
theorem add_right_le_iff [AddGroup X] [LE X] [AddRightMono X] (a b c : X) : a + b ≤ c ↔ a ≤ c - b :=
  le_sub_iff_add_le.symm

@[isolate]
theorem add_right_lt_iff [AddGroup X] [LT X] [AddRightStrictMono X] (a b c : X) :
    a + b < c ↔ a < c - b := lt_sub_iff_add_lt.symm

@[isolate]
theorem le_add_right_iff [Add X] [Sub X] [LE X] [OrderedSub X] (a b c : X) :
    c ≤ a + b ↔ c - b ≤ a := tsub_le_iff_right.symm

@[isolate]
theorem lt_add_right_iff [AddGroup X] [LT X] [AddRightStrictMono X] (a b c : X) :
    c < a + b ↔ c - b < a := sub_lt_iff_lt_add.symm

@[isolate]
theorem add_left_eq_iff [AddCommGroup X] (a b c : X) : b + a = c ↔ a = c - b :=
  eq_sub_iff_add_eq'.symm

@[isolate]
theorem add_left_le_iff [AddCommGroup X] [LE X] [AddLeftMono X] (a b c : X) :
    b + a ≤ c ↔ a ≤ c - b := le_sub_iff_add_le'.symm

@[isolate]
theorem add_left_lt_iff [AddCommGroup X] [LT X] [AddLeftStrictMono X] (a b c : X) :
    b + a < c ↔ a < c - b := lt_sub_iff_add_lt'.symm

@[isolate]
theorem le_add_left_iff [AddCommSemigroup X] [Sub X] [Preorder X] [OrderedSub X] (a b c : X) :
    c ≤ b + a ↔ c - b ≤ a := tsub_le_iff_left.symm

@[isolate]
theorem lt_add_left_iff [AddCommGroup X] [LT X] [AddLeftStrictMono X] (a b c : X) :
    c < b + a ↔ c - b < a := sub_lt_iff_lt_add'.symm

/- ### Negation -/

attribute [isolate] neg_eq_iff_eq_neg neg_lt lt_neg

theorem neg_le_iff [AddCommGroup X] [LE X] [AddRightMono X] {a b : X} : - a ≤ b ↔ -b ≤ a := by
  rw [neg_le_iff_add_nonneg, neg_le_iff_add_nonneg, add_comm]

theorem le_neg_iff [AddCommGroup X] [LE X] [AddRightMono X] {a b : X} : b ≤ - a ↔ a ≤ -b := by
  rw [le_neg_iff_add_nonpos_right, le_neg_iff_add_nonpos_right, add_comm]

/- ### Subtraction -/

attribute [isolate] sub_eq_iff_eq_add tsub_le_iff_right sub_lt_iff_lt_add le_sub_iff_add_le
  lt_tsub_iff_right

@[isolate]
theorem sub_left_eq_iff [AddCommGroup X] (a b c : X) : b - a = c ↔ a = b - c := by
  rw [sub_eq_iff_eq_add, eq_sub_iff_add_eq, add_comm, eq_comm]

@[isolate]
theorem sub_left_le_iff [AddCommGroup X] [LE X] [OrderedSub X] (a b c : X) :
    b - a ≤ c ↔ b - c ≤ a := by rw [tsub_le_iff_right, tsub_le_iff_right, add_comm]

@[isolate]
theorem sub_left_lt_iff [AddCommGroup X] [LT X] [AddRightStrictMono X] (a b c : X) :
    b - a < c ↔ b - c < a := by rw [sub_lt_iff_lt_add, sub_lt_iff_lt_add, add_comm]

@[isolate]
theorem le_sub_left_iff [AddCommGroup X] [LE X] [AddRightMono X] (a b c : X) :
    c ≤ b - a ↔ a ≤ b - c := by rw [le_sub_iff_add_le, le_sub_iff_add_le, add_comm]

@[isolate]
theorem lt_sub_left_iff [AddCommSemigroup X] [Sub X] [LinearOrder X] [OrderedSub X] (a b c : X) :
    c < b - a ↔ a < b - c := by
  rw [lt_tsub_iff_right, lt_tsub_iff_right, add_comm]

/- ### Multiplication -/

@[isolate]
theorem mul_right_eq_iff [GroupWithZero X] (a : X) {b : X} (c : X) (hb : b ≠ 0) :
    a * b = c ↔ a = c / b := (eq_div_iff hb).symm

@[isolate]
theorem mul_right_le_iff [GroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : a * b ≤ c ↔ a ≤ c / b := (le_div_iff₀ hb).symm

@[isolate]
theorem mul_right_lt_iff [GroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : a * b < c ↔ a < c / b := (lt_div_iff₀ hb).symm

@[isolate]
theorem le_mul_right_iff [GroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : c ≤ a * b ↔ c / b ≤ a := (div_le_iff₀ hb).symm

@[isolate]
theorem lt_mul_right_iff [GroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : c < a * b ↔ c / b < a := (div_lt_iff₀ hb).symm

@[isolate]
theorem mul_left_eq_iff [CommGroupWithZero X] (a : X) {b : X} (c : X) (hb : b ≠ 0) :
    b * a = c ↔ a = c / b := by rw [eq_div_iff hb, mul_comm]

@[isolate]
theorem mul_left_le_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : b * a ≤ c ↔ a ≤ c / b := by rw [le_div_iff₀ hb, mul_comm]

@[isolate]
theorem mul_left_lt_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : b * a < c ↔ a < c / b := by rw [lt_div_iff₀ hb, mul_comm]

@[isolate]
theorem le_mul_left_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : c ≤ b * a ↔ c / b ≤ a := by rw [div_le_iff₀ hb, mul_comm]

@[isolate]
theorem lt_mul_left_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] (a : X) {b : X}
    (c : X) (hb : 0 < b) : c < b * a ↔ c / b < a := by rw [div_lt_iff₀ hb, mul_comm]

/- ### Inversion -/

attribute [isolate] inv_eq_iff_eq_inv inv_le_comm₀ inv_lt_comm₀ le_inv_comm₀ lt_inv_comm₀

/- ### Division -/

attribute [isolate] div_eq_iff div_le_iff₀ div_lt_iff₀ le_div_iff₀ lt_div_iff₀

@[isolate]
theorem div_left_eq_iff [CommGroupWithZero X] (a : X) {b c : X} (hb : b ≠ 0) (hc : c ≠ 0) :
    b / a = c ↔ a = b / c := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [div_zero]
    suffices b / c ≠ 0 by
      constructor
      · intro h
        exact absurd h.symm hc
      · intro h
        exact absurd h.symm this
    exact div_ne_zero hb hc
  rw [div_eq_iff ha, eq_div_iff_mul_eq hc, mul_comm, eq_comm]

@[isolate]
theorem div_left_le_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] {a : X} (b : X)
    {c : X} (ha : 0 < a) (hc : 0 < c) : b / a ≤ c ↔ b / c ≤ a := by
  rw [div_le_iff₀ ha, div_le_iff₀ hc, mul_comm]

@[isolate]
theorem div_left_lt_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] {a : X} (b : X)
    {c : X} (ha : 0 < a) (hc : 0 < c) : b / a < c ↔ b / c < a := by
  rw [div_lt_iff₀ ha, div_lt_iff₀ hc, mul_comm]

@[isolate]
theorem le_div_left_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] {a : X} (b : X)
    {c : X} (ha : 0 < a) (hc : 0 < c) : c ≤ b / a ↔ a ≤ b / c := by
  rw [le_div_iff₀ ha, le_div_iff₀ hc, mul_comm]

@[isolate]
theorem lt_div_left_iff [CommGroupWithZero X] [PartialOrder X] [MulPosReflectLT X] {a : X} (b : X)
    {c : X} (ha : 0 < a) (hc : 0 < c) : c < b / a ↔ a < b / c := by
  rw [lt_div_iff₀ ha, lt_div_iff₀ hc, mul_comm]

end Mathlib.Tactic.Isolate
