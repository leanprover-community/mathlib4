/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs


/-!
# Lemmas for units in an ordered monoid
-/

theorem Units.mul_le_mul_left
    {M : Type*} [Monoid M] [LE M] [MulLeftMono M]
    (a : Mˣ) {b c : M} : a * b ≤ a * c ↔ b ≤ c :=
  ⟨(by convert mul_le_mul_left' · (a⁻¹ : Mˣ) <;> rw [← mul_assoc, a.inv_mul, one_mul]),
  (mul_le_mul_left' · _)⟩

theorem IsUnit.mul_le_mul_left
    {M : Type*} [Monoid M] [LE M] [MulLeftMono M]
    {a b c : M} (ha : IsUnit a) : a * b ≤ a * c ↔ b ≤ c :=
  ha.unit.mul_le_mul_left

theorem Units.mul_le_mul_right
    {M : Type*} [Monoid M] [LE M] [MulRightMono M]
    (a : Mˣ) {b c : M} : b * a ≤ c * a ↔ b ≤ c :=
  ⟨(by convert mul_le_mul_right' · (a⁻¹ : Mˣ) <;> rw [mul_assoc, a.mul_inv, mul_one]),
  (mul_le_mul_right' · _)⟩

theorem IsUnit.mul_le_mul_right
    {M : Type*} [Monoid M] [LE M] [MulRightMono M]
    {a b c : M} (ha : IsUnit a) : b * a ≤ c * a ↔ b ≤ c :=
  ha.unit.mul_le_mul_right
