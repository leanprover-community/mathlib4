/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Lemmas for units in an ordered monoid
-/

variable {M : Type*} [Monoid M] [LE M]

theorem Units.mulLECancellable_val [MulLeftMono M] (a : Mˣ) :
    MulLECancellable (↑a : M) := fun _ _ h ↦ by
  simpa using mul_le_mul_left' h ↑a⁻¹

theorem Units.mul_le_mul_left [MulLeftMono M] (a : Mˣ) {b c : M} :
    a * b ≤ a * c ↔ b ≤ c :=
  a.mulLECancellable_val.mul_le_mul_iff_left

theorem IsUnit.mulLECancellable [MulLeftMono M] {a : M} (ha : IsUnit a) :
    MulLECancellable a :=
  ha.unit.mulLECancellable_val

theorem IsUnit.mul_le_mul_left [MulLeftMono M] {a b c : M} (ha : IsUnit a) :
    a * b ≤ a * c ↔ b ≤ c :=
  ha.unit.mul_le_mul_left

theorem Units.mul_le_mul_right [MulRightMono M] (a : Mˣ) {b c : M} :
    b * a ≤ c * a ↔ b ≤ c :=
  ⟨(by simpa using mul_le_mul_right' · ↑a⁻¹), (mul_le_mul_right' · _)⟩

theorem IsUnit.mul_le_mul_right [MulRightMono M] {a b c : M} (ha : IsUnit a) :
    b * a ≤ c * a ↔ b ≤ c :=
  ha.unit.mul_le_mul_right
