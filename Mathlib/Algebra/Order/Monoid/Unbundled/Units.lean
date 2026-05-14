/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Lemmas for units in an ordered monoid
-/

public section

variable {M : Type*} [Monoid M] [LE M]

namespace Units

section MulLeftMono
variable [MulLeftMono M] (u : Mˣ) {a b : M}

theorem mulLECancellable_val : MulLECancellable (↑u : M) := fun _ _ h ↦ by
  simpa using mul_le_mul_right h ↑u⁻¹

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b :=
  u.mulLECancellable_val.mul_le_mul_iff_left

theorem inv_mul_le_iff : u⁻¹ * a ≤ b ↔ a ≤ u * b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]

theorem le_inv_mul_iff : a ≤ u⁻¹ * b ↔ u * a ≤ b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]

@[simp] theorem one_le_inv : (1 : M) ≤ u⁻¹ ↔ (u : M) ≤ 1 := by
  rw [← u.mul_le_mul_iff_left, mul_one, mul_inv]

@[simp] theorem inv_le_one : u⁻¹ ≤ (1 : M) ↔ (1 : M) ≤ u := by
  rw [← u.mul_le_mul_iff_left, mul_one, mul_inv]

theorem one_le_inv_mul : 1 ≤ u⁻¹ * a ↔ u ≤ a := by
  rw [u.le_inv_mul_iff, mul_one]

theorem inv_mul_le_one : u⁻¹ * a ≤ 1 ↔ a ≤ u := by
  rw [u.inv_mul_le_iff, mul_one]

alias ⟨le_mul_of_inv_mul_le, inv_mul_le_of_le_mul⟩ := inv_mul_le_iff
alias ⟨mul_le_of_le_inv_mul, le_inv_mul_of_mul_le⟩ := le_inv_mul_iff
alias ⟨le_of_one_le_inv, one_le_inv_of_le⟩ := one_le_inv
alias ⟨le_of_inv_le_one, inv_le_one_of_le⟩ := inv_le_one
alias ⟨le_of_one_le_inv_mul, one_le_inv_mul_of_le⟩ := one_le_inv_mul
alias ⟨le_of_inv_mul_le_one, inv_mul_le_one_of_le⟩ := inv_mul_le_one

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b : M} (u : Mˣ)

private theorem mul_le_mul_iff_right : a * u ≤ b * u ↔ a ≤ b :=
  ⟨(by simpa using mul_le_mul_left · ↑u⁻¹), (mul_le_mul_left · _)⟩

theorem mul_inv_le_iff : a * u⁻¹ ≤ b ↔ a ≤ b * u := by
  rw [← u.mul_le_mul_iff_right, u.inv_mul_cancel_right]

theorem le_mul_inv_iff : a ≤ b * u⁻¹ ↔ a * u ≤ b := by
  rw [← u.mul_le_mul_iff_right, inv_mul_cancel_right]

theorem one_le_mul_inv : 1 ≤ a * u⁻¹ ↔ u ≤ a := by
  rw [u.le_mul_inv_iff, one_mul]

theorem mul_inv_le_one : a * u⁻¹ ≤ 1 ↔ a ≤ u := by
  rw [u.mul_inv_le_iff, one_mul]

alias ⟨le_mul_of_mul_inv_le, mul_inv_le_of_le_mul⟩ := mul_inv_le_iff
alias ⟨mul_le_of_le_mul_inv, le_mul_inv_of_mul_le⟩ := le_mul_inv_iff
alias ⟨le_of_one_le_mul_inv, one_le_mul_inv_of_le⟩ := one_le_mul_inv
alias ⟨le_of_mul_inv_le_one, mul_inv_le_one_of_le⟩ := mul_inv_le_one

end MulRightMono

end Units

namespace IsUnit

section MulLeftMono
variable [MulLeftMono M] {a b c : M} (ha : IsUnit a)

include ha

theorem mulLECancellable : MulLECancellable a :=
  ha.unit.mulLECancellable_val

theorem mul_le_mul_left : a * b ≤ a * c ↔ b ≤ c :=
  ha.unit.mul_le_mul_iff_left

alias ⟨le_of_mul_le_mul_left, _⟩ := mul_le_mul_left

end MulLeftMono

section MulRightMono
variable [MulRightMono M] {a b c : M} (hc : IsUnit c)

include hc

theorem mul_le_mul_right : a * c ≤ b * c ↔ a ≤ b :=
  hc.unit.mul_le_mul_iff_right

alias ⟨le_of_mul_le_mul_right, _⟩ := mul_le_mul_right

end MulRightMono

end IsUnit
