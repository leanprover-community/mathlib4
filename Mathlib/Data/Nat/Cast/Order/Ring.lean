/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Nat.Cast.NeZero
import Mathlib.Algebra.Order.Ring.Nat

#align_import data.nat.cast.basic from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Cast of natural numbers: lemmas about bundled ordered semirings

-/

variable {α β : Type*}

namespace Nat

section OrderedSemiring
/- Note: even though the section indicates `OrderedSemiring`, which is the common use case,
we use a generic collection of instances so that it applies in other settings (e.g., in a
`StarOrderedRing`, or the `selfAdjoint` or `StarOrderedRing.positive` parts thereof). -/

variable [AddMonoidWithOne α] [PartialOrder α]
variable [CovariantClass α α (· + ·) (· ≤ ·)] [ZeroLEOneClass α]

/-- Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_nonneg {α} [OrderedSemiring α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n
#align nat.cast_nonneg Nat.cast_nonneg

/-- Specialisation of `Nat.ofNat_nonneg'`, which seems to be easier for Lean to use. -/
-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_nonneg {α} [OrderedSemiring α] (n : ℕ) [n.AtLeastTwo] :
    0 ≤ (no_index (OfNat.ofNat n : α)) :=
  ofNat_nonneg' n

@[simp, norm_cast]
theorem cast_min {α} [LinearOrderedSemiring α] {a b : ℕ} : ((min a b : ℕ) : α) = min (a : α) b :=
  (@mono_cast α _).map_min
#align nat.cast_min Nat.cast_min

@[simp, norm_cast]
theorem cast_max {α} [LinearOrderedSemiring α] {a b : ℕ} : ((max a b : ℕ) : α) = max (a : α) b :=
  (@mono_cast α _).map_max
#align nat.cast_max Nat.cast_max

section Nontrivial

variable [NeZero (1 : α)]

/-- Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use. -/
@[simp]
theorem cast_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} : (0 : α) < n ↔ 0 < n := cast_pos'
#align nat.cast_pos Nat.cast_pos

/-- See also `Nat.ofNat_pos`, specialised for an `OrderedSemiring`. -/
-- See note [no_index around OfNat.ofNat]
@[simp low]
theorem ofNat_pos' {n : ℕ} [n.AtLeastTwo] : 0 < (no_index (OfNat.ofNat n : α)) :=
  cast_pos'.mpr (NeZero.pos n)

/-- Specialisation of `Nat.ofNat_pos'`, which seems to be easier for Lean to use. -/
-- See note [no_index around OfNat.ofNat]
@[simp]
theorem ofNat_pos {α} [OrderedSemiring α] [Nontrivial α] {n : ℕ} [n.AtLeastTwo] :
    0 < (no_index (OfNat.ofNat n : α)) :=
  ofNat_pos'

end Nontrivial

end OrderedSemiring

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
theorem cast_tsub [CanonicallyOrderedCommSemiring α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]
#align nat.cast_tsub Nat.cast_tsub

@[simp, norm_cast]
theorem abs_cast [LinearOrderedRing α] (a : ℕ) : |(a : α)| = a :=
  abs_of_nonneg (cast_nonneg a)
#align nat.abs_cast Nat.abs_cast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem abs_ofNat [LinearOrderedRing α] (n : ℕ) [n.AtLeastTwo] :
    |(no_index (OfNat.ofNat n : α))| = OfNat.ofNat n :=
  abs_cast n

end Nat

