/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Rounding

This file defines the `round` function, which uses the `floor` or `ceil` function to round a number
to the nearest integer.

## Main Definitions

* `round a`: Nearest integer to `a`. It rounds halves towards infinity.

## Tags

rounding
-/

assert_not_exists Finset

open Set

variable {F α β : Type*}

open Int

/-! ### Round -/

section round

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/-- `round` rounds a number to the nearest integer. `round (1 / 2) = 1` -/
def round (x : α) : ℤ :=
  if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉

@[simp]
theorem round_zero : round (0 : α) = 0 := by simp [round]

@[simp]
theorem round_one : round (1 : α) = 1 := by simp [round]

@[simp]
theorem round_natCast (n : ℕ) : round (n : α) = n := by simp [round]

@[simp]
theorem round_ofNat (n : ℕ) [n.AtLeastTwo] : round (ofNat(n) : α) = ofNat(n) :=
  round_natCast n

@[simp]
theorem round_intCast (n : ℤ) : round (n : α) = n := by simp [round]

@[simp]
theorem round_add_intCast (x : α) (y : ℤ) : round (x + y) = round x + y := by
  rw [round, round, Int.fract_add_intCast, Int.floor_add_intCast, Int.ceil_add_intCast,
    ← apply_ite₂, ite_self]

@[simp]
theorem round_add_one (a : α) : round (a + 1) = round a + 1 := by
  rw [← round_add_intCast a 1, cast_one]

@[simp]
theorem round_sub_intCast (x : α) (y : ℤ) : round (x - y) = round x - y := by
  rw [sub_eq_add_neg]
  norm_cast
  rw [round_add_intCast, sub_eq_add_neg]

@[simp]
theorem round_sub_one (a : α) : round (a - 1) = round a - 1 := by
  rw [← round_sub_intCast a 1, cast_one]

@[simp]
theorem round_add_natCast (x : α) (y : ℕ) : round (x + y) = round x + y :=
  mod_cast round_add_intCast x y

@[simp]
theorem round_add_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x + ofNat(n)) = round x + ofNat(n) :=
  round_add_natCast x n

@[simp]
theorem round_sub_natCast (x : α) (y : ℕ) : round (x - y) = round x - y :=
  mod_cast round_sub_intCast x y

@[simp]
theorem round_sub_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x - ofNat(n)) = round x - ofNat(n) :=
  round_sub_natCast x n

@[simp]
theorem round_intCast_add (x : α) (y : ℤ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_intCast, add_comm]

@[simp]
theorem round_natCast_add (x : α) (y : ℕ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_natCast, add_comm]

@[simp]
theorem round_ofNat_add (n : ℕ) [n.AtLeastTwo] (x : α) :
    round (ofNat(n) + x) = ofNat(n) + round x :=
  round_natCast_add x n

theorem abs_sub_round_eq_min (x : α) : |x - round x| = min (fract x) (1 - fract x) := by
  simp_rw [round, min_def_lt, two_mul, ← lt_tsub_iff_left]
  rcases lt_or_ge (fract x) (1 - fract x) with hx | hx
  · rw [if_pos hx, if_pos hx, self_sub_floor, abs_fract]
  · have : 0 < fract x := by
      replace hx : 0 < fract x + fract x := lt_of_lt_of_le zero_lt_one (tsub_le_iff_left.mp hx)
      simpa only [← two_mul, mul_pos_iff_of_pos_left, zero_lt_two] using hx
    rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr hx), abs_sub_comm, ceil_sub_self_eq this.ne.symm,
      abs_one_sub_fract]

theorem round_le (x : α) (z : ℤ) : |x - round x| ≤ |x - z| := by
  rw [abs_sub_round_eq_min, min_le_iff]
  rcases le_or_gt (z : α) x with (hx | hx) <;> [left; right]
  · conv_rhs => rw [abs_eq_self.mpr (sub_nonneg.mpr hx), ← fract_add_floor x, add_sub_assoc]
    simpa only [le_add_iff_nonneg_right, sub_nonneg, cast_le] using le_floor.mpr hx
  · rw [abs_eq_neg_self.mpr (sub_neg.mpr hx).le]
    conv_rhs => rw [← fract_add_floor x]
    rw [add_sub_assoc, add_comm, neg_add, neg_sub, le_add_neg_iff_add_le, sub_add_cancel,
      le_sub_comm]
    norm_cast
    exact floor_le_sub_one_iff.mpr hx

end LinearOrderedRing

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  simp_rw [round, (by simp only [lt_div_iff₀', two_pos] : 2 * fract x < 1 ↔ fract x < 1 / 2)]
  rcases lt_or_ge (fract x) (1 / 2) with hx | hx
  · conv_rhs => rw [← fract_add_floor x, add_assoc, add_left_comm, floor_intCast_add]
    rw [if_pos hx, left_eq_add, floor_eq_iff, cast_zero, zero_add]
    constructor
    · linarith [fract_nonneg x]
    · linarith
  · have : ⌊fract x + 1 / 2⌋ = 1 := by
      rw [floor_eq_iff]
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [fract_lt_one x]
    rw [if_neg (not_lt.mpr hx), ← fract_add_floor x, add_assoc, add_left_comm, floor_intCast_add,
      ceil_add_intCast, add_comm _ ⌊x⌋, add_right_inj, ceil_eq_iff, this, cast_one, sub_self]
    constructor
    · linarith
    · linarith [fract_lt_one x]

@[simp]
theorem round_two_inv : round (2⁻¹ : α) = 1 := by
  simp only [round_eq, ← one_div, add_halves, floor_one]

@[simp]
theorem round_neg_two_inv : round (-2⁻¹ : α) = 0 := by
  simp only [round_eq, ← one_div, neg_add_cancel, floor_zero]

@[simp]
theorem round_eq_zero_iff {x : α} : round x = 0 ↔ x ∈ Ico (-(1 / 2)) ((1 : α) / 2) := by
  rw [round_eq, floor_eq_zero_iff, add_mem_Ico_iff_left]
  norm_num

theorem abs_sub_round (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq, abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

theorem abs_sub_round_div_natCast_eq {m n : ℕ} :
    |(m : α) / n - round ((m : α) / n)| = ↑(min (m % n) (n - m % n)) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min, Nat.cast_min, ← min_div_div_right hn'.le,
    fract_div_natCast_eq_div_natCast_mod, Nat.cast_sub (m.mod_lt hn).le, sub_div, div_self hn'.ne']

@[bound]
theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
  rw [round_eq x, show x - 1 / 2 = x + 1 / 2 - 1 by linarith]
  exact Int.sub_one_lt_floor (x + 1 / 2)

@[bound]
theorem round_le_add_half (x : α) : round x ≤ x + 1 / 2 := by
  rw [round_eq x]
  exact Int.floor_le (x + 1 / 2)

end LinearOrderedField

end round

namespace Int

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [LinearOrder β] [IsStrictOrderedRing β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_ofNat]

end Int
