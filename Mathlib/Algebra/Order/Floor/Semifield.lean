/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

/-!
# Lemmas on `Nat.floor` and `Nat.ceil` for semifields

This file contains basic results on the natural-valued floor and ceiling functions.

## Tags

rounding, floor, ceil
-/

assert_not_exists Finset

open Set

variable {R K : Type*}

namespace Nat

section LinearOrderedSemifield

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

-- TODO: should these lemmas be `simp`? `norm_cast`?

theorem floor_div_natCast (a : K) (n : ℕ) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply div_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  refine eq_of_forall_le_iff fun m ↦ ?_
  rw [Nat.le_div_iff_mul_le hn, le_floor_iff (by positivity), le_floor_iff ha,
    le_div_iff₀ (by positivity), cast_mul]

theorem cast_mul_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : K) : ⌊n * a⌋₊ / n = ⌊a⌋₊ := by
  simpa [hn] using (floor_div_natCast (n * a) n).symm

theorem mul_cast_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : K) : ⌊a * n⌋₊ / n = ⌊a⌋₊ := by
  rw [mul_comm, cast_mul_floor_div_cancel hn]

@[deprecated (since := "2025-04-01")] alias floor_div_nat := floor_div_natCast

theorem floor_div_ofNat (a : K) (n : ℕ) [n.AtLeastTwo] :
    ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n) :=
  floor_div_natCast a n

/-- Natural division is the floor of field division. -/
theorem floor_div_eq_div (m n : ℕ) : ⌊(m : K) / n⌋₊ = m / n := by
  convert floor_div_natCast (m : K) n
  rw [m.floor_natCast]

end LinearOrderedSemifield

section LinearOrderedField
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K] {a b : K}

lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ ≤ a) : b * a < ⌊a⌋₊ := by
  calc
    b * a < b * (⌊a⌋₊ + 1) := by gcongr; apply lt_floor_add_one
    _ ≤ ⌊a⌋₊ := by
      rw [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le]
      exact le_floor hba

lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a) : ⌈a⌉₊ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉₊ ≤ (⌈(b - 1)⁻¹⌉₊ : K) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉₊ < a + 1 := ceil_lt_add_one <| hba.trans' <| by positivity
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b ≤ a) : ⌈a⌉₊ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (ceil_lt_mul hb hba).le

lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋₊ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉₊ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉₊ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField

end Nat
