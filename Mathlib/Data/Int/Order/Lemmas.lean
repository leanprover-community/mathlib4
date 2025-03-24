/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Further lemmas about the integers

The distinction between this file and `Data.Int.Order.Basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. Please feel free to reorganize these two files.
-/

open Function Nat

namespace Int

/-! ### nat abs -/

theorem natAbs_eq_iff_mul_self_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a * a = b * b := by
  rw [← abs_eq_iff_mul_self_eq, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.natCast_inj.symm

theorem natAbs_lt_iff_mul_self_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a * a < b * b := by
  rw [← abs_lt_iff_mul_self_lt, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_lt.symm

theorem natAbs_le_iff_mul_self_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a * a ≤ b * b := by
  rw [← abs_le_iff_mul_self_le, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_le.symm

theorem div_le_iff_of_dvd_of_pos {a b c : ℤ} (h1 :0 < b) (h2 : b ∣ a): a / b ≤ c ↔ a ≤  b * c := by
  obtain  ⟨_,hx⟩ := h2
  simp only [hx,ne_eq, Int.ne_of_gt,gt_iff_lt, h1, _root_.mul_le_mul_left, ne_eq, not_false_eq_true,
      Int.mul_ediv_cancel_left]

theorem div_lt_iff_of_dvd_of_pos {a b c : ℤ}(h1 :0 < b) (h2 : b ∣ a): a / b < c ↔ a <  b * c := by
  obtain  ⟨_,hx⟩ := h2
  simp only [hx,ne_eq, _root_.ne_of_gt,gt_iff_lt, h1, mul_lt_mul_left, ne_eq, not_false_eq_true,
      Int.mul_ediv_cancel_left]

theorem le_div_iff_of_dvd_of_pos {a b c : ℤ} (h1 :0 < c) (h2 : c ∣ b): a ≤ b / c ↔ c * a ≤  b := by
  obtain  ⟨_,hx⟩ := h2
  simp only [hx,ne_eq,_root_.ne_of_gt,gt_iff_lt,h1,_root_.mul_le_mul_left,ne_eq,not_false_eq_true,
      Int.mul_ediv_cancel_left]

theorem lt_div_iff_of_dvd_of_pos {a b c : ℤ} (h1 :0 < c) (h2 : c ∣ b): a < b / c ↔ c * a <  b := by
  obtain  ⟨_,hx⟩ := h2
  simp only [hx,ne_eq, _root_.ne_of_gt,gt_iff_lt, h1, mul_lt_mul_left, ne_eq, not_false_eq_true,
      Int.mul_ediv_cancel_left]

lemma div_le_div_iff_of_dvd_of_pos {a b c d : ℤ} (h1 : 0 < b) (h2 : 0 < d) (h3 : b ∣ a)
    (h4 : d ∣ c) : a / b ≤  c / d ↔ d * a ≤ c * b := by
  obtain ⟨x,hx⟩ := h3
  obtain ⟨y,hy⟩ := h4
  rw [hx,hy]
  rw [mul_ediv_cancel_left,mul_ediv_cancel_left,mul_assoc,mul_comm y b]
  · simp only [gt_iff_lt, h2, _root_.mul_le_mul_left, h1]
  · exact Int.ne_of_gt h2
  · exact Int.ne_of_gt h1

lemma div_lt_div_iff_of_dvd_of_pos {a b c d : ℤ} (h1 : 0 < b) (h2 : 0 < d) (h3 : b ∣ a)
    (h4 : d ∣ c) : a / b <  c / d ↔ d * a < c * b := by
  obtain ⟨x,hx⟩ := h3
  obtain ⟨y,hy⟩ := h4
  rw [hx,hy]
  rw [mul_ediv_cancel_left,mul_ediv_cancel_left,mul_assoc,mul_comm y b]
  · simp only [gt_iff_lt, h2, _root_.mul_lt_mul_left, h1]
  · exact Int.ne_of_gt h2
  · exact Int.ne_of_gt h1

end Int
