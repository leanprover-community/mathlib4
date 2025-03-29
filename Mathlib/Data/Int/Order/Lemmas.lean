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

theorem div_le_iff_of_dvd_of_pos {a b : ℤ} (hb : 0 < b) (hba : b ∣ a) (c : ℤ) :
    a / b ≤ c ↔ a ≤ b * c := by
  obtain ⟨_, hx⟩ := hba
  simp only [hx, ne_eq, hb, Int.ne_of_gt, not_false_eq_true, mul_div_cancel_left₀,
    _root_.mul_le_mul_left]

theorem div_le_iff_of_dvd_of_neg {a b : ℤ} (hb : b < 0) (hba : b ∣ a) (c : ℤ) :
    a / b ≤ c ↔ b * c ≤ a := by
  obtain ⟨_, hx⟩ := hba
  simp only [hx, ne_eq, hb, Int.ne_of_lt, not_false_eq_true, mul_div_cancel_left₀,
    mul_le_mul_left_of_neg]

theorem div_lt_iff_of_dvd_of_pos {a b : ℤ} (hb : 0 < b) (hba : b ∣ a) (c : ℤ) :
    a / b < c ↔ a < b * c := by
  obtain ⟨_, hx⟩ := hba
  simp only [hx, ne_eq, hb, _root_.ne_of_gt, not_false_eq_true, mul_div_cancel_left₀,
    mul_lt_mul_left]

theorem div_lt_iff_of_dvd_of_neg {a b : ℤ} (hb : b < 0) (hba : b ∣ a) (c : ℤ) :
    a / b < c ↔ b * c < a := by
  obtain ⟨_, hx⟩ := hba
  simp only [hx, ne_eq, hb, _root_.ne_of_lt, not_false_eq_true, mul_div_cancel_left₀,
    mul_lt_mul_left_of_neg hb]

theorem le_div_iff_of_dvd_of_pos {b c : ℤ} (hc : 0 < c) (hcb : c ∣ b) (a : ℤ):
    a ≤ b / c ↔ c * a ≤ b := by
  obtain ⟨_, hx⟩ := hcb
  simp only [hx, ne_eq, hc, _root_.ne_of_gt, not_false_eq_true, mul_div_cancel_left₀,
    _root_.mul_le_mul_left]

theorem le_div_iff_of_dvd_of_neg {b c : ℤ} (hc : c < 0) (hcb : c ∣ b) (a : ℤ):
    a ≤ b / c ↔ b ≤ c * a := by
  obtain ⟨_, hx⟩ := hcb
  simp only [hx, ne_eq, hc, _root_.ne_of_lt, not_false_eq_true, mul_div_cancel_left₀,
    mul_le_mul_left_of_neg hc]

theorem lt_div_iff_of_dvd_of_pos {b c : ℤ} (hc : 0 < c) (hcb : c ∣ b) (a : ℤ):
    a < b / c ↔ c * a < b := by
  obtain ⟨_, hx⟩ := hcb
  simp only [hx, ne_eq, hc, _root_.ne_of_gt, not_false_eq_true, mul_div_cancel_left₀,
    mul_lt_mul_left]

theorem lt_div_iff_of_dvd_of_neg {b c : ℤ} (hc : c < 0) (hcb : c ∣ b) (a : ℤ) :
    a < b / c ↔ b < c * a := by
  obtain ⟨_, hx⟩ := hcb
  simp only [hx, ne_eq, hc, _root_.ne_of_lt, not_false_eq_true, mul_div_cancel_left₀,
    mul_lt_mul_left_of_neg hc]

lemma div_le_div_iff_of_dvd_of_pos_of_pos {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤  c / d ↔ d * a ≤ c * b := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_gt hd), mul_ediv_cancel_left _ (Int.ne_of_gt hb),
    mul_assoc,mul_comm y b,_root_.mul_le_mul_left hd,_root_.mul_le_mul_left hb]

lemma div_le_div_iff_of_dvd_of_pos_of_neg {a b c d : ℤ} (hb : 0 < b) (hd : d < 0) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤  c / d ↔ c * b ≤ d * a := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_lt hd), mul_ediv_cancel_left _ (Int.ne_of_gt hb),
    mul_assoc,mul_comm y b,mul_le_mul_left_of_neg hd,mul_le_mul_iff_of_pos_left hb]

lemma div_le_div_iff_of_dvd_of_neg_of_pos {a b c d : ℤ} (hb : b < 0) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤  c / d ↔ c * b ≤ d * a := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_lt hb), mul_ediv_cancel_left _ (Int.ne_of_gt hd),
    mul_assoc, mul_le_mul_iff_of_pos_left hd, mul_comm y b,mul_le_mul_left_of_neg hb]

lemma div_le_div_iff_of_dvd_of_neg_of_neg {a b c d : ℤ} (hb : b < 0) (hd : d < 0) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b ≤  c / d ↔ d * a ≤ c * b := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_lt hd), mul_ediv_cancel_left _ (Int.ne_of_lt hb),
    mul_assoc,mul_comm y b,mul_le_mul_left_of_neg hd,mul_le_mul_left_of_neg hb]

lemma div_lt_div_iff_of_dvd_of_pos {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b <  c / d ↔ d * a < c * b := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_gt hd), mul_ediv_cancel_left _ (Int.ne_of_gt hb),
    mul_assoc, mul_comm y b, _root_.mul_lt_mul_left hd, _root_.mul_lt_mul_left hb]

lemma div_lt_div_iff_of_dvd_of_pos_of_neg {a b c d : ℤ} (hb : 0 < b) (hd : d < 0) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_lt hd), mul_ediv_cancel_left _ (Int.ne_of_gt hb),
    mul_assoc,mul_comm y b,mul_lt_mul_left_of_neg hd,mul_lt_mul_iff_of_pos_left hb]

lemma div_lt_div_iff_of_dvd_of_neg_of_pos {a b c d : ℤ} (hb : b < 0) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b < c / d ↔ c * b < d * a := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_lt hb), mul_ediv_cancel_left _ (Int.ne_of_gt hd),
    mul_assoc, mul_lt_mul_iff_of_pos_left hd, mul_comm y b,mul_lt_mul_left_of_neg hb]

lemma div_lt_div_iff_of_dvd_of_neg_of_neg {a b c d : ℤ} (hb : b < 0) (hd : d < 0) (hba : b ∣ a)
    (hdc : d ∣ c) : a / b <  c / d ↔ d * a < c * b := by
  obtain ⟨_, hx⟩ := hba
  obtain ⟨y, hy⟩ := hdc
  rw [hx, hy, mul_ediv_cancel_left _ (Int.ne_of_lt hd), mul_ediv_cancel_left _ (Int.ne_of_lt hb),
    mul_assoc,mul_comm y b,mul_lt_mul_left_of_neg hd,mul_lt_mul_left_of_neg hb]

end Int
