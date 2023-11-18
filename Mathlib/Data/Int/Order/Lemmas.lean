/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Lemmas

#align_import data.int.order.lemmas from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Further lemmas about the integers
The distinction between this file and `Data.Int.Order.Basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. After `data.rat.order` has been ported, please feel free to reorganize these two files.
-/

open Nat

namespace Int

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

theorem natAbs_eq_iff_mul_self_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a * a = b * b := by
  rw [← abs_eq_iff_mul_self_eq, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.coe_nat_inj'.symm
#align int.nat_abs_eq_iff_mul_self_eq Int.natAbs_eq_iff_mul_self_eq

#align int.eq_nat_abs_iff_mul_eq_zero Int.eq_natAbs_iff_mul_eq_zero

theorem natAbs_lt_iff_mul_self_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a * a < b * b := by
  rw [← abs_lt_iff_mul_self_lt, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_lt.symm
#align int.nat_abs_lt_iff_mul_self_lt Int.natAbs_lt_iff_mul_self_lt

theorem natAbs_le_iff_mul_self_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a * a ≤ b * b := by
  rw [← abs_le_iff_mul_self_le, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_le.symm
#align int.nat_abs_le_iff_mul_self_le Int.natAbs_le_iff_mul_self_le

theorem dvd_div_of_mul_dvd {a b c : ℤ} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Int.ediv_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine' ⟨d, _⟩
  rw [mul_assoc, Int.mul_ediv_cancel_left _ ha]
#align int.dvd_div_of_mul_dvd Int.dvd_div_of_mul_dvd

/-! ### units -/


theorem eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_cases hm : m = 0
  · subst m
    exact zero_dvd_iff.mp h1
  rcases h1 with ⟨d, rfl⟩
  apply mul_eq_zero_of_right
  rw [← abs_lt_one_iff, ← mul_lt_iff_lt_one_right (abs_pos.mpr hm), ← abs_mul]
  exact lt_of_lt_of_le h2 (le_abs_self m)
#align int.eq_zero_of_abs_lt_dvd Int.eq_zero_of_abs_lt_dvd

/-! ### Div -/

theorem div_le_iff_of_dvd_of_pos {x y z : ℤ} (h1 :0 < y) (h2 : y ∣  x): x / y ≤ z ↔ x ≤  y * z := by
  rcases h2 with ⟨a,ha⟩
  simp only [ha,ne_eq, Int.ne_of_gt,gt_iff_lt, h1, _root_.mul_le_mul_left, ne_eq, not_false_eq_true,
      Int.mul_ediv_cancel_left]

theorem div_lt_iff_of_dvd_of_pos {x y z : ℤ}(h1 :0 < y) (h2 : y ∣  x): x / y < z ↔ x <  y * z := by
  rcases h2 with ⟨a,ha⟩
  simp only [ha,ne_eq, _root_.ne_of_gt,gt_iff_lt, h1, mul_lt_mul_left, ne_eq, not_false_eq_true,
      Int.mul_ediv_cancel_left]

theorem le_div_iff_of_dvd_of_pos {x y z : ℤ} (h1 :0 < z) (h2 : z ∣ y): x ≤ y / z ↔ z * x ≤  y := by
  rcases h2 with ⟨a,ha⟩
  simp only [ha,ne_eq,_root_.ne_of_gt,gt_iff_lt,h1,_root_.mul_le_mul_left,ne_eq,not_false_eq_true,
      Int.mul_ediv_cancel_left]

theorem lt_div_iff_of_dvd_of_pos {x y z : ℤ} (h1 :0 < z) (h2 : z ∣ y): x < y / z ↔ z * x <  y := by
  rcases h2 with ⟨a,ha⟩
  simp only [ha,ne_eq, _root_.ne_of_gt,gt_iff_lt, h1, mul_lt_mul_left, ne_eq, not_false_eq_true,
      Int.mul_ediv_cancel_left]

lemma div_le_div_iff_of_dvd_of_pos {x y z t : ℤ} (h1 : 0 < y) (h2 : 0 < t) (h3 : y ∣ x)
    (h4 : t ∣ z) : x / y ≤  z / t ↔ t * x ≤ z * y := by
  cases' h3 with a ha
  cases' h4 with b hb
  rw [ha,hb]
  rw [mul_ediv_cancel_left,mul_ediv_cancel_left,mul_assoc,mul_comm b y]
  · simp only [gt_iff_lt, h2, _root_.mul_le_mul_left, h1]
  · exact Int.ne_of_gt h2
  · exact Int.ne_of_gt h1

lemma div_lt_div_iff_of_dvd_of_pos {x y z t : ℤ} (h1 : 0 < y) (h2 : 0 < t) (h3 : y ∣ x)
    (h4 : t ∣ z) : x / y <  z / t ↔ t * x < z * y := by
  cases' h3 with a ha
  cases' h4 with b hb
  rw [ha,hb]
  rw [mul_ediv_cancel_left,mul_ediv_cancel_left,mul_assoc,mul_comm b y]
  · simp only [gt_iff_lt, h2, _root_.mul_lt_mul_left, h1]
  · exact Int.ne_of_gt h2
  · exact Int.ne_of_gt h1

end Int
