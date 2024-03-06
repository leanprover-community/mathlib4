/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Mathlib.Tactic.Bound

/-!
## Tests for the `bound` tactic
-/

open Complex (abs)
open scoped NNReal

section positive_tests
variable {n : ℕ}
variable {x y : ℝ}
variable {u : ℝ≥0}
variable {z : ℂ}
lemma test_pos_lt_sq (h : 0 < x) : x^2 > 0 := by bound
lemma test_pos_gt_sq (h : x > 0) : x^2 > 0 := by bound
lemma test_pos_mul (p : x > 0) (q : y > 0) : x * y > 0 := by bound
lemma test_pos_div (p : x > 0) (q : y > 0) : x / y > 0 := by bound
lemma test_pos_4 : 0 < 4 := by bound
lemma test_pos_7 : 0 < 7 := by bound
lemma test_pos_4_real : 0 < (4 : ℝ) := by bound
lemma test_pos_7_real : 0 < (7 : ℝ) := by bound
lemma test_pos_zero_one : 0 < (1 : ℝ) := by bound
lemma test_pos_nnreal (h : u > 0) : 0 < (u : ℝ) := by bound
lemma test_pos_pow : 0 < 2^n := by bound
lemma test_pos_inv : 0 < (1 : ℝ)⁻¹ := by bound
end positive_tests

section nonneg_tests
variable {n : ℕ}
variable {x y : ℝ}
variable {u : ℝ≥0}
variable {z : ℂ}
lemma test_abs : 0 ≤ abs z := by bound
lemma test_abs_ge : abs z ≥ 0 := by bound
lemma test_nn_sq : x^2 ≥ 0 := by bound
lemma test_mul (p : x ≥ 0) (q : y ≥ 0) : x * y ≥ 0 := by bound
lemma test_div (p : x ≥ 0) (q : y ≥ 0) : x / y ≥ 0 := by bound
lemma test_add (p : x ≥ 0) (q : y ≥ 0) : x + y ≥ 0 := by bound
lemma test_nat : (n : ℝ) ≥ 0 := by bound
lemma test_num : 0 ≤ 7 := by bound
lemma test_num_real : 0 ≤ (7 : ℝ) := by bound
lemma test_zero_one : 0 ≤ (1 : ℝ) := by bound
lemma test_nnreal : 0 ≤ (u : ℝ) := by bound
lemma test_zero : 0 ≤ (0 : ℝ) := by bound
lemma test_pow : 0 ≤ 2^n := by bound
lemma test_inv : 0 ≤ (0 : ℝ)⁻¹ := by bound
end nonneg_tests

section bound_tests
variable {a b c x y : ℝ}
variable {z : ℂ}
variable {n : ℕ}
lemma test_sq (n : x ≥ 0) (h : x ≤ y) : x^2 ≤ y^2 := by bound
lemma test_sq_ge (n : x ≥ 0) (h : x ≤ y) : y^2 ≥ x^2 := by bound
lemma test_mul_left (n : a ≥ 0) (h : x ≤ y) : a * x ≤ a * y := by bound
lemma test_mul_right (n : a ≥ 0) (h : x ≤ y) : x * a ≤ y * a := by bound
lemma test_mul_both (bp : b ≥ 0) (xp : x ≥ 0) (ab : a ≤ b) (xy : x ≤ y) : a * x ≤ b * y := by bound
lemma test_abs_mul (h : x ≤ y) : abs z * x ≤ abs z * y := by bound
lemma test_add_left (h : x ≤ y) : a + x ≤ a + y := by bound
lemma test_add_right (h : x ≤ y) : x + a ≤ y + a := by bound
lemma test_add_both (ab : a ≤ b) (xy : x ≤ y) : a + x ≤ b + y := by bound
lemma test_sub_left (h : x ≥ y) : a - x ≤ a - y := by bound
lemma test_sub_right (h : x ≤ y) : x - a ≤ y - a := by bound
lemma test_sub_both (ab : a ≤ b) (xy : x ≥ y) : a - x ≤ b - y := by bound
lemma test_sub_pos (h : x < y) : y - x > 0 := by bound
lemma test_le_of_lt (h : x > 0) : x ≥ 0 := by bound
lemma test_extra (f : ℕ → ℝ) (h : ∀ n, f n ≥ 0) : f n ≥ 0 := by bound [h n]
lemma test_1_4 : (1 : ℝ) < 4 := by bound
lemma test_2_4 : (2 : ℝ) < 4 := by bound
lemma test_div_left (hc : c ≥ 0) (h : a ≤ b) : a / c ≤ b / c := by bound
lemma test_div_right (ha : a ≥ 0) (hc : c > 0) (h : b ≥ c) : a / b ≤ a / c := by bound
lemma test_coe (x y : ℝ≥0) (h : x < y) : (x : ℝ) < y := by bound
lemma test_dist : dist a c ≤ dist a b + dist b c := by bound
lemma test_log (x y : ℝ) (x0 : 0 < x) (h : x ≤ y) : x.log ≤ y.log := by bound
end bound_tests

section guess_tests
variable {a b c : ℝ}
variable {n m : ℕ}
lemma test_le_max_of_le_left (h : a ≤ b) : a ≤ max b c := by bound
lemma test_le_max_of_le_right (h : a ≤ c) : a ≤ max b c := by bound
lemma test_lt_max_of_lt_left (h : a < b) : a < max b c := by bound
lemma test_lt_max_of_lt_right (h : a < c) : a < max b c := by bound
lemma test_min_le_of_left_le (h : a ≤ c) : min a b ≤ c := by bound
lemma test_min_le_of_right_le (h : b ≤ c) : min a b ≤ c := by bound
lemma test_min_lt_of_left_lt (h : a < c) : min a b < c := by bound
lemma test_min_lt_of_right_lt (h : b < c) : min a b < c := by bound
lemma test_pow_le_pow_right (a1 : 1 ≤ a) (h : m ≤ n) : a^m ≤ a^n := by bound
lemma test_pow_le_pow_of_le_one (a0 : 0 ≤ a) (a1 : a ≤ 1) (h : n ≤ m) : a^m ≤ a^n := by bound
lemma test_rpow_le_rpow_of_exponent_le (a1 : 1 ≤ a) (h : b ≤ c) : a^b ≤ a^c := by bound
lemma test_rpow_le_rpow_of_exponent_ge (a0 : 0 < a) (a1 : a ≤ 1) (h : c ≤ b) : a^b ≤ a^c := by bound
end guess_tests

-- This breaks without appropriate g.withContext use
lemma test_with_context {s : Set ℂ} (o : IsOpen s) (z) (h : z ∈ s) : ∃ r : ℝ, r > 0 := by
  rw [Metric.isOpen_iff] at o
  rcases o z h with ⟨t, tp, bs⟩
  exists t/2
  clear o h bs z s
  bound

-- Test various elaboration issues
lemma test_try_elab {f : ℂ → ℂ} {z w : ℂ} {s r c e : ℝ}
      (sc : ∀ {w}, abs (w - z) < s → abs (f w - f z) < e) (wz : abs (w - z) < s) (wr : abs w < r)
      (h : ∀ z : ℂ, abs z < r → abs (f z) ≤ c * abs z) :
      abs (f z) ≤ c * abs w + e := by
  calc abs (f z) = abs (f w - (f w - f z)) := by ring_nf
    _ ≤ abs (f w) + abs (f w - f z) := by bound
    _ ≤ c * abs w + e := by bound [h w wr, sc wz]

-- Test a lemma that requires function inference
lemma test_fun_inference {α : Type} {s : Finset α} {f g : α → ℂ} :
    ‖s.sum (fun x ↦ f x + g x)‖ ≤ s.sum (fun x ↦ ‖f x + g x‖) := by
  bound

-- A test that requires reduction to weak head normal form to work (surfaced by `Hartogs.lean`)
lemma test_whnf (x y : ℝ) (h : x < y ∧ True) : x ≤ y := by
  bound [h.1]

-- Used to fail with `unknown identifier n`, since I wasn't elaborating [] inside the goal
theorem test_unknown_identifier {f : ℕ → ℝ} (le : ∀ n, f n ≤ n) : ∀ n : ℕ, f n ≤ n := by
  intro n; bound [le n]

-- Calc example: A weak lower bound for `z ← z^2 + c`
lemma le_sqr_add {c z : ℂ} (cz : Complex.abs c ≤ Complex.abs z) (z3 : 3 ≤ Complex.abs z) :
    2 * Complex.abs z ≤ Complex.abs (z^2 + c) := by
  calc Complex.abs (z^2 + c)
    _ ≥ Complex.abs (z^2) - Complex.abs c := by bound
    _ ≥ Complex.abs (z^2) - Complex.abs z := by bound
    _ ≥ (Complex.abs z - 1) * Complex.abs z := by
      rw [mul_comm, mul_sub_one, ← pow_two, ← Complex.abs.map_pow]
    _ ≥ 2 * Complex.abs z := by bound
