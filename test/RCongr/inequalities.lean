/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.RCongr.Basic
import Mathlib.Tactic.Linarith

/-! ## Inequalities -/

open Nat Finset BigOperators
set_option linter.unusedVariables false
-- set_option trace.aesop true

example {x : ℤ} (hx : x ≥ 12) : x * x ^ 2 ≥ 12 * x ^ 2 := by
  rcongr

example {x y : ℤ} (hx : x ≥ 12) : y + x * x ≥ y + 12 * x := by
  rcongr

example {x : ℤ} (hx : x > 12) : x * x ^ 2 > 12 * x ^ 2 := by
  rcongr

example {x y : ℤ} (hx : x > 12) : y + x * x > y + 12 * x := by
  rcongr

-- not solved by `nlinarith` because of the cube
example {n m : ℤ} (hn : n ≥ 10) : n * n ^ 3 - m ≥ 10 * n ^ 3 - m := by
  rcongr

example {k m n : ℤ} (hn : n ≥ 10) : m + 7 * n * n ^ 2 - k ≥ m + 7 * 10 * n ^ 2 - k := by
  rcongr

example {x y : ℤ} (hx : x ≥ 12) : x ≥ 12 := by
  rcongr

example {x y : ℤ} (hx : x ≥ 12) : y + 8 * x ≥ y + 8 * 12 := by
  rcongr

-- not solved by `nlinarith` because of the cube and the absolute value
example {a b c x  y : ℤ} (hb : b ≥ 4) (hxy : x ≤ y) :
    c + (3 * |a| ^ 3 * b + b * 7 + 14) * x ≤ c + (3 * |a| ^ 3 * b + b * 7 + 14) * y := by
  rcongr

example {x y : ℤ} (hy : 3 ≤ y) (hx : x ≥ 9) : y + 2 * x ≥ 3 + 2 * 9 := by
  rcongr

example {a b : ℤ} (h2 : b ≥ 3) : 2 * b + 5 ≥ 2 * 3 + 5 := by
  rcongr

example {x y : ℝ} (h1 : x ≤ 3) : 4 * x - 3 ≤ 4 * 3 - 3 := by
  rcongr

example {x : ℝ} (h : x < 1) : 3 * x ≤ 3 * 1 := by
  rcongr

example {x y : ℝ} (h1 : x < 3) : 4 * x - 3 < 4 * 3 - 3 := by
  rcongr

example {x : ℝ} (h : x < 1) : 3 * x < 3 * 1 := by
  rcongr

example {x y : ℝ} (h1 : 1 ≤ y) (h2 : x < 2) : x * y ≤ 2 * y := by
  rcongr

-- for this test to pass, need the check to ensure that leading function application is
-- syntactically (not just definitionally) the same on both sides.
example {a b c : ℚ} (h2 : 2 ≤ a + b) : 2 + c ≤ (a + b) + c := by
  rcongr

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : 4 ≤ b) : (3 + 4) / 2 ≤ (a + b) / 2 := by
  rcongr

-- for this test to pass, need to ensure it's treated as a division, not a multiplication
example {a : ℚ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by
  rcongr

example {a : ℝ} (h1 : 3 ≤ a) : 3 / 2 ≤ a / 2 := by
  rcongr

example {x y : ℝ} (h : 3 ≤ x) (h' : 1 ≤ y) : (3 + 1) / 2 ≤ (x + y) / 2 := by
  rcongr

-- needs `OfScientific ℝ`
example {x y : ℝ} (h : x ≤ 3) : 0.1 * x ≤ 0.1 * 3 := by
  rcongr

example {x y : ℝ} (h : x ≤ 3) : x / 10 ≤ 3 / 10 := by
  rcongr

example {x y : ℝ} (h : x ≤ 3) : 1 / 10 * x ≤ 1 / 10 * 3 := by
  rcongr

-- this tests that the tactic prioritizes applying hypotheses (such as, here, `0 ≤ a ^ 6`) over the
-- greedy application of nonnegativity lemmas
example {a b : ℚ} (h : 0 ≤ a ^ 6) : 0 + b ≤ a ^ 6 + b := by rcongr

-- another priority test
example {k m n : ℤ}  (H : m ^ 2 ≤ n ^ 2) : k + m ^ 2 ≤ k + n ^ 2 := by
  rcongr

example {x y z : ℝ} (h : 2 ≤ z) : z * |x + y| ≤ z * (|x| + |y|) := by
  -- rcongr (add apply safe abs_add)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity) -- `rcongrm _ * ?_`
  apply abs_add

example (A B C : ℝ) : |A + B| + C ≤ |A| + |B| + C := by
  -- rcongr (add apply safe abs_add)
  refine add_le_add_right ?_ _ -- `rcongrm ?_ + _`
  apply abs_add

example (n i : ℕ) (hi : i ∈ range n) : 2 ^ i ≤ 2 ^ n := by
  refine pow_le_pow (by norm_num) (le_of_lt ?_) -- `rcongrm 2 ^ _`
  simpa using hi

example (n' : ℕ) (hn': 6 ≤ n') : 2 ^ ((n' + 1) * (n' + 1)) ≤ 2 ^ (n' * n' + 4 * n') := by
  refine pow_le_pow_of_le_right (by positivity) ?_ -- `rcongrm 2 ^ _`
  linarith

example (F : ℕ → ℕ) (le_sum: ∀ {N : ℕ}, 6 ≤ N → 15 ≤ F N) {n' : ℕ} (hn' : 6 ≤ n') :
    let A := F n' ;
    A ! * (15 + 1) ^ n' ≤ A ! * (A + 1) ^ n' := by
  intro A
  -- `rcongrm A! * (_ + 1) ^ n'`
  refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left (add_le_add_right ?_ _) _) (by positivity)
  exact le_sum hn'

example : ∏ i in range n, (2 ^ n - 2 ^ i : ℤ) ≤ ∏ i in range n, (2 ^ n : ℤ) := by
  refine prod_le_prod (fun i hi => ?_) (fun i _ => ?_) -- `rcongrm ∏ i in range n, _`
  sorry
  sorry
