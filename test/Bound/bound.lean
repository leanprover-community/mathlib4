/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Bound

/-!
## Tests for the `bound` tactic
-/

open Complex (abs)
open scoped NNReal

-- Tests that work with `bound`, but not `positivity`, `gcongr`, or `norm_num`
section bound_only
variable {a b c x y : ℝ} {z : ℂ} {n : ℕ}

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, these next three are no longer working.
-/
-- example (h : x < y) : y - x > 0 := by bound
-- example (h : x < y) : Real.exp (y - x) > 1 := by bound
-- example (h : x < y) (y0 : 0 < y) : x / y < 1 := by bound

example (f : ℕ → ℝ) (h : ∀ n, f n ≥ 0) : f n ≥ 0 := by bound [h n]
example (x y : ℝ≥0) (h : x < y) : (x : ℝ) < y := by bound
example : dist a c ≤ dist a b + dist b c := by bound
example {α : Type} {s : Finset α} {f g : α → ℂ} :  -- An example that requires function inference
    ‖s.sum (fun x ↦ f x + g x)‖ ≤ s.sum (fun x ↦ ‖f x + g x‖) := by bound
end bound_only

-- Calc example: A weak lower bound for `z ← z^2 + c`
example {c z : ℂ} (cz : Complex.abs c ≤ Complex.abs z) (z3 : 3 ≤ Complex.abs z) :
    2 * Complex.abs z ≤ Complex.abs (z^2 + c) := by
  calc Complex.abs (z^2 + c)
    _ ≥ Complex.abs (z^2) - Complex.abs c := by bound
    _ ≥ Complex.abs (z^2) - Complex.abs z := by bound  -- gcongr works here, not for the other two
    _ ≥ (Complex.abs z - 1) * Complex.abs z := by
      rw [mul_comm, mul_sub_one, ← pow_two, ← Complex.abs.map_pow]
    _ ≥ 2 * Complex.abs z := by bound

-- Testing branching functionality. None of these tests work with `positivity` or `bound`.
section guess_tests
variable {a b c : ℝ} {n m : ℕ}
example (h : a ≤ b) : a ≤ max b c := by bound
example (h : a ≤ c) : a ≤ max b c := by bound
example (h : a ≤ c) : min a b ≤ c := by bound
example (h : b ≤ c) : min a b ≤ c := by bound

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, these next four are no longer working.
-/
-- example (h : a < b) : a < max b c := by bound
-- example (h : a < c) : a < max b c := by bound
-- example (h : a < c) : min a b < c := by bound
-- example (h : b < c) : min a b < c := by bound

example (a1 : 1 ≤ a) (h : m ≤ n) : a^m ≤ a^n := by bound
example (a0 : 0 ≤ a) (a1 : a ≤ 1) (h : n ≤ m) : a^m ≤ a^n := by bound
example (a1 : 1 ≤ a) (h : b ≤ c) : a^b ≤ a^c := by bound

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, this is not working.
-/
-- example (a0 : 0 < a) (a1 : a ≤ 1) (h : c ≤ b) : a^b ≤ a^c := by bound

end guess_tests

section positive_tests
variable {n : ℕ} {x y : ℝ} {u : ℝ≥0} {z : ℂ}
example (h : 0 < x) : x^2 > 0 := by bound
example (h : x > 0) : x^2 > 0 := by bound

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, this is not working.
-/
-- example (p : x > 0) (q : y > 0) : x * y > 0 := by bound
-- example (p : x > 0) (q : y > 0) : x / y > 0 := by bound

example : 0 < 4 := by bound
example : 0 < 7 := by bound
example : 0 < (4 : ℝ) := by bound
example : 0 < (7 : ℝ) := by bound
example : 0 < (1 : ℝ) := by bound
example (h : u > 0) : 0 < (u : ℝ) := by bound
example : 0 < 2^n := by bound
example : 0 < (1 : ℝ)⁻¹ := by bound
end positive_tests

section nonneg_tests
variable {n : ℕ} {x y : ℝ} {u : ℝ≥0} {z : ℂ}
example : 0 ≤ abs z := by bound
example : abs z ≥ 0 := by bound
example : x^2 ≥ 0 := by bound
example (p : x ≥ 0) (q : y ≥ 0) : x * y ≥ 0 := by bound
example (p : x ≥ 0) (q : y ≥ 0) : x / y ≥ 0 := by bound
example (p : x ≥ 0) (q : y ≥ 0) : x + y ≥ 0 := by bound
example : (n : ℝ) ≥ 0 := by bound
example : 0 ≤ 7 := by bound
example : 0 ≤ (7 : ℝ) := by bound
example : 0 ≤ (1 : ℝ) := by bound
example : 0 ≤ (u : ℝ) := by bound
example : 0 ≤ (0 : ℝ) := by bound
example : 0 ≤ 2^n := by bound
example : 0 ≤ (0 : ℝ)⁻¹ := by bound
end nonneg_tests

section bound_tests
variable {a b c x y : ℝ} {z : ℂ} {n : ℕ}
example : (1 : ℝ) < 4 := by bound
example : (2 : ℝ) < 4 := by bound
example (n : x ≥ 0) (h : x ≤ y) : x^2 ≤ y^2 := by bound
example (n : x ≥ 0) (h : x ≤ y) : y^2 ≥ x^2 := by bound
example (n : a ≥ 0) (h : x ≤ y) : a * x ≤ a * y := by bound
example (n : a ≥ 0) (h : x ≤ y) : x * a ≤ y * a := by bound
example (bp : b ≥ 0) (xp : x ≥ 0) (ab : a ≤ b) (xy : x ≤ y) : a * x ≤ b * y := by bound
example (h : x ≤ y) : abs z * x ≤ abs z * y := by bound
example (h : x ≤ y) : a + x ≤ a + y := by bound
example (h : x ≤ y) : x + a ≤ y + a := by bound
example (ab : a ≤ b) (xy : x ≤ y) : a + x ≤ b + y := by bound
example (h : x ≥ y) : a - x ≤ a - y := by bound
example (h : x ≤ y) : x - a ≤ y - a := by bound
example (ab : a ≤ b) (xy : x ≥ y) : a - x ≤ b - y := by bound
example (h : x > 0) : x ≥ 0 := by bound
example (hc : c ≥ 0) (h : a ≤ b) : a / c ≤ b / c := by bound

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, this is not working.
-/
-- example (ha : a ≥ 0) (hc : c > 0) (h : b ≥ c) : a / b ≤ a / c := by bound
-- example (x y : ℝ) (x0 : 0 < x) (h : x ≤ y) : x.log ≤ y.log := by bound

end bound_tests

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, this is not working.
-/
-- /-- This broke without appropriate `g.withContext` use in an older implementation of `bound`.
-- Leaving the test here just in case. -/
-- example {s : Set ℂ} (o : IsOpen s) (z) (h : z ∈ s) : ∃ r : ℝ, r > 0 := by
--   rw [Metric.isOpen_iff] at o
--   rcases o z h with ⟨t, tp, bs⟩
--   exists t/2
--   clear o h bs z s
--   bound

#adaptation_note
/--
Due to changes in https://github.com/leanprover/lean4/pull/5225 and
https://github.com/leanprover/lean4/pull/5226, this is not working.
-/
-- -- Test various elaboration issues
-- example {f : ℂ → ℂ} {z w : ℂ} {s r c e : ℝ}
--       (sc : ∀ {w}, abs (w - z) < s → abs (f w - f z) < e) (wz : abs (w - z) < s) (wr : abs w < r)
--       (h : ∀ z : ℂ, abs z < r → abs (f z) ≤ c * abs z) :
--       abs (f z) ≤ c * abs w + e := by
--   calc abs (f z) = abs (f w - (f w - f z)) := by ring_nf
--     _ ≤ abs (f w) + abs (f w - f z) := by bound
--     _ ≤ c * abs w + e := by bound [h w wr, sc wz]

-- A test that requires reduction to weak head normal form to work (surfaced by `Hartogs.lean`)
example (x y : ℝ) (h : x < y ∧ True) : x ≤ y := by
  bound [h.1]

-- Used to fail with `unknown identifier n`, since I wasn't elaborating [] inside the goal
theorem test_unknown_identifier {f : ℕ → ℝ} (le : ∀ n, f n ≤ n) : ∀ n : ℕ, f n ≤ n := by
  intro n; bound [le n]
