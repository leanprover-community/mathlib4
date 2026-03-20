import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Rify
import Mathlib.Data.NNReal.Basic

set_option linter.unusedVariables false

example {n : ℕ} {k : ℤ} (hn : 8 ≤ n) (hk : 2 * k ≤ n + 2) :
    (0 : ℝ) < n - k - 1 := by
  rify at hn hk
  linarith

example {n : ℕ} {k : ℤ} (hn : 8 ≤ n) (hk : (2 : ℚ) * k ≤ n + 2) :
    (0 : ℝ) < n - k - 1 := by
  rify at hn hk
  linarith

example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : a < b + c := by
  rify [hab] at h ⊢
  linarith

example {n : ℕ} (h : 8 ≤ n) : (0 : ℝ) < n - 1 := by
  rify at h
  linarith

example {n k : ℕ} (h : 2 * k ≤ n + 2) (h' : 8 ≤ n) : (0 : ℝ) ≤ 3 * n - 4 - 4 * k := by
  rify at *
  linarith

example {n k : ℕ} (h₁ : 8 ≤ n) (h₂ : 2 * k > n) (h₃ : k + 1 < n) :
    n - (k + 1) + 3 ≤ n := by
  rify [h₃] at *
  linarith

example {n k : ℕ} (h₁ : 8 ≤ n) (h₂ : 2 * k > n) (h₃ : k + 1 < n) :
    n - (n - (k + 1)) = k + 1 := by
  have f₁ : k + 1 ≤ n := by linarith
  have f₂ : n - (k + 1) ≤ n := by rify [f₁]; linarith
  rify [f₁, f₂] at *
  linarith

/- ℝ≥0 Tests -/

open NNReal

example {a : ℝ≥0} {b : ℝ} (ha : 8 ≤ a) (hb : 2 * b ≤ a + 2) :
    (0 : ℝ) < a - b - 1 := by
  rify at ha hb
  linarith

example {a : ℝ≥0} {b : ℝ} (ha : 8 ≤ a) (hb : (2 : ℚ) * b ≤ b + 2) :
    (0 : ℝ) < a - b - 1 := by
  rify at ha hb
  linarith

example (a b c : ℝ≥0) (h : a - b < c) (hab : b ≤ a) : a < b + c := by
  rify [hab] at h ⊢
  linarith

example {a : ℝ≥0} (h : 8 ≤ a) : (0 : ℝ) < a - 1 := by
  rify at h
  linarith

example {a b : ℝ≥0} (h : 2 * b ≤ a + 2) (h' : 8 ≤ a) : (0 : ℝ) ≤ 3 * a - 4 - 4 * b := by
  rify at *
  linarith

example {a b : ℝ≥0} (h₁ : 8 ≤ a) (h₂ : 2 * b > a) (h₃ : b + 1 < a) :
    a - (b + 1) + 3 ≤ a := by
  rify [h₃] at *
  linarith
