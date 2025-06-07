import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Int.CharZero
import Mathlib.Tactic.Qify

example (a b : ℕ) : (a : ℚ) ≤ b ↔ a ≤ b := by qify
example (a b : ℕ) : (a : ℚ) < b ↔ a < b := by qify
example (a b : ℕ) : (a : ℚ) = b ↔ a = b := by qify
example (a b : ℕ) : (a : ℚ) ≠ b ↔ a ≠ b := by qify

example (a b : ℤ) : (a : ℚ) ≤ b ↔ a ≤ b := by qify
example (a b : ℤ) : (a : ℚ) < b ↔ a < b := by qify
example (a b : ℤ) : (a : ℚ) = b ↔ a = b := by qify
example (a b : ℤ) : (a : ℚ) ≠ b ↔ a ≠ b := by qify

example (a b : ℚ≥0) : (a : ℚ) ≤ b ↔ a ≤ b := by qify
example (a b : ℚ≥0) : (a : ℚ) < b ↔ a < b := by qify
example (a b : ℚ≥0) : (a : ℚ) = b ↔ a = b := by qify
example (a b : ℚ≥0) : (a : ℚ) ≠ b ↔ a ≠ b := by qify

example (a b c : ℕ) (h : a - b = c) (hab : b ≤ a) : a = c + b := by
  qify [hab] at h ⊢ -- `zify` does the same thing here.
  exact sub_eq_iff_eq_add.1 h

example (a b c : ℚ≥0) (h : a - b = c) (hab : b ≤ a) : a = c + b := by
  qify [hab] at h ⊢
  exact sub_eq_iff_eq_add.1 h

example (a b c : ℤ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b := by
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h

-- Regression test for https://github.com/leanprover-community/mathlib4/issues/7480
example (a b c : ℕ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b := by
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h
