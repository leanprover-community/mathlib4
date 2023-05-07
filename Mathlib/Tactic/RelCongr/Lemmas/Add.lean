import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.LibrarySearch

/-! # ≤, tt + tt -/

#check add_le_add -- for "covariant class ....." (this covers `ℝ≥0∞`)
-- (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d

/-! # ≤, ff + tt -/

#check add_le_add_left -- for "covariant class ....." (this covers `ℝ≥0∞`)
-- (bc : b ≤ c) (a : α) : a + b ≤ a + c

/-! # ≤, tt + ff -/

#check add_le_add_right -- for "covariant class ....." (this covers `ℝ≥0∞`)
--  (bc : b ≤ c) (a : α) : b + a ≤ c + a

/-! # <, tt + tt -/

#check add_lt_add -- for "covariant class ...."
--  (h₁ : a < b) (h₂ : c < d) : a + c < b + d

#check ENNReal.add_lt_add
-- (ac : a < c) (bd : b < d) : a + b < c + d

/-! # <, ff + tt -/

#check add_lt_add_left -- for "covariant class ...."
-- (bc : b < c) (a : α) : a + b < a + c

#check ENNReal.add_lt_add_left
-- (a✝ : a ≠ ⊤) (a✝¹ : b < c) : a + b < a + c


/-! # <, tt + ff -/

#check add_lt_add_right -- for "covariant class ...."
-- (bc : b < c) (a : α) : b + a < c + a

#check ENNReal.add_lt_add_right
-- (a✝ : a ≠ ⊤) (a✝¹ : b < c) : b + a < c + a
