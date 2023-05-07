import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.LibrarySearch

/-! # ≤, tt - tt -/

#check sub_le_sub -- for AddCommGroup, ...
-- (hab : a ≤ b) (hcd : c ≤ d) : a - d ≤ b - c

/-! # ≤, ff - tt -/

#check sub_le_sub_left -- for AddGroup, ...
-- (h : a ≤ b) : c - b ≤ c - a

/-! # ≤, tt - ff -/

#check sub_le_sub_right -- for AddGroup, ...
-- (bc : b ≤ c) : b - a ≤ c - a

/-! # <, tt - tt -/

#check sub_lt_sub -- for AddCommGroup, ...
-- (hab : a < b) (hcd : c < d) : a - d < b - c

-- **don't include these, they are asymmetric**

example (a b c d : ℝ) (h1 : a ≤ c) (h2 : d < b) : a - b < c - d :=
  calc a - b ≤ c - b := sub_le_sub_right h1 _
    _ < c - d := sub_lt_sub_left h2 _

example (a b c d : ℝ) (h1 : a < c) (h2 : d ≤ b) : a - b < c - d :=
  calc a - b < c - b := sub_lt_sub_right h1 _
    _ ≤ c - d := sub_le_sub_left h2 _

/-! # <, ff - tt -/

#check sub_lt_sub_left -- for AddGroup ...
-- (h : a < b) : c - b < c - a

/-! # <, tt - ff -/

#check sub_lt_sub_right -- for AddGroup ...
-- (h : a < b) : a - c < b - c
