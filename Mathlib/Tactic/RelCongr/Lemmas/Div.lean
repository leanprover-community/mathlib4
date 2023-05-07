import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.LibrarySearch

/-! # ≤, tt / tt -/

#check div_le_div'' -- for CommGroup ..
-- (hab : a ≤ b) (hcd : c ≤ d) : a / d ≤ b / c

#check div_le_div -- for LinearOrderedSemifield
-- (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d

theorem Nat.div_le_div (a b c d : ℕ) (h1 : a ≤ b) (h2 : d ≤ c) (h3 : d ≠ 0) : a / c ≤ b / d :=
  calc a / c ≤ b / c := Nat.div_le_div_right h1
    _ ≤ b / d := Nat.div_le_div_left h2 (Nat.pos_of_ne_zero h3)

-- something for `Int`?

#check ENNReal.div_le_div
-- (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d

/-! # ≤, ff / tt -/

#check div_le_div_left' -- for Group ...
-- (h : a ≤ b) (c : α) : c / b ≤ c / a

#check div_le_div_of_le_left -- for LinearOrderedSemifield
-- (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c

#check Nat.div_le_div_left
-- (h₁ : c ≤ b) (h₂ : 0 < c) : a / b ≤ a / c

-- something for `Int`?

#check ENNReal.div_le_div_left
-- (h : a ≤ b) (c : ENNReal) : c / b ≤ c / a

-- **don't include these, they are subsumed by others**

-- `LinearOrderedSemifield` has weaker hypotheses than this, when they both apply
theorem div_le_div_left₀' [LinearOrderedCommGroupWithZero α]
    {a b c : α} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hcb : c ≤ b) :
    a / b ≤ a / c :=
  (div_le_div_left₀ ha hb hc).mpr hcb

-- more user-friendly conditions than for LinearOrderedSemifield, but equivalent
#check NNReal.div_le_div_left_of_le
-- (c0 : c ≠ 0) (cb : c ≤ b) : a / b ≤ a / c


/-! # ≤, tt / ff -/

#check div_le_div_right' -- for Group ...
-- (h : a ≤ b) (c : α) : a / c ≤ b / c

#check div_le_div_of_le -- for LinearOrderedSemifield
--  (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c

#check Nat.div_le_div_right
-- (h : n ≤ m) {k : ℕ} : n / k ≤ m / k

-- something for `Int`?

#check ENNReal.div_le_div_right
-- (h : a ≤ b) (c : ENNReal) : a / c ≤ b / c

-- **don't include, a duplicate**

#check div_le_div_of_le_of_nonneg -- for LinearOrderedSemifield
-- (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c


/-! # <, tt / tt -/

#check div_lt_div'' -- for CommGroup ...
-- (hac : a < c) (hbd : b < d) : a / b < c / d

#check div_lt_div -- for LinearOrderedSemifield
-- (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) : a / b < c / d

-- **don't include this, overlaps**

#check div_lt_div' -- for LinearOrderedSemifield
-- (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) : a / b < c / d



/-! # <, ff / tt -/

#check div_lt_div_left' -- for "covariant class ...."
-- (h : a < b) : c / b < c / a

#check div_lt_div_of_lt_left -- for LinearOrderedSemifield
--  (hc : 0 < c) (hb : 0 < b) (h : b < a) : c / a < c / b

/-! # <, tt / ff -/

#check div_lt_div_right' -- for "covariant class ...."
-- (bc : b < c) : b / a < c / a

#check div_lt_div_of_lt -- for LinearOrderedSemifield
--  (hc : 0 < c) (h : a < b) : a / c < b / c
