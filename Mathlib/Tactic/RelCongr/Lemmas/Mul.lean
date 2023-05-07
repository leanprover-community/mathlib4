import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.LibrarySearch

/-! # ≤, tt * tt -/

#check mul_le_mul' -- for "covariant class ....." (this covers `ℝ≥0∞`)
-- (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d

#check mul_le_mul -- for "MulPosMono PosMulMono ..."
-- (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d

/-! # ≤, ff * tt -/

#check mul_le_mul_left' -- for "covariant class ....." (this covers `ℝ≥0∞`)
-- (bc : b ≤ c) (a : α) : a * b ≤ a * c

#check mul_le_mul_of_nonneg_left -- for "PosMulMono ..."
-- (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c

/-! # ≤, tt * ff -/

#check mul_le_mul_right' -- for "covariant class ....." (this covers `ℝ≥0∞`)
--  (bc : b ≤ c) (a : α) : b * a ≤ c * a

#check mul_le_mul_of_nonneg_right -- for "MulPosMono ..."
-- (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a

/-! # <, tt * tt -/

#check mul_lt_mul_of_lt_of_lt -- for "covariant class ...."
-- (hac : a < c) (hbd : b < d) : a * b < c * d

#check mul_lt_mul'' -- for StrictOrderedSemiring
-- (hac : a < c) (hbd : b < d) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b < c * d

#check ENNReal.mul_lt_mul -- for `ℝ≥0∞`
-- (hac : a < c) (hbd : b < d) : a * b < c * d

-- **don't include these, they are asymmetric**

#check mul_lt_mul -- for StrictOrderedSemiring
-- (hac : a < c) (hbd : b ≤ d) (hb : 0 < b) (hc : 0 ≤ c) : a * b < c * d

#check mul_lt_mul_of_nonneg_of_pos -- weird typeclasses
-- (hac : a < c) (hbd : b ≤ d) (ha : 0 ≤ a) (hd : 0 < d) : a * b < c * d

#check mul_lt_mul_of_pos_of_nonneg -- weird typeclasses
-- (hac : a ≤ c) (hbd : b < d) (ha : 0 < a) (hd : 0 ≤ d) : a * b < c * d

#check mul_lt_mul' -- for StrictOrderedSemiring
-- (hac : a ≤ c) (hbd : b < d) (hb : 0 ≤ b) (hc : 0 < c) : a * b < c * d


/-! # <, ff * tt -/

#check mul_lt_mul_left' -- for "covariant class ...."
-- (bc : b < c) (a : α) : a * b < a * c

#check mul_lt_mul_of_pos_left -- PosMulStrictMono
-- (bc : b < c) (a0 : 0 < a) : a * b < a * c

theorem ENNReal.mul_lt_mul_left' {a b c : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_left_strictMono h0 hinf bc

/-! # <, tt * ff -/

#check mul_lt_mul_right' -- for "covariant class ...."
-- (bc : b < c) (a : α) : b * a < c * a

#check mul_lt_mul_of_pos_right -- MulPosStrictMono
-- (bc : b < c) (a0 : 0 < a) : b * a < c * a

theorem ENNReal.mul_lt_mul_right' {a b c : ENNReal} (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_left_strictMono h0 hinf bc
