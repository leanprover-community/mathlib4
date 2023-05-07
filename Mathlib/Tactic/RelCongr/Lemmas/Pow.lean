import Mathlib.Data.Real.ENNReal
import Mathlib.Tactic.LibrarySearch

/-! # ≤, ff ^ tt -/

#check pow_le_pow -- OrderedSemiring
-- (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m

#check pow_le_pow' -- covariant ... (covers `ℝ≥0∞`)
-- (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m

#check zpow_le_zpow -- OrderedCommGroup (no obvious instances!)
-- (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n

#check zpow_le_of_le -- LinearOrderedSemifield
-- (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n

#check ENNReal.zpow_le_of_le
-- (hx : 1 ≤ x) (h : a ≤ b) : x ^ a ≤ x ^ b

/-! # ≤, tt ^ ff -/

#check pow_le_pow_of_le_left -- OrderedSemiring
-- (ha : 0 ≤ a) (hab : a ≤ b) (i : ℕ) : a ^ i ≤ b ^ i

#check pow_le_pow_of_le_left' -- covariant ... (covers `ℝ≥0∞`)
-- (hab : a ≤ b) : a ^ i ≤ b ^ i

#check zpow_le_zpow' -- OrderedCommGroup (no obvious instances!)
-- (hn : 0 ≤ n) (h : a ≤ b) : a ^ n ≤ b ^ n

/-! # <, ff ^ tt -/

#check pow_lt_pow -- StrictOrderedSemiring
--  (h : 1 < a) (h2 : n < m) : a ^ n < a ^ m

#check pow_lt_pow' -- covariant ... (no obvious instances!)
-- (ha : 1 < a) (h : n < m) : a ^ n < a ^ m

#check zpow_lt_zpow -- OrderedCommGroup (no obvious instances!)
-- (ha : 1 < a) (h : m < n) : a ^ m < a ^ n

theorem zpow_lt_of_lt [LinearOrderedSemifield α] {a : α} {m n : ℤ} (hx : 1 < a) (h : m < n) :
    a ^ m < a ^ n :=
  zpow_strictMono hx h

#check zpow_lt_of_lt -- LinearOrderedSemifield
-- (hx : 1 < a) (h : m < n) : a ^ m < a ^ n

/- **duplicates** -/

#check pow_strictMono_left -- covariant ...
-- (ha : 1 < a) : StrictMono (fun x => a ^ x)

#check pow_lt_pow₀ -- LinearOrderedCommGroupWithZero (no obvious instances except `ℝ≥0`)
-- (ha : 1 < a) (hmn : m < n) : a ^ m < a ^ n

/-! # <, tt ^ ff -/

#check pow_lt_pow_of_lt_left -- StrictOrderedSemiring
-- (h : x < y) (hx : 0 ≤ x) (a✝ : 0 < n) : x ^ n < y ^ n

theorem ENNReal.pow_lt_pow_of_lt_left {x y : ENNReal} (h : x < y) {n : ℕ} (hn : n ≠ 0) :
    x ^ n < y ^ n :=
  ENNReal.pow_strictMono hn h

#check ENNReal.pow_lt_pow_of_lt_left
-- (h : x < y)(hn : n ≠ 0) : x ^ n < y ^ n

#check zpow_lt_zpow' -- OrderedCommGroup (no obvious instances!)
-- (hn : 0 < n) (h : a < b) : a ^ n < b ^ n
