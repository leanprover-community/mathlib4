module

public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.NormNum.Basic

/-! Temporary probe: are `auto_positivity` entries from `Positivity.Basic` visible in a
downstream module file? -/

-- round-2 form (mul)
example (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by positivity
-- round-1 form (natAbs), cross-module
example (n : ℤ) (hn : n ≠ 0) : 0 < n.natAbs := by positivity
