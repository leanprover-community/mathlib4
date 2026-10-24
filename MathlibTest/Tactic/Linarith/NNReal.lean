module
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Tactic.Linarith.NNRealPreprocessor

open NNReal

example {a b c : ℝ≥0} (h1 : 2 * a < b + 1) (h2 : b ≤ c) : a < (c + 1) / 2 := by
  linarith

example {a b c d : ℝ≥0} (h1 : 3 * a + 2 * b ≤ 5 * c + 7) (h2 : c ≤ d) : a ≤ (5 * d + 7) / 3 := by
  linarith

example {a b c d e : ℝ≥0} (h1 : (a + b) / 2 + c ≤ d) (h2 : d ≤ e) : a ≤ 2 * e := by
  linarith

example {a b c d : ℝ≥0} (h1 : (a + 3 * b) / 4 < c + 1) (h2 : c ≤ d) : a < 4 * (d + 1) := by
  linarith

example {a b c d : ℝ≥0} (h1 : 2 * a + b ≤ 3 * c) (h2 : c < d + 5) : a < (3 * (d + 5)) / 2 := by
  linarith

example {a b c d : ℝ≥0} (h1 : a + b ≤ c) (h2 : c ≤ d / 2) : a ≤ d / 2 := by
  linarith

example {a b c d : ℝ≥0} (h1 : a + b ≤ 2 * c + 3) (h2 : c ≤ d) : a ≤ 2 * d + 3 := by
  linarith

-- `linarith?` attributes facts lifted to `ℝ` back to the `ℝ≥0` hypotheses they came from
/--
info: Try this:
  [apply] linarith only [h]
-/
#guard_msgs in
set_option linter.unusedVariables false in
example {a b : ℝ≥0} (h : a < b) (junk : b < b + 1) : a ≤ b := by
  linarith?

-- the certificate uses the nonnegativity fact `0 ≤ (b : ℝ)`, which is tagged with every
-- hypothesis `b` appears in; minimization then drops `junk`
/--
info: Try this:
  [apply] linarith only [h]
-/
#guard_msgs in
set_option linter.unusedVariables false in
example {a b : ℝ≥0} (h : a + b ≤ 0) (junk : b < b + 1) : a ≤ 0 := by
  linarith?
