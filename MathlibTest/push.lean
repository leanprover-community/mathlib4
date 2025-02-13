import Mathlib.Analysis.SpecialFunctions.Log.Basic

example (a b c : Real) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.log (a ^ 4 * b * (c / c) / a * Real.exp b) =
      4 * Real.log a + Real.log b + 0 - Real.log a + b := by
  push (disch := positivity) Real.log
  rfl
