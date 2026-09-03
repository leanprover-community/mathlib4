import Mathlib.Algebra.Order.Ring.Defs

example {K : Type _} [CommRing K] [PartialOrder K] [IsStrictOrderedRing K]
    (this : 0 ≤ (-1 : K)) : False := by
  grind

example {K : Type _} [CommRing K] [PartialOrder K] [IsStrictOrderedRing K]
    (this : 0 ≤ (-c - 1) + c) : b * b - 4 * 0 * c ≤ 0 := by
  grind
