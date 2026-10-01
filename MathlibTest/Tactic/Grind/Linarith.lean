import Mathlib

example {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c d : α) : |a - b| ≤ |a - c| + |c - d| + |b - d| := by
  grind

example (L : ℝ) : 0 < 1 + |L| := by
  grind
