import Mathlib

example {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c d : α) : |a - b| ≤ |a - c| + |c - d| + |b - d| := by
  grind
