import Mathlib

-- This version was failing with a kernel type mismatch, prior to nightly-2025-11-20:

macro "triangle_ineq" : tactic => `(tactic| (
  simp only [abs, max_def]
  split_ifs <;> grind
))

example {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c d : α) : |a - b| ≤ |a - c| + |c - d| + |b - d| := by
  triangle_ineq

-- This version was failing prior to nightly-2025-11-21:

macro "triangle_ineq2" : tactic => `(tactic| (
  simp only [abs, max_def]
  grind
))

example {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c d : α) : |a - b| ≤ |a - c| + |c - d| + |b - d| := by
  triangle_ineq2
