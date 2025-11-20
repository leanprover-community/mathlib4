import Mathlib

-- This version was failing with a kernel type mismatch, prior to nightly-2025-11-20:

macro "triangle_ineq" : tactic => `(tactic| (
  simp only [abs, max_def]
  split_ifs <;> grind
))

example {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c d : α) : |a - b| ≤ |a - c| + |c - d| + |b - d| := by
  triangle_ineq

-- TODO (@kim-em): have `grind` take over more of the work here.
-- As of `nightly-2025-11-20`, there is a grind bug preventing us removing the `split_ifs`:
/-
macro "triangle_ineq2" : tactic => `(tactic| (
  simp only [abs, max_def]
  grind
))

example {α : Type*} [LinearOrder α] [CommRing α] [IsStrictOrderedRing α]
    (a b c d : α) : |a - b| ≤ |a - c| + |c - d| + |b - d| := by
  triangle_ineq2

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.IntModule α] [DecidableLE α] [Lean.Grind.OrderedAdd α]
    (a b c d : α)
    (h : ¬(-(a - b)) ≤ ((-(a - c)) + -(c - d)) + if b - d ≤ -(b - d) then -(b - d) else b - d)
    (h_1 : b - d ≤ -(b - d)) : False := by
  grind -- fails
-/
