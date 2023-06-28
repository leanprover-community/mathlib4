import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Rewrites

example : Real.sin x = 1 ↔ ∃ k : ℤ, x = 2 * Real.pi * k + Real.pi / 2 := by
  rw?
