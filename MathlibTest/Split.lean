import Mathlib.Tactic.Basic

example : (α : Type) × List α := by
  constructor
  · exact [0,1]

-- example : (α : Type) × List α := by
--   fsplit
--   - exact ℕ
--   - exact [0,1]
