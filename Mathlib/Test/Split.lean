import Mathlib.Tactic.Basic
import Mathlib.Tactic.Split

example : (α : Type) × List α := by
  split
  - exact [0,1]

-- example : (α : Type) × List α := by
--   fsplit
--   - exact ℕ
--   - exact [0,1]
