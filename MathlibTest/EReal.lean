module

import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

example : (0 : EReal) + ⊤ = ⊤ := by simp

example : (1 : EReal) + ⊤ = ⊤ := by simp

example : (2 : EReal) + ⊤ = ⊤ := by simp

example : (3 : EReal) + ⊤ = ⊤ := by simp

example : ⊤ + (0 : EReal) = ⊤ := by simp

example : ⊤ + (1 : EReal) = ⊤ := by simp

example : ⊤ + (2 : EReal) = ⊤ := by simp

example : ⊤ + (3 : EReal) = ⊤ := by simp
