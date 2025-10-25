/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Ring.Int.Defs

/-! # `ℤ` is not a field -/

/-- `ℤ` with its usual ring structure is not a field. -/
theorem Int.not_isField : ¬IsField ℤ := fun ⟨_, _, h⟩ ↦ have := @h 2; by grind
