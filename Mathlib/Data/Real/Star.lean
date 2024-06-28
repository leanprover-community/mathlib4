/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic

/-!
# The real numbers are a `*`-ring, with the trivial `*`-structure
-/

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : StarRing ℝ :=
  starRingOfComm

instance : TrivialStar ℝ :=
  ⟨fun _ => rfl⟩
