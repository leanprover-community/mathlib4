/-
Copyright (c) 2024 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Data.Real.Sqrt

/-!
# The reals are a conditionally complete linearly ordered field
-/

/-- The reals are a conditionally complete linearly ordered field. -/
noncomputable instance : ConditionallyCompleteLinearOrderedField ℝ := { }

/-- There exists no nontrivial ring homomorphism `ℝ →+* ℝ`. -/
instance Real.RingHom.unique : Unique (ℝ →+* ℝ) where
  default := RingHom.id ℝ
  uniq f := congr_arg OrderRingHom.toRingHom (@Subsingleton.elim (ℝ →+*o ℝ) _
      ⟨f, ringHom_monotone (fun r hr => ⟨√r, sq_sqrt hr⟩) f⟩ default)
