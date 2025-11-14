/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Regular

/-!
# Torsion-free rings

A characteristic zero domain is torsion-free.
-/

namespace IsDomain

-- This instance is potentially expensive, and is known to slow down grind.
-- Please keep it as a scoped instance.
scoped instance (R : Type*) [Semiring R] [IsDomain R] [CharZero R] :
    IsAddTorsionFree R where
  nsmul_right_injective n h a b w := by
    simp only [nsmul_eq_mul, mul_eq_mul_left_iff, Nat.cast_eq_zero] at w
    grind

end IsDomain
