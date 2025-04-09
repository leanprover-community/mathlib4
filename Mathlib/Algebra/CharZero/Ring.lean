/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Basic facts about rings of characteristic zero.
-/

instance (α : Type*) [∀ n, OfNat α n] [CommRing α] [LawfulOfNat α] [CharZero α] :
    Lean.Grind.IsCharP α 0 where
  ofNat_eq_zero_iff n := by simp [LawfulOfNat.ofNat_eq_natCast]
