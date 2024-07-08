/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Int
-- import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.FractionRing
-- import Mathlib.Algebra.Field.Equiv

#align_import ring_theory.localization.fraction_ring from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# `ℚ` `IsFractionRing` of `ℤ`

-/

/-- The cast from `Int` to `Rat` as a `FractionRing`. -/
instance Rat.isFractionRing : IsFractionRing ℤ ℚ where
  map_units' := by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    simpa only [eq_intCast, isUnit_iff_ne_zero, Int.cast_eq_zero, Ne, Subtype.coe_mk] using hx
  surj' := by
    rintro ⟨n, d, hd, h⟩
    refine ⟨⟨n, ⟨d, ?_⟩⟩, Rat.mul_den_eq_num _⟩
    rw [mem_nonZeroDivisors_iff_ne_zero, Int.natCast_ne_zero_iff_pos]
    exact Nat.zero_lt_of_ne_zero hd
  exists_of_eq {x y} := by
    rw [eq_intCast, eq_intCast, Int.cast_inj]
    rintro rfl
    use 1
#align rat.is_fraction_ring Rat.isFractionRing

