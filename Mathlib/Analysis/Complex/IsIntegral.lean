import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integral elements of ℂ

This file proves that `Complex.I` is integral over ℤ and ℚ.
-/

public section

open Polynomial

namespace Complex

theorem isIntegral_int_I : IsIntegral ℤ I := by
  refine ⟨X ^ 2 + C 1, monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_C, I_sq, eq_intCast, Int.cast_one, neg_add_cancel]

theorem isIntegral_rat_I : IsIntegral ℚ I :=
  isIntegral_int_I.tower_top

end Complex
