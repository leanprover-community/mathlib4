/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Dyadic.Basic

import Mathlib.Algebra.Order.Field.Basic

/-!
# Archimedean instance for dyadic rationals

This file proves `Dyadic` is a dense order and an Archimedean ring.
-/

namespace Dyadic

instance : DenselyOrdered Dyadic where
  dense x y h := by
    use (x + y) >>> 1
    simp_rw [← toRat_lt_toRat_iff] at *
    constructor
    · rw [toRat_shift]
      simpa [inv_mul_eq_div] using left_lt_add_div_two.2 h
    · simpa [inv_mul_eq_div] using add_div_two_lt_right.2 h

instance : Archimedean Dyadic where
  arch x y h := by
    rw [← toRat_lt_toRat_iff, toRat_zero] at h
    obtain ⟨n, hn⟩ := exists_lt_nsmul h x.toRat
    refine ⟨n, ?_⟩
    rw [← toRat_le_toRat_iff, nsmul_eq_mul, toRat_mul, toRat_natCast, ← nsmul_eq_mul]
    exact hn.le

end Dyadic
