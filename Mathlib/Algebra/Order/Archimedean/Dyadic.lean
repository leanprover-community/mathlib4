/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Dyadic.Basic

/-!
# Archimedean instance for dyadic rationals

This file proves `Dyadic` is a dense order and an Archimedean ring.
-/

namespace Dyadic

instance : DenselyOrdered Dyadic where
  dense x y h := by
    refine ⟨(x + y) >>> 1, ?_, ?_⟩ <;>
    · rw [← toRat_lt_toRat_iff] at *
      rw [toRat_shiftRight_nat, Rat.pow_one, toRat_add]
      grind

instance : Archimedean Dyadic where
  arch x y h := by
    rw [← toRat_lt_toRat_iff, toRat_zero] at h
    obtain ⟨n, hn⟩ := exists_lt_nsmul h x.toRat
    refine ⟨n, ?_⟩
    rw [← toRat_le_toRat_iff, nsmul_eq_mul, toRat_mul, toRat_natCast, ← nsmul_eq_mul]
    exact hn.le

end Dyadic
