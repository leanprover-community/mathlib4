/-
Copyright (c) 2019 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Rat.Floor
import Mathlib.Data.NNRat.Lemmas

/-!
# Floor Function for Non-negative Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ≥0`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

nnrat, rationals, ℚ≥0, floor
-/

namespace NNRat

instance : FloorSemiring ℚ≥0 where
  floor q := ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := by simpa using h.trans zero_lt_one
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

theorem floor_coe (q : ℚ≥0) : ⌊(q : ℚ)⌋₊ = ⌊q⌋₊ := rfl

theorem ceil_coe (q : ℚ≥0) : ⌈(q : ℚ)⌉₊ = ⌈q⌉₊ := rfl

@[simp, norm_cast]
theorem coe_floor (q : ℚ≥0) : ↑⌊q⌋₊ = ⌊(q : ℚ)⌋ := Int.ofNat_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]
theorem coe_ceil (q : ℚ≥0) : ↑⌈q⌉₊ = ⌈(q : ℚ)⌉ := Int.ofNat_ceil_eq_ceil q.coe_nonneg

protected theorem floor_def (q : ℚ≥0) : ⌊q⌋₊ = q.num / q.den := by
  rw [← Int.natCast_inj, NNRat.coe_floor, Rat.floor_def, Int.ofNat_ediv, den_coe, num_coe]

@[simp, norm_cast]
theorem floor_cast (x : ℚ≥0) : ⌊(x : K)⌋₊ = ⌊x⌋₊ := by
  have := (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊)
  refine (Nat.floor_eq_iff x.cast_nonneg).2 ?_
  rw [← NNRat.cast_lt (K := K)] at this
  rw [← NNRat.cast_natCast, NNRat.cast_le] at this ⊢
  convert this
#align rat.floor_cast Rat.floor_cast

@[simp, norm_cast]
theorem ceil_cast (x : ℚ≥0) : ⌈(x : K)⌉₊ = ⌈x⌉₊ := by
  rw [Nat.ceil_eq_iff]
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]
#align rat.ceil_cast Rat.ceil_cast

end NNRat
