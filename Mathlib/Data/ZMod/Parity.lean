/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.ZMod.Basic

/-!
# Relating parity to natural numbers mod 2

This module provides lemmas relating `ZMod 2` to `Even` and `Odd`.

## Tags

parity, zmod, even, odd
-/


namespace ZMod

theorem eq_zero_iff_even {n : ℕ} : (n : ZMod 2) = 0 ↔ Even n :=
  (CharP.cast_eq_zero_iff (ZMod 2) 2 n).trans even_iff_two_dvd.symm

theorem eq_one_iff_odd {n : ℕ} : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [← @Nat.cast_one (ZMod 2), ZMod.eq_iff_modEq_nat, Nat.odd_iff, Nat.ModEq]

theorem ne_zero_iff_odd {n : ℕ} : (n : ZMod 2) ≠ 0 ↔ Odd n := by
  constructor <;>
    · contrapose
      simp [eq_zero_iff_even]

end ZMod
