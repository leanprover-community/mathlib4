/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity

/-!
# Results about powers in fields or division rings.

This file exists to ensure we can define `Field` with minimal imports,
so it contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/

public section

variable {α : Type*}

section DivisionMonoid

variable [DivisionMonoid α] [HasDistribNeg α] {n : ℤ}

theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp h
  cases k with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast]
    norm_cast
    simp [pow_add]
  | negSucc k =>
    simp_rw [Int.negSucc_eq, show 2 * -(↑k + 1) + (1 : ℤ) = - (1 + k*2) by grind,  _root_.zpow_neg]
    norm_cast
    simp [pow_add]

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end DivisionMonoid
