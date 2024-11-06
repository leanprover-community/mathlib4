/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Results about powers in fields or division rings.

This file exists to ensure we can define `Field` with minimal imports,
so contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/


variable {α : Type*}

/-- a⁻¹ * d ^ s * a = (a⁻¹ * d * a) ^ s when a is not zero -/
lemma DivisionSemiring.conj_pow [DivisionSemiring α] {s : ℕ} {a d : α} (ha : a ≠ 0) :
    a⁻¹ * d ^ s * a = (a⁻¹ * d * a) ^ s := by
  let u : αˣ := ⟨a, a⁻¹, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha⟩
  exact (Units.conj_pow' u d s).symm

section DivisionRing

variable [DivisionRing α] {n : ℤ}

theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  have hn : n ≠ 0 := by rintro rfl; exact Int.not_even_iff_odd.2 h even_zero
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add' (.inr (.inl hn)), zpow_one, zpow_mul, zpow_two, neg_mul_neg,
    neg_mul_eq_mul_neg]

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end DivisionRing
