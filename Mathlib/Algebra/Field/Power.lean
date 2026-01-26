import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Defs

/-!
# Results about powers in fields or division rings.

This file exists to ensure we can define `Field` with minimal imports,
so it contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/

public section


variable {α : Type*}

section DivisionRing

variable [DivisionRing α] {n : ℤ}

theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  have hn : n ≠ 0 := by rintro rfl; exact Int.not_even_iff_odd.2 h .zero
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add' (.inr (.inl hn)), zpow_one, zpow_mul, zpow_two, neg_mul_neg,
    neg_mul_eq_mul_neg]

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end DivisionRing
