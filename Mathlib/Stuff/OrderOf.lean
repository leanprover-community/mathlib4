import Mathlib.FieldTheory.Finite.Basic

set_option linter.style.header false

lemma orderOf_lt_of {a b n : ℕ} [hn : Fact (b.Prime)] (h : a.Coprime b)
      (H : ∀ i ≤ n, 1 ≤ i → a ^ i % b ≠ 1) :
    n < orderOf (ZMod.unitOfCoprime _ h) := by
  by_contra! Habs
  have := orderOf_pos (ZMod.unitOfCoprime _ h)
  refine H _ Habs (Nat.one_le_iff_ne_zero.mpr (orderOf_pos (ZMod.unitOfCoprime a h)).ne') ?_
  have : Fact (1 < b) := ⟨hn.1.one_lt⟩
  have := pow_orderOf_eq_one (ZMod.unitOfCoprime _ h)
  apply_fun Units.val at this
  simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at this
  simp [← ZMod.val_natCast, Nat.cast_pow, this, ZMod.val_one]
