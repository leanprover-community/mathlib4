/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Ring.Int
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.Ring.Defs

#align_import data.int.order.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# The integers form a linear ordered ring

This file contains:
* instances on `ℤ`. The stronger one is `Int.linearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

open Function Nat

namespace Int

instance linearOrderedCommRing : LinearOrderedCommRing ℤ :=
  { instCommRingInt, instLinearOrderInt, instNontrivialInt with
    add_le_add_left := @Int.add_le_add_left,
    mul_pos := @Int.mul_pos, zero_le_one := le_of_lt Int.zero_lt_one }

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance orderedCommRing : OrderedCommRing ℤ :=
  StrictOrderedCommRing.toOrderedCommRing'

instance orderedRing : OrderedRing ℤ :=
  StrictOrderedRing.toOrderedRing'

/-! ### Miscellaneous lemmas -/

lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : ℤ) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs, Int.cast_natCast]
#align nat.cast_nat_abs Nat.cast_natAbs

lemma sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  have : (1 : ℤ) ≠ -1 := by decide
  rintro ((_ | m) | m) ((_ | n) | n) <;> simp [this, this.symm, Int.negSucc_add_negSucc]
  rw [Int.sign_eq_one_iff_pos]
  apply Int.add_pos <;> · exact zero_lt_one.trans_le (le_add_of_nonneg_left <| natCast_nonneg _)
#align int.sign_add_eq_of_sign_eq Int.sign_add_eq_of_sign_eq

/-- Note this holds in marginally more generality than `Int.cast_mul` -/
lemma cast_mul_eq_zsmul_cast {α : Type*} [AddCommGroupWithOne α] :
    ∀ m n : ℤ, ↑(m * n) = m • (n : α) :=
  fun m ↦ Int.induction_on m (by simp) (fun _ ih ↦ by simp [add_mul, add_zsmul, ih]) fun _ ih ↦ by
    simp only [sub_mul, one_mul, cast_sub, ih, sub_zsmul, one_zsmul, ← sub_eq_add_neg, forall_const]
#align int.cast_mul_eq_zsmul_cast Int.cast_mul_eq_zsmul_cast

/-! #### properties of `/` and `%` -/

lemma emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
  have h : n % 2 < 2 := abs_of_nonneg (show 0 ≤ (2 : ℤ) by decide) ▸ Int.emod_lt _ (by decide)
  have h₁ : 0 ≤ n % 2 := Int.emod_nonneg _ (by decide)
  match n % 2, h, h₁ with
  | (0 : ℕ), _ ,_ => Or.inl rfl
  | (1 : ℕ), _ ,_ => Or.inr rfl
  -- Porting note: this used to be `=> absurd h (by decide)`
  -- see https://github.com/leanprover-community/mathlib4/issues/994
  | (k + 2 : ℕ), h₁, _ => False.elim (h₁.not_le (by
    rw [Nat.cast_add]
    exact (le_add_iff_nonneg_left 2).2 (NonNeg.mk k)))
  -- Porting note: this used to be `=> absurd h₁ (by decide)`
  | -[a+1], _, h₁ => by cases h₁
#align int.mod_two_eq_zero_or_one Int.emod_two_eq_zero_or_one

/-! #### dvd -/

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) {n : ℤ} (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := by
  constructor
  · rintro ⟨k, h1k, h2k⟩ ⟨l, rfl⟩
    rw [mul_lt_mul_left hn] at h1k h2k
    rw [lt_add_one_iff, ← not_lt] at h2k
    exact h2k h1k
  · intro h
    rw [dvd_iff_emod_eq_zero, ← Ne] at h
    have := (emod_nonneg m hn.ne.symm).lt_of_ne h.symm
    rw [← emod_add_ediv m n]
    refine' ⟨m / n, lt_add_of_pos_left _ this, _⟩
    rw [add_comm _ (1 : ℤ), left_distrib, mul_one]
    exact add_lt_add_right (emod_lt_of_pos _ hn) _
#align int.exists_lt_and_lt_iff_not_dvd Int.exists_lt_and_lt_iff_not_dvd

end Int

section bit0_bit1
variable {R}
set_option linter.deprecated false

-- The next four lemmas allow us to replace multiplication by a numeral with a `zsmul` expression.

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] (n r : R)

lemma bit0_mul : bit0 n * r = (2 : ℤ) • (n * r) := by
  rw [bit0, add_mul, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align bit0_mul bit0_mul

lemma mul_bit0 : r * bit0 n = (2 : ℤ) • (r * n) := by
  rw [bit0, mul_add, ← one_add_one_eq_two, add_zsmul, one_zsmul]
#align mul_bit0 mul_bit0

end NonUnitalNonAssocRing

section NonAssocRing
variable [NonAssocRing R] (n r : R)

lemma bit1_mul : bit1 n * r = (2 : ℤ) • (n * r) + r := by rw [bit1, add_mul, bit0_mul, one_mul]
#align bit1_mul bit1_mul

lemma mul_bit1 {n r : R} : r * bit1 n = (2 : ℤ) • (r * n) + r := by
  rw [bit1, mul_add, mul_bit0, mul_one]
#align mul_bit1 mul_bit1

end NonAssocRing
end bit0_bit1

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.range
