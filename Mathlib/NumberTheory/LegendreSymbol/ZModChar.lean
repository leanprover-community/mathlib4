/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Int.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Quadratic characters on ℤ/nℤ

This file defines some quadratic characters on the rings ℤ/4ℤ and ℤ/8ℤ.

We set them up to be of type `MulChar (ZMod n) ℤ`, where `n` is `4` or `8`.

## Tags

quadratic character, zmod
-/


/-!
### Quadratic characters mod 4 and 8

We define the primitive quadratic characters `χ₄`on `ZMod 4`
and `χ₈`, `χ₈'` on `ZMod 8`.
-/


namespace ZMod

section QuadCharModP

/-- Define the nontrivial quadratic character on `ZMod 4`, `χ₄`.
It corresponds to the extension `ℚ(√-1)/ℚ`. -/
@[simps]
def χ₄ : MulChar (ZMod 4) ℤ where
  toFun a :=
    match a with
    | 0 | 2 => 0
    | 1 => 1
    | 3 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- `χ₄` takes values in `{0, 1, -1}` -/
theorem isQuadratic_χ₄ : χ₄.IsQuadratic := by
  unfold MulChar.IsQuadratic
  decide

/-- The value of `χ₄ n`, for `n : ℕ`, depends only on `n % 4`. -/
theorem χ₄_nat_mod_four (n : ℕ) : χ₄ n = χ₄ (n % 4 : ℕ) := by
  rw [← ZMod.natCast_mod n 4]

/-- The value of `χ₄ n`, for `n : ℤ`, depends only on `n % 4`. -/
theorem χ₄_int_mod_four (n : ℤ) : χ₄ n = χ₄ (n % 4 : ℤ) := by
  rw [← ZMod.intCast_mod n 4, Nat.cast_ofNat]

/-- An explicit description of `χ₄` on integers / naturals -/
theorem χ₄_int_eq_if_mod_four (n : ℤ) :
    χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  have help : ∀ m : ℤ, 0 ≤ m → m < 4 → χ₄ m = if m % 2 = 0 then 0 else if m = 1 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by omega : (2 : ℤ) ∣ 4), ← ZMod.intCast_mod n 4]
  exact help (n % 4) (Int.emod_nonneg n (by omega)) (Int.emod_lt_abs n (by omega))

theorem χ₄_nat_eq_if_mod_four (n : ℕ) :
    χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 :=
  mod_cast χ₄_int_eq_if_mod_four n

/-- Alternative description of `χ₄ n` for odd `n : ℕ` in terms of powers of `-1` -/
theorem χ₄_eq_neg_one_pow {n : ℕ} (hn : n % 2 = 1) : χ₄ n = (-1) ^ (n / 2) := by
  rw [χ₄_nat_eq_if_mod_four]
  simp only [hn, Nat.one_ne_zero, if_false]
  nth_rewrite 3 [← Nat.div_add_mod n 4]
  nth_rewrite 3 [show 4 = 2 * 2 by omega]
  rw [mul_assoc, add_comm, Nat.add_mul_div_left _ _ zero_lt_two, pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]
  have help : ∀ m : ℕ, m < 4 → m % 2 = 1 → ite (m = 1) (1 : ℤ) (-1) = (-1) ^ (m / 2) := by decide
  exact help _ (Nat.mod_lt n (by omega)) <| (Nat.mod_mod_of_dvd n (by omega : 2 ∣ 4)).trans hn

/-- If `n % 4 = 1`, then `χ₄ n = 1`. -/
theorem χ₄_nat_one_mod_four {n : ℕ} (hn : n % 4 = 1) : χ₄ n = 1 := by
  rw [χ₄_nat_mod_four, hn]
  rfl

/-- If `n % 4 = 3`, then `χ₄ n = -1`. -/
theorem χ₄_nat_three_mod_four {n : ℕ} (hn : n % 4 = 3) : χ₄ n = -1 := by
  rw [χ₄_nat_mod_four, hn]
  rfl

/-- If `n % 4 = 1`, then `χ₄ n = 1`. -/
theorem χ₄_int_one_mod_four {n : ℤ} (hn : n % 4 = 1) : χ₄ n = 1 := by
  rw [χ₄_int_mod_four, hn]
  rfl

/-- If `n % 4 = 3`, then `χ₄ n = -1`. -/
theorem χ₄_int_three_mod_four {n : ℤ} (hn : n % 4 = 3) : χ₄ n = -1 := by
  rw [χ₄_int_mod_four, hn]
  rfl

/-- If `n % 4 = 1`, then `(-1)^(n/2) = 1`. -/
theorem neg_one_pow_div_two_of_one_mod_four {n : ℕ} (hn : n % 4 = 1) : (-1 : ℤ) ^ (n / 2) = 1 :=
  χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_one hn) ▸ χ₄_nat_one_mod_four hn

/-- If `n % 4 = 3`, then `(-1)^(n/2) = -1`. -/
theorem neg_one_pow_div_two_of_three_mod_four {n : ℕ} (hn : n % 4 = 3) : (-1 : ℤ) ^ (n / 2) = -1 :=
  χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_three hn) ▸ χ₄_nat_three_mod_four hn

/-- Define the first primitive quadratic character on `ZMod 8`, `χ₈`.
It corresponds to the extension `ℚ(√2)/ℚ`. -/
@[simps]
def χ₈ : MulChar (ZMod 8) ℤ where
  toFun a :=
    match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 7 => 1
    | 3 | 5 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- `χ₈` takes values in `{0, 1, -1}` -/
theorem isQuadratic_χ₈ : χ₈.IsQuadratic := by
  unfold MulChar.IsQuadratic
  decide

/-- The value of `χ₈ n`, for `n : ℕ`, depends only on `n % 8`. -/
theorem χ₈_nat_mod_eight (n : ℕ) : χ₈ n = χ₈ (n % 8 : ℕ) := by
  rw [← ZMod.natCast_mod n 8]

/-- The value of `χ₈ n`, for `n : ℤ`, depends only on `n % 8`. -/
theorem χ₈_int_mod_eight (n : ℤ) : χ₈ n = χ₈ (n % 8 : ℤ) := by
  rw [← ZMod.intCast_mod n 8, Nat.cast_ofNat]

/-- An explicit description of `χ₈` on integers / naturals -/
theorem χ₈_int_eq_if_mod_eight (n : ℤ) :
    χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  have help :
    ∀ m : ℤ, 0 ≤ m → m < 8 → χ₈ m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 7 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by omega : (2 : ℤ) ∣ 8), ← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by omega)) (Int.emod_lt_abs n (by omega))

theorem χ₈_nat_eq_if_mod_eight (n : ℕ) :
    χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 :=
  mod_cast χ₈_int_eq_if_mod_eight n

/-- Define the second primitive quadratic character on `ZMod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
@[simps]
def χ₈' : MulChar (ZMod 8) ℤ where
  toFun a :=
    match a with
    | 0 | 2 | 4 | 6 => 0
    | 1 | 3 => 1
    | 5 | 7 => -1
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide

/-- `χ₈'` takes values in `{0, 1, -1}` -/
theorem isQuadratic_χ₈' : χ₈'.IsQuadratic := by
  unfold MulChar.IsQuadratic
  decide

/-- An explicit description of `χ₈'` on integers / naturals -/
theorem χ₈'_int_eq_if_mod_eight (n : ℤ) :
    χ₈' n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  have help :
    ∀ m : ℤ, 0 ≤ m → m < 8 → χ₈' m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 3 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by omega : (2 : ℤ) ∣ 8), ← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by omega)) (Int.emod_lt_abs n (by omega))

theorem χ₈'_nat_eq_if_mod_eight (n : ℕ) :
    χ₈' n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 :=
  mod_cast χ₈'_int_eq_if_mod_eight n

/-- The relation between `χ₄`, `χ₈` and `χ₈'` -/
theorem χ₈'_eq_χ₄_mul_χ₈ : ∀ a : ZMod 8, χ₈' a = χ₄ (cast a) * χ₈ a := by
  decide

theorem χ₈'_int_eq_χ₄_mul_χ₈ (a : ℤ) : χ₈' a = χ₄ a * χ₈ a := by
  rw [← @cast_intCast 8 (ZMod 4) _ 4 _ (by omega) a]
  exact χ₈'_eq_χ₄_mul_χ₈ a

end QuadCharModP

end ZMod
