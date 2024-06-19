/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Int.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter

#align_import number_theory.legendre_symbol.zmod_char from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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
  toFun := (![0, 1, 0, -1] : ZMod 4 → ℤ)
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide
#align zmod.χ₄ ZMod.χ₄

/-- `χ₄` takes values in `{0, 1, -1}` -/
theorem isQuadratic_χ₄ : χ₄.IsQuadratic := by
  intro a
  -- Porting note (#11043): was `decide!`
  fin_cases a
  all_goals decide
#align zmod.is_quadratic_χ₄ ZMod.isQuadratic_χ₄

/-- The value of `χ₄ n`, for `n : ℕ`, depends only on `n % 4`. -/
theorem χ₄_nat_mod_four (n : ℕ) : χ₄ n = χ₄ (n % 4 : ℕ) := by rw [← ZMod.natCast_mod n 4]
#align zmod.χ₄_nat_mod_four ZMod.χ₄_nat_mod_four

/-- The value of `χ₄ n`, for `n : ℤ`, depends only on `n % 4`. -/
theorem χ₄_int_mod_four (n : ℤ) : χ₄ n = χ₄ (n % 4 : ℤ) := by
  rw [← ZMod.intCast_mod n 4]
  norm_cast
#align zmod.χ₄_int_mod_four ZMod.χ₄_int_mod_four

/-- An explicit description of `χ₄` on integers / naturals -/
theorem χ₄_int_eq_if_mod_four (n : ℤ) :
    χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  have help : ∀ m : ℤ, 0 ≤ m → m < 4 → χ₄ m = if m % 2 = 0 then 0 else if m = 1 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by decide : (2 : ℤ) ∣ 4), ← ZMod.intCast_mod n 4]
  exact help (n % 4) (Int.emod_nonneg n (by norm_num)) (Int.emod_lt n (by norm_num))
#align zmod.χ₄_int_eq_if_mod_four ZMod.χ₄_int_eq_if_mod_four

theorem χ₄_nat_eq_if_mod_four (n : ℕ) :
    χ₄ n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 :=
  mod_cast χ₄_int_eq_if_mod_four n
#align zmod.χ₄_nat_eq_if_mod_four ZMod.χ₄_nat_eq_if_mod_four

/-- Alternative description of `χ₄ n` for odd `n : ℕ` in terms of powers of `-1` -/
theorem χ₄_eq_neg_one_pow {n : ℕ} (hn : n % 2 = 1) : χ₄ n = (-1) ^ (n / 2) := by
  rw [χ₄_nat_eq_if_mod_four]
  simp only [hn, Nat.one_ne_zero, if_false]
  conv_rhs => -- Porting note: was `nth_rw`
    arg 2; rw [← Nat.div_add_mod n 4]
    enter [1, 1, 1]; rw [(by norm_num : 4 = 2 * 2)]
  rw [mul_assoc, add_comm, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]
  have help : ∀ m : ℕ, m < 4 → m % 2 = 1 → ite (m = 1) (1 : ℤ) (-1) = (-1) ^ (m / 2) := by decide
  exact
    help (n % 4) (Nat.mod_lt n (by norm_num))
      ((Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans hn)
#align zmod.χ₄_eq_neg_one_pow ZMod.χ₄_eq_neg_one_pow

/-- If `n % 4 = 1`, then `χ₄ n = 1`. -/
theorem χ₄_nat_one_mod_four {n : ℕ} (hn : n % 4 = 1) : χ₄ n = 1 := by
  rw [χ₄_nat_mod_four, hn]
  rfl
#align zmod.χ₄_nat_one_mod_four ZMod.χ₄_nat_one_mod_four

/-- If `n % 4 = 3`, then `χ₄ n = -1`. -/
theorem χ₄_nat_three_mod_four {n : ℕ} (hn : n % 4 = 3) : χ₄ n = -1 := by
  rw [χ₄_nat_mod_four, hn]
  rfl
#align zmod.χ₄_nat_three_mod_four ZMod.χ₄_nat_three_mod_four

/-- If `n % 4 = 1`, then `χ₄ n = 1`. -/
theorem χ₄_int_one_mod_four {n : ℤ} (hn : n % 4 = 1) : χ₄ n = 1 := by
  rw [χ₄_int_mod_four, hn]
  rfl
#align zmod.χ₄_int_one_mod_four ZMod.χ₄_int_one_mod_four

/-- If `n % 4 = 3`, then `χ₄ n = -1`. -/
theorem χ₄_int_three_mod_four {n : ℤ} (hn : n % 4 = 3) : χ₄ n = -1 := by
  rw [χ₄_int_mod_four, hn]
  rfl
#align zmod.χ₄_int_three_mod_four ZMod.χ₄_int_three_mod_four

/-- If `n % 4 = 1`, then `(-1)^(n/2) = 1`. -/
theorem neg_one_pow_div_two_of_one_mod_four {n : ℕ} (hn : n % 4 = 1) : (-1 : ℤ) ^ (n / 2) = 1 := by
  rw [← χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_one hn), ← natCast_mod, hn]
  rfl
#align zmod.neg_one_pow_div_two_of_one_mod_four ZMod.neg_one_pow_div_two_of_one_mod_four

/-- If `n % 4 = 3`, then `(-1)^(n/2) = -1`. -/
theorem neg_one_pow_div_two_of_three_mod_four {n : ℕ} (hn : n % 4 = 3) :
    (-1 : ℤ) ^ (n / 2) = -1 := by
  rw [← χ₄_eq_neg_one_pow (Nat.odd_of_mod_four_eq_three hn), ← natCast_mod, hn]
  rfl
#align zmod.neg_one_pow_div_two_of_three_mod_four ZMod.neg_one_pow_div_two_of_three_mod_four

/-- Define the first primitive quadratic character on `ZMod 8`, `χ₈`.
It corresponds to the extension `ℚ(√2)/ℚ`. -/
@[simps]
def χ₈ : MulChar (ZMod 8) ℤ where
  toFun := (![0, 1, 0, -1, 0, -1, 0, 1] : ZMod 8 → ℤ)
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide
#align zmod.χ₈ ZMod.χ₈

/-- `χ₈` takes values in `{0, 1, -1}` -/
theorem isQuadratic_χ₈ : χ₈.IsQuadratic := by
  intro a
  -- Porting note: was `decide!`
  fin_cases a
  all_goals decide
#align zmod.is_quadratic_χ₈ ZMod.isQuadratic_χ₈

/-- The value of `χ₈ n`, for `n : ℕ`, depends only on `n % 8`. -/
theorem χ₈_nat_mod_eight (n : ℕ) : χ₈ n = χ₈ (n % 8 : ℕ) := by rw [← ZMod.natCast_mod n 8]
#align zmod.χ₈_nat_mod_eight ZMod.χ₈_nat_mod_eight

/-- The value of `χ₈ n`, for `n : ℤ`, depends only on `n % 8`. -/
theorem χ₈_int_mod_eight (n : ℤ) : χ₈ n = χ₈ (n % 8 : ℤ) := by
  rw [← ZMod.intCast_mod n 8]
  norm_cast
#align zmod.χ₈_int_mod_eight ZMod.χ₈_int_mod_eight

/-- An explicit description of `χ₈` on integers / naturals -/
theorem χ₈_int_eq_if_mod_eight (n : ℤ) :
    χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  have help :
    ∀ m : ℤ, 0 ≤ m → m < 8 → χ₈ m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 7 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by decide : (2 : ℤ) ∣ 8), ← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by norm_num)) (Int.emod_lt n (by norm_num))
#align zmod.χ₈_int_eq_if_mod_eight ZMod.χ₈_int_eq_if_mod_eight

theorem χ₈_nat_eq_if_mod_eight (n : ℕ) :
    χ₈ n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 :=
  mod_cast χ₈_int_eq_if_mod_eight n
#align zmod.χ₈_nat_eq_if_mod_eight ZMod.χ₈_nat_eq_if_mod_eight

/-- Define the second primitive quadratic character on `ZMod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
@[simps]
def χ₈' : MulChar (ZMod 8) ℤ where
  toFun := (![0, 1, 0, 1, 0, -1, 0, -1] : ZMod 8 → ℤ)
  map_one' := rfl
  map_mul' := by decide
  map_nonunit' := by decide
#align zmod.χ₈' ZMod.χ₈'

/-- `χ₈'` takes values in `{0, 1, -1}` -/
theorem isQuadratic_χ₈' : χ₈'.IsQuadratic := by
  intro a
  -- Porting note: was `decide!`
  fin_cases a
  all_goals decide
#align zmod.is_quadratic_χ₈' ZMod.isQuadratic_χ₈'

/-- An explicit description of `χ₈'` on integers / naturals -/
theorem χ₈'_int_eq_if_mod_eight (n : ℤ) :
    χ₈' n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  have help :
    ∀ m : ℤ, 0 ≤ m → m < 8 → χ₈' m = if m % 2 = 0 then 0 else if m = 1 ∨ m = 3 then 1 else -1 := by
    decide
  rw [← Int.emod_emod_of_dvd n (by decide : (2 : ℤ) ∣ 8), ← ZMod.intCast_mod n 8]
  exact help (n % 8) (Int.emod_nonneg n (by norm_num)) (Int.emod_lt n (by norm_num))
#align zmod.χ₈'_int_eq_if_mod_eight ZMod.χ₈'_int_eq_if_mod_eight

theorem χ₈'_nat_eq_if_mod_eight (n : ℕ) :
    χ₈' n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 :=
  mod_cast χ₈'_int_eq_if_mod_eight n
#align zmod.χ₈'_nat_eq_if_mod_eight ZMod.χ₈'_nat_eq_if_mod_eight

/-- The relation between `χ₄`, `χ₈` and `χ₈'` -/
theorem χ₈'_eq_χ₄_mul_χ₈ (a : ZMod 8) : χ₈' a = χ₄ (cast a) * χ₈ a := by
    -- Porting note: was `decide!`
  fin_cases a
  all_goals decide
#align zmod.χ₈'_eq_χ₄_mul_χ₈ ZMod.χ₈'_eq_χ₄_mul_χ₈

theorem χ₈'_int_eq_χ₄_mul_χ₈ (a : ℤ) : χ₈' a = χ₄ a * χ₈ a := by
  rw [← @cast_intCast 8 (ZMod 4) _ 4 _ (by decide) a]
  exact χ₈'_eq_χ₄_mul_χ₈ a
#align zmod.χ₈'_int_eq_χ₄_mul_χ₈ ZMod.χ₈'_int_eq_χ₄_mul_χ₈

end QuadCharModP

end ZMod
