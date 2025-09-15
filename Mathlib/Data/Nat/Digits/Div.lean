/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
import Mathlib.Data.List.Palindrome
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Divisibility tests for natural numbers in terms of digits.

We prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

-/

namespace Nat

variable {n : ℕ}

theorem modEq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 3] :=
  modEq_digits_sum 3 10 (by norm_num) n

theorem modEq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] :=
  modEq_digits_sum 9 10 (by norm_num) n

theorem modEq_eleven_digits_sum (n : ℕ) :
    n ≡ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum [ZMOD 11] := by
  have t := zmodeq_ofDigits_digits 11 10 (-1 : ℤ) (by unfold Int.ModEq; rfl) n
  rwa [ofDigits_neg_one] at t

/-! ## Divisibility  -/

theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    b ∣ n ↔ b ∣ (digits b' n).sum := by
  rw [← ofDigits_one]
  conv_lhs => rw [← ofDigits_digits b' n]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, ofDigits_mod, h]

/-- **Divisibility by 3 Rule** -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by norm_num) n

theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by norm_num) n

theorem dvd_iff_dvd_ofDigits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
    b ∣ n ↔ (b : ℤ) ∣ ofDigits c (digits b' n) := by
  rw [← Int.natCast_dvd_natCast]
  exact
    dvd_iff_dvd_of_dvd_sub (zmodeq_ofDigits_digits b b' c (Int.modEq_iff_dvd.2 h).symm _).symm.dvd

theorem eleven_dvd_iff :
    11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum := by
  have t := dvd_iff_dvd_ofDigits 11 10 (-1 : ℤ) (by norm_num) n
  rw [ofDigits_neg_one] at t
  exact t

theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) :
    11 ∣ n := by
  let dig := (digits 10 n).map fun n : ℕ => (n : ℤ)
  replace h : Even dig.length := by rwa [List.length_map]
  refine eleven_dvd_iff.2 ⟨0, (?_ : dig.alternatingSum = 0)⟩
  have := dig.alternatingSum_reverse
  rw [(p.map _).reverse_eq, _root_.pow_succ', h.neg_one_pow, mul_one, neg_one_zsmul] at this
  exact eq_zero_of_neg_eq this.symm

end Nat
