/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.GaussSum

#align_import number_theory.legendre_symbol.quadratic_char.gauss_sum from "leanprover-community/mathlib"@"5b2fe80501ff327b9109fb09b7cc8c325cd0d7d9"

/-!
# Quadratic characters of finite fields

Further facts relying on Gauss sums.

-/


/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The value of the quadratic character at `2` -/
theorem quadraticChar_two [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F 2 = χ₈ (Fintype.card F) :=
  IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F) isQuadratic_χ₈ hF
    ((quadraticChar_eq_pow_of_char_ne_two' hF 2).trans (FiniteField.two_pow_card hF))
#align quadratic_char_two quadraticChar_two

/-- `2` is a square in `F` iff `#F` is not congruent to `3` or `5` mod `8`. -/
theorem FiniteField.isSquare_two_iff :
    IsSquare (2 : F) ↔ Fintype.card F % 8 ≠ 3 ∧ Fintype.card F % 8 ≠ 5 := by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff_iff]
    omega
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (Ring.two_ne_zero hF), quadraticChar_two hF,
      χ₈_nat_eq_if_mod_eight]
    omega
#align finite_field.is_square_two_iff FiniteField.isSquare_two_iff

/-- The value of the quadratic character at `-2` -/
theorem quadraticChar_neg_two [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-2) = χ₈' (Fintype.card F) := by
  rw [(by norm_num : (-2 : F) = -1 * 2), map_mul, χ₈'_eq_χ₄_mul_χ₈, quadraticChar_neg_one hF,
    quadraticChar_two hF, @cast_natCast _ (ZMod 4) _ _ _ (by decide : 4 ∣ 8)]
#align quadratic_char_neg_two quadraticChar_neg_two

/-- `-2` is a square in `F` iff `#F` is not congruent to `5` or `7` mod `8`. -/
theorem FiniteField.isSquare_neg_two_iff :
    IsSquare (-2 : F) ↔ Fintype.card F % 8 ≠ 5 ∧ Fintype.card F % 8 ≠ 7 := by
  classical
  by_cases hF : ringChar F = 2
  · have h := FiniteField.even_card_of_char_two hF
    simp only [FiniteField.isSquare_of_char_two hF, true_iff_iff]
    omega
  · have h := FiniteField.odd_card_of_char_ne_two hF
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr (Ring.two_ne_zero hF)),
      quadraticChar_neg_two hF, χ₈'_nat_eq_if_mod_eight]
    omega
#align finite_field.is_square_neg_two_iff FiniteField.isSquare_neg_two_iff

/-- The relation between the values of the quadratic character of one field `F` at the
cardinality of another field `F'` and of the quadratic character of `F'` at the cardinality
of `F`. -/
theorem quadraticChar_card_card [DecidableEq F] (hF : ringChar F ≠ 2) {F' : Type*} [Field F']
    [Fintype F'] [DecidableEq F'] (hF' : ringChar F' ≠ 2) (h : ringChar F' ≠ ringChar F) :
    quadraticChar F (Fintype.card F') =
    quadraticChar F' (quadraticChar F (-1) * Fintype.card F) := by
  let χ := (quadraticChar F).ringHomComp (algebraMap ℤ F')
  have hχ₁ : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char_ne_two hF'
  have h := Char.card_pow_card hχ₁ ((quadraticChar_isQuadratic F).comp _) h hF'
  rw [← quadraticChar_eq_pow_of_char_ne_two' hF'] at h
  exact (IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F')
    (quadraticChar_isQuadratic F) hF' h).symm
#align quadratic_char_card_card quadraticChar_card_card

/-- The value of the quadratic character at an odd prime `p` different from `ringChar F`. -/
theorem quadraticChar_odd_prime [DecidableEq F] (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp₁ : p ≠ 2) (hp₂ : ringChar F ≠ p) :
    quadraticChar F p = quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) := by
  rw [← quadraticChar_neg_one hF]
  have h := quadraticChar_card_card hF (ne_of_eq_of_ne (ringChar_zmod_n p) hp₁)
    (ne_of_eq_of_ne (ringChar_zmod_n p) hp₂.symm)
  rwa [card p] at h
#align quadratic_char_odd_prime quadraticChar_odd_prime

/-- An odd prime `p` is a square in `F` iff the quadratic character of `ZMod p` does not
take the value `-1` on `χ₄#F * #F`. -/
theorem FiniteField.isSquare_odd_prime_iff (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) :
    IsSquare (p : F) ↔ quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) ≠ -1 := by
  classical
  by_cases hFp : ringChar F = p
  · rw [show (p : F) = 0 by rw [← hFp]; exact ringChar.Nat.cast_ringChar]
    simp only [isSquare_zero, Ne, true_iff_iff, map_mul]
    obtain ⟨n, _, hc⟩ := FiniteField.card F (ringChar F)
    have hchar : ringChar F = ringChar (ZMod p) := by rw [hFp]; exact (ringChar_zmod_n p).symm
    conv => enter [1, 1, 2]; rw [hc, Nat.cast_pow, map_pow, hchar, map_ringChar]
    simp only [zero_pow n.ne_zero, mul_zero, zero_eq_neg, one_ne_zero, not_false_iff]
  · rw [← Iff.not_left (@quadraticChar_neg_one_iff_not_isSquare F _ _ _ _),
      quadraticChar_odd_prime hF hp]
    exact hFp
#align finite_field.is_square_odd_prime_iff FiniteField.isSquare_odd_prime_iff

end SpecialValues
