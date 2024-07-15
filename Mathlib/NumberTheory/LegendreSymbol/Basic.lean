/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

#align_import number_theory.legendre_symbol.basic from "leanprover-community/mathlib"@"5b2fe80501ff327b9109fb09b7cc8c325cd0d7d9"

/-!
# Legendre symbol

This file contains results about Legendre symbols.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendreSym p a`.
Note the order of arguments! The advantage of this form is that then `legendreSym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobiSym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We also prove the supplementary laws that give conditions for when `-1`
is a square modulo a prime `p`:
`legendreSym.at_neg_one` and `ZMod.exists_sq_eq_neg_one_iff` for `-1`.

See `NumberTheory.LegendreSymbol.QuadraticReciprocity` for the conditions when `2` and `-2`
are squares:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2`,
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/


open Nat

section Euler

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

/-- Euler's Criterion: A unit `x` of `ZMod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion_units (x : (ZMod p)ˣ) : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 := by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_isSquare_iff (by rwa [ringChar_zmod_n]) x
    have hs : (∃ y : (ZMod p)ˣ, y ^ 2 = x) ↔ IsSquare x := by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀
#align zmod.euler_criterion_units ZMod.euler_criterion_units

/-- Euler's Criterion: a nonzero `a : ZMod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion {a : ZMod p} (ha : a ≠ 0) : IsSquare (a : ZMod p) ↔ a ^ (p / 2) = 1 := by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simp [zero_pow, mul_zero, ne_eq, not_true] at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp
#align zmod.euler_criterion ZMod.euler_criterion

/-- If `a : ZMod p` is nonzero, then `a^(p/2)` is either `1` or `-1`. -/
theorem pow_div_two_eq_neg_one_or_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 := by
  cases' Prime.eq_two_or_odd (@Fact.out p.Prime _) with hp2 hp_odd
  · subst p; revert a ha; intro a; fin_cases a
    · tauto
    · simp
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha
#align zmod.pow_div_two_eq_neg_one_or_one ZMod.pow_div_two_eq_neg_one_or_one

end ZMod

end Euler

section Legendre

/-!
### Definition of the Legendre symbol and basic properties
-/


open ZMod

variable (p : ℕ) [Fact p.Prime]

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendreSym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendreSym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendreSym (a : ℤ) : ℤ :=
  quadraticChar (ZMod p) a
#align legendre_sym legendreSym

namespace legendreSym

/-- We have the congruence `legendreSym p a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow (a : ℤ) : (legendreSym p a : ZMod p) = (a : ZMod p) ^ (p / 2) := by
  rcases eq_or_ne (ringChar (ZMod p)) 2 with hc | hc
  · by_cases ha : (a : ZMod p) = 0
    · rw [legendreSym, ha, quadraticChar_zero,
        zero_pow (Nat.div_pos (@Fact.out p.Prime).two_le (succ_pos 1)).ne']
      norm_cast
    · have := (ringChar_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym, quadraticChar_eq_one_of_char_two hc ha]
      revert ha
      push_cast
      generalize (a : ZMod 2) = b; fin_cases b
      · tauto
      · simp
  · convert quadraticChar_eq_pow_of_char_ne_two' hc (a : ZMod p)
    exact (card p).symm
#align legendre_sym.eq_pow legendreSym.eq_pow

/-- If `p ∤ a`, then `legendreSym p a` is `1` or `-1`. -/
theorem eq_one_or_neg_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ∨ legendreSym p a = -1 :=
  quadraticChar_dichotomy ha
#align legendre_sym.eq_one_or_neg_one legendreSym.eq_one_or_neg_one

theorem eq_neg_one_iff_not_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = -1 ↔ ¬legendreSym p a = 1 :=
  quadraticChar_eq_neg_one_iff_not_one ha
#align legendre_sym.eq_neg_one_iff_not_one legendreSym.eq_neg_one_iff_not_one

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff (a : ℤ) : legendreSym p a = 0 ↔ (a : ZMod p) = 0 :=
  quadraticChar_eq_zero_iff
#align legendre_sym.eq_zero_iff legendreSym.eq_zero_iff

@[simp]
theorem at_zero : legendreSym p 0 = 0 := by rw [legendreSym, Int.cast_zero, MulChar.map_zero]
#align legendre_sym.at_zero legendreSym.at_zero

@[simp]
theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]
#align legendre_sym.at_one legendreSym.at_one

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp [legendreSym, Int.cast_mul, map_mul, quadraticCharFun_mul]
#align legendre_sym.mul legendreSym.mul

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
def hom : ℤ →*₀ ℤ where
  toFun := legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p
#align legendre_sym.hom legendreSym.hom

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem sq_one {a : ℤ} (ha : (a : ZMod p) ≠ 0) : legendreSym p a ^ 2 = 1 :=
  quadraticChar_sq_one ha
#align legendre_sym.sq_one legendreSym.sq_one

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem sq_one' {a : ℤ} (ha : (a : ZMod p) ≠ 0) : legendreSym p (a ^ 2) = 1 := by
  dsimp only [legendreSym]
  rw [Int.cast_pow]
  exact quadraticChar_sq_one' ha
#align legendre_sym.sq_one' legendreSym.sq_one'

/-- The Legendre symbol depends only on `a` mod `p`. -/
protected theorem mod (a : ℤ) : legendreSym p a = legendreSym p (a % p) := by
  simp only [legendreSym, intCast_mod]
#align legendre_sym.mod legendreSym.mod

/-- When `p ∤ a`, then `legendreSym p a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff {a : ℤ} (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : ZMod p) :=
  quadraticChar_one_iff_isSquare ha0
#align legendre_sym.eq_one_iff legendreSym.eq_one_iff

theorem eq_one_iff' {a : ℕ} (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a = 1 ↔ IsSquare (a : ZMod p) := by
      rw [eq_one_iff]
      · norm_cast
      · exact mod_cast ha0
#align legendre_sym.eq_one_iff' legendreSym.eq_one_iff'

/-- `legendreSym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff {a : ℤ} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) :=
  quadraticChar_neg_one_iff_not_isSquare
#align legendre_sym.eq_neg_one_iff legendreSym.eq_neg_one_iff

theorem eq_neg_one_iff' {a : ℕ} : legendreSym p a = -1 ↔ ¬IsSquare (a : ZMod p) := by
  rw [eq_neg_one_iff]; norm_cast
#align legendre_sym.eq_neg_one_iff' legendreSym.eq_neg_one_iff'

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
theorem card_sqrts (hp : p ≠ 2) (a : ℤ) :
    ↑{x : ZMod p | x ^ 2 = a}.toFinset.card = legendreSym p a + 1 :=
  quadraticChar_card_sqrts ((ringChar_zmod_n p).substr hp) a
#align legendre_sym.card_sqrts legendreSym.card_sqrts

end legendreSym

end Legendre

section QuadraticForm

/-!
### Applications to binary quadratic forms
-/


namespace legendreSym

/-- The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `y ≠ 0`. -/
theorem eq_one_of_sq_sub_mul_sq_eq_zero {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    {x y : ZMod p} (hy : y ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
  apply_fun (· * y⁻¹ ^ 2) at hxy
  simp only [zero_mul] at hxy
  rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2),
    mul_inv_cancel hy, one_pow, mul_one, sub_eq_zero, pow_two] at hxy
  exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩
#align legendre_sym.eq_one_of_sq_sub_mul_sq_eq_zero legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero

/-- The Legendre symbol `legendreSym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `x ≠ 0`. -/
theorem eq_one_of_sq_sub_mul_sq_eq_zero' {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : (a : ZMod p) ≠ 0)
    {x y : ZMod p} (hx : x ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) : legendreSym p a = 1 := by
  haveI hy : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, mul_zero, sub_zero, sq_eq_zero_iff] at hxy
    exact hx hxy
  exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy
#align legendre_sym.eq_one_of_sq_sub_mul_sq_eq_zero' legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'

/-- If `legendreSym p a = -1`, then the only solution of `x^2 - a*y^2 = 0` in `ℤ/pℤ`
is the trivial one. -/
theorem eq_zero_mod_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1)
    {x y : ZMod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have ha : (a : ZMod p) ≠ 0 := by
    intro hf
    rw [(eq_zero_iff p a).mpr hf] at h
    simp at h
  by_contra hf
  cases' imp_iff_or_not.mp (not_and'.mp hf) with hx hy
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy, eq_neg_self_iff] at h
    exact one_ne_zero h
  · rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy, eq_neg_self_iff] at h
    exact one_ne_zero h
#align legendre_sym.eq_zero_mod_of_eq_neg_one legendreSym.eq_zero_mod_of_eq_neg_one

/-- If `legendreSym p a = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide `x` and `y`. -/
theorem prime_dvd_of_eq_neg_one {p : ℕ} [Fact p.Prime] {a : ℤ} (h : legendreSym p a = -1) {x y : ℤ}
    (hxy : (p : ℤ) ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y := by
  simp_rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hxy ⊢
  push_cast at hxy
  exact eq_zero_mod_of_eq_neg_one h hxy
#align legendre_sym.prime_dvd_of_eq_neg_one legendreSym.prime_dvd_of_eq_neg_one

end legendreSym

end QuadraticForm

section Values

/-!
### The value of the Legendre symbol at `-1`

See `jacobiSym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/


variable {p : ℕ} [Fact p.Prime]

open ZMod

/-- `legendreSym p (-1)` is given by `χ₄ p`. -/
theorem legendreSym.at_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p := by
  simp only [legendreSym, card p, quadraticChar_neg_one ((ringChar_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]
#align legendre_sym.at_neg_one legendreSym.at_neg_one

namespace ZMod

/-- `-1` is a square in `ZMod p` iff `p` is not congruent to `3` mod `4`. -/
theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 := by
  rw [FiniteField.isSquare_neg_one_iff, card p]
#align zmod.exists_sq_eq_neg_one_iff ZMod.exists_sq_eq_neg_one_iff

theorem mod_four_ne_three_of_sq_eq_neg_one {y : ZMod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
  exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩
#align zmod.mod_four_ne_three_of_sq_eq_neg_one ZMod.mod_four_ne_three_of_sq_eq_neg_one

/-- If two nonzero squares are negatives of each other in `ZMod p`, then `p % 4 ≠ 3`. -/
theorem mod_four_ne_three_of_sq_eq_neg_sq' {x y : ZMod p} (hy : y ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 ≠ 3 :=
  @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2 at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)
#align zmod.mod_four_ne_three_of_sq_eq_neg_sq' ZMod.mod_four_ne_three_of_sq_eq_neg_sq'

theorem mod_four_ne_three_of_sq_eq_neg_sq {x y : ZMod p} (hx : x ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 ≠ 3 :=
  mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm
#align zmod.mod_four_ne_three_of_sq_eq_neg_sq ZMod.mod_four_ne_three_of_sq_eq_neg_sq

end ZMod

end Values
