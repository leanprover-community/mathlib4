/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Data.Polynomial.Splits

#align_import algebra.cubic_discriminant from "leanprover-community/mathlib"@"930133160e24036d5242039fe4972407cd4f1222"

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

 * `Cubic`: the structure representing a cubic polynomial.
 * `Cubic.disc`: the discriminant of a cubic polynomial.

## Main statements

 * `Cubic.disc_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
    the cubic has no duplicate roots.

## References

 * https://en.wikipedia.org/wiki/Cubic_equation
 * https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/


noncomputable section

/-- The structure representing a cubic polynomial. -/
@[ext]
structure Cubic (R : Type*) where
  (a b c d : R)
#align cubic Cubic

namespace Cubic

open Cubic Polynomial

open Polynomial

variable {R S F K : Type*}

instance [Inhabited R] : Inhabited (Cubic R) :=
  ⟨⟨default, default, default, default⟩⟩

instance [Zero R] : Zero (Cubic R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

section Basic

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

/-- Convert a cubic polynomial to a polynomial. -/
def toPoly (P : Cubic R) : R[X] :=
  C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d
#align cubic.to_poly Cubic.toPoly

theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    C w * (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  simp only [toPoly, C_neg, C_add, C_mul]
  -- ⊢ ↑C w * (X - ↑C x) * (X - ↑C y) * (X - ↑C z) = ↑C w * X ^ 3 + ↑C w * -(↑C x + …
  ring1
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align cubic.C_mul_prod_X_sub_C_eq Cubic.C_mul_prod_X_sub_C_eq

theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  rw [← one_mul <| X - C x, ← C_1, C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align cubic.prod_X_sub_C_eq Cubic.prod_X_sub_C_eq

/-! ### Coefficients -/


section Coeff

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [toPoly, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  -- ⊢ (∀ (n : ℕ), n > 3 → ((((if n = 3 then P.a else 0) + if n = 2 then P.b else 0 …
  norm_num
  -- ⊢ ∀ (n : ℕ), 3 < n → ((((if n = 3 then P.a else 0) + if n = 2 then P.b else 0) …
  intro n hn
  -- ⊢ ((((if n = 3 then P.a else 0) + if n = 2 then P.b else 0) + if n = 1 then P. …
  repeat' rw [if_neg]
  any_goals linarith only [hn]
  -- ⊢ 0 + 0 + 0 + 0 = 0
  repeat' rw [zero_add]
  -- 🎉 no goals

@[simp]
theorem coeff_eq_zero {n : ℕ} (hn : 3 < n) : P.toPoly.coeff n = 0 :=
  coeffs.1 n hn
#align cubic.coeff_eq_zero Cubic.coeff_eq_zero

@[simp]
theorem coeff_eq_a : P.toPoly.coeff 3 = P.a :=
  coeffs.2.1
#align cubic.coeff_eq_a Cubic.coeff_eq_a

@[simp]
theorem coeff_eq_b : P.toPoly.coeff 2 = P.b :=
  coeffs.2.2.1
#align cubic.coeff_eq_b Cubic.coeff_eq_b

@[simp]
theorem coeff_eq_c : P.toPoly.coeff 1 = P.c :=
  coeffs.2.2.2.1
#align cubic.coeff_eq_c Cubic.coeff_eq_c

@[simp]
theorem coeff_eq_d : P.toPoly.coeff 0 = P.d :=
  coeffs.2.2.2.2
#align cubic.coeff_eq_d Cubic.coeff_eq_d

theorem a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]
                                                            -- 🎉 no goals
#align cubic.a_of_eq Cubic.a_of_eq

theorem b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]
                                                            -- 🎉 no goals
#align cubic.b_of_eq Cubic.b_of_eq

theorem c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]
                                                            -- 🎉 no goals
#align cubic.c_of_eq Cubic.c_of_eq

theorem d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]
                                                            -- 🎉 no goals
#align cubic.d_of_eq Cubic.d_of_eq

theorem toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q :=
  ⟨fun h ↦ Cubic.ext P Q (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩
#align cubic.to_poly_injective Cubic.toPoly_injective

theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d := by
  rw [toPoly, ha, C_0, zero_mul, zero_add]
  -- 🎉 no goals
#align cubic.of_a_eq_zero Cubic.of_a_eq_zero

theorem of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d :=
  of_a_eq_zero rfl
#align cubic.of_a_eq_zero' Cubic.of_a_eq_zero'

theorem of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d := by
  rw [of_a_eq_zero ha, hb, C_0, zero_mul, zero_add]
  -- 🎉 no goals
#align cubic.of_b_eq_zero Cubic.of_b_eq_zero

theorem of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d :=
  of_b_eq_zero rfl rfl
#align cubic.of_b_eq_zero' Cubic.of_b_eq_zero'

theorem of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P.d := by
  rw [of_b_eq_zero ha hb, hc, C_0, zero_mul, zero_add]
  -- 🎉 no goals
#align cubic.of_c_eq_zero Cubic.of_c_eq_zero

theorem of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d :=
  of_c_eq_zero rfl rfl rfl
#align cubic.of_c_eq_zero' Cubic.of_c_eq_zero'

theorem of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly = 0 := by
  rw [of_c_eq_zero ha hb hc, hd, C_0]
  -- 🎉 no goals
#align cubic.of_d_eq_zero Cubic.of_d_eq_zero

theorem of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0 :=
  of_d_eq_zero rfl rfl rfl rfl
#align cubic.of_d_eq_zero' Cubic.of_d_eq_zero'

theorem zero : (0 : Cubic R).toPoly = 0 :=
  of_d_eq_zero'
#align cubic.zero Cubic.zero

theorem toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero, toPoly_injective]
  -- 🎉 no goals
#align cubic.to_poly_eq_zero_iff Cubic.toPoly_eq_zero_iff

private theorem ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  -- ⊢ P.a = 0 ∧ P.b = 0 ∧ P.c = 0 ∧ P.d = 0
  rw [(toPoly_eq_zero_iff P).mp h0]
  -- ⊢ 0.a = 0 ∧ 0.b = 0 ∧ 0.c = 0 ∧ 0.d = 0
  exact ⟨rfl, rfl, rfl, rfl⟩
  -- 🎉 no goals

theorem ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp ne_zero).1 ha
#align cubic.ne_zero_of_a_ne_zero Cubic.ne_zero_of_a_ne_zero

theorem ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp ne_zero).2).1 hb
#align cubic.ne_zero_of_b_ne_zero Cubic.ne_zero_of_b_ne_zero

theorem ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).1 hc
#align cubic.ne_zero_of_c_ne_zero Cubic.ne_zero_of_c_ne_zero

theorem ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).2 hd
#align cubic.ne_zero_of_d_ne_zero Cubic.ne_zero_of_d_ne_zero

@[simp]
theorem leadingCoeff_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.leadingCoeff = P.a :=
  leadingCoeff_cubic ha
#align cubic.leading_coeff_of_a_ne_zero Cubic.leadingCoeff_of_a_ne_zero

@[simp]
theorem leadingCoeff_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).leadingCoeff = a :=
  leadingCoeff_of_a_ne_zero ha
#align cubic.leading_coeff_of_a_ne_zero' Cubic.leadingCoeff_of_a_ne_zero'

@[simp]
theorem leadingCoeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.leadingCoeff = P.b := by
  rw [of_a_eq_zero ha, leadingCoeff_quadratic hb]
  -- 🎉 no goals
#align cubic.leading_coeff_of_b_ne_zero Cubic.leadingCoeff_of_b_ne_zero

@[simp]
theorem leadingCoeff_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).leadingCoeff = b :=
  leadingCoeff_of_b_ne_zero rfl hb
#align cubic.leading_coeff_of_b_ne_zero' Cubic.leadingCoeff_of_b_ne_zero'

@[simp]
theorem leadingCoeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.leadingCoeff = P.c := by
  rw [of_b_eq_zero ha hb, leadingCoeff_linear hc]
  -- 🎉 no goals
#align cubic.leading_coeff_of_c_ne_zero Cubic.leadingCoeff_of_c_ne_zero

@[simp]
theorem leadingCoeff_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c :=
  leadingCoeff_of_c_ne_zero rfl rfl hc
#align cubic.leading_coeff_of_c_ne_zero' Cubic.leadingCoeff_of_c_ne_zero'

@[simp]
theorem leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.leadingCoeff = P.d := by
  rw [of_c_eq_zero ha hb hc, leadingCoeff_C]
  -- 🎉 no goals
#align cubic.leading_coeff_of_c_eq_zero Cubic.leadingCoeff_of_c_eq_zero

-- @[simp] -- Porting note: simp can prove this
theorem leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d :=
  leadingCoeff_of_c_eq_zero rfl rfl rfl
#align cubic.leading_coeff_of_c_eq_zero' Cubic.leadingCoeff_of_c_eq_zero'

theorem monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic := by
  nontriviality R
  -- ⊢ Monic (toPoly P)
  rw [Monic, leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero), ha]
  -- 🎉 no goals
#align cubic.monic_of_a_eq_one Cubic.monic_of_a_eq_one

theorem monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic :=
  monic_of_a_eq_one rfl
#align cubic.monic_of_a_eq_one' Cubic.monic_of_a_eq_one'

theorem monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic := by
  nontriviality R
  -- ⊢ Monic (toPoly P)
  rw [Monic, leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero), hb]
  -- 🎉 no goals
#align cubic.monic_of_b_eq_one Cubic.monic_of_b_eq_one

theorem monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic :=
  monic_of_b_eq_one rfl rfl
#align cubic.monic_of_b_eq_one' Cubic.monic_of_b_eq_one'

theorem monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.Monic := by
  nontriviality R
  -- ⊢ Monic (toPoly P)
  rw [Monic, leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero), hc]
  -- 🎉 no goals
#align cubic.monic_of_c_eq_one Cubic.monic_of_c_eq_one

theorem monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic :=
  monic_of_c_eq_one rfl rfl rfl
#align cubic.monic_of_c_eq_one' Cubic.monic_of_c_eq_one'

theorem monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
    P.toPoly.Monic := by
  rw [Monic, leadingCoeff_of_c_eq_zero ha hb hc, hd]
  -- 🎉 no goals
#align cubic.monic_of_d_eq_one Cubic.monic_of_d_eq_one

theorem monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic :=
  monic_of_d_eq_one rfl rfl rfl rfl
#align cubic.monic_of_d_eq_one' Cubic.monic_of_d_eq_one'

end Coeff

/-! ### Degrees -/


section Degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
@[simps]
def equiv : Cubic R ≃ { p : R[X] // p.degree ≤ 3 } where
  toFun P := ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [Subtype.coe_mk, coeffs]
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
                           -- 🎉 no goals
  right_inv f := by
    -- Porting note: Added `simp only [Nat.zero_eq, Nat.succ_eq_add_one] <;> ring_nf`
    -- There's probably a better way to do this.
    ext (_ | _ | _ | _ | n) <;> simp only [Nat.zero_eq, Nat.succ_eq_add_one] <;> ring_nf
                                -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                                                                 -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                                                                 -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                                                                 -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                                                                 -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
                                                                                 -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
      <;> try simp only [coeffs]
          -- 🎉 no goals
          -- 🎉 no goals
          -- 🎉 no goals
          -- 🎉 no goals
          -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
    have h3 : 3 < 4 + n := by linarith only
    -- ⊢ coeff (toPoly { a := coeff (↑f) 3, b := coeff (↑f) 2, c := coeff (↑f) 1, d : …
    rw [coeff_eq_zero h3,
      (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2 _ <| WithBot.coe_lt_coe.mpr (by exact h3)]
#align cubic.equiv Cubic.equiv

@[simp]
theorem degree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.degree = 3 :=
  degree_cubic ha
#align cubic.degree_of_a_ne_zero Cubic.degree_of_a_ne_zero

@[simp]
theorem degree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).degree = 3 :=
  degree_of_a_ne_zero ha
#align cubic.degree_of_a_ne_zero' Cubic.degree_of_a_ne_zero'

theorem degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le
  -- 🎉 no goals
#align cubic.degree_of_a_eq_zero Cubic.degree_of_a_eq_zero

theorem degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree ≤ 2 :=
  degree_of_a_eq_zero rfl
#align cubic.degree_of_a_eq_zero' Cubic.degree_of_a_eq_zero'

@[simp]
theorem degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.degree = 2 := by
  rw [of_a_eq_zero ha, degree_quadratic hb]
  -- 🎉 no goals
#align cubic.degree_of_b_ne_zero Cubic.degree_of_b_ne_zero

@[simp]
theorem degree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).degree = 2 :=
  degree_of_b_ne_zero rfl hb
#align cubic.degree_of_b_ne_zero' Cubic.degree_of_b_ne_zero'

theorem degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le
  -- 🎉 no goals
#align cubic.degree_of_b_eq_zero Cubic.degree_of_b_eq_zero

theorem degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree ≤ 1 :=
  degree_of_b_eq_zero rfl rfl
#align cubic.degree_of_b_eq_zero' Cubic.degree_of_b_eq_zero'

@[simp]
theorem degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.toPoly.degree = 1 := by
  rw [of_b_eq_zero ha hb, degree_linear hc]
  -- 🎉 no goals
#align cubic.degree_of_c_ne_zero Cubic.degree_of_c_ne_zero

@[simp]
theorem degree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).degree = 1 :=
  degree_of_c_ne_zero rfl rfl hc
#align cubic.degree_of_c_ne_zero' Cubic.degree_of_c_ne_zero'

theorem degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.degree ≤ 0 := by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le
  -- 🎉 no goals
#align cubic.degree_of_c_eq_zero Cubic.degree_of_c_eq_zero

theorem degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree ≤ 0 :=
  degree_of_c_eq_zero rfl rfl rfl
#align cubic.degree_of_c_eq_zero' Cubic.degree_of_c_eq_zero'

@[simp]
theorem degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
    P.toPoly.degree = 0 := by
  rw [of_c_eq_zero ha hb hc, degree_C hd]
  -- 🎉 no goals
#align cubic.degree_of_d_ne_zero Cubic.degree_of_d_ne_zero

@[simp]
theorem degree_of_d_ne_zero' (hd : d ≠ 0) : (toPoly ⟨0, 0, 0, d⟩).degree = 0 :=
  degree_of_d_ne_zero rfl rfl rfl hd
#align cubic.degree_of_d_ne_zero' Cubic.degree_of_d_ne_zero'

@[simp]
theorem degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly.degree = ⊥ := by
  rw [of_d_eq_zero ha hb hc hd, degree_zero]
  -- 🎉 no goals
#align cubic.degree_of_d_eq_zero Cubic.degree_of_d_eq_zero

-- @[simp] -- Porting note: simp can prove this
theorem degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero rfl rfl rfl rfl
#align cubic.degree_of_d_eq_zero' Cubic.degree_of_d_eq_zero'

@[simp]
theorem degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero'
#align cubic.degree_of_zero Cubic.degree_of_zero

@[simp]
theorem natDegree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.natDegree = 3 :=
  natDegree_cubic ha
#align cubic.nat_degree_of_a_ne_zero Cubic.natDegree_of_a_ne_zero

@[simp]
theorem natDegree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).natDegree = 3 :=
  natDegree_of_a_ne_zero ha
#align cubic.nat_degree_of_a_ne_zero' Cubic.natDegree_of_a_ne_zero'

theorem natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le
  -- 🎉 no goals
#align cubic.nat_degree_of_a_eq_zero Cubic.natDegree_of_a_eq_zero

theorem natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree ≤ 2 :=
  natDegree_of_a_eq_zero rfl
#align cubic.nat_degree_of_a_eq_zero' Cubic.natDegree_of_a_eq_zero'

@[simp]
theorem natDegree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.natDegree = 2 := by
  rw [of_a_eq_zero ha, natDegree_quadratic hb]
  -- 🎉 no goals
#align cubic.nat_degree_of_b_ne_zero Cubic.natDegree_of_b_ne_zero

@[simp]
theorem natDegree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).natDegree = 2 :=
  natDegree_of_b_ne_zero rfl hb
#align cubic.nat_degree_of_b_ne_zero' Cubic.natDegree_of_b_ne_zero'

theorem natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le
  -- 🎉 no goals
#align cubic.nat_degree_of_b_eq_zero Cubic.natDegree_of_b_eq_zero

theorem natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree ≤ 1 :=
  natDegree_of_b_eq_zero rfl rfl
#align cubic.nat_degree_of_b_eq_zero' Cubic.natDegree_of_b_eq_zero'

@[simp]
theorem natDegree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.natDegree = 1 := by
  rw [of_b_eq_zero ha hb, natDegree_linear hc]
  -- 🎉 no goals
#align cubic.nat_degree_of_c_ne_zero Cubic.natDegree_of_c_ne_zero

@[simp]
theorem natDegree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).natDegree = 1 :=
  natDegree_of_c_ne_zero rfl rfl hc
#align cubic.nat_degree_of_c_ne_zero' Cubic.natDegree_of_c_ne_zero'

@[simp]
theorem natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.natDegree = 0 := by
  rw [of_c_eq_zero ha hb hc, natDegree_C]
  -- 🎉 no goals
#align cubic.nat_degree_of_c_eq_zero Cubic.natDegree_of_c_eq_zero

-- @[simp] -- Porting note: simp can prove this
theorem natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0 :=
  natDegree_of_c_eq_zero rfl rfl rfl
#align cubic.nat_degree_of_c_eq_zero' Cubic.natDegree_of_c_eq_zero'

@[simp]
theorem natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0 :=
  natDegree_of_c_eq_zero'
#align cubic.nat_degree_of_zero Cubic.natDegree_of_zero

end Degree

/-! ### Map across a homomorphism -/


section Map

variable [Semiring S] {φ : R →+* S}

/-- Map a cubic polynomial across a semiring homomorphism. -/
def map (φ : R →+* S) (P : Cubic R) : Cubic S :=
  ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩
#align cubic.map Cubic.map

theorem map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  -- 🎉 no goals
#align cubic.map_to_poly Cubic.map_toPoly

end Map

end Basic

section Roots

open Multiset

/-! ### Roots over an extension -/


section Extension

variable {P : Cubic R} [CommRing R] [CommRing S] {φ : R →+* S}

/-- The roots of a cubic polynomial. -/
def roots [IsDomain R] (P : Cubic R) : Multiset R :=
  P.toPoly.roots
#align cubic.roots Cubic.roots

theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  rw [roots, map_toPoly]
  -- 🎉 no goals
#align cubic.map_roots Cubic.map_roots

theorem mem_roots_iff [IsDomain R] (h0 : P.toPoly ≠ 0) (x : R) :
    x ∈ P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [roots, mem_roots h0, IsRoot, toPoly]
  -- ⊢ eval x (↑C P.a * X ^ 3 + ↑C P.b * X ^ 2 + ↑C P.c * X + ↑C P.d) = 0 ↔ P.a * x …
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
  -- 🎉 no goals
#align cubic.mem_roots_iff Cubic.mem_roots_iff

theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  apply (toFinset_card_le P.toPoly.roots).trans
  -- ⊢ ↑card (Polynomial.roots (toPoly P)) ≤ 3
  by_cases hP : P.toPoly = 0
  -- ⊢ ↑card (Polynomial.roots (toPoly P)) ≤ 3
  · exact (card_roots' P.toPoly).trans (by rw [hP, natDegree_zero]; exact zero_le 3)
    -- 🎉 no goals
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)
    -- 🎉 no goals
#align cubic.card_roots_le Cubic.card_roots_le

end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/


section Split

theorem splits_iff_card_roots (ha : P.a ≠ 0) :
    Splits φ P.toPoly ↔ Multiset.card (map φ P).roots = 3 := by
  replace ha : (map φ P).a ≠ 0 := (_root_.map_ne_zero φ).mpr ha
  -- ⊢ Splits φ (toPoly P) ↔ ↑card (roots (map φ P)) = 3
  nth_rw 1 [← RingHom.id_comp φ]
  -- ⊢ Splits (RingHom.comp (RingHom.id K) φ) (toPoly P) ↔ ↑card (roots (map φ P))  …
  rw [roots, ← splits_map_iff, ← map_toPoly, Polynomial.splits_iff_card_roots,
    ← ((degree_eq_iff_natDegree_eq <| ne_zero_of_a_ne_zero ha).1 <| degree_of_a_ne_zero ha : _ = 3)]
#align cubic.splits_iff_card_roots Cubic.splits_iff_card_roots

theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) :
    Splits φ P.toPoly ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} := by
  rw [splits_iff_card_roots ha, card_eq_three]
  -- 🎉 no goals
#align cubic.splits_iff_roots_eq_three Cubic.splits_iff_roots_eq_three

theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    (map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) := by
  rw [map_toPoly,
    eq_prod_roots_of_splits <|
      (splits_iff_roots_eq_three ha).mpr <| Exists.intro x <| Exists.intro y <| Exists.intro z h3,
    leadingCoeff_of_a_ne_zero ha, ← map_roots, h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _
  -- ⊢ ↑C (↑φ P.a) * prod ((X - ↑C x) ::ₘ (X - ↑C y) ::ₘ {X - ↑C z}) = ↑C (↑φ P.a)  …
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]
  -- 🎉 no goals
#align cubic.eq_prod_three_roots Cubic.eq_prod_three_roots

theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    map φ P =
      ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ := by
  apply_fun @toPoly _ _
  -- ⊢ toPoly (map φ P) = toPoly { a := ↑φ P.a, b := ↑φ P.a * -(x + y + z), c := ↑φ …
  · rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
    -- 🎉 no goals
  · exact fun P Q ↦ (toPoly_injective P Q).mp
    -- 🎉 no goals
#align cubic.eq_sum_three_roots Cubic.eq_sum_three_roots

theorem b_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.b = φ P.a * -(x + y + z) := by
  injection eq_sum_three_roots ha h3
  -- 🎉 no goals
#align cubic.b_eq_three_roots Cubic.b_eq_three_roots

theorem c_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.c = φ P.a * (x * y + x * z + y * z) := by
  injection eq_sum_three_roots ha h3
  -- 🎉 no goals
#align cubic.c_eq_three_roots Cubic.c_eq_three_roots

theorem d_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.d = φ P.a * -(x * y * z) := by
  injection eq_sum_three_roots ha h3
  -- 🎉 no goals
#align cubic.d_eq_three_roots Cubic.d_eq_three_roots

end Split

/-! ### Discriminant over a splitting field -/


section Discriminant

/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [Ring R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d
#align cubic.disc Cubic.disc

theorem disc_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.disc = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
  simp only [disc, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, map_pow]
  -- ⊢ ↑φ P.b ^ 2 * ↑φ P.c ^ 2 - ↑φ 4 * ↑φ P.a * ↑φ P.c ^ 3 - ↑φ 4 * ↑φ P.b ^ 3 * ↑ …
  -- Porting note: Replaced `simp only [RingHom.map_one, map_bit0, map_bit1]` with f4, f18, f27
  have f4 : φ 4 = 4 := map_natCast φ 4
  -- ⊢ ↑φ P.b ^ 2 * ↑φ P.c ^ 2 - ↑φ 4 * ↑φ P.a * ↑φ P.c ^ 3 - ↑φ 4 * ↑φ P.b ^ 3 * ↑ …
  have f18 : φ 18 = 18 := map_natCast φ 18
  -- ⊢ ↑φ P.b ^ 2 * ↑φ P.c ^ 2 - ↑φ 4 * ↑φ P.a * ↑φ P.c ^ 3 - ↑φ 4 * ↑φ P.b ^ 3 * ↑ …
  have f27 : φ 27 = 27 := map_natCast φ 27
  -- ⊢ ↑φ P.b ^ 2 * ↑φ P.c ^ 2 - ↑φ 4 * ↑φ P.a * ↑φ P.c ^ 3 - ↑φ 4 * ↑φ P.b ^ 3 * ↑ …
  rw [f4, f18, f27, b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3]
  -- ⊢ (↑φ P.a * -(x + y + z)) ^ 2 * (↑φ P.a * (x * y + x * z + y * z)) ^ 2 - 4 * ↑ …
  ring1
  -- 🎉 no goals
#align cubic.disc_eq_prod_three_roots Cubic.disc_eq_prod_three_roots

theorem disc_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.disc ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  rw [← _root_.map_ne_zero φ, disc_eq_prod_three_roots ha h3, pow_two]
  -- ⊢ ↑φ P.a * ↑φ P.a * (x - y) * (x - z) * (y - z) * (↑φ P.a * ↑φ P.a * (x - y) * …
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self_iff, and_iff_right ha,
    and_assoc]
#align cubic.disc_ne_zero_iff_roots_ne Cubic.disc_ne_zero_iff_roots_ne

theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.disc ≠ 0 ↔ (map φ P).roots.Nodup := by
  rw [disc_ne_zero_iff_roots_ne ha h3, h3]
  -- ⊢ x ≠ y ∧ x ≠ z ∧ y ≠ z ↔ Nodup {x, y, z}
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  -- ⊢ x ≠ y ∧ x ≠ z ∧ y ≠ z ↔ Nodup (x ::ₘ y ::ₘ {z})
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton]
  -- ⊢ x ≠ y ∧ x ≠ z ∧ y ≠ z ↔ ¬(x = y ∨ x = z) ∧ ¬y = z ∧ Nodup {z}
  simp only [nodup_singleton]
  -- ⊢ x ≠ y ∧ x ≠ z ∧ y ≠ z ↔ ¬(x = y ∨ x = z) ∧ ¬y = z ∧ True
  tauto
  -- 🎉 no goals
#align cubic.disc_ne_zero_iff_roots_nodup Cubic.disc_ne_zero_iff_roots_nodup

theorem card_roots_of_disc_ne_zero [DecidableEq K] (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z})
    (hd : P.disc ≠ 0) : (map φ P).roots.toFinset.card = 3 := by
  rw [toFinset_card_of_nodup <| (disc_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← splits_iff_card_roots ha, splits_iff_roots_eq_three ha]
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩
  -- 🎉 no goals
#align cubic.card_roots_of_disc_ne_zero Cubic.card_roots_of_disc_ne_zero

end Discriminant

end Roots

end Cubic
