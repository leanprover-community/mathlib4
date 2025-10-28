/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.IntervalCases

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

* `Cubic`: the structure representing a cubic polynomial.
* `Cubic.discr`: the discriminant of a cubic polynomial.

## Main statements

* `Cubic.discr_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
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
  /-- The degree-3 coefficient -/
  a : R
  /-- The degree-2 coefficient -/
  b : R
  /-- The degree-1 coefficient -/
  c : R
  /-- The degree-0 coefficient -/
  d : R

namespace Cubic

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

theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    C w * (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  simp only [toPoly, C_neg, C_add, C_mul]
  ring1

theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  rw [← one_mul <| X - C x, ← C_1, C_mul_prod_X_sub_C_eq, one_mul, one_mul, one_mul]

/-! ### Coefficients -/


section Coeff

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [toPoly, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num
  intro n hn
  repeat' rw [if_neg]
  any_goals cutsat
  repeat' rw [zero_add]

@[simp]
theorem coeff_eq_zero {n : ℕ} (hn : 3 < n) : P.toPoly.coeff n = 0 :=
  coeffs.1 n hn

@[simp]
theorem coeff_eq_a : P.toPoly.coeff 3 = P.a :=
  coeffs.2.1

@[simp]
theorem coeff_eq_b : P.toPoly.coeff 2 = P.b :=
  coeffs.2.2.1

@[simp]
theorem coeff_eq_c : P.toPoly.coeff 1 = P.c :=
  coeffs.2.2.2.1

@[simp]
theorem coeff_eq_d : P.toPoly.coeff 0 = P.d :=
  coeffs.2.2.2.2

theorem a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]

theorem b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]

theorem c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]

theorem d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]

theorem toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q :=
  ⟨fun h ↦ Cubic.ext (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩

theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d := by
  rw [toPoly, ha, C_0, zero_mul, zero_add]

theorem of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d :=
  of_a_eq_zero rfl

theorem of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d := by
  rw [of_a_eq_zero ha, hb, C_0, zero_mul, zero_add]

theorem of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d :=
  of_b_eq_zero rfl rfl

theorem of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P.d := by
  rw [of_b_eq_zero ha hb, hc, C_0, zero_mul, zero_add]

theorem of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d :=
  of_c_eq_zero rfl rfl rfl

theorem of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly = 0 := by
  rw [of_c_eq_zero ha hb hc, hd, C_0]

theorem of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0 :=
  of_d_eq_zero rfl rfl rfl rfl

theorem zero : (0 : Cubic R).toPoly = 0 :=
  of_d_eq_zero'

theorem toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero, toPoly_injective]

private theorem ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  rw [(toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp ne_zero).1 ha

theorem ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp ne_zero).2).1 hb

theorem ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).1 hc

theorem ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.toPoly ≠ 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).2 hd

@[simp]
theorem leadingCoeff_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.leadingCoeff = P.a :=
  leadingCoeff_cubic ha

theorem leadingCoeff_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).leadingCoeff = a := by
  simp [ha]

@[simp]
theorem leadingCoeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.leadingCoeff = P.b := by
  rw [of_a_eq_zero ha, leadingCoeff_quadratic hb]

theorem leadingCoeff_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).leadingCoeff = b := by
  simp [hb]

@[simp]
theorem leadingCoeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.leadingCoeff = P.c := by
  rw [of_b_eq_zero ha hb, leadingCoeff_linear hc]

theorem leadingCoeff_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c := by
  simp [hc]

@[simp]
theorem leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.leadingCoeff = P.d := by
  rw [of_c_eq_zero ha hb hc, leadingCoeff_C]

theorem leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d :=
  leadingCoeff_of_c_eq_zero rfl rfl rfl

theorem monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero), ha]

theorem monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic :=
  monic_of_a_eq_one rfl

theorem monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero), hb]

theorem monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic :=
  monic_of_b_eq_one rfl rfl

theorem monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic, leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero), hc]

theorem monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic :=
  monic_of_c_eq_one rfl rfl rfl

theorem monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
    P.toPoly.Monic := by
  rw [Monic, leadingCoeff_of_c_eq_zero ha hb hc, hd]

theorem monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic :=
  monic_of_d_eq_one rfl rfl rfl rfl

end Coeff

/-! ### Degrees -/


section Degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
@[simps]
def equiv : Cubic R ≃ { p : R[X] // p.degree ≤ 3 } where
  toFun P := ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [coeffs]
  right_inv f := by
    ext n
    obtain hn | hn := le_or_gt n 3
    · interval_cases n <;> simp only <;> ring_nf <;> try simp only [coeffs]
    · rw [coeff_eq_zero hn, (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2]
      simpa using hn

@[simp]
theorem degree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.degree = 3 :=
  degree_cubic ha

theorem degree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).degree = 3 := by
  simp [ha]

theorem degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le

theorem degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree ≤ 2 :=
  degree_of_a_eq_zero rfl

@[simp]
theorem degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.degree = 2 := by
  rw [of_a_eq_zero ha, degree_quadratic hb]

theorem degree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).degree = 2 := by
  simp [hb]

theorem degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le

theorem degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree ≤ 1 :=
  degree_of_b_eq_zero rfl rfl

@[simp]
theorem degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.toPoly.degree = 1 := by
  rw [of_b_eq_zero ha hb, degree_linear hc]

theorem degree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).degree = 1 := by
  simp [hc]

theorem degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.degree ≤ 0 := by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le

theorem degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree ≤ 0 :=
  degree_of_c_eq_zero rfl rfl rfl

@[simp]
theorem degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
    P.toPoly.degree = 0 := by
  rw [of_c_eq_zero ha hb hc, degree_C hd]

theorem degree_of_d_ne_zero' (hd : d ≠ 0) : (toPoly ⟨0, 0, 0, d⟩).degree = 0 := by
  simp [hd]

@[simp]
theorem degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly.degree = ⊥ := by
  rw [of_d_eq_zero ha hb hc hd, degree_zero]

theorem degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero rfl rfl rfl rfl

@[simp]
theorem degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero'

@[simp]
theorem natDegree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.natDegree = 3 :=
  natDegree_cubic ha

theorem natDegree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).natDegree = 3 := by
  simp [ha]

theorem natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree ≤ 2 := by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le

theorem natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree ≤ 2 :=
  natDegree_of_a_eq_zero rfl

@[simp]
theorem natDegree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.natDegree = 2 := by
  rw [of_a_eq_zero ha, natDegree_quadratic hb]

theorem natDegree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).natDegree = 2 := by
  simp [hb]

theorem natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree ≤ 1 := by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le

theorem natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree ≤ 1 :=
  natDegree_of_b_eq_zero rfl rfl

@[simp]
theorem natDegree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.natDegree = 1 := by
  rw [of_b_eq_zero ha hb, natDegree_linear hc]

theorem natDegree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).natDegree = 1 := by
  simp [hc]

@[simp]
theorem natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.natDegree = 0 := by
  rw [of_c_eq_zero ha hb hc, natDegree_C]

theorem natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0 :=
  natDegree_of_c_eq_zero rfl rfl rfl

@[simp]
theorem natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0 :=
  natDegree_of_c_eq_zero'

end Degree

/-! ### Map across a homomorphism -/


section Map

variable [Semiring S] {φ : R →+* S}

/-- Map a cubic polynomial across a semiring homomorphism. -/
def map (φ : R →+* S) (P : Cubic R) : Cubic S :=
  ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

theorem map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

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

theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  rw [roots, map_toPoly]

theorem mem_roots_iff [IsDomain R] (h0 : P.toPoly ≠ 0) (x : R) :
    x ∈ P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [roots, mem_roots h0, IsRoot, toPoly]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]

theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · exact (card_roots' P.toPoly).trans (by rw [hP, natDegree_zero]; exact zero_le 3)
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/


section Split

theorem splits_iff_card_roots (ha : P.a ≠ 0) :
    Splits φ P.toPoly ↔ Multiset.card (map φ P).roots = 3 := by
  replace ha : (map φ P).a ≠ 0 := (_root_.map_ne_zero φ).mpr ha
  nth_rw 1 [← RingHom.id_comp φ]
  rw [roots, ← splits_map_iff, ← map_toPoly, Polynomial.splits_iff_card_roots,
    ← ((degree_eq_iff_natDegree_eq <| ne_zero_of_a_ne_zero ha).1 <| degree_of_a_ne_zero ha : _ = 3)]

theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) :
    Splits φ P.toPoly ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} := by
  rw [splits_iff_card_roots ha, card_eq_three]

theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    (map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) := by
  rw [map_toPoly,
    eq_prod_roots_of_splits <|
      (splits_iff_roots_eq_three ha).mpr <| Exists.intro x <| Exists.intro y <| Exists.intro z h3,
    leadingCoeff_of_a_ne_zero ha, ← map_roots, h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _
  rw [prod_cons, prod_cons, prod_singleton, mul_assoc, mul_assoc]

theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    map φ P =
      ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ := by
  apply_fun @toPoly _ _
  · rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
  · exact fun P Q ↦ (toPoly_injective P Q).mp

theorem b_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.b = φ P.a * -(x + y + z) := by
  injection eq_sum_three_roots ha h3

theorem c_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.c = φ P.a * (x * y + x * z + y * z) := by
  injection eq_sum_three_roots ha h3

theorem d_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.d = φ P.a * -(x * y * z) := by
  injection eq_sum_three_roots ha h3

end Split

/-! ### Discriminant over a splitting field -/


section Discriminant

/-- The discriminant of a cubic polynomial. -/
def discr {R : Type*} [Ring R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d

theorem discr_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.discr = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
  simp only [discr, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, map_pow, map_ofNat]
  rw [b_eq_three_roots ha h3, c_eq_three_roots ha h3, d_eq_three_roots ha h3]
  ring1

theorem discr_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.discr ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  rw [← _root_.map_ne_zero φ, discr_eq_prod_three_roots ha h3, pow_two]
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self_iff, and_iff_right ha,
    and_assoc]

theorem discr_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.discr ≠ 0 ↔ (map φ P).roots.Nodup := by
  rw [discr_ne_zero_iff_roots_ne ha h3, h3]
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  rw [nodup_cons, nodup_cons, mem_cons, mem_singleton, mem_singleton]
  simp only [nodup_singleton]
  tauto

theorem card_roots_of_discr_ne_zero [DecidableEq K] (ha : P.a ≠ 0)
    (h3 : (map φ P).roots = {x, y, z}) (hd : P.discr ≠ 0) : (map φ P).roots.toFinset.card = 3 := by
  rw [toFinset_card_of_nodup <| (discr_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← splits_iff_card_roots ha, splits_iff_roots_eq_three ha]
  exact ⟨x, ⟨y, ⟨z, h3⟩⟩⟩

@[deprecated (since := "2025-10-20")] alias disc := discr
@[deprecated (since := "2025-10-20")] alias disc_eq_prod_three_roots := discr_eq_prod_three_roots
@[deprecated (since := "2025-10-20")] alias disc_ne_zero_iff_roots_ne := discr_ne_zero_iff_roots_ne
@[deprecated (since := "2025-10-20")] alias disc_ne_zero_iff_roots_nodup :=
  discr_ne_zero_iff_roots_nodup
@[deprecated (since := "2025-10-20")] alias card_roots_of_disc_ne_zero :=
  card_roots_of_discr_ne_zero

end Discriminant

end Roots

end Cubic
