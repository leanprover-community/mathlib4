/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Rational root theorem (for usual rational numbers and integers)

This file contains specialization of the rational root theorem -
to use with usual rational numbers and integers.
It (`num_dvd_of_is_root_standard_case` and `den_dvd_of_is_root_standard_case`)
states that for any `p : ℤ[X]` any rational root `r : ℚ` of polynomial
`p.map (Int.castRingHom ℚ)` are such that `r.den ∣ p.leadingCoeff.natAbs`
and `r.num.natAbs ∣ (p.coeff 0).natAbs`.

The file also contains the corresponding integral root theorem for integers
(`root_dvd_of_is_root_of_monic_standard_case`).

## References

 * https://en.wikipedia.org/wiki/Rational_root_theorem
-/

open Polynomial

lemma rat_as_divInt_in_fraction_ring (r : ℚ) :
    r = Rat.divInt (IsFractionRing.num ℤ r : ℤ) (IsFractionRing.den ℤ r : ℤ) := by
  nth_rw 1 [<- IsFractionRing.mk'_num_den ℤ r]
  simp only [IsFractionRing.mk'_eq_div, algebraMap_int_eq, eq_intCast]
  norm_cast

lemma rat_eq_divInt_of_relprimes_aux {r : ℚ} {a b : ℤ}
    (Hb : 0 < b) (H : IsRelPrime a b) (H0 : r = Rat.divInt a b) :
    r.num = a ∧ (r.den : ℤ) = b := by
  apply Rat.div_int_inj (Int.ofNat_lt.mpr (Rat.den_pos r)) Hb r.reduced
  · rw [Nat.Coprime, <- Int.gcd_eq_natAbs]
    rw [<- gcd_isUnit_iff_isRelPrime, Int.isUnit_iff] at H
    simp only [Int.reduceNeg, reduceCtorEq, or_false] at H
    exact (Int.ofNat_inj.mp H)
  · rw [Int.cast_natCast, H0, Rat.num_div_den, Rat.intCast_div_eq_divInt]

lemma nonzero_rat_eq_divInt_of_relprimes {r : ℚ} {a b : ℤ}
    (Hr : r ≠ 0) (H : IsRelPrime a b) (H0 : r = Rat.divInt a b) :
    r.num.natAbs = a.natAbs ∧ r.den = b.natAbs := by
  obtain H1 | H1 | H1 := Int.lt_trichotomy b 0
  · have H2 : r = Rat.divInt (-a) (-b) := by rw [Rat.divInt_neg, neg_neg]; exact H0
    have H3 := rat_eq_divInt_of_relprimes_aux (Int.neg_pos_of_neg H1) (IsRelPrime.neg_neg H) H2
    omega
  · subst b; simp only [Rat.divInt_zero] at H0; exact (Hr H0).elim
  · have H2 := rat_eq_divInt_of_relprimes_aux H1 H H0
    omega

lemma rat_num_abs_and_den_in_fraction_ring (r : ℚ) :
    r.num.natAbs = (IsFractionRing.num ℤ r : ℤ).natAbs ∧
    r.den = (IsFractionRing.den ℤ r : ℤ).natAbs := by
  obtain H | H := eq_or_ne r 0
  · subst r
    simp only [Rat.num_ofNat, Int.natAbs_zero, IsFractionRing.num_zero, Rat.den_ofNat, true_and]
    have H0 := IsFractionRing.isUnit_den_zero (A := ℤ) (K := ℚ)
    obtain H0 | H0 := Int.isUnit_iff.mp H0 <;> simp [H0]
  · exact (nonzero_rat_eq_divInt_of_relprimes H
           (IsFractionRing.num_den_reduced ℤ r) (rat_as_divInt_in_fraction_ring r))

lemma aeval_eq_zero_of_eval_eq_zero {p : ℤ[X]} {r : ℚ}
    (H : eval r (p.map (Int.castRingHom ℚ)) = 0) :
    p.aeval r = 0 := by
  rw [<- eval_map_algebraMap, algebraMap_int_eq]; exact H

/-- **Rational root theorem**, part 1 -/
theorem den_dvd_of_is_root_standard_case {p : ℤ[X]} {r : ℚ}
    (H : r ∈ (p.map (Int.castRingHom ℚ)).roots) :
    r.den ∣ p.leadingCoeff.natAbs := by
  simp only [mem_roots', ne_eq, IsRoot.def] at H; obtain ⟨H, H0⟩ := H
  obtain ⟨d, H1⟩ := den_dvd_of_is_root (aeval_eq_zero_of_eval_eq_zero H0)
  rw [H1, Int.natAbs_mul, (rat_num_abs_and_den_in_fraction_ring r).2]
  apply dvd_mul_right

/-- **Rational root theorem**, part 2 -/
theorem num_dvd_of_is_root_standard_case {p : ℤ[X]} {r : ℚ}
    (H : r ∈ (p.map (Int.castRingHom ℚ)).roots) :
    r.num.natAbs ∣ (p.coeff 0).natAbs := by
  simp only [mem_roots', ne_eq, IsRoot.def] at H
  simp [Int.natAbs_dvd_natAbs]
  obtain ⟨H, H0⟩ := H
  obtain ⟨d, H1⟩ := num_dvd_of_is_root (aeval_eq_zero_of_eval_eq_zero H0)
  rw [H1, <- Int.sign_mul_natAbs r.num, <- Int.sign_mul_natAbs (IsFractionRing.num ℤ r),
      (rat_num_abs_and_den_in_fraction_ring r).1]
  use (d * (IsFractionRing.num ℤ r).sign * r.num.sign)
  ring_nf
  obtain H2 | H2 | H2 := Int.lt_trichotomy r.num 0
  · simp [Int.sign_eq_neg_one_iff_neg.mpr H2]
  · simp only [Rat.num_eq_zero] at H2; subst r; simp
  · simp [Int.sign_eq_one_iff_pos.mpr H2]

/-- **Integral root theorem** -/
theorem root_dvd_of_is_root_of_monic_standard_case {p : ℤ[X]} {n: ℤ}
    (H : p.Monic) (H0 : n ∈ p.roots) :
    n.natAbs ∣ (p.coeff 0).natAbs := by
  have H1 : (n : ℚ) ∈ (p.map (Int.castRingHom ℚ)).roots := by
    simp only [mem_roots', ne_eq, IsRoot.def] at H0
    simp [map_monic_ne_zero H, H0.2]
  have H2 : (n : ℚ).num = n := by rfl
  rw [<- H2]
  exact num_dvd_of_is_root_standard_case H1


--- Example of use

example (r : ℚ) (H : r ∈ (2 * X ^ 3 + 3 * X ^ 2 - 3 : ℚ[X]).roots) :
    r.den ∣ 2 ∧ r.num.natAbs ∣ 3 := by
  have H0 : (2 * X ^ 3 + 3 * X ^ 2 - 3 : ℚ[X]) =
            (2 * X ^ 3 + 3 * X ^ 2 - 3 : ℤ[X]).map (Int.castRingHom ℚ) := by simp
  have H1 : (2 * X ^ 3 + 3 * X ^ 2 - 3: ℤ[X]).natDegree = 3 := by compute_degree!
  rw [H0] at H; constructor
  · apply den_dvd_of_is_root_standard_case at H
    unfold leadingCoeff at H; rw [H1] at H; simp at H; exact H
  · apply num_dvd_of_is_root_standard_case at H
    simp at H; exact H
