/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module data.polynomial.mirror
! leanprover-community/mathlib commit 2196ab363eb097c008d4497125e0dde23fb36db2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.NatAntidiagonal
import Mathbin.Data.Polynomial.RingDivision

/-!
# "Mirror" of a univariate polynomial

In this file we define `polynomial.mirror`, a variant of `polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `polynomial.mirror`

## Main results

- `polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/


namespace Polynomial

open Polynomial

section Semiring

variable {R : Type _} [Semiring R] (p q : R[X])

/-- mirror of a polynomial: reverses the coefficients while preserving `polynomial.nat_degree` -/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree
#align polynomial.mirror Polynomial.mirror

@[simp]
theorem mirror_zero : (0 : R[X]).mirror = 0 := by simp [mirror]
#align polynomial.mirror_zero Polynomial.mirror_zero

theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    ·
      rw [mirror, reverse, nat_degree_monomial n a, if_neg ha, nat_trailing_degree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, rev_at_le (le_refl n), tsub_self, pow_zero,
        mul_one]
#align polynomial.mirror_monomial Polynomial.mirror_monomial

theorem mirror_c (a : R) : (C a).mirror = C a :=
  mirror_monomial 0 a
#align polynomial.mirror_C Polynomial.mirror_c

theorem mirror_x : X.mirror = (X : R[X]) :=
  mirror_monomial 1 (1 : R)
#align polynomial.mirror_X Polynomial.mirror_x

theorem mirror_natDegree : p.mirror.natDegree = p.natDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  nontriviality R
  rw [mirror, nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
    tsub_add_cancel_of_le p.nat_trailing_degree_le_nat_degree]
  rwa [leading_coeff_X_pow, mul_one, reverse_leading_coeff, Ne, trailing_coeff_eq_zero]
#align polynomial.mirror_nat_degree Polynomial.mirror_natDegree

theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  ·
    rw [mirror, nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      reverse_nat_trailing_degree, zero_add]
#align polynomial.mirror_nat_trailing_degree Polynomial.mirror_natTrailingDegree

theorem coeff_mirror (n : ℕ) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) :=
  by
  by_cases h2 : p.nat_degree < n
  · rw [coeff_eq_zero_of_nat_degree_lt (by rwa [mirror_nat_degree])]
    by_cases h1 : n ≤ p.nat_degree + p.nat_trailing_degree
    · rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree]
      exact (tsub_lt_iff_left h1).mpr (Nat.add_lt_add_right h2 _)
    · rw [← rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2]
  rw [not_lt] at h2
  rw [rev_at_le (h2.trans (Nat.le_add_right _ _))]
  by_cases h3 : p.nat_trailing_degree ≤ n
  ·
    rw [← tsub_add_eq_add_tsub h2, ← tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow', if_pos h3,
      coeff_reverse, rev_at_le (tsub_le_self.trans h2)]
  rw [not_le] at h3
  rw [coeff_eq_zero_of_nat_degree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_left h3 _))]
  exact coeff_eq_zero_of_lt_nat_trailing_degree (by rwa [mirror_nat_trailing_degree])
#align polynomial.coeff_mirror Polynomial.coeff_mirror

--TODO: Extract `finset.sum_range_rev_at` lemma.
theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 :=
  by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, mirror_nat_degree]
  refine' Finset.sum_bij_ne_zero _ _ _ _ _
  · exact fun n hn hp => rev_at (p.nat_degree + p.nat_trailing_degree) n
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [rev_at_le (hn.trans (Nat.le_add_right _ _))]
    rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right, ← mirror_nat_trailing_degree]
    exact nat_trailing_degree_le_of_ne_zero hp
  · exact fun n₁ n₂ hn₁ hp₁ hn₂ hp₂ h => by rw [← @rev_at_invol _ n₁, h, rev_at_invol]
  · intro n hn hp
    use rev_at (p.nat_degree + p.nat_trailing_degree) n
    refine' ⟨_, _, rev_at_invol.symm⟩
    · rw [Finset.mem_range_succ_iff] at *
      rw [rev_at_le (hn.trans (Nat.le_add_right _ _))]
      rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right]
      exact nat_trailing_degree_le_of_ne_zero hp
    · change p.mirror.coeff _ ≠ 0
      rwa [coeff_mirror, rev_at_invol]
  · exact fun n hn hp => p.coeff_mirror n
#align polynomial.mirror_eval_one Polynomial.mirror_eval_one

theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext fun n => by
    rw [coeff_mirror, coeff_mirror, mirror_nat_degree, mirror_nat_trailing_degree, rev_at_invol]
#align polynomial.mirror_mirror Polynomial.mirror_mirror

variable {p q}

theorem mirror_involutive : Function.Involutive (mirror : R[X] → R[X]) :=
  mirror_mirror
#align polynomial.mirror_involutive Polynomial.mirror_involutive

theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
  mirror_involutive.eq_iff
#align polynomial.mirror_eq_iff Polynomial.mirror_eq_iff

@[simp]
theorem mirror_inj : p.mirror = q.mirror ↔ p = q :=
  mirror_involutive.Injective.eq_iff
#align polynomial.mirror_inj Polynomial.mirror_inj

@[simp]
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩
#align polynomial.mirror_eq_zero Polynomial.mirror_eq_zero

variable (p q)

@[simp]
theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  rw [leading_coeff, trailing_coeff, mirror_nat_trailing_degree, coeff_mirror,
    rev_at_le (Nat.le_add_left _ _), add_tsub_cancel_right]
#align polynomial.mirror_trailing_coeff Polynomial.mirror_trailingCoeff

@[simp]
theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← p.mirror_mirror, mirror_trailing_coeff, p.mirror_mirror]
#align polynomial.mirror_leading_coeff Polynomial.mirror_leadingCoeff

theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.Sum fun n => (· ^ 2) :=
  by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine'
    (Finset.sum_congr rfl fun n hn => _).trans
      (p.sum_eq_of_subset (fun n => (· ^ 2)) (fun n => zero_pow zero_lt_two) _ fun n hn =>
          finset.mem_range_succ_iff.mpr
            ((le_nat_degree_of_mem_supp n hn).trans (Nat.le_add_right _ _))).symm
  rw [coeff_mirror, ← rev_at_le (finset.mem_range_succ_iff.mp hn), rev_at_invol, ← sq]
#align polynomial.coeff_mul_mirror Polynomial.coeff_mul_mirror

variable [NoZeroDivisors R]

theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, MulZeroClass.zero_mul, nat_degree_zero, MulZeroClass.mul_zero]
  rw [nat_degree_mul hp (mt mirror_eq_zero.mp hp), mirror_nat_degree, two_mul]
#align polynomial.nat_degree_mul_mirror Polynomial.natDegree_mul_mirror

theorem natTrailingDegree_mul_mirror : (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, MulZeroClass.zero_mul, nat_trailing_degree_zero, MulZeroClass.mul_zero]
  rw [nat_trailing_degree_mul hp (mt mirror_eq_zero.mp hp), mirror_nat_trailing_degree, two_mul]
#align polynomial.nat_trailing_degree_mul_mirror Polynomial.natTrailingDegree_mul_mirror

end Semiring

section Ring

variable {R : Type _} [Ring R] (p q : R[X])

theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [mirror, mirror, reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]
#align polynomial.mirror_neg Polynomial.mirror_neg

variable [NoZeroDivisors R]

theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror :=
  by
  by_cases hp : p = 0
  · rw [hp, MulZeroClass.zero_mul, mirror_zero, MulZeroClass.zero_mul]
  by_cases hq : q = 0
  · rw [hq, MulZeroClass.mul_zero, mirror_zero, MulZeroClass.mul_zero]
  rw [mirror, mirror, mirror, reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_add]
  rw [mul_assoc, ← mul_assoc q.reverse]
  conv_lhs =>
    congr
    skip
    congr
    rw [← X_pow_mul]
  repeat' rw [mul_assoc]
#align polynomial.mirror_mul_of_domain Polynomial.mirror_mul_of_domain

theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  rw [← C_mul', ← C_mul', mirror_mul_of_domain, mirror_C]
#align polynomial.mirror_smul Polynomial.mirror_smul

end Ring

section CommRing

variable {R : Type _} [CommRing R] [NoZeroDivisors R] {f : R[X]}

theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : ∀ g, g ∣ f → g ∣ f.mirror → IsUnit g) : Irreducible f :=
  by
  constructor
  · exact h1
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror, mul_assoc, mul_comm h,
        mul_comm g.mirror, mul_assoc, ← mul_assoc]
    have g_dvd_f : g ∣ f := by
      rw [fgh]
      exact dvd_mul_right g h
    have h_dvd_f : h ∣ f := by
      rw [fgh]
      exact dvd_mul_left h g
    have g_dvd_k : g ∣ k := dvd_mul_right g h.mirror
    have h_dvd_k_rev : h ∣ k.mirror :=
      by
      rw [mirror_mul_of_domain, mirror_mirror]
      exact dvd_mul_left h g.mirror
    have hk := h2 k key
    rcases hk with (hk | hk | hk | hk)
    · exact Or.inr (h3 h h_dvd_f (by rwa [← hk]))
    · exact Or.inr (h3 h h_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, mirror_neg, dvd_neg]))
    · exact Or.inl (h3 g g_dvd_f (by rwa [← hk]))
    · exact Or.inl (h3 g g_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, dvd_neg]))
#align polynomial.irreducible_of_mirror Polynomial.irreducible_of_mirror

end CommRing

end Polynomial

