/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module ring_theory.polynomial.rational_root
! leanprover-community/mathlib commit 62c0a4ef1441edb463095ea02a06e87f3dfe135c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.IntegrallyClosed
import Mathlib.RingTheory.Localization.NumDenom
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem for a unique factorization domain `A`
with localization `S`, states that the roots of `p : A[X]` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leading_coeff`.
The corollary is the integral root theorem `is_integer_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

 * https://en.wikipedia.org/wiki/Rational_root_theorem
-/


open scoped Polynomial

section ScaleRoots

variable {A K R S : Type _} [CommRing A] [Field K] [CommRing R] [CommRing S]

variable {M : Submonoid A} [Algebra A S] [IsLocalization M S] [Algebra A K] [IsFractionRing A K]

open Finsupp IsFractionRing IsLocalization Polynomial

theorem scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : A[X]} {r : A} {s : M}
    (hr : aeval (mk' S r s) p = 0) : aeval (algebraMap A S r) (scaleRoots p s) = 0 := by
  convert scale_roots_eval₂_eq_zero (algebraMap A S) hr
  rw [aeval_def, mk'_spec' _ r s]
#align scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero

variable [IsDomain A]

theorem num_isRoot_scaleRoots_of_aeval_eq_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K}
    (hr : aeval x p = 0) : IsRoot (scaleRoots p (den A x)) (Num A x) := by
  apply is_root_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  refine' scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero _
  rw [mk'_num_denom]
  exact hr
#align num_is_root_scale_roots_of_aeval_eq_zero num_isRoot_scaleRoots_of_aeval_eq_zero

end ScaleRoots

section RationalRootTheorem

variable {A K : Type _} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]

variable [Algebra A K] [IsFractionRing A K]

open IsFractionRing IsLocalization Polynomial UniqueFactorizationMonoid

/-- Rational root theorem part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
theorem num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : Num A r ∣ p.coeff 0 := by
  suffices Num A r ∣ (scale_roots p (denom A r)).coeff 0 by
    simp only [coeff_scale_roots, tsub_zero] at this 
    haveI := Classical.propDecidable
    by_cases hr : Num A r = 0
    · obtain ⟨u, hu⟩ := (is_unit_denom_of_num_eq_zero hr).pow p.nat_degree
      rw [← hu] at this 
      exact units.dvd_mul_right.mp this
    · refine' dvd_of_dvd_mul_left_of_no_prime_factors hr _ this
      intro q dvd_num dvd_denom_pow hq
      apply hq.not_unit
      exact num_denom_reduced A r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow)
  convert dvd_term_of_is_root_of_dvd_terms 0 (num_isRoot_scaleRoots_of_aeval_eq_zero hr) _
  · rw [pow_zero, mul_one]
  intro j hj
  apply dvd_mul_of_dvd_right
  convert pow_dvd_pow (Num A r) (Nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj))
  exact (pow_one _).symm
#align num_dvd_of_is_root num_dvd_of_is_root

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
theorem den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    (den A r : A) ∣ p.leadingCoeff := by
  suffices (denom A r : A) ∣ p.leading_coeff * Num A r ^ p.nat_degree by
    refine'
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_non_zero_divisors_iff_ne_zero.mp (denom A r).2) _
        this
    intro q dvd_denom dvd_num_pow hq
    apply hq.not_unit
    exact num_denom_reduced A r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_denom
  rw [← coeff_scale_roots_nat_degree]
  apply dvd_term_of_is_root_of_dvd_terms _ (num_isRoot_scaleRoots_of_aeval_eq_zero hr)
  intro j hj
  by_cases h : j < p.nat_degree
  · rw [coeff_scale_roots]
    refine' (dvd_mul_of_dvd_right _ _).mul_right _
    convert pow_dvd_pow _ (nat.succ_le_iff.mpr (lt_tsub_iff_left.mpr _))
    · exact (pow_one _).symm
    simpa using h
  rw [← nat_degree_scale_roots p (denom A r)] at *
  rw [coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_ne (le_of_not_gt h) hj.symm),
    MulZeroClass.zero_mul]
  exact dvd_zero _
#align denom_dvd_of_is_root den_dvd_of_is_root

/-- Integral root theorem:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
theorem isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    IsInteger A r :=
  isInteger_of_isUnit_den (isUnit_of_dvd_one _ (hp ▸ den_dvd_of_is_root hr))
#align is_integer_of_is_root_of_monic isInteger_of_is_root_of_monic

namespace UniqueFactorizationMonoid

theorem integer_of_integral {x : K} : IsIntegral A x → IsInteger A x := fun ⟨p, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx
#align unique_factorization_monoid.integer_of_integral UniqueFactorizationMonoid.integer_of_integral

-- See library note [lower instance priority]
instance (priority := 100) : IsIntegrallyClosed A :=
  ⟨fun x => integer_of_integral⟩

end UniqueFactorizationMonoid

end RationalRootTheorem

