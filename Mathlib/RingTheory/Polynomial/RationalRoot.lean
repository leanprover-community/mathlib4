/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.IntegrallyClosed
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Polynomial.ScaleRoots

#align_import ring_theory.polynomial.rational_root from "leanprover-community/mathlib"@"62c0a4ef1441edb463095ea02a06e87f3dfe135c"

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem for a unique factorization domain `A`
with localization `S`, states that the roots of `p : A[X]` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leadingCoeff`.
The corollary is the integral root theorem `isInteger_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

 * https://en.wikipedia.org/wiki/Rational_root_theorem
-/


open scoped Polynomial

section ScaleRoots

variable {A K R S : Type*} [CommRing A] [Field K] [CommRing R] [CommRing S]

variable {M : Submonoid A} [Algebra A S] [IsLocalization M S] [Algebra A K] [IsFractionRing A K]

open Finsupp IsFractionRing IsLocalization Polynomial

theorem scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : A[X]} {r : A} {s : M}
    (hr : aeval (mk' S r s) p = 0) : aeval (algebraMap A S r) (scaleRoots p s) = 0 := by
  convert scaleRoots_eval₂_eq_zero (algebraMap A S) hr
  -- ⊢ ↑(aeval (↑(algebraMap A S) r)) = eval₂ (algebraMap A S) (↑(algebraMap A S) ↑ …
  -- Porting note: added
  funext
  -- ⊢ ↑(aeval (↑(algebraMap A S) r)) x✝ = eval₂ (algebraMap A S) (↑(algebraMap A S …
  rw [aeval_def, mk'_spec' _ r s]
  -- 🎉 no goals
#align scale_roots_aeval_eq_zero_of_aeval_mk'_eq_zero scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero

variable [IsDomain A]

theorem num_isRoot_scaleRoots_of_aeval_eq_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K}
    (hr : aeval x p = 0) : IsRoot (scaleRoots p (den A x)) (num A x) := by
  apply isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  -- ⊢ eval₂ (algebraMap A K) (↑(algebraMap A K) (num A x)) (scaleRoots p ↑(den A x …
  refine' scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero _
  -- ⊢ ↑(aeval (mk' K (num A x) (den A x))) p = 0
  rw [mk'_num_den]
  -- ⊢ ↑(aeval x) p = 0
  exact hr
  -- 🎉 no goals
#align num_is_root_scale_roots_of_aeval_eq_zero num_isRoot_scaleRoots_of_aeval_eq_zero

end ScaleRoots

section RationalRootTheorem

variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]

variable [Algebra A K] [IsFractionRing A K]

open IsFractionRing IsLocalization Polynomial UniqueFactorizationMonoid

/-- Rational root theorem part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
theorem num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : num A r ∣ p.coeff 0 := by
  suffices num A r ∣ (scaleRoots p (den A r)).coeff 0 by
    simp only [coeff_scaleRoots, tsub_zero] at this
    haveI inst := Classical.propDecidable
    by_cases hr : num A r = 0
    · obtain ⟨u, hu⟩ := (isUnit_den_of_num_eq_zero hr).pow p.natDegree
      rw [← hu] at this
      exact Units.dvd_mul_right.mp this
    · refine' dvd_of_dvd_mul_left_of_no_prime_factors hr _ this
      intro q dvd_num dvd_denom_pow hq
      apply hq.not_unit
      exact num_den_reduced A r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow)
  convert dvd_term_of_isRoot_of_dvd_terms 0 (num_isRoot_scaleRoots_of_aeval_eq_zero hr) _
  -- ⊢ coeff (scaleRoots p ↑(den A r)) 0 = coeff (scaleRoots p ↑(den A r)) 0 * num  …
  · rw [pow_zero, mul_one]
    -- 🎉 no goals
  intro j hj
  -- ⊢ num A r ∣ coeff (scaleRoots p ↑(den A r)) j * num A r ^ j
  apply dvd_mul_of_dvd_right
  -- ⊢ num A r ∣ num A r ^ j
  convert pow_dvd_pow (num A r) (Nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj))
  -- ⊢ num A r = num A r ^ Nat.succ ⊥
  exact (pow_one _).symm
  -- 🎉 no goals
#align num_dvd_of_is_root num_dvd_of_is_root

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
theorem den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    (den A r : A) ∣ p.leadingCoeff := by
  suffices (den A r : A) ∣ p.leadingCoeff * num A r ^ p.natDegree by
    refine'
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_nonZeroDivisors_iff_ne_zero.mp (den A r).2) _
        this
    intro q dvd_den dvd_num_pow hq
    apply hq.not_unit
    exact num_den_reduced A r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_den
  rw [← coeff_scaleRoots_natDegree]
  -- ⊢ ↑(den A r) ∣ coeff (scaleRoots p ?s) (natDegree p) * num A r ^ natDegree p
  apply dvd_term_of_isRoot_of_dvd_terms _ (num_isRoot_scaleRoots_of_aeval_eq_zero hr)
  -- ⊢ ∀ (j : ℕ), j ≠ natDegree p → ↑(den A r) ∣ coeff (scaleRoots p ↑(den A r)) j  …
  intro j hj
  -- ⊢ ↑(den A r) ∣ coeff (scaleRoots p ↑(den A r)) j * num A r ^ j
  by_cases h : j < p.natDegree
  -- ⊢ ↑(den A r) ∣ coeff (scaleRoots p ↑(den A r)) j * num A r ^ j
  · rw [coeff_scaleRoots]
    -- ⊢ ↑(den A r) ∣ coeff p j * ↑(den A r) ^ (natDegree p - j) * num A r ^ j
    refine' (dvd_mul_of_dvd_right _ _).mul_right _
    -- ⊢ ↑(den A r) ∣ ↑(den A r) ^ (natDegree p - j)
    convert pow_dvd_pow (den A r : A) (Nat.succ_le_iff.mpr (lt_tsub_iff_left.mpr _))
    · exact (pow_one _).symm
      -- 🎉 no goals
    simpa using h
    -- 🎉 no goals
  rw [← natDegree_scaleRoots p (den A r)] at *
  -- ⊢ ↑(den A r) ∣ coeff (scaleRoots p ↑(den A r)) j * num A r ^ j
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (le_of_not_gt h) hj.symm),
    zero_mul]
  exact dvd_zero _
  -- 🎉 no goals
#align denom_dvd_of_is_root den_dvd_of_is_root

/-- Integral root theorem:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
theorem isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    IsInteger A r :=
  isInteger_of_isUnit_den (isUnit_of_dvd_one (hp ▸ den_dvd_of_is_root hr))
#align is_integer_of_is_root_of_monic isInteger_of_is_root_of_monic

namespace UniqueFactorizationMonoid

theorem integer_of_integral {x : K} : IsIntegral A x → IsInteger A x := fun ⟨_, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx
#align unique_factorization_monoid.integer_of_integral UniqueFactorizationMonoid.integer_of_integral

-- See library note [lower instance priority]
instance (priority := 100) instIsIntegrallyClosed : IsIntegrallyClosed A :=
  ⟨fun {_} => integer_of_integral⟩
#align unique_factorization_monoid.is_integrally_closed UniqueFactorizationMonoid.instIsIntegrallyClosed

end UniqueFactorizationMonoid

end RationalRootTheorem
