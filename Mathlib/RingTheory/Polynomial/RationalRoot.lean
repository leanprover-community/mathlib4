/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Owen Kent
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem (`num_dvd_of_is_root` and `den_dvd_of_is_root`)
for a unique factorization domain `A`
with localization `S`, states that the roots of `p : A[X]` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leadingCoeff`.
The corollary is the integral root theorem `isInteger_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.
We also prove the generalization to root multiplicity: if `r` is a root of `p` with multiplicity
`m`, then `(den A r) ^ m ∣ p.leadingCoeff` (`den_pow_rootMultiplicity_dvd_leadingCoeff`), together
with the multi-point product form over a finite set of points
(`prod_den_pow_rootMultiplicity_dvd_leadingCoeff`). Both descend from the `A[X]`-level divisibility
`den_mul_X_sub_C_num_pow_rootMultiplicity_dvd`.

## References

* https://en.wikipedia.org/wiki/Rational_root_theorem
-/

public section


open scoped Polynomial

section ScaleRoots

variable {A K S : Type*} [CommRing A] [Field K] [CommRing S]
variable {M : Submonoid A} [Algebra A S] [IsLocalization M S] [Algebra A K] [IsFractionRing A K]

open IsFractionRing IsLocalization Polynomial

theorem scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : A[X]} {r : A} {s : M}
    (hr : aeval (mk' S r s) p = 0) : aeval (algebraMap A S r) (scaleRoots p s) = 0 := by
  convert! scaleRoots_eval₂_eq_zero (algebraMap A S) hr
  funext
  rw [aeval_def, mk'_spec' _ r s]

variable [IsDomain A]

theorem num_isRoot_scaleRoots_of_aeval_eq_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K}
    (hr : aeval x p = 0) : IsRoot (scaleRoots p (den A x)) (num A x) := by
  apply isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  refine scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero ?_
  rw [mk'_num_den]
  exact hr

end ScaleRoots

section RationalRootTheorem

variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]
variable [Algebra A K] [IsFractionRing A K]

open IsFractionRing IsLocalization Polynomial UniqueFactorizationMonoid

/-- **Rational root theorem** part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
theorem num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : num A r ∣ p.coeff 0 := by
  suffices num A r ∣ (scaleRoots p (den A r)).coeff 0 by
    simp only [coeff_scaleRoots] at this
    have inst := Classical.propDecidable
    by_cases hr : num A r = 0
    · simp_all [nonZeroDivisors.coe_ne_zero]
    · refine dvd_of_dvd_mul_left_of_no_prime_factors hr ?_ this
      intro q dvd_num dvd_denom_pow hq
      apply hq.not_isUnit
      exact num_den_reduced A r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow)
  convert! dvd_term_of_isRoot_of_dvd_terms 0 (num_isRoot_scaleRoots_of_aeval_eq_zero hr) _
  · rw [pow_zero, mul_one]
  intro j hj
  apply dvd_mul_of_dvd_right
  convert! pow_dvd_pow (num A r) (Nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj))
  exact (pow_one _).symm

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
theorem den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    (den A r : A) ∣ p.leadingCoeff := by
  suffices (den A r : A) ∣ p.leadingCoeff * num A r ^ p.natDegree by
    refine
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_nonZeroDivisors_iff_ne_zero.mp (den A r).2) ?_
        this
    intro q dvd_den dvd_num_pow hq
    apply hq.not_isUnit
    exact num_den_reduced A r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_den
  rw [← coeff_scaleRoots_natDegree]
  apply dvd_term_of_isRoot_of_dvd_terms _ (num_isRoot_scaleRoots_of_aeval_eq_zero hr)
  intro j hj
  by_cases! h : j < p.natDegree
  · rw [coeff_scaleRoots]
    refine (dvd_mul_of_dvd_right ?_ _).mul_right _
    convert! pow_dvd_pow (den A r : A) (Nat.succ_le_iff.mpr (lt_tsub_iff_left.mpr _))
    · exact (pow_one _).symm
    simpa using h
  rw [← natDegree_scaleRoots p (den A r)] at *
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h hj.symm),
    zero_mul]
  exact dvd_zero _

/-- **Integral root theorem**:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
theorem isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    IsInteger A r :=
  isInteger_of_isUnit_den (isUnit_of_dvd_one (hp ▸ den_dvd_of_is_root hr))

theorem exists_integer_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    ∃ r' : A, r = algebraMap A K r' ∧ r' ∣ p.coeff 0 := by
  /- I tried deducing this from above by unwrapping IsInteger,
    but the divisibility condition is annoying -/
  obtain ⟨inv, h_inv⟩ := hp ▸ den_dvd_of_is_root hr
  use num A r * inv, ?_
  · have h : inv ∣ 1 := ⟨den A r, by simpa [mul_comm] using h_inv⟩
    simpa using mul_dvd_mul (num_dvd_of_is_root hr) h
  · have d_ne_zero : algebraMap A K (den A r) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A r).prop
    nth_rw 1 [← mk'_num_den' A r]
    rw [div_eq_iff d_ne_zero, map_mul, mul_assoc, mul_comm ((algebraMap A K) inv),
      ← map_mul, ← h_inv, map_one, mul_one]

/-! ### Rational root theorem with multiplicity -/

/-- The reduced linear factor `C (den A r) * X - C (num A r)` of `r : K` is primitive.
A constant divisor of it divides both `den A r` (the coefficient of `X`) and `num A r`
(up to sign, the constant coefficient), so it is a unit by `num_den_reduced`. -/
private theorem isPrimitive_den_mul_X_sub_C_num (r : K) :
    (C (den A r : A) * X - C (num A r)).IsPrimitive := by
  intro c hc
  have h1 : c ∣ (den A r : A) := by
    have h := (C_dvd_iff_dvd_coeff c _).mp hc 1
    simpa using h
  have h0 : c ∣ num A r := by
    have h := (C_dvd_iff_dvd_coeff c _).mp hc 0
    simpa using h
  exact num_den_reduced A r h0 h1

/-- Over `K`, the reduced linear factor of `r` is the unit multiple
`C (den A r) * (X - C r)` of the root factor at `r`. -/
private theorem map_den_mul_X_sub_C_num (r : K) :
    (C (den A r : A) * X - C (num A r)).map (algebraMap A K)
      = C (algebraMap A K (den A r : A)) * (X - C r) := by
  have hden0 : algebraMap A K (den A r : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A r).2
  have hnum : algebraMap A K (num A r) = r * algebraMap A K (den A r : A) :=
    (div_eq_iff hden0).mp (mk'_num_den' A r)
  rw [Polynomial.map_sub, Polynomial.map_mul, map_C, map_C, Polynomial.map_X,
    hnum, C_mul]
  ring

/-- The leading coefficient of the reduced linear factor is `den A r`. -/
private theorem leadingCoeff_den_mul_X_sub_C_num (r : K) :
    (C (den A r : A) * X - C (num A r)).leadingCoeff = (den A r : A) := by
  have h : C (den A r : A) * X - C (num A r)
      = C (den A r : A) * X + C (-(num A r)) := by
    rw [map_neg, sub_eq_add_neg]
  rw [h, leadingCoeff_linear (nonZeroDivisors.coe_ne_zero _)]

/-- The `rootMultiplicity` power of the reduced linear factor `C (den A r) * X - C (num A r)`
divides `p` in `A[X]`. This is the `A`-level form of the rational root theorem with
multiplicity, of which `den_pow_rootMultiplicity_dvd_leadingCoeff` is the leading-coefficient
corollary. -/
theorem den_mul_X_sub_C_num_pow_rootMultiplicity_dvd (p : A[X]) (r : K) :
    (C (den A r : A) * X - C (num A r))
      ^ rootMultiplicity r (p.map (algebraMap A K)) ∣ p := by
  let : NormalizedGCDMonoid A := Nonempty.some inferInstance
  refine IsPrimitive.dvd_of_fraction_map_dvd_fraction_map (K := K)
    (IsPrimitive.pow (isPrimitive_den_mul_X_sub_C_num r) _) ?_
  rw [Polynomial.map_pow, map_den_mul_X_sub_C_num, mul_pow]
  have hunit : IsUnit (C (algebraMap A K (den A r : A))
      ^ rootMultiplicity r (p.map (algebraMap A K))) :=
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A r).2))).pow _
  rw [hunit.mul_left_dvd]
  exact pow_rootMultiplicity_dvd _ r

/-- **Rational root theorem with multiplicity.** If `r : K` is a root of
`p : A[X]` over the fraction field `K` of the UFD `A` with multiplicity `m`, then
`(den A r) ^ m` divides the leading coefficient of `p`. Stated unconditionally with
`m = rootMultiplicity r (p.map (algebraMap A K))`; at `m = 1` it recovers
`den_dvd_of_is_root`. -/
theorem den_pow_rootMultiplicity_dvd_leadingCoeff (p : A[X]) (r : K) :
    (den A r : A) ^ rootMultiplicity r (p.map (algebraMap A K))
      ∣ p.leadingCoeff := by
  have h := leadingCoeff_dvd_leadingCoeff
    (den_mul_X_sub_C_num_pow_rootMultiplicity_dvd p r)
  rwa [leadingCoeff_pow, leadingCoeff_den_mul_X_sub_C_num] at h

/-- **Multi-point rational root theorem with multiplicities.** For any
finite set `s` of points of the fraction field, the product over `r ∈ s` of
`(den A r) ^ rootMultiplicity r` divides the leading coefficient of `p`. The
denominators need NOT be pairwise coprime in `A`; the recombination happens on the
polynomial side, where the root factors at distinct points are pairwise coprime
over the field `K`. -/
theorem prod_den_pow_rootMultiplicity_dvd_leadingCoeff (p : A[X]) (s : Finset K) :
    (∏ r ∈ s, (den A r : A) ^ rootMultiplicity r (p.map (algebraMap A K)))
      ∣ p.leadingCoeff := by
  have hgdvd : (∏ r ∈ s, (C (den A r : A) * X - C (num A r))
      ^ rootMultiplicity r (p.map (algebraMap A K))) ∣ p := by
    let : NormalizedGCDMonoid A := Nonempty.some inferInstance
    refine IsPrimitive.dvd_of_fraction_map_dvd_fraction_map (K := K)
      (isPrimitive_prod _ _ fun r _ =>
        IsPrimitive.pow (isPrimitive_den_mul_X_sub_C_num r) _) ?_
    have hmap : (∏ r ∈ s, (C (den A r : A) * X - C (num A r))
          ^ rootMultiplicity r (p.map (algebraMap A K))).map (algebraMap A K)
        = (∏ r ∈ s, C (algebraMap A K (den A r : A))
              ^ rootMultiplicity r (p.map (algebraMap A K)))
            * ∏ r ∈ s, (X - C r) ^ rootMultiplicity r (p.map (algebraMap A K)) := by
      rw [Polynomial.map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [Polynomial.map_pow, map_den_mul_X_sub_C_num, mul_pow]
    have hunit : IsUnit (∏ r ∈ s, C (algebraMap A K (den A r : A))
        ^ rootMultiplicity r (p.map (algebraMap A K))) :=
      Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        fun r _ => (isUnit_C.mpr (isUnit_iff_ne_zero.mpr
          (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A r).2))).pow _
    rw [hmap, hunit.mul_left_dvd]
    refine Finset.prod_dvd_of_coprime ?_ fun r _ => pow_rootMultiplicity_dvd _ r
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
  have hleadeq : (∏ r ∈ s, (C (den A r : A) * X - C (num A r))
        ^ rootMultiplicity r (p.map (algebraMap A K))).leadingCoeff
      = ∏ r ∈ s, (den A r : A) ^ rootMultiplicity r (p.map (algebraMap A K)) := by
    rw [leadingCoeff_prod]
    exact Finset.prod_congr rfl fun r _ => by
      rw [leadingCoeff_pow, leadingCoeff_den_mul_X_sub_C_num]
  rw [← hleadeq]
  exact leadingCoeff_dvd_leadingCoeff hgdvd

namespace UniqueFactorizationMonoid

theorem integer_of_integral {x : K} : IsIntegral A x → IsInteger A x := fun ⟨_, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx

-- See library note [lower instance priority]
instance (priority := 100) instIsIntegrallyClosed : IsIntegrallyClosed A :=
  (isIntegrallyClosed_iff (FractionRing A)).mpr fun {_} => integer_of_integral

end UniqueFactorizationMonoid

end RationalRootTheorem
