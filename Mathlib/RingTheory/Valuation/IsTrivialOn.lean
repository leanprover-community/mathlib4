/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Valuation.Basic


/-!
# Basic lemmas on valuations that are trivial over a base ring

This file contains additional results about `Valuation.IsTrivialOn` which is defined in
`Mathlib.RingTheory.Valuation.Basic`.

In what follows, we consider a `A`-algebra `B` and a valuation `v` over `B` which is trivial on `A`.

## Main results
* `valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`: Let `p` be a polynomial
over `A` evaluated at an element of `B`. We have the equality `v (p.aeval w) = v w ^ p.natDegree`.
* `Valuation.transcendental_of_lt_one`: If `y : B` is such that `y ≠ 0` and `v y < 1`,
then it is transcendental over `A`.
Note that this means that any non zero element of the maximal ideal of `v.valuationSubring` is
transcendental over `A`.
-/

@[expose] public section

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

section Ring

variable (A : Type*) [CommSemiring A]
variable (B : Type*) [Ring B] [Algebra A B] {v : Valuation B Γ} [hv : v.IsTrivialOn A]

namespace Polynomial

lemma valuation_aeval_monomial_eq_valuation_pow (w : B) (n : ℕ) {a : A} (ha : a ≠ 0) :
    v ((monomial n a).aeval w) = (v w) ^ n := by
  simp [← C_mul_X_pow_eq_monomial, map_mul, map_pow, one_mul, hv.eq_one a ha]

theorem valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X (w : B) (hpos : 1 < v w)
    {p : Polynomial A} (hp : p ≠ 0) : v (p.aeval w) = v w ^ p.natDegree := by
  rw [← valuation_aeval_monomial_eq_valuation_pow _ _ _ _ (leadingCoeff_ne_zero.mpr hp)]
  nth_rw 1 [as_sum_range p, map_sum]
  apply Valuation.map_sum_eq_of_lt _ (by simp)
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, Nat.lt_add_one_iff, Finset.mem_singleton,
    ← lt_iff_le_and_ne] at hi
  simp only [← C_mul_X_pow_eq_monomial, map_mul, aeval_C, map_pow, aeval_X, coeff_natDegree]
  by_cases h0 : (p.coeff i) = 0
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      h0, pow_pos (lt_of_le_of_lt zero_le_one hpos) p.natDegree]
  · simp [hv.eq_one p.leadingCoeff (leadingCoeff_ne_zero.mpr hp),
      hv.eq_one _ h0, pow_lt_pow_right₀ hpos hi]

end Polynomial

end Ring

section Field

variable (A : Type*) [CommRing A]
variable (K : Type*) [Field K] [Algebra A K] {v : Valuation K Γ} [hv : v.IsTrivialOn A]

open Polynomial

/--
For a `A`-algebra `K` and a valuation `v` over `K` which is trivial on `A`.
If `y : K` is such that `y ≠ 0` and `v y < 1`, then it is transcendental over `A`. -/
theorem Valuation.transcendental_of_ne_one (y : K) (h0 : y ≠ 0) (hy : v y ≠ 1) :
    Transcendental A y := by
  wlog! hlt : 1 < v y generalizing v y
  · rw [Transcendental, ← IsAlgebraic.inv_iff]
    apply this (v := v) _ (by simpa) (by simpa)
    rw [← val_lt_one_iff _ h0]
    exact lt_of_le_of_ne hlt hy
  simp_all only [ne_eq, Transcendental]
  by_contra!
  replace ha : IsAlgebraic A y := .algebraMap this
  obtain ⟨p, hpnt, hp⟩ := ha
  suffices v y ^ p.natDegree = 0 by simp_all
  rw [← valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X _ _ _ hlt] <;> simp_all

end Field
